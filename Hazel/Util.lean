/-
SPDX-FileCopyrightText: 2026 Mingtong Lin
SPDX-License-Identifier: MIT
-/
module

public meta import Lean

/-!
# Shared helpers for Hazel linters
-/

meta section

open Lean

namespace Hazel.Util

/-- Find all syntax nodes in a tree matching a predicate. -/
public partial def findAll (stx : Syntax) (p : Syntax → Bool) : Array Syntax :=
  let found := if p stx then #[stx] else #[]
  match stx with
  | .node _ _ args => found ++ (args.flatMap (findAll · p))
  | _ => found

/-- Collect all import syntax nodes from a module syntax. -/
public partial def getImports (s : Syntax) : Array Syntax :=
  let rest : Array Syntax := (s.getArgs.map getImports).flatten
  if s.isOfKind `Lean.Parser.Module.import then rest.push s else rest

/--
Extract the exact source text spanned by a syntax node.  Unlike
`Syntax.reprint`, this is faithful for docstrings parsed with `doc.verso`,
whose syntax tree tokens do not round-trip to the source text, and it
excludes trailing trivia.
-/
public def sourceText? (stx : Syntax) : Option String :=
  stx.getSubstring? (withLeading := false) (withTrailing := false) |>.map (·.toString)

/-! ## Docstring span-aware iteration

Utilities for iterating over prose characters in docstrings.  Non-prose
spans (escaped characters, backtick code spans, `$`/`$$` math spans, URLs,
and markdown links) are recognized by `SpanSkipper` functions, so new span
kinds can be added by extending the skipper array passed to `forProse`.
-/

/--
A non-prose span recognizer for `forProse`: given the docstring's characters
and an index, return the index just past the span starting there, or `none`
if no span starts at that index.  The returned index must be strictly
greater than the input index; non-advancing results are ignored.
-/
public abbrev SpanSkipper := Array Char → Nat → Option Nat

/-- Skip an escaped character (a backslash and the character after it). -/
public def skipEscape? (chars : Array Char) (i : Nat) : Option Nat :=
  if i < chars.size && chars[i]! == '\\' then some (i + 2) else none

/--
Skip a span delimited by a run of `delim` characters starting at index `i`,
closed by a run of the same length.  Instantiated with a backtick for code
spans and with `$` for math spans, covering both the single and doubled
delimiter forms.  An unclosed span extends to the end of the string.
-/
public def skipDelimRun? (delim : Char) (chars : Array Char) (i : Nat) : Option Nat := Id.run do
  let len := chars.size
  unless i < len && chars[i]! == delim do return none
  let mut j := i
  let mut count := 0
  while j < len && chars[j]! == delim do
    j := j + 1
    count := count + 1
  let mut run := 0
  while j < len do
    if chars[j]! == delim then
      run := run + 1
      if run == count then return some (j + 1)
    else
      run := 0
    j := j + 1
  return some j

/--
If a URL starts at index `i`, return the index after it; otherwise `none`.
A URL is an RFC 3986 scheme (a letter followed by letters, digits, `+`, `-`,
or `.`) followed by `://`, extending to the next whitespace character.
Trailing punctuation deliberately belongs to the span: RFC 3986 allows
sentence-ending characters such as `.` and `?` in URLs, so punctuation
adjacent to a URL cannot be reliably attributed to the surrounding prose.
-/
public def skipUrlSpan? (chars : Array Char) (i : Nat) : Option Nat := Id.run do
  let len := chars.size
  unless i < len && (chars[i]!).isAlpha do return none
  let mut j := i + 1
  while j < len && ((chars[j]!).isAlphanum || chars[j]! == '+' ||
      chars[j]! == '-' || chars[j]! == '.') do
    j := j + 1
  unless j + 2 < len && chars[j]! == ':' && chars[j + 1]! == '/' && chars[j + 2]! == '/' do
    return none
  j := j + 3
  while j < len && !(chars[j]!).isWhitespace do
    j := j + 1
  return some j

/--
Scan a balanced `openC`/`closeC` region starting at index `i` (which must
point to `openC`), respecting escapes.  `openC` and `closeC` must differ.
Returns the index after the closing character, or `none` if the region is
unclosed or contains a blank line (which ends any markdown inline construct).
-/
public def scanDelimited (chars : Array Char) (i : Nat) (openC closeC : Char) :
    Option Nat := Id.run do
  let len := chars.size
  unless i < len && chars[i]! == openC do return none
  let mut j := i + 1
  let mut depth := 1
  while j < len do
    let c := chars[j]!
    if c == '\\' then
      j := j + 2
      continue
    if c == '\n' then
      let mut k := j + 1
      while k < len && (chars[k]! == ' ' || chars[k]! == '\t' || chars[k]! == '\r') do
        k := k + 1
      if k < len && chars[k]! == '\n' then return none
    if c == openC then
      depth := depth + 1
    else if c == closeC then
      depth := depth - 1
      if depth == 0 then return some (j + 1)
    j := j + 1
  return none

/--
If a markdown link starts at index `i`, return the index after it; otherwise
`none`.  A link is a label with balanced nested brackets, optionally
followed by an inline target in parentheses or a bracketed reference name.
Labels hold citations, titles, and similar non-prose material, so prose
checks should not fire inside them.  An unclosed label is not a span.
-/
public def skipLinkSpan? (chars : Array Char) (i : Nat) : Option Nat := Id.run do
  let some j := scanDelimited chars i '[' ']' | return none
  if let some k := scanDelimited chars j '(' ')' then return some k
  if let some k := scanDelimited chars j '[' ']' then return some k
  return some j

/--
If a Verso role header starts at index `i`, return the index after it;
otherwise `none`.  A role header is a braced name with arguments, as in
`{lean}` or `{lean type:="Nat"}`, and Verso only accepts one immediately
before a delimited inline (a code or math span, a bracketed inline sequence,
or another role); a literal brace must be escaped.  The inline that follows
is left to the other skippers, so a docstring opening with a role-annotated
code span starts with non-prose.  Only meaningful under `doc.verso`: in
Markdown docstrings, braces are ordinary prose.
-/
public def skipVersoRoleSpan? (chars : Array Char) (i : Nat) : Option Nat :=
  scanDelimited chars i '{' '}'

/--
The non-prose spans recognized by default: escaped characters, backtick code
spans, `$`/`$$` math spans, URLs, and markdown links.
-/
public def proseSkippers : Array SpanSkipper :=
  #[skipEscape?, skipDelimRun? '`', skipDelimRun? '$', skipUrlSpan?, skipLinkSpan?]

/--
Whether a docstring at the current command is parsed with Verso syntax.
Module docstrings follow `doc.verso.module` when it is set explicitly and
`doc.verso` otherwise; other docstrings follow `doc.verso`.
-/
public def isVersoDoc (opts : Options) (isModuleDoc : Bool) : Bool :=
  if isModuleDoc && opts.contains `doc.verso.module then opts.getBool `doc.verso.module
  else doc.verso.get opts

/--
Iterate over prose characters in a docstring, skipping the non-prose spans
recognized by `skippers` (see `proseSkippers` for the defaults).  Calls `f`
with `(index, char, chars)` for each prose character.  Returns `some a` on
the first `f` that returns `some`.
-/
public def forProse (s : String) (skippers : Array SpanSkipper)
    (f : Nat → Char → Array Char → Option α) : Option α := Id.run do
  let chars := s.toList.toArray
  let len := chars.size
  let mut i := 0
  while i < len do
    let mut next := i
    for sk in skippers do
      if let some j := sk chars i then
        next := j
        break
    if next > i then
      i := next
      continue
    if let some result := f i chars[i]! chars then
      return some result
    i := i + 1
  return none

/-! ## Tactic sequence helpers -/

/--
Collect tactic-level children from a tactic sequence, flattening wrapper
nodes.  The Lean parser wraps tactic sequences in several layers
(`tacticSeq` > `tacticSeq1Indented` > `null` > tactic).  This recurses
through all wrapper kinds and collects leaf tactic nodes.
-/
public partial def collectTactics (stx : Syntax) : Array Syntax :=
  let kind := stx.getKind
  if kind == ``Parser.Tactic.tacticSeq1Indented ||
     kind == ``Parser.Tactic.seq1 ||
     kind == ``Parser.Tactic.tacticSeq ||
     kind == `null then
    stx.getArgs.foldl (init := #[]) fun acc arg =>
      if arg.isAtom || arg.isMissing then acc
      else
        let sub := collectTactics arg
        if sub.isEmpty then acc.push arg else acc ++ sub
  else #[]

end Hazel.Util

end -- meta section
