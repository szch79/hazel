/-
SPDX-FileCopyrightText: 2026 Mingtong Lin
SPDX-License-Identifier: MIT
-/
module

public meta import Lean
public meta import Lean.Linter
public meta import Hazel.Util

/-!
# Docstring prose linters

Checks on docstring prose content:

- `linter.hazel.docstring.doubleSpace`: two spaces after sentence-ending punctuation
- `linter.hazel.docstring.noUnicodeProse`: no non-ASCII outside backtick/math spans
- `linter.hazel.docstring.capitalStart`: docstring starts with uppercase or backtick

Under `doc.verso`, role headers such as `{lean}` before a code span are also
treated as non-prose.
-/

meta section

open Lean Elab Command Linter Hazel.Util

/-! ## Options -/

/--
Two spaces after sentence-ending punctuation (`.`, `!`, `?`).  Non-prose
spans (code, math, URLs, markdown links) are exempt: a period inside a link
label or right after a URL is not sentence punctuation.
-/
public register_option linter.hazel.docstring.doubleSpace : Bool := {
  defValue := false
  descr := "check for two spaces after sentence-ending punctuation in docstrings"
}

/-- No non-ASCII characters in prose (code, math, URLs, and markdown links excluded). -/
public register_option linter.hazel.docstring.noUnicodeProse : Bool := {
  defValue := false
  descr := "check for non-ASCII characters in docstring prose"
}

/-- Docstring starts with an uppercase letter, a header, or a non-prose span. -/
public register_option linter.hazel.docstring.capitalStart : Bool := {
  defValue := false
  descr := "check that docstrings start with an uppercase letter"
}

namespace Hazel.DocString.Prose

/-! ## Configuration -/

/--
Characters allowed in docstring prose despite being non-ASCII.
Empty by default.  Override in your project's init module:

```
meta initialize Hazel.DocString.Prose.allowedUnicodeRef.modify (· ++ #['—', '–'])
```
-/
public initialize allowedUnicodeRef : IO.Ref (Array Char) ← IO.mkRef #[]

/--
Non-prose span skippers applied in addition to `Hazel.Util.proseSkippers`
(escapes, backtick code, math, URLs, markdown links).  Prose checks skip
the spans these recognize.  Extend in your project's init module:

```
meta initialize Hazel.DocString.Prose.extraSkippersRef.modify (·.push mySkipper)
```
-/
public initialize extraSkippersRef : IO.Ref (Array SpanSkipper) ← IO.mkRef #[]

/-! ## Helpers -/

/-- Check if a character is sentence-ending punctuation. -/
private def isSentenceEnd (c : Char) : Bool :=
  c == '.' || c == '!' || c == '?'

/-- Check for single space after sentence-ending punctuation followed by uppercase. -/
private def hasSingleSpaceViolation (s : String) (skippers : Array SpanSkipper) : Bool :=
  (forProse s skippers fun i c chars =>
    if isSentenceEnd c && i + 2 < chars.size then
      let next1 := chars[i + 1]!
      let next2 := chars[i + 2]!
      -- Skip numbered list markers like "1. Foo" (digit before the period).
      let prev? := if i > 0 then some chars[i - 1]! else none
      if prev?.any Char.isDigit then none
      else if next1 == ' ' && next2.isUpper then some () else none
    else none).isSome

/-- Check for non-ASCII characters in prose (respects `allowedUnicodeRef`). -/
private def hasUnicodeProseViolation (s : String) (allowed : Array Char)
    (skippers : Array SpanSkipper) : Bool :=
  (forProse s skippers fun _ c _ =>
    if c.val > 127 && !allowed.contains c then some () else none).isSome

/-- Check that the first non-whitespace character is uppercase, a header, or starts a non-prose span. -/
private def hasCapitalStartViolation (s : String) (skippers : Array SpanSkipper) : Bool := Id.run do
  let chars := s.toList.toArray
  let mut i := 0
  while i < chars.size do
    let c := chars[i]!
    if c == ' ' || c == '\n' || c == '\r' || c == '\t' then
      i := i + 1
      continue
    -- '#' for markdown headers (# Section)
    if c == '#' || c.isUpper then return false
    -- A docstring may open with non-prose (a code span, URL, or link);
    -- there is no capitalization to demand there.
    if skippers.any (· chars i |>.isSome) then return false
    return true
  return false

/-- Extract `declModifiers` syntax nodes from a command syntax. -/
public def getDeclModifiers : Syntax → Array Syntax
  | s@(.node _ kind args) =>
    (if kind == ``Parser.Command.declModifiers then #[s] else #[]) ++
      args.flatMap getDeclModifiers
  | _ => #[]

/-- Collect all `docComment` syntax nodes from a command syntax tree. -/
public def getDocComments : Syntax → Array Syntax
  | s@(.node _ kind args) =>
    (if kind == ``Parser.Command.docComment then #[s] else #[]) ++
      args.flatMap getDocComments
  | _ => #[]

/--
Extract the body text (between the delimiters) of a `docComment` or
`moduleDoc` node: both kinds have a 3-byte opener and a 2-byte closer.  The
text is extracted from source positions rather than the syntax tree: with
`doc.verso`, the body parses into a markup tree that does not round-trip to
the source text (and `getDocStringText` throws on it).
-/
public def docBodyText? (stx : Syntax) : Option String := do
  let ss ← stx.getSubstring? (withLeading := false) (withTrailing := false)
  return { ss with startPos := ss.startPos.offsetBy ⟨3⟩,
                   stopPos := ss.stopPos.unoffsetBy ⟨2⟩ }.toString

/-! ## Linter -/

/-- The docstring prose linter. -/
def proseLinter : Lean.Linter where run := withSetOptionIn fun stx => do
  let opts ← getLinterOptions
  let chkDouble := getLinterValue linter.hazel.docstring.doubleSpace opts
  let chkUnicode := getLinterValue linter.hazel.docstring.noUnicodeProse opts
  let chkCapital := getLinterValue linter.hazel.docstring.capitalStart opts
  unless chkDouble || chkUnicode || chkCapital do return
  if (← MonadState.get).messages.hasErrors then return
  let allowedChars ← allowedUnicodeRef.get
  let extraSkippers ← extraSkippersRef.get
  let versoOpts ← getOptions
  -- Under Verso, `{role}` headers annotate the inline that follows them and
  -- are not prose; in Markdown, braces are.
  let skippersFor (isModuleDoc : Bool) : Array SpanSkipper :=
    proseSkippers ++
      (if isVersoDoc versoOpts isModuleDoc then #[skipVersoRoleSpan?] else #[]) ++
      extraSkippers
  -- Check all docstrings (declarations, syntax, macro, etc.)
  let skippers := skippersFor false
  for docStx in getDocComments stx do
    let some docString := docBodyText? docStx | continue
    if docString.trimAscii.isEmpty then continue
    if chkDouble && hasSingleSpaceViolation docString skippers then
      Linter.logLint linter.hazel.docstring.doubleSpace docStx
        m!"Use two spaces after sentence-ending punctuation in docstrings."
    if chkUnicode && hasUnicodeProseViolation docString allowedChars skippers then
      Linter.logLint linter.hazel.docstring.noUnicodeProse docStx
        m!"Avoid non-ASCII characters in docstring prose; use backtick spans for code."
    if chkCapital && hasCapitalStartViolation docString skippers then
      Linter.logLint linter.hazel.docstring.capitalStart docStx
        m!"Docstrings should start with an uppercase letter."
  -- Check module docstrings
  if stx.isOfKind ``Parser.Command.moduleDoc then
    let some docString := docBodyText? stx | return
    if docString.trimAscii.isEmpty then return
    let skippers := skippersFor true
    if chkDouble && hasSingleSpaceViolation docString skippers then
      Linter.logLint linter.hazel.docstring.doubleSpace stx
        m!"Use two spaces after sentence-ending punctuation in module docstrings."
    if chkUnicode && hasUnicodeProseViolation docString allowedChars skippers then
      Linter.logLint linter.hazel.docstring.noUnicodeProse stx
        m!"Avoid non-ASCII characters in module docstring prose."
    if chkCapital && hasCapitalStartViolation docString skippers then
      Linter.logLint linter.hazel.docstring.capitalStart stx
        m!"Module docstrings should start with an uppercase letter."

initialize addLinter proseLinter

end Hazel.DocString.Prose

end -- meta section
