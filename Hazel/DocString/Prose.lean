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
-/

meta section

open Lean Elab Command Linter Hazel.Util

/-! ## Options -/

/-- Two spaces after sentence-ending punctuation (`.`, `!`, `?`). -/
public register_option linter.hazel.docstring.doubleSpace : Bool := {
  defValue := false
  descr := "check for two spaces after sentence-ending punctuation in docstrings"
}

/-- No non-ASCII characters in prose (backtick spans and `$...$` math excluded). -/
public register_option linter.hazel.docstring.noUnicodeProse : Bool := {
  defValue := false
  descr := "check for non-ASCII characters in docstring prose"
}

/-- Docstring starts with an uppercase letter or backtick. -/
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

/-! ## Helpers -/

/-- Check if a character is sentence-ending punctuation. -/
private def isSentenceEnd (c : Char) : Bool :=
  c == '.' || c == '!' || c == '?'

/-- Check for single space after sentence-ending punctuation followed by uppercase. -/
private def hasSingleSpaceViolation (s : String) : Bool :=
  (forProse s fun i c chars =>
    if isSentenceEnd c && i + 2 < chars.size then
      let next1 := chars[i + 1]!
      let next2 := chars[i + 2]!
      -- Skip numbered list markers like "1. Foo" (digit before the period).
      let prev? := if i > 0 then some chars[i - 1]! else none
      if prev?.any Char.isDigit then none
      else if next1 == ' ' && next2.isUpper then some () else none
    else none).isSome

/-- Check for non-ASCII characters in prose (respects `allowedUnicodeRef`). -/
private def hasUnicodeProseViolation (s : String) (allowed : Array Char) : Bool :=
  (forProse s fun _ c _ =>
    if c.val > 127 && !allowed.contains c then some () else none).isSome

/-- Check that the first non-whitespace character is uppercase or a backtick. -/
private def hasCapitalStartViolation (s : String) : Bool := Id.run do
  for c in s.toList do
    if c == ' ' || c == '\n' || c == '\r' || c == '\t' then continue
    -- '`' for code spans, '#' for markdown headers (# Section)
    if c == '`' || c == '#' || c.isUpper then return false
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
  -- Check all docstrings (declarations, syntax, macro, etc.)
  for docStx in getDocComments stx do
    let some _ := docStx.getPos? | continue
    if docStx.isMissing then continue
    let docString ← try getDocStringText ⟨docStx⟩ catch _ => continue
    if docString.trimAscii.isEmpty then continue
    if chkDouble && hasSingleSpaceViolation docString then
      Linter.logLint linter.hazel.docstring.doubleSpace docStx
        m!"Use two spaces after sentence-ending punctuation in docstrings."
    if chkUnicode && hasUnicodeProseViolation docString allowedChars then
      Linter.logLint linter.hazel.docstring.noUnicodeProse docStx
        m!"Avoid non-ASCII characters in docstring prose; use backtick spans for code."
    if chkCapital && hasCapitalStartViolation docString then
      Linter.logLint linter.hazel.docstring.capitalStart docStx
        m!"Docstrings should start with an uppercase letter."
  -- Check module docstrings
  if stx.isOfKind ``Parser.Command.moduleDoc then
    let body := stx[1]
    let docString := match body with
      | .atom _ val => String.Pos.Raw.extract val 0 (val.rawEndPos.unoffsetBy ⟨2⟩)
      | .node _ _ _ => match body[0] with
        | .atom _ val => String.Pos.Raw.extract val 0 (val.rawEndPos.unoffsetBy ⟨2⟩)
        | _ => ""
      | _ => ""
    if docString.trimAscii.isEmpty then return
    if chkDouble && hasSingleSpaceViolation docString then
      Linter.logLint linter.hazel.docstring.doubleSpace stx
        m!"Use two spaces after sentence-ending punctuation in module docstrings."
    if chkUnicode && hasUnicodeProseViolation docString allowedChars then
      Linter.logLint linter.hazel.docstring.noUnicodeProse stx
        m!"Avoid non-ASCII characters in module docstring prose."
    if chkCapital && hasCapitalStartViolation docString then
      Linter.logLint linter.hazel.docstring.capitalStart stx
        m!"Module docstrings should start with an uppercase letter."

initialize addLinter proseLinter

end Hazel.DocString.Prose

end -- meta section
