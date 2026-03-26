/-
SPDX-FileCopyrightText: 2026 Mingtong Lin
SPDX-License-Identifier: MIT
-/
module

public meta import Lean
public meta import Lean.Linter
public meta import Hazel.DocString.Prose

/-!
# Docstring multiline format linter

Multi-line docstrings must have `/--` alone on the first line and `-/` alone
on the last line.  Single-line docstrings pass automatically.
-/

meta section

open Lean Elab Command Linter

/-- Multi-line docstrings must have delimiters alone on their lines. -/
public register_option linter.hazel.docstring.multilineFormat : Bool := {
  defValue := false
  descr := "check multi-line docstring delimiter placement"
}

/-- Single-line docstrings that span multiple lines should be collapsed. -/
public register_option linter.hazel.docstring.collapsible : Bool := {
  defValue := false
  descr := "check that single-paragraph docstrings use single-line format"
}

namespace Hazel.DocString.MultilineFormat

open Hazel.DocString.Prose (getDeclModifiers)

/-- Check multi-line docstring format.  Returns `none` if OK, or a message string if violated. -/
private def checkMultilineFormat (raw : String) : Option String := Id.run do
  let trimmed := raw.trimAscii.toString
  -- Split into lines to check opening/closing delimiter placement.
  let lines := trimmed.splitOn "\n"
  -- Single line (no newlines): always fine
  if lines.length ≤ 1 then return none
  -- Multi-line: nothing after opening delimiter, nothing before closing
  let firstLine := lines[0]!.trimAsciiEnd.toString
  if firstLine != "/--" && firstLine != "/-!" then
    return some "Nothing should follow the opening delimiter on its line."
  let lastLine := lines.getLast!.trimAsciiStart.toString
  if lastLine != "-/" then
    return some "Nothing should precede `-/` on its line."
  return none

/--
Check if a multi-line docstring could be collapsed to a single line.  A
docstring with 3 lines (opener, one line of body, closer) should be written as
`/-- body -/` instead.
-/
private def isCollapsible (raw : String) : Bool := Id.run do
  let trimmed := raw.trimAscii.toString
  -- Split into lines: collapsible = exactly 3 lines (opener, body, closer).
  let lines := trimmed.splitOn "\n"
  if lines.length != 3 then return false
  let firstLine := lines[0]!.trimAsciiEnd.toString
  let lastLine := lines[2]!.trimAsciiStart.toString
  -- Must be well-formed: opener alone, closer alone, single body line
  (firstLine == "/--" || firstLine == "/-!") && lastLine == "-/"

/-- The multiline format linter. -/
def multilineFormatLinter : Lean.Linter where run := withSetOptionIn fun stx => do
  let opts ← getLinterOptions
  let chkFormat := getLinterValue linter.hazel.docstring.multilineFormat opts
  let chkCollapse := getLinterValue linter.hazel.docstring.collapsible opts
  unless chkFormat || chkCollapse do return
  if (← MonadState.get).messages.hasErrors then return
  for declMods in getDeclModifiers stx do
    let docStx := declMods[0][0]
    let some _ := docStx.getPos? | continue
    if docStx.isMissing then continue
    let raw := docStx.reprint.getD ""
    if chkFormat then
      if let some msg := checkMultilineFormat raw then
        Linter.logLint linter.hazel.docstring.multilineFormat docStx m!"{msg}"
    if chkCollapse && isCollapsible raw then
      Linter.logLint linter.hazel.docstring.collapsible docStx
        m!"Single-line docstring should use `/-- ... -/` format."
  if stx.isOfKind ``Parser.Command.moduleDoc then
    -- Use source positions to extract the exact `/-! ... -/` text.
    -- `stx.reprint` includes trailing trivia (whitespace, next-line content)
    -- which breaks the last-line check.
    let fm ← getFileMap
    let some startPos := stx.getPos? | return
    let some endPos := stx.getTailPos? | return
    let raw := { str := fm.source, startPos, stopPos := endPos : Substring.Raw }.toString
    if chkFormat then
      if let some msg := checkMultilineFormat raw then
        Linter.logLint linter.hazel.docstring.multilineFormat stx m!"{msg}"
    if chkCollapse && isCollapsible raw then
      Linter.logLint linter.hazel.docstring.collapsible stx
        m!"Single-line docstring should use `/-- ... -/` format."

initialize addLinter multilineFormatLinter

end Hazel.DocString.MultilineFormat

end -- meta section
