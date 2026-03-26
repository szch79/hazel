/-
SPDX-FileCopyrightText: 2026 Mingtong Lin
SPDX-License-Identifier: MIT
-/
module

public meta import Lean
public meta import Lean.Linter

/-!
# Section/namespace indentation linter

Per style guide, `namespace` and `section` do not increase indent.  All
top-level commands should remain at column 0 regardless of nesting depth.

In Lean 4, `section`/`namespace`/`end` are separate commands — the linter
cannot inspect the block structure.  Instead, it checks that every command
starts at column 0 (since the convention says nesting never adds indent).
-/

meta section

open Lean Elab Command Linter

/-- Commands inside `section`/`namespace` must not be indented. -/
public register_option linter.hazel.style.sectionNoIndent : Bool := {
  defValue := false
  descr := "check that commands are not indented by section/namespace nesting"
}

namespace Hazel.Style.SectionNoIndent

/-- Commands that are expected to be at non-zero column (skip these). -/
private def isSubcommand (stx : Syntax) : Bool :=
  stx.isOfKind ``Parser.Command.eoi

/-- The section indentation linter. -/
def sectionNoIndentLinter : Lean.Linter where run := withSetOptionIn fun stx => do
  unless getLinterValue linter.hazel.style.sectionNoIndent (← getLinterOptions) do return
  if (← MonadState.get).messages.hasErrors then return
  if isSubcommand stx then return
  let some pos := stx.getPos? | return
  let fm ← getFileMap
  let col := (fm.toPosition pos).column
  if col != 0 then
    Linter.logLint linter.hazel.style.sectionNoIndent stx
      m!"Command should not be indented (column {col}, expected 0)"

initialize addLinter sectionNoIndentLinter

end Hazel.Style.SectionNoIndent

end -- meta section
