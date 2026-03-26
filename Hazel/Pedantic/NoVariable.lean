/-
SPDX-FileCopyrightText: 2026 Mingtong Lin
SPDX-License-Identifier: MIT
-/
module

public meta import Lean
public meta import Lean.Linter

/-!
# No `variable` linter

Flags `variable` commands.  Prefer full explicit signatures.
-/

meta section

open Lean Elab Command Linter

/-- Flag `variable` commands. -/
public register_option linter.hazel.pedantic.noVariable : Bool := {
  defValue := false
  descr := "warn on `variable` commands"
}

namespace Hazel.Pedantic.NoVariable

/-- The `variable` linter. -/
def noVariableLinter : Lean.Linter where run := withSetOptionIn fun stx => do
  unless getLinterValue linter.hazel.pedantic.noVariable (← getLinterOptions) do return
  if (← MonadState.get).messages.hasErrors then return
  if stx.isOfKind ``Parser.Command.variable then
    Linter.logLint linter.hazel.pedantic.noVariable stx
      m!"Avoid `variable` declarations; prefer full explicit signatures."

initialize addLinter noVariableLinter

end Hazel.Pedantic.NoVariable

end -- meta section
