/-
SPDX-FileCopyrightText: 2026 Mingtong Lin
SPDX-License-Identifier: MIT
-/
module

public meta import Lean
public meta import Lean.Linter
public meta import Hazel.Util

/-!
# No `erw` linter

Flags any use of `erw`.  Prefer `rw` with appropriate lemmas.
-/

meta section

open Lean Elab Command Linter Hazel.Util

/-- Flag `erw` usage. -/
public register_option linter.hazel.tactic.noErw : Bool := {
  defValue := false
  descr := "warn on `erw` usage"
}

namespace Hazel.Tactic.NoErw

/-- The `erw` linter. -/
def noErwLinter : Lean.Linter where run := withSetOptionIn fun stx => do
  unless getLinterValue linter.hazel.tactic.noErw (← getLinterOptions) do return
  if (← MonadState.get).messages.hasErrors then return
  let erwNodes := findAll stx fun s =>
    match s with
    | .atom _ val => val == "erw"
    | _ => false
  for node in erwNodes do
    Linter.logLint linter.hazel.tactic.noErw node
      m!"Avoid `erw`; prefer `rw` with appropriate lemmas."

initialize addLinter noErwLinter

end Hazel.Tactic.NoErw

end -- meta section
