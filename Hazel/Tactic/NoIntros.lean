/-
SPDX-FileCopyrightText: 2026 Mingtong Lin
SPDX-License-Identifier: MIT
-/
module

public meta import Lean
public meta import Lean.Linter
public meta import Hazel.Util

/-!
# No `intros` linter

Flags `intros x y z` where `intro x y z` is preferred.  Bare `intros` (without
named arguments) is not flagged.
-/

meta section

open Lean Elab Command Linter Hazel.Util

/-- Use `intro` instead of `intros` with named arguments. -/
public register_option linter.hazel.tactic.noIntros : Bool := {
  defValue := false
  descr := "flag `intros` with named arguments (prefer `intro`)"
}

namespace Hazel.Tactic.NoIntros

/-- The `intros` linter. -/
def noIntrosLinter : Lean.Linter where run := withSetOptionIn fun stx => do
  unless getLinterValue linter.hazel.tactic.noIntros (← getLinterOptions) do return
  if (← MonadState.get).messages.hasErrors then return
  -- `intros` syntax: "intros" (ppSpace colGt (ident | hole))*
  -- The `*` produces a `null` node as the second child.
  -- Bare `intros`: null node has 0 children.
  -- `intros x y`: null node has 2 children.
  let nodes := findAll stx fun s =>
    s.isOfKind ``Parser.Tactic.intros &&
    s.getNumArgs >= 2 && s[1].getNumArgs > 0
  for node in nodes do
    Linter.logLint linter.hazel.tactic.noIntros node
      m!"Use `intro` instead of `intros` with named arguments."

initialize addLinter noIntrosLinter

end Hazel.Tactic.NoIntros

end -- meta section
