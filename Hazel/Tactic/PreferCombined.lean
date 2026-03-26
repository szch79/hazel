/-
SPDX-FileCopyrightText: 2026 Mingtong Lin
SPDX-License-Identifier: MIT
-/
module

public meta import Lean
public meta import Lean.Linter
public meta import Hazel.Util

/-!
# Combine assumption linter

Flags `simp [...]; assumption` and `rw [...]; assumption`, suggesting
`simpa [...]` and `rwa [...]` respectively.

Works on the pre-expansion syntax tree: finds tactic sequence nodes and
checks for consecutive rw/simp + assumption pairs.
-/

meta section

open Lean Elab Command Linter Hazel.Util

/-- Use `simpa` instead of `simp; assumption`. -/
public register_option linter.hazel.tactic.preferSimpA : Bool := {
  defValue := false
  descr := "flag `simp; assumption` (prefer `simpa`)"
}

/-- Use `rwa` instead of `rw; assumption`. -/
public register_option linter.hazel.tactic.preferRwA : Bool := {
  defValue := false
  descr := "flag `rw; assumption` (prefer `rwa`)"
}

namespace Hazel.Tactic.PreferCombined

/-- Check if a syntax node is `assumption` (kind or atom). -/
private def isAssumptionStx (stx : Syntax) : Bool :=
  stx.isOfKind ``Parser.Tactic.assumption ||
  (match stx with
   | .atom _ val => val == "assumption"
   | _ => false) ||
  -- Might be wrapped: check children recursively for the atom
  (stx.getArgs.any fun a => match a with
    | .atom _ val => val == "assumption"
    | _ => false)

/-- Check if a syntax node is a rw tactic (rwSeq kind). -/
private def isRwStx (stx : Syntax) : Bool :=
  stx.isOfKind `Lean.Parser.Tactic.rwSeq

/-- Check if a syntax node is a simp tactic. -/
private def isSimpStx (stx : Syntax) : Bool :=
  stx.isOfKind ``Parser.Tactic.simp ||
  stx.isOfKind ``Parser.Tactic.simpAll

/-- The combine assumption linter. -/
def combineAssumptionLinter : Lean.Linter where run := withSetOptionIn fun stx => do
  let opts ← getLinterOptions
  let chkSimpa := getLinterValue linter.hazel.tactic.preferSimpA opts
  let chkRwa := getLinterValue linter.hazel.tactic.preferRwA opts
  unless chkSimpa || chkRwa do return
  if (← MonadState.get).messages.hasErrors then return
  -- Find all tactic sequence nodes in the command syntax
  let seqNodes := findAll stx fun s =>
    s.isOfKind ``Parser.Tactic.tacticSeq1Indented ||
    s.isOfKind ``Parser.Tactic.seq1
  for seqNode in seqNodes do
    -- Filter out empty/null wrapper nodes
    let tactics := (collectTactics seqNode).filter fun t =>
      !t.isMissing && t.getKind != `null
    -- Check consecutive pairs
    for i in [:tactics.size - 1] do
      let cur := tactics[i]!
      let next := tactics[i + 1]!
      if !isAssumptionStx next then continue
      if chkRwa && isRwStx cur then
        Linter.logLint linter.hazel.tactic.preferRwA cur
          m!"Use `rwa` instead of `rw; assumption`."
      if chkSimpa && isSimpStx cur then
        Linter.logLint linter.hazel.tactic.preferSimpA cur
          m!"Use `simpa` instead of `simp; assumption`."

initialize addLinter combineAssumptionLinter

end Hazel.Tactic.PreferCombined

end -- meta section
