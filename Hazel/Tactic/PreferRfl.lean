/-
SPDX-FileCopyrightText: 2026 Mingtong Lin
SPDX-License-Identifier: MIT
-/
module

public meta import Lean
public meta import Lean.Linter

/-!
# Prefer `rfl` linter

Flags `simp` (or `simp only [...]`) that closes a goal which was already
provable by `rfl` (definitional equality).  The check: if the goal before
`simp` was `a = b` where `a` and `b` are definitionally equal, then `rfl`
suffices and `simp` is overkill.
-/

meta section

open Lean Meta Elab Command Linter Server

/-- Prefer `rfl` when `simp` closes a definitionally-equal goal. -/
public register_option linter.hazel.tactic.preferRfl : Bool := {
  defValue := false
  descr := "flag `simp` on goals provable by `rfl`"
}

namespace Hazel.Tactic.PreferRfl

/-- Check if an expression is an equality `a = b` and return `(a, b)`. -/
private def getEqSides? (e : Expr) : Option (Expr × Expr) :=
  match e.eq? with
  | some (_, lhs, rhs) => some (lhs, rhs)
  | none => none

/-- Check if a tactic syntax is a simp variant. -/
private def isSimpTactic (stx : Syntax) : Bool :=
  stx.isOfKind ``Parser.Tactic.simp ||
  stx.isOfKind ``Parser.Tactic.simpAll

/-- The prefer rfl linter. -/
def preferRflLinter : Lean.Linter where run := withSetOptionIn fun _stx => do
  unless getLinterValue linter.hazel.tactic.preferRfl (← getLinterOptions) &&
         (← getInfoState).enabled do
    return
  if (← MonadState.get).messages.hasErrors then return
  let trees ← getInfoTrees
  -- Collect (ContextInfo, TacticInfo) pairs
  let mut tacInfos : Array (ContextInfo × TacticInfo) := #[]
  for tree in trees.toArray do
    tacInfos := tree.foldInfo (init := tacInfos) fun ctx info acc =>
      match info with
      | .ofTacticInfo ti => acc.push (ctx, ti)
      | _ => acc
  for (ctx, ti) in tacInfos do
    -- Skip synthetic syntax (from macro expansion, etc.)
    match ti.stx.getHeadInfo with
    | .original .. => pure ()
    | _ => continue
    -- Only check simp tactics
    unless isSimpTactic ti.stx do continue
    -- Must have closed the goal
    unless ti.goalsAfter.isEmpty do continue
    if ti.goalsBefore.isEmpty then continue
    -- Check if the goal before simp was `a = b` with `a` defeq `b`.
    -- Uses `withReducible` to match `rfl`'s actual semantics — only
    -- kernel-reducible unfolding, not full transparency.  This avoids
    -- false positives where `simp` succeeds via semireducible unfolding
    -- but `rfl` would fail.
    let goal := ti.goalsBefore[0]!
    let isRflGoal ← liftCoreM do
      try
        ctx.runMetaM {} do
          goal.withContext do
            let target ← instantiateMVars (← goal.getType)
            match getEqSides? target with
            | some (lhs, rhs) => withReducible <| isDefEq lhs rhs
            | none => return false
      catch _ => return false
    if isRflGoal then
      Linter.logLint linter.hazel.tactic.preferRfl ti.stx
        m!"Use `rfl` instead of `simp` (goal is definitionally equal)."

initialize addLinter preferRflLinter

end Hazel.Tactic.PreferRfl

end -- meta section
