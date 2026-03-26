/-
SPDX-FileCopyrightText: 2026 Mingtong Lin
SPDX-License-Identifier: MIT
-/
module

public meta import Lean
public meta import Lean.Linter

/-!
# Prefer anonymous constructor linter

Flags `constructor; exact a; exact b` patterns where `exact ⟨a, b⟩` is
simpler.  Uses the `InfoTree` to match `constructor` creating N subgoals,
all closed by `exact`.
-/

meta section

open Lean Meta Elab Command Linter Server

/-- Prefer `exact ⟨...⟩` over `constructor` followed by `exact` on each subgoal. -/
public register_option linter.hazel.tactic.preferConstructor : Bool := {
  defValue := false
  descr := "flag `constructor; exact a; exact b` (prefer `exact ⟨a, b⟩`)"
}

namespace Hazel.Tactic.PreferConstructor

/-- The prefer constructor linter. -/
def preferConstructorLinter : Lean.Linter where run := withSetOptionIn fun _stx => do
  unless getLinterValue linter.hazel.tactic.preferConstructor (← getLinterOptions) &&
         (← getInfoState).enabled do
    return
  if (← MonadState.get).messages.hasErrors then return
  let trees ← getInfoTrees
  let fm ← getFileMap
  -- Collect all TacticInfo
  let mut allTacInfos : Array TacticInfo := #[]
  for tree in trees.toArray do
    allTacInfos := tree.foldInfo (init := allTacInfos) fun _ctx info acc =>
      match info with
      | .ofTacticInfo ti => acc.push ti
      | _ => acc
  -- Find `constructor` tactics that create multiple subgoals
  for ti in allTacInfos do
    match ti.stx.getHeadInfo with
    | .original .. => pure ()
    | _ => continue
    unless ti.stx.isOfKind ``Parser.Tactic.constructor do continue
    if ti.goalsAfter.length < 2 then continue
    -- For each goal created by constructor, find the tactic that closes it
    let mut allExact := true
    let mut exactArgs : Array String := #[]
    for goal in ti.goalsAfter do
      -- Find a TacticInfo whose goalsBefore contains this goal and is `exact`
      let mut found := false
      for other in allTacInfos do
        unless other.stx.isOfKind ``Parser.Tactic.exact do continue
        unless other.goalsBefore.any (·.name == goal.name) do continue
        unless other.goalsAfter.isEmpty do continue
        -- Extract the argument source text
        let args := other.stx.getArgs
        if args.size >= 2 then
          let argStx := args[1]!
          let argSrc := match argStx.getPos?, argStx.getTailPos? with
            | some s, some e =>
              ({ str := fm.source, startPos := s, stopPos := e : Substring.Raw }
                ).toString.trimAscii.toString
            | _, _ => (argStx.reprint.getD "?").trimAscii.toString
          exactArgs := exactArgs.push argSrc
          found := true
          break
      unless found do
        allExact := false
        break
    if allExact && exactArgs.size == ti.goalsAfter.length then
      let argsStr := ", ".intercalate exactArgs.toList
      Linter.logLint linter.hazel.tactic.preferConstructor ti.stx
        m!"Use `exact ⟨{argsStr}⟩` instead of `constructor` with individual `exact` calls."

initialize addLinter preferConstructorLinter

end Hazel.Tactic.PreferConstructor

end -- meta section
