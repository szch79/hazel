/-
SPDX-FileCopyrightText: 2026 Mingtong Lin
SPDX-License-Identifier: MIT
-/
module

public meta import Lean
public meta import Lean.Linter

/-!
# Use exact linter

Flags `apply foo` or `refine foo` when they close the goal entirely (zero
remaining goals), suggesting `exact foo` instead.
-/

meta section

open Lean Meta Elab Command Linter Server

/-- Use `exact` when `apply`/`refine` closes the goal. -/
public register_option linter.hazel.tactic.preferExact : Bool := {
  defValue := false
  descr := "flag `apply`/`refine` that close the goal (prefer `exact`)"
}

namespace Hazel.Tactic.PreferExact

/-- The use exact linter. -/
def useExactLinter : Lean.Linter where run := withSetOptionIn fun _stx => do
  unless getLinterValue linter.hazel.tactic.preferExact (← getLinterOptions) &&
         (← getInfoState).enabled do
    return
  if (← MonadState.get).messages.hasErrors then return
  let trees ← getInfoTrees
  let mut tacticInfos : Array TacticInfo := #[]
  for tree in trees.toArray do
    tacticInfos := tree.foldInfo (init := tacticInfos) fun _ctx info acc =>
      match info with
      | .ofTacticInfo ti => acc.push ti
      | _ => acc
  for ti in tacticInfos do
    match ti.stx.getHeadInfo with
    | .original .. => pure ()
    | _ => continue
    let stx := ti.stx
    let isApply := stx.isOfKind ``Parser.Tactic.apply
    let isRefine := stx.isOfKind ``Parser.Tactic.refine
    unless isApply || isRefine do continue
    unless ti.goalsAfter.isEmpty do continue
    if ti.goalsBefore.isEmpty then continue
    let tacName := if isApply then "apply" else "refine"
    -- Extract the argument from source text via FileMap positions
    let args := stx.getArgs
    if args.size < 2 then continue
    let argStx := args[1]!
    let some argStart := argStx.getPos? | continue
    let some argEnd := argStx.getTailPos? | continue
    let fm ← getFileMap
    let arg : String :=
      { str := fm.source, startPos := argStart, stopPos := argEnd : Substring.Raw
        }.toString.trimAscii.toString
    Linter.logLint linter.hazel.tactic.preferExact stx
      m!"Use `exact {arg}` instead of `{tacName}`."

initialize addLinter useExactLinter

end Hazel.Tactic.PreferExact

end -- meta section
