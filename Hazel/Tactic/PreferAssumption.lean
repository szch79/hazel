/-
SPDX-FileCopyrightText: 2026 Mingtong Lin
SPDX-License-Identifier: MIT
-/
module

public meta import Lean
public meta import Lean.Linter

/-!
# Use assumption linter

Flags `exact h` where `h` is a local hypothesis, suggesting `assumption`
instead.  This is a style preference: `assumption` is shorter and doesn't
break when hypotheses are renamed.
-/

meta section

open Lean Meta Elab Command Linter Server

/-- Prefer `assumption` over `exact h` for local hypotheses. -/
public register_option linter.hazel.tactic.preferAssumption : Bool := {
  defValue := false
  descr := "flag `exact <hypothesis>` (prefer `assumption`)"
}

namespace Hazel.Tactic.PreferAssumption

/-- The use assumption linter. -/
def useAssumptionLinter : Lean.Linter where run := withSetOptionIn fun _stx => do
  unless getLinterValue linter.hazel.tactic.preferAssumption (← getLinterOptions) &&
         (← getInfoState).enabled do
    return
  if (← MonadState.get).messages.hasErrors then return
  let trees ← getInfoTrees
  -- Collect TacticInfo and TermInfo
  let mut tacticInfos : Array TacticInfo := #[]
  let mut termInfos : Array TermInfo := #[]
  for tree in trees.toArray do
    tacticInfos := tree.foldInfo (init := tacticInfos) fun _ctx info acc =>
      match info with
      | .ofTacticInfo ti => acc.push ti
      | _ => acc
    termInfos := tree.foldInfo (init := termInfos) fun _ctx info acc =>
      match info with
      | .ofTermInfo ti => acc.push ti
      | _ => acc
  for ti in tacticInfos do
    -- Skip synthetic syntax (from macro expansion, etc.)
    match ti.stx.getHeadInfo with
    | .original .. => pure ()
    | _ => continue
    unless ti.stx.isOfKind ``Parser.Tactic.exact do continue
    unless ti.goalsAfter.isEmpty do continue
    if ti.goalsBefore.isEmpty then continue
    let args := ti.stx.getArgs
    if args.size < 2 then continue
    let termArg := args[1]!
    unless termArg.isIdent do continue
    -- Check if any TermInfo shows this ident elaborated to an FVar
    let isFVar := termInfos.any fun ti' =>
      ti'.stx.isIdent && ti'.stx.getId == termArg.getId && ti'.expr.isFVar
    if isFVar then
      Linter.logLint linter.hazel.tactic.preferAssumption ti.stx
        m!"Use `assumption` instead of `exact {termArg.getId}`."

initialize addLinter useAssumptionLinter

end Hazel.Tactic.PreferAssumption

end -- meta section
