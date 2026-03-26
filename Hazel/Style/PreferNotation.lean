/-
SPDX-FileCopyrightText: 2026 Mingtong Lin
SPDX-License-Identifier: MIT
-/
module

public meta import Lean
public meta import Lean.Linter
public meta import Lean.PrettyPrinter
public meta import Lean.Meta.Tactic.TryThis

/-!
# Use notation linter

Flags cases where a registered notation could be used but the user wrote an
explicit function application instead.  For example, `And p q` should be written
as `p ∧ q`, and `HAdd.hAdd a b` should be written as `a + b`.

The check: for each `TermInfo`, delaborate the `Expr` and compare the outermost
syntax kind with the source syntax kind.  If they differ (delab chose a notation
but source used a plain application), suggest the notation form.
-/

meta section

open Lean Meta Elab Command Linter Server PrettyPrinter

/-- Suggest registered notations where applicable. -/
public register_option linter.hazel.style.preferNotation : Bool := {
  defValue := false
  descr := "suggest using registered notations where applicable"
}

namespace Hazel.Style.PreferNotation

/--
Check if the delab output uses a different syntax kind than the source.
Returns the reprinted delab syntax if it differs, or `none` if they match.
-/
private def checkNotation (e : Expr) (srcStx : Syntax) :
    MetaM (Option String) := do
  -- Only check if source is a plain function application
  unless srcStx.isOfKind ``Parser.Term.app do return none
  -- The function head must be a named constant
  let fn := e.getAppFn
  let .const _ _ := fn | return none
  -- Skip applications with lambda arguments before delab (which is expensive).
  -- Delab will produce compound forms (do blocks, fun bodies) that aren't
  -- useful notation suggestions.  Cheap check: O(1) per arg.
  if e.getAppArgs.any (·.isLambda) then return none
  -- Delab the expression
  let delabStx ← delab e
  -- Only flag if delab chose a DIFFERENT syntax kind (i.e., a notation)
  if srcStx.getKind == delabStx.raw.getKind then return none
  -- The delab kind should be a notation, not just a different app or dot notation
  if delabStx.raw.isOfKind ``Parser.Term.app then return none
  if delabStx.raw.isOfKind ``Parser.Term.proj then return none
  if delabStx.raw.isOfKind ``Parser.Term.fun then return none
  -- Check reprint for multi-line (free — already computed by delab).
  -- Real notations (`a + b`, `¬p`) are always single-line.
  let raw := (delabStx.raw.reprint.getD "").trimAscii.toString
  if raw.isEmpty || raw.contains '\n' then return none
  -- Only now call ppExpr for clean formatting (expensive, but rare at this point)
  let suggestion := (← PrettyPrinter.ppExpr e).pretty.trimAscii.toString
  if suggestion.isEmpty then return none
  return some suggestion

/-- The use notation linter. -/
def useNotationLinter : Lean.Linter where run := withSetOptionIn fun _stx => do
  unless getLinterValue linter.hazel.style.preferNotation (← getLinterOptions) &&
         (← getInfoState).enabled do
    return
  if (← MonadState.get).messages.hasErrors then return
  let trees ← getInfoTrees
  let mut termInfos : Array (ContextInfo × TermInfo) := #[]
  for tree in trees.toArray do
    termInfos := tree.foldInfo (init := termInfos) fun ctx info acc =>
      match info with
      | .ofTermInfo ti => acc.push (ctx, ti)
      | _ => acc
  for (ctx, ti) in termInfos do
    if ti.isBinder then continue
    let some _ := ti.stx.getPos? | continue
    -- Only check explicit function applications
    unless ti.stx.isOfKind ``Parser.Term.app do continue
    -- Skip @-prefixed explicit calls — user deliberately used explicit form
    if (ti.stx.find? (fun s =>
      s.isOfKind ``Parser.Term.explicit)).isSome then continue
    -- Skip calls with named arguments (e.g., `(L₂ := L₂)`) — notation may
    -- not support them
    if (ti.stx.find? (fun s =>
      s.isOfKind ``Parser.Term.namedArgument)).isSome then continue
    -- Skip synthetic syntax (from macro expansion — user already wrote notation)
    match ti.stx.getHeadInfo with
    | .original .. => pure ()
    | _ => continue
    -- The source must contain the function name literally — if the user wrote
    -- notation that macro-expanded to this application, the name won't be there
    let fn := ti.expr.getAppFn
    let .const fnName _ := fn | continue
    -- Check source syntax contains the function name as an identifier.
    -- The source ident may be partially qualified (e.g., `AndOp.and`) while
    -- the Expr constant is fully qualified (e.g., `MyLib.AndOp.and`), so we
    -- check suffix matching.
    unless (ti.stx.find? (fun s =>
      s.isIdent && (s.getId == fnName || fnName.isSuffixOf s.getId ||
                    s.getId.isSuffixOf fnName))).isSome do continue
    let result ← liftCoreM do
      try ti.runMetaM ctx (checkNotation ti.expr ti.stx)
      catch _ => return none
    let some suggestion := result | continue
    Linter.logLint linter.hazel.style.preferNotation ti.stx
      m!"Use notation: `{suggestion}`"
    liftCoreM <| Lean.Meta.Tactic.TryThis.addSuggestion ti.stx
      { suggestion := .string suggestion
        toCodeActionTitle? := some fun s => s!"Use notation: {s}" }
      (origSpan? := ti.stx)
      (header := "Try this:")

initialize addLinter useNotationLinter

end Hazel.Style.PreferNotation

end -- meta section
