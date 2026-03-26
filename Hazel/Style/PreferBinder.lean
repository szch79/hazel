/-
SPDX-FileCopyrightText: 2026 Mingtong Lin
SPDX-License-Identifier: MIT
-/
module

public meta import Lean
public meta import Lean.Linter

/-!
# Prefer explicit binder linter

Flags top-level `→` arrows and `∀` in declaration type signatures where the
domain is `Prop`.  These should be explicit binders instead.

```lean
-- Preferred
theorem foo (h : P) : Q := by ...

-- Flagged
theorem foo : P → Q := by ...
```

Only flags when the domain is `Prop` (checked via `Meta.isProp`), so data
arrows like `Nat → Nat` are not affected.

Two-phase approach: (1) collect domain syntax nodes from the type syntax,
(2) use the elaborated declaration type via `forallTelescope` to check which
domains are `Prop`.
-/

meta section

open Lean Meta Elab Command Linter Server

/-- Prefer explicit binders over Prop-valued arrows in type signatures. -/
public register_option linter.hazel.style.preferBinder : Bool := {
  defValue := false
  descr := "prefer explicit binders over Prop-valued arrows in signatures"
}

namespace Hazel.Style.PreferBinder

/--
Collect domain syntax nodes of top-level arrows/foralls in a type syntax.
Follows the right spine without descending into domain sides.
-/
private def collectLiftableDomains (typStx : Syntax) : Array Syntax := Id.run do
  let mut stx := typStx
  let mut doms := #[]
  while true do
    if stx.isOfKind ``Parser.Term.arrow then
      doms := doms.push stx[0]
      stx := stx[2]
    else if stx.isOfKind ``Parser.Term.forall then
      let typeSpecOpt := stx[2]
      if let some ts := typeSpecOpt.getArgs.find? fun s =>
        s.isOfKind ``Parser.Term.typeSpec then
        doms := doms.push ts[1]
      for arg in stx.getArgs do
        if arg.isOfKind ``Parser.Term.explicitBinder then
          if arg.getNumArgs >= 4 then
            doms := doms.push arg[3]
      stx := stx[4]
    else
      break
  return doms

/-- Get the declaration name from a command syntax. -/
private def getDeclName? (stx : Syntax) : Option Name :=
  let declId? := stx.find? fun s => s.isOfKind ``Parser.Command.declId
  declId?.bind fun declId =>
    match declId[0] with
    | .ident _ _ val _ => some val
    | _ => none

/--
Count the number of individual binder names in the source signature.
A group like `(P Q R : Prop)` counts as 3.

Assumes binder syntax:
- `explicitBinder`: `["(", names, ":", type, ")"]` — `arg[1]` = names null node
- `implicitBinder`: `["{", names, ":", type, "}"]` — `arg[1]` = names null node
- `instBinder`: `["[", ...]` — always 1 binder
-/
private def countSourceBinders (sigStx : Syntax) : Nat := Id.run do
  let binders := sigStx[0]  -- first child of declSig/optDeclSig is the binders null node
  let mut count := 0
  for arg in binders.getArgs do
    if arg.isOfKind ``Parser.Term.explicitBinder then
      count := count + arg[1].getNumArgs
    else if arg.isOfKind ``Parser.Term.implicitBinder ||
            arg.isOfKind ``Parser.Term.strictImplicitBinder then
      count := count + arg[1].getNumArgs
    else if arg.isOfKind ``Parser.Term.instBinder then
      count := count + 1
  return count

/-- The prefer-binder linter. -/
def preferBinderLinter : Linter where run := withSetOptionIn fun stx => do
  unless getLinterValue linter.hazel.style.preferBinder (← getLinterOptions) do return
  if (← MonadState.get).messages.hasErrors then return
  unless stx.isOfKind ``Parser.Command.declaration do return
  -- Find the signature
  let some sigStx := stx.find? fun s =>
    s.isOfKind ``Parser.Command.declSig ||
    s.isOfKind ``Parser.Command.optDeclSig
  | return
  -- Find the type inside the signature
  let some typeSpec := sigStx.find? fun s => s.isOfKind ``Parser.Term.typeSpec
  | return
  let typeNode := typeSpec[1]
  -- Collect domain syntax nodes
  let doms := collectLiftableDomains typeNode
  if doms.isEmpty then return
  -- Get the declaration name and look it up
  let some declName := getDeclName? stx | return
  let env ← getEnv
  let resolvedName? ← try
    some <$> resolveGlobalConstNoOverload (mkIdent declName)
  catch _ => pure none
  let ns ← getCurrNamespace
  let some ci := resolvedName?.bind env.find?
    |>.or (env.find? (ns ++ declName))
    |>.or (env.find? declName)
  | return
  -- Count source binders
  let sourceBinderCount := countSourceBinders sigStx
  -- Walk the elaborated type with forallTelescope
  liftTermElabM do
    forallTelescope ci.type fun args _body => do
      let mut arrowIdx := 0
      for i in [:args.size] do
        let ldecl ← args[i]!.fvarId!.getDecl
        -- Skip non-default binders (implicit, instance, etc.)
        unless ldecl.binderInfo == .default do continue
        -- Skip binders that correspond to source explicit binders
        if i < sourceBinderCount then continue
        -- This is a default binder from the return type (arrow/forall)
        let isProp ← Meta.isProp ldecl.type
        if isProp && arrowIdx < doms.size then
          let dom := doms[arrowIdx]!
          let domStr := (dom.reprint.getD "?").trimAscii.toString
          Linter.logLint linter.hazel.style.preferBinder dom
            m!"`{domStr}` could be an explicit argument instead."
        arrowIdx := arrowIdx + 1

initialize addLinter preferBinderLinter

end Hazel.Style.PreferBinder

end -- meta section
