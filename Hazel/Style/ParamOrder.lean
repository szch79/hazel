/-
SPDX-FileCopyrightText: 2026 Mingtong Lin
SPDX-License-Identifier: MIT
-/
module

public meta import Lean
public meta import Lean.Linter

/-!
# Parameter order linter

Checks that declaration parameters are ordered by first use in the signature.
If parameter group `B` is first needed at an earlier binder than group `A`,
but `A` is declared before `B`, the linter flags the misordering.

Parameters that share a source binder (e.g., `{a b : α}`) are treated as a
single group and move together.  The group's score is the minimum first-use
index across all its members.  Ties keep declaration order.

Respects dependency constraints: if any member of `B` depends on any member
of `A`, then `A` must come before `B` regardless of usage position.

Instance-implicit binders (`[Foo α]`) are skipped entirely — their order is
determined by Lean's typeclass resolution, not the user.
-/

meta section

open Lean Meta Elab Command Linter

/-- Check that parameters are ordered by first use. -/
public register_option linter.hazel.style.paramOrder : Bool := {
  defValue := false
  descr := "check that declaration parameters are ordered by first use"
}

namespace Hazel.Style.ParamOrder

/-- Get the declaration name from a command syntax. -/
private def getDeclName? (stx : Syntax) : Option Name :=
  (stx.find? (·.isOfKind ``Parser.Command.declId)).bind fun declId =>
    match declId[0] with
    | .ident _ _ val _ => some val
    | _ => none

/-- Collect all FVarIds in an expression (no duplicates). -/
private partial def collectFVarIds (e : Expr) : Array FVarId :=
  go e #[]
where
  go (e : Expr) (acc : Array FVarId) : Array FVarId := match e with
    | .fvar id => if acc.contains id then acc else acc.push id
    | .app f a => go a (go f acc)
    | .lam _ d b _ => go b (go d acc)
    | .forallE _ d b _ => go b (go d acc)
    | .letE _ t v b _ => go b (go v (go t acc))
    | .mdata _ e => go e acc
    | .proj _ _ e => go e acc
    | _ => acc

/--
For each binder, compute the index of the first later binder whose type
mentions it.  Returns `n` (= args.size) if only used in the body.
-/
private def computeFirstUseIndex (args : Array Expr) : MetaM (Array Nat) := do
  let n := args.size
  let mut result := Array.replicate n n
  for j in [:n] do
    -- Scan ALL binders' types (including instance-implicit).  Instance binders
    -- like `[Add α]` DO use `α`, and that usage must count toward `α`'s
    -- first-use index.  The instance skip is only in the pair comparison
    -- (we don't flag instance binders themselves as misordered).
    let ldeclJ ← args[j]!.fvarId!.getDecl
    let fvars := collectFVarIds ldeclJ.type
    for fv in fvars do
      for i in [:j] do
        if args[i]!.fvarId! == fv && result[i]! > j then
          result := result.set! i j
  return result

/-- Check if binder `j`'s type mentions binder `i`. -/
private def dependsOn (args : Array Expr) (j i : Nat) : MetaM Bool := do
  let fvars := collectFVarIds (← args[j]!.fvarId!.getDecl).type
  return fvars.any (· == args[i]!.fvarId!)

/-- Find source binder syntax for a given name. -/
private def findBinderSyntax (sigStx : Syntax) (name : Name) :
    Option Syntax := Id.run do
  let binders := sigStx[0]
  for arg in binders.getArgs do
    let names? : Option Syntax :=
      if arg.isOfKind ``Parser.Term.explicitBinder ||
         arg.isOfKind ``Parser.Term.implicitBinder ||
         arg.isOfKind ``Parser.Term.strictImplicitBinder then
        some arg[1]
      else none
    if let some names := names? then
      for nameStx in names.getArgs do
        if nameStx.isIdent && nameStx.getId == name then
          return some arg
    if arg.isOfKind ``Parser.Term.instBinder then
      for child in arg.getArgs do
        if child.isIdent && child.getId == name then
          return some arg
  return none

/--
Compute binder groups from source syntax.  Each group is an array of
telescope indices that share the same source binder node (e.g., `{a b : α}`
is one group containing the indices for `a` and `b`).

Binders not found in source syntax (e.g., auto-inserted by `forallTelescope`
from return-type arrows) are placed in singleton groups.
-/
private def computeBinderGroups (sigStx : Syntax) (args : Array Expr) :
    MetaM (Array (Array Nat)) := do
  let mut groups : Array (Array Nat) := #[]
  let mut i := 0
  while i < args.size do
    let ldecl ← args[i]!.fvarId!.getDecl
    -- Skip instance-implicit binders
    if ldecl.binderInfo.isInstImplicit then
      i := i + 1
      continue
    let binderStx? := findBinderSyntax sigStx ldecl.userName
    -- Collect all subsequent binders that share the same source syntax node
    let mut group := #[i]
    let mut j := i + 1
    while j < args.size do
      let ldeclJ ← args[j]!.fvarId!.getDecl
      if ldeclJ.binderInfo.isInstImplicit then break
      let binderStxJ? := findBinderSyntax sigStx ldeclJ.userName
      match binderStx?, binderStxJ? with
      | some s1, some s2 =>
        -- Same source syntax node means same binder group.
        -- Compare by source position since Syntax BEq may differ on SourceInfo.
        if s1.getPos? == s2.getPos? && s1.getPos?.isSome then
          group := group.push j
          j := j + 1
        else break
      | _, _ => break
    groups := groups.push group
    i := j
  return groups

/-- The argument order linter. -/
def paramOrderLinter : Linter where run := withSetOptionIn fun stx => do
  unless getLinterValue linter.hazel.style.paramOrder (← getLinterOptions) do return
  if (← MonadState.get).messages.hasErrors then return
  unless stx.isOfKind ``Parser.Command.declaration do return
  let some sigStx := stx.find? fun s =>
    s.isOfKind ``Parser.Command.declSig ||
    s.isOfKind ``Parser.Command.optDeclSig
  | return
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
  liftTermElabM do
    forallTelescope ci.type fun args _body => do
      if args.size < 2 then return
      let n := args.size
      let firstUse ← computeFirstUseIndex args
      let groups ← computeBinderGroups sigStx args
      if groups.size < 2 then return
      -- For each group, compute its score: min first-use across members
      let groupScores ← groups.mapM fun group => do
        let mut minFu := n  -- body-only default
        for idx in group do
          let fu := firstUse[idx]!
          if fu < minFu then minFu := fu
        return minFu
      -- Check adjacent group pairs
      for gi in [:groups.size - 1] do
        let gj := gi + 1
        let fuGI := groupScores[gi]!
        let fuGJ := groupScores[gj]!
        -- Skip if either group is body-only
        if fuGI == n || fuGJ == n then continue
        -- Core comparison: is group j first needed earlier than group i?
        let shouldFlag ←
          if fuGJ < fuGI then
            pure true
          else if fuGI < fuGJ then
            pure false
          else
            -- Tied: keep declaration order
            pure false
        unless shouldFlag do continue
        -- Check dependency: if any member of group j depends on any member of group i
        let forced ← groups[gj]!.anyM fun jIdx =>
          groups[gi]!.anyM fun iIdx => dependsOn args jIdx iIdx
        unless forced do
          let nameI := (← args[groups[gi]![0]!]!.fvarId!.getDecl).userName
          let nameJ := (← args[groups[gj]![0]!]!.fvarId!.getDecl).userName
          -- Skip if either binder has no source syntax (auto-generated by elaborator)
          let some targetStx := findBinderSyntax sigStx nameI | continue
          unless (findBinderSyntax sigStx nameJ).isSome do continue
          Linter.logLint linter.hazel.style.paramOrder targetStx
            m!"`{nameI}` is declared before `{nameJ}` but used later.  \
               Consider reordering."

initialize addLinter paramOrderLinter

end Hazel.Style.ParamOrder

end -- meta section
