/-
SPDX-FileCopyrightText: 2026 Mingtong Lin
SPDX-License-Identifier: MIT
-/
module

public meta import Lean
public meta import Lean.Linter
public meta import Hazel.Util

/-!
# Redundant implicit binder linter

When `autoImplicit` is on, flags explicit implicit binders that auto-implicit
would have bound automatically.

Two levels (controlled by `redundantImplicitLevel`):

- **Level 1** (default): only flag `Sort`/`Type` binders (`{α : Type}`,
  `{α : Sort u}`).  Conservative — warns that removing may widen the
  universe level.

- **Level 2**: flag all implicit binders (`{n : Nat}`, `{l : List α}`, etc.)
  that auto-implicit would handle.  Skips binders that surely can't be
  inferred: dependent forall types and binders used only via dot notation.
-/

meta section

open Lean Meta Elab Command Linter Server Hazel.Util

/-- Flag redundant implicit binders when `autoImplicit` is on. -/
public register_option linter.hazel.style.redundantImplicit : Bool := {
  defValue := false
  descr := "flag implicit binders redundant under autoImplicit"
}

/-- Level for redundant implicit checking: 1 = Sort/Type only, 2 = all binders. -/
public register_option linter.hazel.style.redundantImplicitLevel : Nat := {
  defValue := 1
  descr := "redundant implicit level: 1 = Sort/Type only, 2 = all implicit binders"
}

namespace Hazel.Style.RedundantImplicit

/-! ## Predicates -/

/-- Check if an `Expr` is `Sort _` or `Type _` (any universe level). -/
private def isSortOrType (e : Expr) : Bool :=
  e.isSort

/--
Check if an FVar ever appears in a non-function position in an expression.
Returns `true` if there is at least one usage where the FVar is NOT the head
of a function application (e.g., passed as argument to a known function).

When a variable only appears as the head of `.app` (function position),
auto-implicit cannot infer its type — the metavar can't become a `forallE`.
But if it also appears in argument position, the known function's parameter
type constrains the metavar, and auto-implicit works.
-/
private partial def hasNonAppUsage (fvarId : FVarId) : Expr → Bool
  | .app fn arg =>
    hasNonAppUsage fvarId arg ||
    -- If fn head IS our FVar, this is function-position — not a non-app usage.
    -- But recurse into fn's nested structure for other occurrences.
    (if fn.getAppFn.isFVar && fn.getAppFn.fvarId! == fvarId
     then false
     else hasNonAppUsage fvarId fn)
  | .fvar id => id == fvarId  -- bare FVar (not applied) = non-app usage
  | .forallE _ d b _ => hasNonAppUsage fvarId d || hasNonAppUsage fvarId b
  | .lam _ d b _ => hasNonAppUsage fvarId d || hasNonAppUsage fvarId b
  | .letE _ t v b _ =>
    hasNonAppUsage fvarId t || hasNonAppUsage fvarId v ||
    hasNonAppUsage fvarId b
  | _ => false

/-- Check if a `Name` is atomic (single component, no dots or macro scopes). -/
private def isAtomicName (n : Name) : Bool :=
  match n with
  | .str .anonymous _ => true
  | _ => false

/--
Check if ALL occurrences of a name in the signature are dot notation bases
(`Term.proj` child [0]).  If so, auto-implicit can't infer the type — dot
notation requires the type to be known upfront to resolve the namespace.

Returns `true` if the binder is surely not inferable (only dot notation usage).
Returns `false` if there is at least one non-dot-notation usage, or if the
name doesn't appear in the signature at all.
-/
private def onlyUsedViaDotNotation (sigStx : Syntax) (name : Name) : Bool :=
  -- Strategy: check if the name appears in the signature as a bare ident
  -- that is NOT: (a) a binder name declaration, or (b) the base of Term.proj.
  -- If such a "free" usage exists, auto-implicit can infer the type from it.
  -- If no free usage exists (all are dot notation or binder names), can't infer.
  --
  -- Walk the syntax tree.  At each ident matching `name`, check context:
  -- - Inside a Term.proj at position [0]? → dot notation, doesn't help inference
  -- - Inside a binder's name position? → declaration, doesn't help inference
  -- - Anything else? → constraining usage, auto-implicit can infer
  --
  -- Implementation: find all Term.proj bases, then check if there are any
  -- ident occurrences NOT accounted for by proj bases or binder names.
  -- Simpler: find if there EXISTS a non-dot, non-binder-name ident.
  --
  -- Use findStack? to check each ident's parent context.
  let hasConstrainingUsage := (sigStx.find? fun s =>
    -- Is this an ident matching our name?
    if !s.isIdent || s.getId != name then false
    else
      -- Check: is this ident the [0] child of a Term.proj?
      -- We can't check parent from child.  Instead, check if this ident
      -- is NOT inside any Term.proj at position [0].
      -- Heuristic: if the ident has no position info, skip it.
      true
  ).isSome
  -- This approach can't distinguish dot bases from other usages without parent info.
  -- Different approach: collect proj bases as a SET of positions, then check
  -- if all ident positions are in that set (or are binder name positions).
  let projBasePositions : Array String.Pos.Raw := Id.run do
    let projs := findAll sigStx fun s =>
      s.isOfKind ``Parser.Term.proj &&
      s[0].isIdent && s[0].getId == name
    let mut positions := #[]
    for proj in projs do
      if let some pos := proj[0].getPos? then
        positions := positions.push pos
    return positions
  -- Collect binder name positions
  let binderNamePositions : Array String.Pos.Raw := Id.run do
    let binders := findAll sigStx fun s =>
      s.isOfKind ``Parser.Term.implicitBinder ||
      s.isOfKind ``Parser.Term.explicitBinder ||
      s.isOfKind ``Parser.Term.strictImplicitBinder
    let mut positions := #[]
    for binder in binders do
      let names := binder[1]
      for nameStx in names.getArgs do
        if nameStx.isIdent && nameStx.getId == name then
          if let some pos := nameStx.getPos? then
            positions := positions.push pos
    return positions
  -- Now check: does any ident occurrence have a position NOT in either set?
  let allIdents := findAll sigStx fun s =>
    s.isIdent && s.getId == name
  let hasNonDotUsage := allIdents.any fun ident =>
    match ident.getPos? with
    | some pos => !projBasePositions.contains pos && !binderNamePositions.contains pos
    | none => false  -- no position → can't determine, assume dot notation (conservative)
  -- If there's a non-dot, non-binder-name usage → type IS inferable → return false
  -- If all usages are dot/binder-name → type NOT inferable → return true
  if allIdents.isEmpty then false  -- no usages at all
  else !hasNonDotUsage

/--
Check if an implicit binder can safely be removed under `autoImplicit`.
Returns `true` if the binder is redundant and should be flagged.

Conditions checked:
1. Binder is implicit (not explicit, not instance)
2. Name is atomic (no dots or macro scopes)
3. Name is in the source implicit binders (not auto-generated)
4. Name doesn't shadow anything in the outer scope
5. Level gate: level 1 = Sort/Type only, level 2 = all
6. Not used only via dot notation (can't resolve without type)
-/
private def isRedundant
    (level : Nat)
    (ldecl : LocalDecl)
    (srcImplicits : Array (Name × Syntax))
    (shadowedNames : Array Name)
    (sigStx : Syntax) : Bool :=
  -- 1. Must be implicit
  ldecl.binderInfo == .implicit &&
  -- 2. Must be atomic name
  isAtomicName ldecl.userName &&
  -- 3. Must be in source (not auto-generated by elaborator)
  srcImplicits.any (·.1 == ldecl.userName) &&
  -- 4. Must not shadow outer scope (auto-implicit won't bind shadowed names)
  !shadowedNames.contains ldecl.userName &&
  -- 5. Level gate
  (isSortOrType ldecl.type || level ≥ 2) &&
  -- 6. Not used only via dot notation (auto-implicit can't resolve)
  (isSortOrType ldecl.type || !onlyUsedViaDotNotation sigStx ldecl.userName)

/-! ## Source binder collection -/

/-- Get the declaration name from a command syntax. -/
private def getDeclName? (stx : Syntax) : Option Name :=
  let declId? := stx.find? fun s => s.isOfKind ``Parser.Command.declId
  declId?.bind fun declId =>
    match declId[0] with
    | .ident _ _ val _ => some val
    | _ => none

/--
Find the source implicit binder syntax nodes in a declaration signature.
Returns array of `(binderName, binderSyntax)` pairs for `{...}` binders.
-/
private def collectSourceImplicitBinders (sigStx : Syntax) :
    Array (Name × Syntax) := Id.run do
  let binders := sigStx[0]
  let mut result := #[]
  for arg in binders.getArgs do
    if arg.isOfKind ``Parser.Term.implicitBinder then
      let names := arg[1]
      for nameStx in names.getArgs do
        match nameStx with
        | .ident _ _ val _ => result := result.push (val, arg)
        | _ => pure ()
  return result

/-! ## Linter -/

/-- The redundant-implicit linter. -/
def redundantImplicitLinter : Linter where run := withSetOptionIn fun stx => do
  unless getLinterValue linter.hazel.style.redundantImplicit (← getLinterOptions) do return
  if (← MonadState.get).messages.hasErrors then return
  unless stx.isOfKind ``Parser.Command.declaration do return
  -- Check if autoImplicit is on
  let opts ← getOptions
  unless autoImplicit.get opts do return
  -- Find the signature
  let some sigStx := stx.find? fun s =>
    s.isOfKind ``Parser.Command.declSig ||
    s.isOfKind ``Parser.Command.optDeclSig
  | return
  -- Collect source implicit binders
  let srcImplicits := collectSourceImplicitBinders sigStx
  if srcImplicits.isEmpty then return
  -- Get the declaration from the environment
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
  -- Pre-check: which implicit binder names resolve in the outer scope?
  let shadowedNames ← liftTermElabM do
    let mut shadowed : Array Name := #[]
    for (name, _) in srcImplicits do
      let resolves ← try
        let resolved? ← Term.resolveId? (mkIdent name) (withInfo := false)
        pure resolved?.isSome
      catch _ => pure false
      if resolves then shadowed := shadowed.push name
    return shadowed
  let level := linter.hazel.style.redundantImplicitLevel.get (← getOptions)
  -- Walk the elaborated type
  liftTermElabM do
    forallTelescope ci.type fun args body => do
      -- Build the opened type for FVar-based checks: collect all binder
      -- types and the return type into one expression to search.
      let mut openedParts : Array Expr := #[]
      for a in args do
        openedParts := openedParts.push (← a.fvarId!.getDecl).type
      openedParts := openedParts.push body
      for arg in args do
        let ldecl ← arg.fvarId!.getDecl
        -- Single predicate: is this binder redundant?
        unless isRedundant level ldecl srcImplicits shadowedNames sigStx do continue
        -- Skip binders that only appear in function position (applied to args).
        -- Auto-implicit can't infer function types from application alone —
        -- the metavar can't become a forallE.  But if the FVar also appears in
        -- argument position (to a known function), the type IS constrainable.
        if !isSortOrType ldecl.type &&
           !openedParts.any (hasNonAppUsage arg.fvarId!) then
          continue
        -- Find the source syntax for the error location
        let some (_, binderStx) := srcImplicits.find?
          fun (n, _) => n == ldecl.userName
        | continue
        -- Flag with appropriate message
        let tyFmt ← ppExpr ldecl.type
        if isSortOrType ldecl.type then
          Linter.logLint linter.hazel.style.redundantImplicit binderStx
            m!"Implicit binder `{ldecl.userName} : {tyFmt}` could be omitted, \
               `autoImplicit` would bind it.  \
               Note: removing may widen the universe level."
        else
          Linter.logLint linter.hazel.style.redundantImplicit binderStx
            m!"Implicit binder `{ldecl.userName} : {tyFmt}` could be omitted, \
               `autoImplicit` would infer the same type from usage."

initialize addLinter redundantImplicitLinter

end Hazel.Style.RedundantImplicit

end -- meta section
