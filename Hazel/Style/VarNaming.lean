/-
SPDX-FileCopyrightText: 2026 Mingtong Lin
SPDX-License-Identifier: MIT
-/
module

public meta import Lean
public meta import Lean.Linter

/-!
# Variable naming linter

A linter that checks binder names in declaration signatures against type-based
naming rules.  Two registration mechanisms:

1. `@[suggested_var_names]` attribute on named type declarations:

```
@[suggested_var_names "l"]
abbrev MyList := List Nat
```

2. `suggest_var_names` command for structural type expressions:

```
suggest_var_names "f" "g" for Nat → Bool
```

The linter warns when a binder's name doesn't start with any of the registered
prefixes for its type.
-/

meta section

open Lean Meta Elab Command Linter

/-- Option controlling the variable naming linter. -/
public register_option linter.hazel.style.varNaming : Bool := {
  defValue := false
  descr := "check that binder names match @[suggested_var_names] rules"
}

namespace Hazel.Style.VarNaming

/--
A variable naming rule.  Either `typeName` is set (for attribute-based rules on
named types) or `typeExpr?` is set (for structural type patterns from the
`suggest_var_names` command).
-/
public structure VarNamingRule where
  typeName : Name
  typeExpr? : Option Expr := none
  prefixes : Array String
  deriving Inhabited

/-- Persistent environment extension storing all naming rules. -/
public initialize varNamingExt :
    SimplePersistentEnvExtension VarNamingRule (Array VarNamingRule) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := Array.push
    addImportedFn := fun arrays => arrays.foldl (· ++ ·) #[]
  }

/-! ## Attribute: `@[suggested_var_names]` -/

/--
Register suggested variable name prefixes for binders of a type.  When
`linter.hazel.style.varNaming` is enabled, binders whose type has this
declaration as head will be checked against the given prefixes.

```
@[suggested_var_names "l"]
abbrev MyList := List Nat
-- Now `{l : MyList}` passes, but `{x : MyList}` warns.
```

Multiple prefixes are allowed: `@[suggested_var_names "f" "g" "h"]`.
Subscripts and numeric suffixes are accepted (e.g., `f₁` matches `"f"`).
-/
syntax (name := suggested_var_names) "suggested_var_names" (ppSpace str)+ : attr

initialize registerBuiltinAttribute {
  name := `suggested_var_names
  descr := "Register suggested variable name prefixes for binders of this type."
  add := fun declName stx _attrKind => do
    let mut prefixes : Array String := #[]
    for i in [:stx.getNumArgs] do
      let arg := stx[i]
      if let some s := arg.isStrLit? then
        prefixes := prefixes.push s
      for j in [:arg.getNumArgs] do
        if let some s := arg[j].isStrLit? then
          prefixes := prefixes.push s
    if prefixes.isEmpty then
      throwError "@[suggested_var_names] requires at least one prefix"
    modifyEnv fun env => varNamingExt.addEntry env
      { typeName := declName, prefixes := prefixes }
}

/-! ## Command: `suggest_var_names` -/

/--
Register naming rules for structural type expressions that cannot be
captured by `@[suggested_var_names]` (which only matches the head constant).
Use `_` as a wildcard for type arguments.

```
suggest_var_names "f" "g" "h" for Nat → Bool
suggest_var_names "s" for MyState _
```
-/
syntax "suggest_var_names" str+ "for" term : command

elab_rules : command
  | `(suggest_var_names $prefixes:str* for $ty) => do
    let tyExpr ← liftTermElabM do
      let e ← Term.elabType ty
      instantiateMVars e
    let ps := prefixes.map (·.getString)
    if ps.isEmpty then
      throwError "suggest_var_names requires at least one prefix string"
    modifyEnv fun env => varNamingExt.addEntry env
      { typeName := .anonymous, typeExpr? := some tyExpr, prefixes := ps }

/-! ## Linter -/

/--
Structural matching with wildcards.  Compares two `Expr`s node by node.
Metavars in the pattern (from `_` holes) match anything.  All other nodes
must match structurally (same constructor, same constant name with suffix
matching for module-qualified names).
-/
private partial def matchWithWildcards (ty pat : Expr) : Bool :=
  -- Pattern is a metavar → wildcard, matches anything
  if pat.isMVar then true
  -- Both are constants: suffix match for module-qualified names
  else if let (.const tn _, .const pn _) := (ty, pat) then
    tn == pn || tn.isSuffixOf pn || pn.isSuffixOf tn
  -- Both are applications: match function and argument recursively
  else if ty.isApp && pat.isApp then
    matchWithWildcards ty.appFn! pat.appFn! &&
    matchWithWildcards ty.appArg! pat.appArg!
  -- Both are foralls (function types): match domain and body
  else if ty.isForall && pat.isForall then
    matchWithWildcards ty.bindingDomain! pat.bindingDomain!
  -- Fallback: structural equality
  else ty == pat

/--
Check binders in a declaration's type against the naming rules.  Returns an
array of `(binderName, prettyType, expectedPrefixes)` violations.
-/
private def checkBinders (rules : Array VarNamingRule) (declName : Name) :
    MetaM (Array (Name × String × Array String)) := do
  let some info := (← getEnv).find? declName | return #[]
  forallTelescope info.type fun args _ => do
    let mut violations := #[]
    for arg in args do
      let ldecl ← arg.fvarId!.getDecl
      if ldecl.userName.hasMacroScopes then continue
      let ty := ldecl.type
      let nameStr := ldecl.userName.toString
      if nameStr.startsWith "_" then continue
      -- Check head-name rules (from @[suggested_var_names])
      if let some headName := ty.getAppFn.constName? then
        for rule in rules do
          if rule.typeName != .anonymous && headName == rule.typeName then
            unless rule.prefixes.any (nameStr.startsWith ·) do
              let tyStr := toString (← Meta.ppExpr ty)
              violations := violations.push (ldecl.userName, tyStr, rule.prefixes)
              break
      -- Check structural rules (from suggest_var_names command).
      -- The stored pattern may have stale metavars (from `_` holes).
      -- For patterns with metavars, use structural matching where metavar
      -- positions are wildcards.  For patterns without metavars, use isDefEq.
      for rule in rules do
        if let some patExpr := rule.typeExpr? then
          let isMatch ← if patExpr.hasExprMVar then
            -- Structural match: compare head + args, treating metavars as wildcards.
            pure (matchWithWildcards ty patExpr)
          else
            isDefEq ty patExpr
          if isMatch then
            unless rule.prefixes.any (nameStr.startsWith ·) do
              let tyStr := toString (← Meta.ppExpr ty)
              violations := violations.push (ldecl.userName, tyStr, rule.prefixes)
              break
    return violations

/-- The variable naming linter. -/
def varNamingLinter : Lean.Linter where run := withSetOptionIn fun stx => do
  unless getLinterValue linter.hazel.style.varNaming (← getLinterOptions) do return
  if (← MonadState.get).messages.hasErrors then return
  let rules := varNamingExt.getState (← getEnv)
  if rules.isEmpty then return
  let some declId := stx.find? (·.isOfKind ``Lean.Parser.Command.declId) | return
  let id := declId[0]
  let declName := id.getId
  if declName.isAnonymous || declName.hasMacroScopes then return
  let resolved ← liftCoreM <|
    try pure (some (← resolveGlobalConstNoOverload id))
    catch _ => pure none
  let some fullName := resolved | return
  let violations ← liftTermElabM <| checkBinders rules fullName
  for (binderName, tyStr, prefixes) in violations do
    let prefixList := " ".intercalate prefixes.toList
    let binderStx := stx.find? fun s =>
      s.isIdent && s.getId == binderName
    let target := binderStx.getD stx
    Linter.logLint linter.hazel.style.varNaming target
      m!"Suggested names of type `{tyStr}`: {prefixList}"
  -- Body-level check: lambda and let binders in the definition body.
  -- Walk InfoTree for TermInfo where the Expr is a lambda or letE.
  unless (← getInfoState).enabled do return
  let trees ← getInfoTrees
  let mut lamCandidates : Array (ContextInfo × Name × Expr × Syntax) := #[]
  for tree in trees.toArray do
    lamCandidates := tree.foldInfo (init := lamCandidates) fun ctx info acc =>
      match info with
      | .ofTermInfo ti =>
        -- Only original syntax (user-written)
        match ti.stx.getHeadInfo with
        | .original .. =>
          -- Check for lambda or letE at the Expr level
          match ti.expr with
          | .lam name ty _ _ =>
            if !name.hasMacroScopes && !name.toString.startsWith "_" then
              acc.push (ctx, name, ty, ti.stx)
            else acc
          | .letE name ty _ _ _ =>
            if !name.hasMacroScopes && !name.toString.startsWith "_" then
              acc.push (ctx, name, ty, ti.stx)
            else acc
          | _ => acc
        | _ => acc
      | _ => acc
  -- Deduplicate by (name, source position)
  let mut seen : Array (Name × String.Pos.Raw) := #[]
  for (ctx, name, ty, lamStx) in lamCandidates do
    let some pos := lamStx.getPos? | continue
    if seen.contains (name, pos) then continue
    seen := seen.push (name, pos)
    let nameStr := name.toString
    -- Check against naming rules
    let violation? ← liftCoreM do
      -- The lambda's domain type may contain FVars from a context that
      -- `runMetaM` cannot fully restore (stale InfoTree FVars).  Catch
      -- and skip rather than crash.
      try ctx.runMetaM {} do
        -- Head-name rules
        if let some headName := ty.getAppFn.constName? then
          for rule in rules do
            if rule.typeName != .anonymous && headName == rule.typeName then
              unless rule.prefixes.any (nameStr.startsWith ·) do
                let tyStr := toString (← Meta.ppExpr ty)
                return some (tyStr, rule.prefixes)
        -- Structural rules
        for rule in rules do
          if let some patExpr := rule.typeExpr? then
            let isMatch ← if patExpr.hasExprMVar then
              pure (matchWithWildcards ty patExpr)
            else
              isDefEq ty patExpr
            if isMatch then
              unless rule.prefixes.any (nameStr.startsWith ·) do
                let tyStr := toString (← Meta.ppExpr ty)
                return some (tyStr, rule.prefixes)
        return none
      catch _ => return none
    if let some (tyStr, prefixes) := violation? then
      let prefixList := " ".intercalate prefixes.toList
      Linter.logLint linter.hazel.style.varNaming lamStx
        m!"Suggested names of type `{tyStr}`: {prefixList}"

initialize addLinter varNamingLinter

end Hazel.Style.VarNaming

end -- meta section
