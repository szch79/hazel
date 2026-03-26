/-
SPDX-FileCopyrightText: 2026 Mingtong Lin
SPDX-License-Identifier: MIT
-/
module

public meta import Lean
public meta import Lean.Linter

/-!
# Parameter naming linter

A linter that checks binder names when they appear as arguments to registered
type constructors / typeclasses.  Rules are registered via the
`@[suggested_param_names]` attribute:

```
@[suggested_param_names (α "x" "y")]
class MyClass (α : Type) where ...
```

This means: any binder that appears as the `α` argument of `MyClass` in a
declaration signature should be named starting with `x` or `y`.
-/

meta section

open Lean Meta Elab Command Linter

/-- Option controlling the parameter naming linter. -/
public register_option linter.hazel.style.paramNaming : Bool := {
  defValue := false
  descr := "check that binder names match @[suggested_param_names] rules"
}

namespace Hazel.Style.ParamNaming

/--
A single parameter rule: for param at index `paramIdx` in type `typeName`,
binders should start with one of `prefixes`.
-/
public structure ParamRule where
  typeName : Name
  paramName : Name
  paramIdx : Nat
  prefixes : Array String
  deriving Inhabited

/-- Persistent environment extension storing all parameter naming rules. -/
public initialize paramNamingExt :
    SimplePersistentEnvExtension ParamRule (Array ParamRule) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := Array.push
    addImportedFn := fun arrays => arrays.foldl (· ++ ·) #[]
  }

/-! ## Attribute: `@[suggested_param_names]` -/

/--
Register suggested names for typeclass parameter binders.  Each group
maps a parameter name of the type to allowed prefixes for binders that
fill that position.

```
@[suggested_param_names (α "l" "l'")]
class Container (α : Type) where ...
-- Now `{l : Container α}` is fine, but `{x : Container α}` warns about `α`.
```

Multiple parameter groups can be specified in one attribute.
-/
syntax (name := suggested_param_names)
  "suggested_param_names" (ppSpace "(" ident (ppSpace str)+ ")")+ : attr

initialize registerBuiltinAttribute {
  name := `suggested_param_names
  descr := "Register suggested names for binders appearing as arguments to this type."
  add := fun declName stx _attrKind => do
    -- Get the declaration's parameter names
    let env ← getEnv
    let some info := env.find? declName | throwError "unknown declaration `{declName}`"
    let paramNames ← MetaM.run' do
      forallTelescope info.type fun args _ => do
        let mut names : Array Name := #[]
        for arg in args do
          let ldecl ← arg.fvarId!.getDecl
          names := names.push ldecl.userName
        return names
    -- Parse: stx[0] is the keyword, stx[1] is a null node wrapping the
    -- repetition of (ident str+) groups
    let mut allRules : Array (Name × Array String) := #[]
    let groups := stx[1]  -- null node containing the repeated groups
    for i in [:groups.getNumArgs] do
      let group := groups[i]
      let mut ident? : Option Name := none
      let mut strs : Array String := #[]
      -- Check direct children
      for j in [:group.getNumArgs] do
        let child := group[j]
        if child.isIdent && ident?.isNone then ident? := some child.getId
        if let some v := child.isStrLit? then strs := strs.push v
        -- Check grandchildren (str+ may be wrapped in a null node)
        for k in [:child.getNumArgs] do
          let gc := child[k]
          if gc.isIdent && ident?.isNone then ident? := some gc.getId
          if let some v := gc.isStrLit? then strs := strs.push v
      if let some n := ident? then
        if !strs.isEmpty then
          allRules := allRules.push (n, strs)
    if allRules.isEmpty then
      throwError "@[suggested_param_names] requires at least one (param \"prefix\") group"
    for (pName, prefixes) in allRules do
      match paramNames.findIdx? (· == pName) with
      | some idx =>
        modifyEnv fun env => paramNamingExt.addEntry env
          { typeName := declName, paramName := pName, paramIdx := idx,
            prefixes := prefixes }
      | none =>
        throwError "@[suggested_param_names]: parameter `{pName}` not found \
          in `{declName}`.  Available parameters: {paramNames}"
}

/-! ## Linter -/

/-- Check binders in a declaration's type against parameter naming rules. -/
private def checkBinders (rules : Array ParamRule) (declName : Name) :
    MetaM (Array (Name × Name × Name × Array String)) := do
  let some info := (← getEnv).find? declName | return #[]
  forallTelescope info.type fun args _ => do
    let mut violations := #[]
    -- Build a map from FVarId to binder name
    let mut fvarNames : Std.HashMap FVarId Name := {}
    for arg in args do
      let ldecl ← arg.fvarId!.getDecl
      fvarNames := fvarNames.insert arg.fvarId! ldecl.userName
    -- For each binder, check if its type is an application of a registered type
    for arg in args do
      let ldecl ← arg.fvarId!.getDecl
      let ty := ldecl.type
      -- Check if this type is an application of a registered type constructor
      if let some headName := ty.getAppFn.constName? then
        let appArgs := ty.getAppArgs
        for rule in rules do
          if rule.typeName == headName && rule.paramIdx < appArgs.size then
            let paramExpr := appArgs[rule.paramIdx]!
            -- The argument at this position should be an FVar (a binder)
            if paramExpr.isFVar then
              if let some binderName := fvarNames[paramExpr.fvarId!]? then
                let nameStr := binderName.toString
                if nameStr.startsWith "_" then continue
                if binderName.hasMacroScopes then continue
                unless rule.prefixes.any (nameStr.startsWith ·) do
                  violations := violations.push
                    (binderName, headName, rule.paramName, rule.prefixes)
    return violations

/-- The parameter naming linter. -/
def paramNamingLinter : Lean.Linter where run := withSetOptionIn fun stx => do
  unless getLinterValue linter.hazel.style.paramNaming (← getLinterOptions) do return
  if (← MonadState.get).messages.hasErrors then return
  let rules := paramNamingExt.getState (← getEnv)
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
  for (binderName, _headName, paramName, prefixes) in violations do
    let prefixList := " ".intercalate prefixes.toList
    let binderStx := stx.find? fun s =>
      s.isIdent && s.getId == binderName
    let target := binderStx.getD stx
    Linter.logLint linter.hazel.style.paramNaming target
      m!"Suggested names for parameter `{paramName}`: {prefixList}"

initialize addLinter paramNamingLinter

end Hazel.Style.ParamNaming

end -- meta section
