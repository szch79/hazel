/-
SPDX-FileCopyrightText: 2026 Mingtong Lin
SPDX-License-Identifier: MIT
-/
module

public meta import Lean
public meta import Lean.Linter

/-!
# Strong postcondition linter

Flags `@[spec]` lemmas where the postcondition `Q` is not universally
quantified (i.e., fixed to a concrete postcondition).  A generic `Q` makes
the spec more composable with `mvcgen`.

Auto-enabled when `Std.Do.Triple` is in the environment.
-/

meta section

open Lean Meta Elab Command Linter

/-- Check that `@[spec]` lemmas have a universally quantified postcondition. -/
public register_option linter.hazel.do.strongPostCond : Bool := {
  defValue := true
  descr := "check that @[spec] lemmas have a generic postcondition Q"
}

namespace Hazel.Do.StrongPostCond

/-- Check if `Std.Do.Triple` is available in the environment. -/
private def hasTriple (env : Environment) : Bool :=
  env.contains ``Std.Do.Triple

/--
Check if the conclusion of a `@[spec]` theorem has `Q` as a free variable.
Returns `true` if the postcondition is generic (good), `false` if fixed (bad).
-/
private def hasGenericPostCond (declName : Name) : MetaM Bool := do
  let some info := (← getEnv).find? declName | return true
  forallTelescope info.type fun fvars body => do
    -- The body should be `Triple prog P Q` or `⦃P⦄ prog ⦃Q⦄`
    -- Triple is applied as: Triple.{...} prog P Q
    let fn := body.getAppFn
    let fnName := match fn with
      | .const n _ => n
      | _ => .anonymous
    -- Check if this is a Triple application
    unless fnName == ``Std.Do.Triple do return true  -- not a Triple, skip
    let args := body.getAppArgs
    -- Triple has args: [m, ps, WP_inst, alpha, prog, P, Q]
    -- Q is the last argument
    let some qArg := args.back? | return true
    -- Q is "generic" if it's an FVar (bound by the forall telescope)
    if qArg.isFVar then
      -- Check it's one of the telescope variables
      return fvars.any (· == qArg)
    return false

/-- The strong postcondition linter. -/
def strongPostCondLinter : Lean.Linter where run := withSetOptionIn fun stx => do
  unless getLinterValue linter.hazel.do.strongPostCond (← getLinterOptions) do return
  if (← MonadState.get).messages.hasErrors then return
  let env ← getEnv
  -- Auto-disable: skip if Triple is not imported
  unless hasTriple env do return
  -- Only check declarations
  unless stx.getKind == ``Parser.Command.declaration do return
  -- Find the declaration name
  let some declId := stx.find? (·.isOfKind ``Parser.Command.declId) | return
  let declName := declId[0].getId
  if declName.isAnonymous then return
  let resolved ← liftCoreM do
    try pure (some (← resolveGlobalConstNoOverload declId[0]))
    catch _ => pure none
  let some fullName := resolved | return
  -- Check if this declaration has the @[spec] attribute
  -- We check by looking for `spec` in the declModifiers attributes
  let hasSpec := stx.find? fun s =>
    match s with
    | .node _ ``Parser.Term.attrInstance args =>
      args.any fun a =>
        match a with
        | .atom _ "spec" => true
        | .node _ _ children => children.any fun c =>
          match c with
          | .atom _ "spec" => true
          | _ => false
        | _ => false
    | _ => false
  unless hasSpec.isSome do return
  -- Check if the postcondition is generic
  let isGeneric ← liftTermElabM <| hasGenericPostCond fullName
  unless isGeneric do
    Linter.logLint linter.hazel.do.strongPostCond stx
      m!"@[spec] lemma should have a universally quantified postcondition `Q` for better composability with `mvcgen`."

initialize addLinter strongPostCondLinter

end Hazel.Do.StrongPostCond

end -- meta section
