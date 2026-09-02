/-
SPDX-FileCopyrightText: 2026 Mingtong Lin
SPDX-License-Identifier: MIT
-/
module

public meta import Lean
public meta import Lean.Linter

/-!
# Redundant implicit binder linter

When `autoImplicit` is on, flags implicit binders `{x : T}` that the
declaration does not need: removing them and letting auto-implicit bind the
name yields the same declaration type.

The verdict comes from the elaborator, not from a heuristic.  The header
(binders and result type) is elaborated again without the binder, exactly as
`elabHeaders` does it, and the result is compared with the header elaborated
as written.  The comparison ignores universe levels and binder order (an
auto-bound implicit moves to the front of the implicit block), but insists
that every accessible binder name survives, so that named arguments keep
working.

Binders are examined in source order, and each candidate is removed together
with every binder already reported, so removing all reported binders at once
is known to work.  A binder that can be removed on its own but not together
with the reported ones is reported as an alternative, leaving the choice to
the author.

Two levels (controlled by `redundantImplicitLevel`):

- **Level 1** (default): only examine `Sort`/`Type` binders (`{α : Type}`,
  `{α : Sort u}`).  Removing such a binder may widen the universe level,
  which the warning notes.

- **Level 2**: examine all implicit binders (`{n : Nat}`, `{l : List α}`,
  etc.).
-/

meta section

open Lean Meta Elab Command Linter

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

/-! ## Header extraction -/

/-- A source implicit binder node `{x y : T}` at index `idx` of the binder list. -/
private structure SourceBinder where
  idx : Nat
  stx : Syntax
  names : Array Name

/-- The parts of a declaration header needed to elaborate it again. -/
private structure Header where
  /-- The binder nodes of the signature. -/
  binders : Array Syntax
  /-- The result type. -/
  type : Syntax
  /-- Declaration name, for auxiliary declarations created by the header. -/
  declName : Name
  /-- Short declaration name, never auto-bound. -/
  shortName : Name
  /-- Universe names declared with the `declId`. -/
  levelNames : List Name

/-- Declaration kinds whose signature is `binders : type`. -/
private def headerKinds : Array Name := #[
  ``Parser.Command.definition, ``Parser.Command.theorem, ``Parser.Command.abbrev,
  ``Parser.Command.instance, ``Parser.Command.example, ``Parser.Command.opaque,
  ``Parser.Command.axiom
]

/-- The `declId` child of a declaration node, if any. -/
private def getDeclId? (decl : Syntax) : Option Syntax :=
  decl.getArgs.findSome? fun arg =>
    if arg.isOfKind ``Parser.Command.declId then some arg
    else if arg.isOfKind nullKind && arg.getNumArgs == 1 &&
        arg[0].isOfKind ``Parser.Command.declId then some arg[0]
    else none

/--
Extract the header of a declaration, or `none` if the declaration is not of
a supported kind or has no result type.
-/
private def getHeader? (stx : Syntax) : CommandElabM (Option Header) := do
  let decl := stx[1]
  unless headerKinds.contains decl.getKind do return none
  let some sigStx := decl.getArgs.find? fun s =>
    s.isOfKind ``Parser.Command.declSig || s.isOfKind ``Parser.Command.optDeclSig
    | return none
  let (bindersStx, type?) :=
    if sigStx.isOfKind ``Parser.Command.declSig then
      let (binders, type) := expandDeclSig sigStx
      (binders, some type)
    else
      expandOptDeclSig sigStx
  let some type := type? | return none
  let (shortName, levelNames) := match getDeclId? decl with
    | some declId =>
      let (shortName, univs) := expandDeclIdCore declId
      let levelNames :=
        if univs.isNone then [] else univs[1].getArgs.getEvenElems.toList.map (·.getId)
      (shortName, levelNames)
    | none => (`_hazel_header, [])
  let declName := (← getCurrNamespace) ++ shortName
  return some { binders := bindersStx.getArgs, type, declName, shortName, levelNames }

/-- Find the source implicit binder nodes `{...}` of a binder list. -/
private def collectSourceImplicitBinders (binders : Array Syntax) : Array SourceBinder :=
  Id.run do
    let mut result := #[]
    for h : idx in [:binders.size] do
      let stx := binders[idx]
      if stx.isOfKind ``Parser.Term.implicitBinder then
        let names := stx[1].getArgs.filterMap fun id =>
          if id.isIdent then some id.getId else none
        result := result.push { idx, stx, names }
    return result

/-! ## Header elaboration -/

/--
Elaborate `header` with the binder list `binders` under auto-bound implicits,
the way `elabHeaders` does, and return the resulting declaration type, or
`none` if elaboration fails.  Every effect (messages, info trees, environment
changes) is discarded.

Error recovery stays on deliberately: Lean accepts `(h : l.length > 0) : l ≠ []`
only because the `l.length` error is recovered as `sorry`, the later atomic `l`
throws the auto-bound exception, and `withAutoBoundImplicit` restores the
message log and retries.  Failure is therefore judged by the message log after
the whole attempt.
-/
private def elabHeader? (sectionVars : Array Expr) (header : Header) (binders : Array Syntax) :
    TermElabM (Option Expr) := do
  let s ← Term.saveState
  try
    Core.resetMessageLog
    let type? ← Term.withDeclName header.declName <|
      Term.withAutoBoundImplicitForbiddenPred (· == header.shortName) <|
      Term.withAutoBoundImplicit <|
      Term.withLevelNames (header.levelNames ++ (← Term.getLevelNames)) <|
      Term.elabBinders binders fun xs => do
        let type ← Term.elabType header.type
        Term.synthesizeSyntheticMVarsNoPostponing
        let xs ← Term.addAutoBoundImplicits xs none
        let type ← mkForallFVars' xs type
        let type ← instantiateMVars type
        if type.hasExprMVar then return none
        -- Only the section variables that occur belong to the declaration type.
        let used := sectionVars.filter fun v => type.containsFVar v.fvarId!
        let type ← mkForallFVars used type
        return some (← Term.levelMVarToParam type)
    let failed := (← Core.getMessageLog).hasErrors
    s.restore (restoreInfo := true)
    return if failed then none else type?
  catch ex =>
    s.restore (restoreInfo := true)
    if ex.isInterrupt || ex.isRuntime then throw ex
    return none

/-! ## Comparison -/

/-- Erase universe levels, so that types can be compared up to universes. -/
private def eraseLevels (e : Expr) : Expr :=
  e.replace fun
    | .sort _ => some (.sort .zero)
    | .const n _ => some (.const n [])
    | _ => none

/--
Whether `variant` is the same declaration type as `base` up to universe
levels and binder order.  Binders are aligned by binder info and type, in
the order of `variant`; a binder whose name is accessible in `base` must keep
that name, since a leftover metavariable turned into a hygienic binder can no
longer be passed as a named argument.
-/
private def eqvModuloReorder (base variant : Expr) : MetaM Bool :=
  forallTelescope base fun xs₁ body₁ => forallTelescope variant fun xs₂ body₂ => do
    if xs₁.size != xs₂.size then return false
    let mut variantFVars : Array Expr := #[]
    let mut baseFVars : Array Expr := #[]
    let mut unmatched := xs₁
    for x₂ in xs₂ do
      let d₂ ← x₂.fvarId!.getDecl
      let ty₂ := eraseLevels (d₂.type.replaceFVars variantFVars baseFVars)
      let mut fits := #[]
      for x₁ in unmatched do
        let d₁ ← x₁.fvarId!.getDecl
        if d₁.binderInfo == d₂.binderInfo && eraseLevels d₁.type == ty₂ &&
            (d₁.userName.hasMacroScopes || d₁.userName == d₂.userName) then
          fits := fits.push (x₁, d₁.userName == d₂.userName)
      let some (x₁, _) := fits.find? (·.2) <|> fits[0]? | return false
      variantFVars := variantFVars.push x₂
      baseFVars := baseFVars.push x₁
      unmatched := unmatched.erase x₁
    return eraseLevels (body₂.replaceFVars variantFVars baseFVars) == eraseLevels body₁

/-! ## Linter -/

/-- Render the names of a binder node, `p q`. -/
private def namesText (c : SourceBinder) : String :=
  " ".intercalate (c.names.toList.map toString)

/-- The redundant-implicit linter. -/
def redundantImplicitLinter : Linter where run := withSetOptionIn fun stx => do
  unless getLinterValue linter.hazel.style.redundantImplicit (← getLinterOptions) do return
  if (← MonadState.get).messages.hasErrors then return
  unless stx.isOfKind ``Parser.Command.declaration do return
  unless autoImplicit.get (← getOptions) do return
  let some header ← getHeader? stx | return
  let candidates := collectSourceImplicitBinders header.binders
  if candidates.isEmpty then return
  let level := linter.hazel.style.redundantImplicitLevel.get (← getOptions)
  runTermElabM fun sectionVars => do
    let some base ← elabHeader? sectionVars header header.binders | return
    -- Whether each candidate is a `Sort` binder, and its type, for the messages.
    -- The type is rendered on one line, since it is quoted inline.
    let info ← forallTelescope base fun xs _ =>
      candidates.mapM fun c => do
        let some x ← xs.findM? fun x => return c.names.contains (← x.fvarId!.getUserName)
          | return none
        let type := (← x.fvarId!.getDecl).type
        return some (type.isSort, (← ppExpr type).pretty (width := 10000))
    -- Elaborate the header without the binders `removed`, and compare.
    let check (removed : Array SourceBinder) : TermElabM Bool := do
      let binders := header.binders.zipIdx.filterMap fun (b, i) =>
        if removed.any (·.idx == i) then none else some b
      let some variant ← elabHeader? sectionVars header binders | return false
      eqvModuloReorder base variant
    let mut reported : Array SourceBinder := #[]
    for c in candidates, i? in info do
      let some (isSort, tyFmt) := i? | continue
      unless isSort || level ≥ 2 do continue
      let trial := reported.push c
      if ← check trial then
        reported := trial
        if isSort then
          logLint linter.hazel.style.redundantImplicit c.stx
            m!"Implicit binder `{namesText c} : {tyFmt}` could be omitted, \
               `autoImplicit` would bind it.  \
               Note: removing may widen the universe level."
        else
          logLint linter.hazel.style.redundantImplicit c.stx
            m!"Implicit binder `{namesText c} : {tyFmt}` could be omitted, \
               `autoImplicit` would infer the same type from usage."
      else if !reported.isEmpty then
        -- Removable on its own, but not together with the reported binders.
        if ← check #[c] then
          let others := ", ".intercalate (reported.toList.map fun r => s!"`{namesText r}`")
          let pronoun := if reported.size == 1 then "it" else "them"
          logLint linter.hazel.style.redundantImplicit c.stx
            m!"Implicit binder `{namesText c} : {tyFmt}` could be omitted instead of \
               {others}, but not together with {pronoun}."

initialize addLinter redundantImplicitLinter

end Hazel.Style.RedundantImplicit

end -- meta section
