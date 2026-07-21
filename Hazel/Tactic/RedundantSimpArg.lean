/-
SPDX-FileCopyrightText: 2026 Mingtong Lin
SPDX-License-Identifier: MIT
-/
module

public meta import Lean
public meta import Lean.Linter

/-!
# Redundant simp arg linter

Flags `simp [foo]` (non-`only`) where `foo` is already `@[simp]` — the
argument is redundant since `simp` fires it from the default set anyway.

`simp only` is not flagged: it is a deliberate choice for controlled
simplification, and plain `simp` may over-simplify and break the proof.

Only positive lemma args (`simpLemma` nodes) are checked.  Erasures
(`simp [-foo]`) are skipped — `-foo` is only meaningful when `foo` *is*
`@[simp]` — as are the location clause (`at h`) and config.

Args with a modifier are also skipped: `← foo` supplies the *reversed*
rewrite and `↓ foo` (or `↑ foo`) changes *when* it fires, neither of which
the default registration provides, so such args are not redundant.  This
trades a rare false negative (`↑ foo` on a plainly-registered `foo`) for
never mislabeling a deliberate direction or timing change.
-/

meta section

open Lean Meta Elab Command Linter

/-- Option controlling the redundant simp arg linter. -/
public register_option linter.hazel.tactic.redundantSimpArg : Bool := {
  defValue := false
  descr := "warn when simp [foo] passes an already-@[simp] argument"
}

namespace Hazel.Tactic.RedundantSimpArg

/-- Check if a name is in the default simp set. -/
private def isSimpRegistered (simps : SimpTheorems) (name : Name) : Bool :=
  simps.isLemma (.decl name) || simps.isDeclToUnfold name

/-- Collect all ident names from a syntax tree. -/
private partial def collectIdents (stx : Syntax) (acc : Array Name := #[]) : Array Name :=
  match stx with
  | .ident _ _ name _ => acc.push name
  | .node _ _ args => args.foldl (init := acc) fun acc arg => collectIdents arg acc
  | _ => acc

/-- Collect ident names from the positive simp args (`simpLemma` nodes) only,
skipping erasures (`-foo`), the location clause, and config.  A `simpLemma`
with a modifier (slot 0: `↑`/`↓`, slot 1: `←`, mirroring core's
`elabSimpArgs`) is skipped too: it changes direction or timing relative to
the default registration, so it is not redundant. -/
private partial def collectSimpArgIdents (stx : Syntax) (acc : Array Name := #[]) : Array Name :=
  match stx with
  | .node _ kind args =>
    if kind == ``Lean.Parser.Tactic.simpLemma then
      if stx[0].isNone && stx[1].isNone then collectIdents stx acc else acc
    else
      args.foldl (init := acc) fun acc arg => collectSimpArgIdents arg acc
  | _ => acc

/-- Check a single syntax node for redundant simp args. -/
private partial def findRedundantSimpArgs
    (simps : SimpTheorems) (stx : Syntax) :
    CommandElabM Unit := do
  match stx with
  | .node _ kind args =>
    let isSimpCall := kind == ``Lean.Parser.Tactic.simp ||
                      kind == ``Lean.Parser.Tactic.simpAll
    if isSimpCall then
      -- Skip `simp only`: deliberate controlled simplification.
      let isOnly := (stx.find? fun s => s.getAtomVal == "only").isSome
      if !isOnly then
        let names := collectSimpArgIdents stx
        for name in names do
          if name.isAnonymous then continue
          let resolved? ← liftCoreM <|
            try pure (some (← resolveGlobalConstNoOverload (mkIdent name)))
            catch _ => pure none
          if let some fullName := resolved? then
            if isSimpRegistered simps fullName then
              Linter.logLint linter.hazel.tactic.redundantSimpArg stx
                m!"Redundant simp argument: `{name}` is already `@[simp]`."
    for arg in args do
      findRedundantSimpArgs simps arg
  | _ => pure ()

/-- The redundant simp arg linter. -/
def redundantSimpArgLinter : Lean.Linter where
  run := withSetOptionIn fun stx => do
    unless getLinterValue linter.hazel.tactic.redundantSimpArg (← getLinterOptions) &&
      (← getInfoState).enabled do return
    if (← MonadState.get).messages.hasErrors then return
    let simps ← liftTermElabM getSimpTheorems
    findRedundantSimpArgs simps stx

initialize addLinter redundantSimpArgLinter

end Hazel.Tactic.RedundantSimpArg

end -- meta section
