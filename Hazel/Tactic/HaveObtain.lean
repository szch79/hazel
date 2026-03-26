/-
SPDX-FileCopyrightText: 2026 Mingtong Lin
SPDX-License-Identifier: MIT
-/
module

public meta import Lean
public meta import Lean.Linter
public meta import Hazel.Util

/-!
# Have/obtain linter

Flags `have ⟨...⟩ := ...` where `obtain ⟨...⟩ := ...` is preferred.  The rule:
if the binder uses pattern matching (anonymous constructor `⟨⟩`), use `obtain`.
Use `have` only for plain introduction without destructuring.
-/

meta section

open Lean Elab Command Linter Hazel.Util

/-- Use `obtain` for destructuring, not `have`. -/
public register_option linter.hazel.tactic.haveObtain : Bool := {
  defValue := false
  descr := "flag `have ⟨...⟩` patterns that should use `obtain`"
}

namespace Hazel.Tactic.HaveObtain

/-- Check if a syntax node is or contains anonymous constructor syntax `⟨...⟩`. -/
private partial def hasAnonymousCtor (stx : Syntax) : Bool :=
  stx.isOfKind ``Parser.Term.anonymousCtor ||
  match stx with
  | .node _ _ args => args.any hasAnonymousCtor
  | _ => false

/-- The have/obtain linter. -/
def haveObtainLinter : Lean.Linter where run := withSetOptionIn fun stx => do
  unless getLinterValue linter.hazel.tactic.haveObtain (← getLinterOptions) do return
  if (← MonadState.get).messages.hasErrors then return
  -- Find all `have` tactic nodes
  let haveNodes := findAll stx fun s =>
    s.isOfKind ``Parser.Tactic.tacticHave__
  for haveNode in haveNodes do
    -- The `have` tactic syntax is: have letConfig letDecl
    --   [0] = "have" keyword
    --   [1] = letConfig
    --   [2] = letDecl, which contains letPatDecl or letIdDecl
    -- For `have ⟨h1, _⟩ := h`, letDecl contains letPatDecl with the
    -- anonymous constructor pattern.
    -- For `have h : T := e`, letDecl contains letIdDecl with an ident.
    -- We only check the **pattern** part (first child of letPatDecl),
    -- NOT the value expression, to avoid false positives when the
    -- value contains ⟨...⟩.
    let args := haveNode.getArgs
    let some letDecl := args[2]? | continue
    -- letDecl has one child: either letPatDecl or letIdDecl.
    let some innerDecl := letDecl.getArgs[0]? | continue
    -- Only flag if it's a letPatDecl (pattern matching).
    -- letIdDecl (plain `have h := ...`) never has anonymous constructors
    -- in the binder.
    unless innerDecl.isOfKind ``Parser.Term.letPatDecl do continue
    -- The first child of letPatDecl is the pattern.
    let some patternPart := innerDecl.getArgs[0]? | continue
    let hasCtor := hasAnonymousCtor patternPart
    if hasCtor then
      Linter.logLint linter.hazel.tactic.haveObtain haveNode
        m!"Use `obtain ⟨...⟩` for destructuring instead of `have ⟨...⟩`."

initialize addLinter haveObtainLinter

end Hazel.Tactic.HaveObtain

end -- meta section
