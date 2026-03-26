/-
SPDX-FileCopyrightText: 2026 Mingtong Lin
SPDX-License-Identifier: MIT
-/
module

public meta import Lean
public meta import Lean.Linter
public meta import Hazel.Util

/-!
# Prefer `rintro` linter

Flags `intro h; rcases h with pat` or `intro h; obtain pat := h`, suggesting
`rintro pat` instead.
-/

meta section

open Lean Elab Command Linter Hazel.Util

/-- Prefer `rintro` over `intro` followed by `rcases`/`obtain` on the same variable. -/
public register_option linter.hazel.tactic.preferRintro : Bool := {
  defValue := false
  descr := "flag `intro h; rcases h` (prefer `rintro`)"
}

namespace Hazel.Tactic.PreferRintro

/--
Extract the introduced variable name from an `intro` tactic syntax.
Returns `none` if the tactic introduces multiple variables or zero.
`intro` syntax: `"intro" notFollowedBy("|") (ppSpace colGt term:max)*`
Children: `["intro", ...terms]`.  Single-var intro has exactly 2 children.
-/
private def getIntroVar (stx : Syntax) : Option Name :=
  if !stx.isOfKind ``Parser.Tactic.intro then none
  else
    -- `intro` syntax: "intro" notFollowedBy("|") (ppSpace colGt term:max)*
    -- Children: ["intro", null[args...]]
    -- For single-var intro, the null node has exactly 1 child that is an ident
    let argsNode := stx[1]
    if argsNode.getNumArgs != 1 then none
    else
      let arg := argsNode[0]
      if arg.isIdent then some arg.getId else none

/--
Check if an `rcases`/`obtain` syntax destructures a given variable.
For `rcases h with ...`: first target ident matches the variable.
For `obtain ... := h`: value after `:=` is the variable.
Uses syntax tree traversal (not `reprint` string matching).
-/
private def destructuresVar (stx : Syntax) (varName : Name) : Bool :=
  if stx.isOfKind ``Parser.Tactic.rcases then
    -- rcases syntax: "rcases" targets "with" pat
    -- Search for an ident matching `varName` in the target portion (before "with").
    -- We stop at the first "with" atom to avoid matching inside the pattern.
    let args := stx.getArgs
    Id.run do
      for arg in args do
        if arg.getAtomVal == "with" then return false
        if let some _ := arg.find? (fun s => s.isIdent && s.getId == varName) then
          return true
      return false
  else if stx.isOfKind ``Parser.Tactic.obtain then
    -- obtain syntax: "obtain" pat ":=" val | "obtain" pat ":" ty ":=" val
    -- Find the first ident after ":=" in the children.
    let args := stx.getArgs
    Id.run do
      let mut foundAssign := false
      for arg in args do
        if foundAssign then
          return arg.isIdent && arg.getId == varName
        if arg.getAtomVal == ":=" then
          foundAssign := true
      return false
  else false

/-- The prefer rintro linter. -/
def preferRintroLinter : Lean.Linter where run := withSetOptionIn fun stx => do
  unless getLinterValue linter.hazel.tactic.preferRintro (← getLinterOptions) do return
  if (← MonadState.get).messages.hasErrors then return
  let seqNodes := findAll stx fun s =>
    s.isOfKind ``Parser.Tactic.tacticSeq1Indented ||
    s.isOfKind ``Parser.Tactic.seq1
  for seqNode in seqNodes do
    let tactics := (collectTactics seqNode).filter fun t =>
      !t.isMissing && t.getKind != `null
    for i in [:tactics.size - 1] do
      let cur := tactics[i]!
      let next := tactics[i + 1]!
      if let some varName := getIntroVar cur then
        if destructuresVar next varName then
          Linter.logLint linter.hazel.tactic.preferRintro cur
            m!"Use `rintro` instead of `intro {varName}` followed by destructuring."

initialize addLinter preferRintroLinter

end Hazel.Tactic.PreferRintro

end -- meta section
