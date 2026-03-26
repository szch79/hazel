/-
SPDX-FileCopyrightText: 2026 Mingtong Lin
SPDX-License-Identifier: MIT
-/
module

public meta import Lean
public meta import Lean.Linter

/-!
# By indentation linter

Checks that the tactic body after a top-level `:= by` is indented exactly
2 spaces from the declaration keyword's column.

Only checks the outermost `by` in each declaration (the one directly after
`:=`).  Nested `by` blocks (inside `have`, `fun`, `show`, `exact`, etc.)
are not checked — their correct indentation depends on surrounding context
that the syntax tree does not encode.
-/

meta section

open Lean Elab Command Linter

/-- Tactic body after `:= by` must be indented 2 from the declaration. -/
public register_option linter.hazel.style.byIndent : Bool := {
  defValue := false
  descr := "check that tactic body after `:= by` is indented 2 from the declaration"
}

namespace Hazel.Style.ByIndent

/--
Find the first non-wrapper tactic in a tactic sequence.  Recurses through
wrapper kinds (`tacticSeq`, `tacticSeq1Indented`, `seq1`, `null`).
-/
private partial def findFirstTactic : Syntax → Option Syntax
  | .node _ kind args =>
    if kind == ``Parser.Tactic.tacticSeq1Indented ||
       kind == ``Parser.Tactic.tacticSeq ||
       kind == ``Parser.Tactic.seq1 ||
       kind == `null then
      args.findSome? fun arg =>
        if arg.isAtom || arg.isMissing then none
        else findFirstTactic arg
    else some (.node .none kind args)
  | _ => none

/-- The by indentation linter. -/
def byIndentLinter : Lean.Linter where run := withSetOptionIn fun stx => do
  unless getLinterValue linter.hazel.style.byIndent (← getLinterOptions) do return
  if (← MonadState.get).messages.hasErrors then return
  unless stx.isOfKind ``Parser.Command.declaration do return
  let fm ← getFileMap
  -- Find the `:= ...` node (declValSimple)
  let some declVal := stx.find? (·.isOfKind ``Parser.Command.declValSimple) | return
  -- declValSimple children: ":=" body "where"?
  -- The body is at index [1].  Check if it's a byTactic.
  let body := declVal[1]
  unless body.isOfKind ``Parser.Term.byTactic do return
  -- Get the tactic sequence (last child of byTactic, after "by" atom)
  let some tacSeq := body.getArgs.back? | return
  let some firstTac := findFirstTactic tacSeq | return
  let some tacPos := firstTac.getPos? | return
  -- Skip single-line `:= by tac` (no indentation to check)
  if let some byPos := body.getPos? then
    let byLine := (fm.toPosition byPos).line
    let tacLine := (fm.toPosition tacPos).line
    if byLine == tacLine then return
  -- Check: first tactic column should be command column + 2
  let cmdCol := match stx.getPos? with
    | some pos => (fm.toPosition pos).column
    | none => 0
  let tacCol := (fm.toPosition tacPos).column
  let expectedCol := cmdCol + 2
  if tacCol != expectedCol then
    Linter.logLint linter.hazel.style.byIndent firstTac
      m!"Tactic proof after `by` is not indented correctly \
         (expected {expectedCol - cmdCol} spaces from enclosing declaration)."

initialize addLinter byIndentLinter

end Hazel.Style.ByIndent

end -- meta section
