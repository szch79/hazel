/-
SPDX-FileCopyrightText: 2026 Mingtong Lin
SPDX-License-Identifier: MIT
-/
module

public meta import Lean
public meta import Lean.Linter
public meta import Hazel.Util

/-!
# Require suppression comment linter

Flags `set_option linter.hazel.* false` without a `--` comment explaining
why the lint is being suppressed.

Following the conventions of ESLint (`-- reason`) and Clippy (`reason = "..."`),
every suppression should document the rationale.
-/

meta section

open Lean Elab Command Linter

/-- Require a comment when disabling hazel linters. -/
public register_option linter.hazel.meta.requireSuppressionComment : Bool := {
  defValue := false
  descr := "require a comment when disabling hazel linters via set_option"
}

namespace Hazel.Meta.RequireSuppressionComment

/-- Check if a source line contains a `--` comment. -/
private def lineHasComment (line : String) : Bool :=
  (line.splitOn "--").length > 1

/--
Check if a `set_option` disables a hazel linter.  Returns the option name
if it does, or `none` otherwise.
-/
private def isHazelSuppression (stx : Syntax) : Option Name :=
  if stx.isOfKind ``Parser.Command.set_option then
    let optName := stx[1].getId
    -- Value is at stx[3] (stx[0]=atom, stx[1]=ident, stx[2]=null/ppSpace, stx[3]=value)
    let optVal := stx[3]
    -- Check: option name starts with linter.hazel
    if optName.toString.startsWith "linter.hazel" then
      -- Check: value is false (Bool suppression) or 0 (Nat suppression)
      match optVal with
      | .atom _ "false" => some optName
      | .atom _ "0" => some optName
      | _ => none
    else none
  else none

/-- Check if a `set_option` node has a `--` comment on the same line or the line above. -/
private def hasSuppressionComment (setOptStx : Syntax) (lines : Array String)
    (fm : FileMap) : Bool :=
  match setOptStx.getPos? with
  | some pos =>
    let lineIdx := (fm.toPosition pos).line - 1
    -- 1. Inline comment on the same line as `set_option`
    let sameLineOk := lineIdx < lines.size && lineHasComment lines[lineIdx]!
    -- 2. Comment on the line immediately above
    let aboveOk := lineIdx > 0 && lineHasComment lines[lineIdx - 1]!
    sameLineOk || aboveOk
  | none => false

/-- The suppression comment linter.  Checks both file-wide and scoped
`set_option linter.hazel.* false` commands for a `--` comment on the
same line or the line above. -/
def requireSuppressionCommentLinter : Lean.Linter where run stx := do
  unless getLinterValue linter.hazel.meta.requireSuppressionComment (← getLinterOptions) do return
  if (← MonadState.get).messages.hasErrors then return
  let suppressions := Hazel.Util.findAll stx fun s => isHazelSuppression s |>.isSome
  if suppressions.isEmpty then return
  let fm ← getFileMap
  let lines := (fm.source.splitOn "\n").toArray
  for setOpt in suppressions do
    let some optName := isHazelSuppression setOpt | continue
    unless hasSuppressionComment setOpt lines fm do
      Linter.logLint linter.hazel.meta.requireSuppressionComment setOpt
        m!"Suppression of `{optName}` should have a `--` comment explaining why."

initialize addLinter requireSuppressionCommentLinter

end Hazel.Meta.RequireSuppressionComment

end -- meta section
