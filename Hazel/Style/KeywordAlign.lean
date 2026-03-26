/-
SPDX-FileCopyrightText: 2026 Mingtong Lin
SPDX-License-Identifier: MIT
-/
module

public meta import Lean
public meta import Lean.Linter
public meta import Hazel.Util

/-!
# Keyword alignment linter

Checks that `deriving`, `termination_by`, `decreasing_by`, and `where` are
aligned with their parent declaration keyword.
-/

meta section

open Lean Elab Command Linter Hazel.Util

/-! ## Options -/

/-- `deriving` must align with its parent declaration. -/
public register_option linter.hazel.style.keywordAlign.deriving : Bool := {
  defValue := false
  descr := "check that `deriving` aligns with its declaration"
}

/-- `termination_by` must align with its parent declaration. -/
public register_option linter.hazel.style.keywordAlign.terminationBy : Bool := {
  defValue := false
  descr := "check that `termination_by` aligns with its declaration"
}

/-- `decreasing_by` must align with its parent declaration. -/
public register_option linter.hazel.style.keywordAlign.decreasingBy : Bool := {
  defValue := false
  descr := "check that `decreasing_by` aligns with its declaration"
}

/-- `where` must align with its parent declaration. -/
public register_option linter.hazel.style.keywordAlign.where : Bool := {
  defValue := false
  descr := "check that `where` aligns with its declaration"
}

namespace Hazel.Style.KeywordAlign

/--
Check that a keyword atom aligns with its parent declaration, but only if the
keyword is the first non-whitespace token on its line (i.e., on its own line,
not inline).
-/
private def checkKeywordCol (fm : FileMap) (lines : Array String) (atom : Syntax)
    (keyword : String) (opt : Lean.Option Bool) (declCol : Nat) :
    CommandElabM Unit := do
  let some pos := atom.getPos? | return
  let position := fm.toPosition pos
  -- Only check if the keyword is the first non-whitespace on its line
  let lineIdx := position.line - 1  -- Position.line is 1-indexed
  if lineIdx < lines.size then
    let line := lines[lineIdx]!
    let beforeKw := (line.take position.column).trimAscii.toString
    if !beforeKw.isEmpty then return  -- something before keyword, it's inline
  if position.column != declCol then
    Linter.logLint opt atom
      m!"`{keyword}` should align with its declaration (column {declCol})"

/-- The keyword alignment linter. -/
def keywordAlignLinter : Lean.Linter where run := withSetOptionIn fun stx => do
  let opts ← getLinterOptions
  let chkDeriving := getLinterValue linter.hazel.style.keywordAlign.deriving opts
  let chkTermBy := getLinterValue linter.hazel.style.keywordAlign.terminationBy opts
  let chkDecrBy := getLinterValue linter.hazel.style.keywordAlign.decreasingBy opts
  let chkWhere := getLinterValue linter.hazel.style.keywordAlign.where opts
  unless chkDeriving || chkTermBy || chkDecrBy || chkWhere do return
  if (← MonadState.get).messages.hasErrors then return
  let fm ← getFileMap
  let lines := (fm.source.splitOn "\n").toArray
  -- Find the declaration keyword's column
  let some declPos := stx.getPos? | return
  let declCol := (fm.toPosition declPos).column
  let atoms := findAll stx fun s =>
    match s with
    | .atom _ val => val == "deriving" || val == "termination_by" ||
                     val == "decreasing_by" || val == "where"
    | _ => false
  for atom in atoms do
    match atom with
    | .atom _ "deriving" =>
      if chkDeriving then checkKeywordCol fm lines atom "deriving" linter.hazel.style.keywordAlign.deriving declCol
    | .atom _ "termination_by" =>
      if chkTermBy then checkKeywordCol fm lines atom "termination_by" linter.hazel.style.keywordAlign.terminationBy declCol
    | .atom _ "decreasing_by" =>
      if chkDecrBy then checkKeywordCol fm lines atom "decreasing_by" linter.hazel.style.keywordAlign.decreasingBy declCol
    | .atom _ "where" =>
      if chkWhere then checkKeywordCol fm lines atom "where" linter.hazel.style.keywordAlign.where declCol
    | _ => pure ()

initialize addLinter keywordAlignLinter

end Hazel.Style.KeywordAlign

end -- meta section
