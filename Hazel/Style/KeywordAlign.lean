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
aligned with the declaration they belong to, when they start their own line.

A keyword belongs to the nearest enclosing declaration that can carry it.  A
`where` helper or a `let rec` owns its own `termination_by` and
`decreasing_by`, and inside `mutual` each member owns its keywords.  The
expected column is the indentation of the line where that declaration starts,
so the `termination_by` of `let rec go` aligns with `let`.
-/

meta section

open Lean Elab Command Linter Hazel.Util

/-! ## Options -/

/-- `deriving` must align with the declaration it belongs to. -/
public register_option linter.hazel.style.keywordAlign.deriving : Bool := {
  defValue := false
  descr := "check that `deriving` aligns with its declaration"
}

/-- `termination_by` must align with the declaration it belongs to. -/
public register_option linter.hazel.style.keywordAlign.terminationBy : Bool := {
  defValue := false
  descr := "check that `termination_by` aligns with its declaration"
}

/-- `decreasing_by` must align with the declaration it belongs to. -/
public register_option linter.hazel.style.keywordAlign.decreasingBy : Bool := {
  defValue := false
  descr := "check that `decreasing_by` aligns with its declaration"
}

/-- `where` must align with the declaration it belongs to. -/
public register_option linter.hazel.style.keywordAlign.where : Bool := {
  defValue := false
  descr := "check that `where` aligns with its declaration"
}

namespace Hazel.Style.KeywordAlign

/-- The checked keywords, each with the option that enables its check. -/
private def keywords : Array (String × Lean.Option Bool) := #[
  ("deriving", linter.hazel.style.keywordAlign.deriving),
  ("termination_by", linter.hazel.style.keywordAlign.terminationBy),
  ("decreasing_by", linter.hazel.style.keywordAlign.decreasingBy),
  ("where", linter.hazel.style.keywordAlign.where)
]

/--
Collect the checked keyword atoms of `stx`, each paired with the column of the
declaration it belongs to.  That column is the indentation of the line where
the nearest enclosing `declaration` or `letRecDecl` starts, or `ownerCol`
outside any.
-/
private partial def collectKeywords (fm : FileMap) (ownerCol : Nat) :
    Syntax → Array (Syntax × Nat)
  | stx@(.node _ kind args) =>
    let ownerCol :=
      if kind == ``Lean.Parser.Command.declaration || kind == ``Lean.Parser.Term.letRecDecl then
        (stx.getPos?.map (lineIndent fm)).getD ownerCol
      else ownerCol
    args.flatMap (collectKeywords fm ownerCol)
  | stx@(.atom _ val) => if keywords.any (·.1 == val) then #[(stx, ownerCol)] else #[]
  | _ => #[]

/--
Check that a keyword atom aligns with the declaration it belongs to, but only
if the keyword is the first token on its line (i.e., on its own line, not
inline).
-/
private def checkKeywordCol (fm : FileMap) (atom : Syntax) (keyword : String)
    (opt : Lean.Option Bool) (declCol : Nat) : CommandElabM Unit := do
  let some pos := atom.getPos? | return
  unless firstOnLine fm pos do return
  if (fm.toPosition pos).column != declCol then
    Linter.logLint opt atom
      m!"`{keyword}` should align with its declaration (column {declCol})"

/-- The keyword alignment linter. -/
def keywordAlignLinter : Lean.Linter where run := withSetOptionIn fun stx => do
  let opts ← getLinterOptions
  let enabled := keywords.filter (getLinterValue ·.2 opts)
  if enabled.isEmpty then return
  if (← MonadState.get).messages.hasErrors then return
  let fm ← getFileMap
  let some pos := stx.getPos? | return
  for (atom, declCol) in collectKeywords fm (lineIndent fm pos) stx do
    let .atom _ keyword := atom | continue
    let some (_, opt) := enabled.find? (·.1 == keyword) | continue
    checkKeywordCol fm atom keyword opt declCol

initialize addLinter keywordAlignLinter

end Hazel.Style.KeywordAlign

end -- meta section
