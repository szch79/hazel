/-
SPDX-FileCopyrightText: 2026 Mingtong Lin
SPDX-License-Identifier: MIT
-/
module

public meta import Lean
public meta import Lean.Linter
public meta import Hazel.Util

/-!
# Inline show linter

Flags multi-line `show` proofs that appear inline inside `rw [...]`,
`simp [...]`, `exact (show ...)`, etc.  These should be extracted to
`have` for readability.

Single-line inline `show` proofs are fine and not flagged.
-/

meta section

open Lean Elab Command Linter Hazel.Util

/-- Flag multi-line inline `show` proofs (suggest extracting to `have`). -/
public register_option linter.hazel.tactic.inlineShow : Bool := {
  defValue := false
  descr := "flag multi-line inline `show` proofs inside rw/simp/exact"
}

namespace Hazel.Tactic.InlineShow

/-- Check if a syntax node is a `show` term (not tactic). -/
private def isShowTerm (stx : Syntax) : Bool :=
  stx.isOfKind ``Parser.Term.show

/--
Check if a `show` node is inside a tactic argument list (rw, simp, exact,
etc.) rather than standalone.  We check if any ancestor is a rw/simp/exact
tactic by walking up via `findAll` — since we can't walk up, we instead
check: does the show appear as a descendant of a tactic argument?

Simpler approach: a `show` term appearing anywhere inside a `byTactic`
block that is NOT the direct child of a tactic sequence is "inline."
We approximate: if the `show` is inside a `rw`/`simp` argument list
(i.e., inside a `null` node that's a child of `rwRuleSeq` or similar),
it's inline.
-/
private def isInsideTacticArg (stx : Syntax) (showStx : Syntax) : Bool :=
  -- Find all rw/simp/exact nodes, check if showStx is a descendant
  let tacNodes := findAll stx fun s =>
    s.isOfKind `Lean.Parser.Tactic.rwSeq ||
    s.isOfKind ``Parser.Tactic.simp ||
    s.isOfKind ``Parser.Tactic.simpAll ||
    s.isOfKind ``Parser.Tactic.exact ||
    s.isOfKind ``Parser.Tactic.apply
  tacNodes.any fun tac =>
    -- Check if showStx is a descendant of this tactic
    let shows := findAll tac isShowTerm
    shows.any fun s =>
      s.getPos? == showStx.getPos? && s.getTailPos? == showStx.getTailPos?

/-- The inline show linter. -/
def inlineShowLinter : Lean.Linter where run := withSetOptionIn fun stx => do
  unless getLinterValue linter.hazel.tactic.inlineShow (← getLinterOptions) do return
  if (← MonadState.get).messages.hasErrors then return
  let fm ← getFileMap
  -- Find all `show` term nodes
  let showNodes := findAll stx isShowTerm
  for showNode in showNodes do
    -- Must be inside a tactic argument, not standalone
    unless isInsideTacticArg stx showNode do continue
    -- Check if the show spans multiple lines
    let some startPos := showNode.getPos? | continue
    let some endPos := showNode.getTailPos? | continue
    let startLine := (fm.toPosition startPos).line
    let endLine := (fm.toPosition endPos).line
    if startLine == endLine then continue  -- single-line, fine
    -- Multi-line inline show — flag it
    Linter.logLint linter.hazel.tactic.inlineShow showNode
      m!"Multi-line inline `show` proof.  Consider extracting to `have` for readability."

initialize addLinter inlineShowLinter

end Hazel.Tactic.InlineShow

end -- meta section
