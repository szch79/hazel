/-
SPDX-FileCopyrightText: 2026 Mingtong Lin
SPDX-License-Identifier: MIT
-/
module

public meta import Lean
public meta import Lean.Linter
public meta import Hazel.Util

/-!
# Inline `do` linter

Checks that `do` is on the same line as `:=` (i.e., `:= do`, not `do` on its
own line).
-/

meta section

open Lean Elab Command Linter Hazel.Util

/-- `do` must be on the same line as the preceding token. -/
public register_option linter.hazel.style.inlineDo : Bool := {
  defValue := false
  descr := "check that `do` is on the same line as the preceding token"
}

namespace Hazel.Style.InlineDo

/--
The inline `do` linter.  For each `do` atom, check that something non-whitespace
precedes it on the same line.
-/
def inlineDoLinter : Lean.Linter where run := withSetOptionIn fun stx => do
  unless getLinterValue linter.hazel.style.inlineDo (← getLinterOptions) do return
  if (← MonadState.get).messages.hasErrors then return
  let fm ← getFileMap
  let lines := (fm.source.splitOn "\n").toArray
  let doAtoms := findAll stx fun s =>
    match s with
    | .atom _ val => val == "do"
    | _ => false
  for doAtom in doAtoms do
    let some doPos := doAtom.getPos? | continue
    let doPosition := fm.toPosition doPos
    let lineIdx := doPosition.line - 1
    if lineIdx < lines.size then
      let line := lines[lineIdx]!
      let beforeDo := (line.take doPosition.column).trimAscii.toString
      if beforeDo.isEmpty then
        Linter.logLint linter.hazel.style.inlineDo doAtom
          m!"`do` should be on the same line as the preceding token"

initialize addLinter inlineDoLinter

end Hazel.Style.InlineDo

end -- meta section
