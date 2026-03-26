/-
SPDX-FileCopyrightText: 2026 Mingtong Lin
SPDX-License-Identifier: MIT
-/
module

public meta import Lean
public meta import Lean.Linter
public meta import Hazel.Util

/-!
# Inline `by` linter

Checks that `by` is on the same line as the preceding token (`:=`, `=>`, etc.).
-/

meta section

open Lean Elab Command Linter Hazel.Util

/-- `by` must be on the same line as the preceding token. -/
public register_option linter.hazel.style.inlineBy : Bool := {
  defValue := false
  descr := "check that `by` is on the same line as the preceding token"
}

namespace Hazel.Style.InlineBy

/--
The inline `by` linter.  For each `by` atom, check that the source line
immediately before the `by` position contains a non-whitespace token (i.e.,
`by` is not on its own line).
-/
def inlineByLinter : Lean.Linter where run := withSetOptionIn fun stx => do
  unless getLinterValue linter.hazel.style.inlineBy (← getLinterOptions) do return
  if (← MonadState.get).messages.hasErrors then return
  let fm ← getFileMap
  let lines := (fm.source.splitOn "\n").toArray
  let byAtoms := findAll stx fun s =>
    match s with
    | .atom _ val => val == "by"
    | _ => false
  for byAtom in byAtoms do
    let some byPos := byAtom.getPos? | continue
    let byPosition := fm.toPosition byPos
    -- `by` is fine if something non-whitespace precedes it on the same line
    -- (e.g., `:= by` or `=> by`)
    if byPosition.column == 0 then
      -- `by` at column 0 means nothing precedes it
      Linter.logLint linter.hazel.style.inlineBy byAtom
        m!"`by` should not start a new line"
    else
      -- Check if everything before `by` on its line is whitespace
      let lineIdx := byPosition.line - 1  -- Position.line is 1-indexed
      if lineIdx < lines.size then
        let line := lines[lineIdx]!
        let beforeBy := (line.take byPosition.column).trimAscii.toString
        if beforeBy.isEmpty then
          Linter.logLint linter.hazel.style.inlineBy byAtom
            m!"`by` should not start a new line"

initialize addLinter inlineByLinter

end Hazel.Style.InlineBy

end -- meta section
