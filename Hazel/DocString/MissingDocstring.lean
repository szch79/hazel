/-
SPDX-FileCopyrightText: 2026 Mingtong Lin
SPDX-License-Identifier: MIT
-/
module

public meta import Lean
public meta import Lean.Linter
public meta import Hazel.DocString.Prose

/-!
# Missing docstring linter

Flags public `def`, `theorem`, `class`, `structure`, and `inductive` declarations
that lack a docstring.
-/

meta section

open Lean Elab Command Linter

/-- Public declarations must have a docstring. -/
public register_option linter.hazel.docstring.missingDocstring : Bool := {
  defValue := false
  descr := "check that public declarations have docstrings"
}

namespace Hazel.DocString.MissingDocstring

open Hazel.DocString.Prose (getDeclModifiers)

/-- The missing docstring linter. -/
def missingDocstringLinter : Lean.Linter where run := withSetOptionIn fun stx => do
  unless getLinterValue linter.hazel.docstring.missingDocstring (← getLinterOptions) do return
  if (← MonadState.get).messages.hasErrors then return
  unless stx.getKind == ``Parser.Command.declaration do return
  -- Skip instances — they typically don't need docstrings
  if stx.find? (·.isOfKind ``Parser.Command.instance) |>.isSome then return
  -- Check all declModifiers in the tree
  let mods := getDeclModifiers stx
  -- If any declModifiers has a docstring, we're good
  let hasDoc := mods.any fun m =>
    let docStx := m[0][0]
    !docStx.isMissing
  if hasDoc then return
  -- Check if private (visibility is at index 2 in declModifiers)
  let isPriv := mods.any fun m =>
    let visMod := m[2]
    !visMod.isMissing && (visMod.reprint.getD "").trimAscii.toString == "private"
  if isPriv then return
  -- Find the declaration name for a better message
  let declId := stx.find? (·.isOfKind ``Parser.Command.declId)
  let target := declId.getD stx
  Linter.logLint linter.hazel.docstring.missingDocstring target
    m!"Public declaration is missing a docstring."

initialize addLinter missingDocstringLinter

end Hazel.DocString.MissingDocstring

end -- meta section
