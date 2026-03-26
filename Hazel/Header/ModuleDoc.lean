/-
SPDX-FileCopyrightText: 2026 Mingtong Lin
SPDX-License-Identifier: MIT
-/
module

public meta import Lean
public meta import Lean.Linter

/-!
# Module docstring linter

Checks that every file has a `/-! ... -/` module docstring and that it is the
first command after imports.  Runs at `eoi` (end of input) so it can see the
full file structure.
-/

meta section

open Lean Elab Command Linter

/-- Require a module docstring (`/-! ... -/`) as the first command after imports. -/
public register_option linter.hazel.header.moduleDoc : Bool := {
  defValue := false
  descr := "require a module docstring after imports"
}

namespace Hazel.Header.ModuleDoc

/-- Check if a string contains only whitespace. -/
private def isOnlyWhitespace (s : String) : Bool :=
  s.all fun c => c == ' ' || c == '\n' || c == '\r' || c == '\t'

/-- The module docstring linter.  Runs at `eoi`. -/
def moduleDocLinter : Lean.Linter where run := withSetOptionIn fun stx => do
  unless getLinterValue linter.hazel.header.moduleDoc (← getLinterOptions) do return
  unless stx.isOfKind ``Parser.Command.eoi do return
  if (← MonadState.get).messages.hasErrors then return
  let fm ← getFileMap
  let env ← getEnv
  let mdDocs := (getMainModuleDoc env).toArray
  -- Parse header to find where imports end
  let fil ← getFileName
  let (hdrStx, _) ← Parser.parseHeader
    { inputString := fm.source, fileName := fil, fileMap := fm }
  let hdrEndPos := hdrStx.raw.getTailPos?.getD default
  -- Skip re-export files: nothing after imports means nothing to document.
  let afterImports : Substring.Raw :=
    { str := fm.source, startPos := hdrEndPos, stopPos := fm.source.rawEndPos }
  if isOnlyWhitespace afterImports.toString then return
  if mdDocs.isEmpty then
    -- No module docstring anywhere in the file.
    Linter.logLint linter.hazel.header.moduleDoc stx
      m!"Missing module docstring.  Please add a `/-! ... -/` comment after the imports."
  else
    -- There is a module docstring.  Check it's the first thing after imports.
    if let some firstDoc := mdDocs[0]? then
      let docStartPos := fm.ofPosition firstDoc.declarationRange.pos
      -- Extract text between end of imports and start of first module doc.
      -- If there's any non-whitespace content, something comes before the doc.
      if docStartPos > hdrEndPos then
        -- Extract text between end of imports and start of first module doc.
        let between : Substring.Raw := { str := fm.source, startPos := hdrEndPos, stopPos := docStartPos }
        unless isOnlyWhitespace between.toString do
          -- Find the first non-whitespace position for better error location
          Linter.logLint linter.hazel.header.moduleDoc stx
            m!"Module docstring should be the first command after imports.  \
               Other commands appear before `/-! ... -/`."

initialize addLinter moduleDocLinter

end Hazel.Header.ModuleDoc

end -- meta section
