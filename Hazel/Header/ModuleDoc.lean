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
  -- Module docs land in different environment extensions depending on their
  -- format: Markdown in `getMainModuleDoc`, Verso (under `doc.verso.module`)
  -- in `getMainVersoModuleDocs`.  Collect source ranges from both.
  let docRanges := (getMainModuleDoc env).toArray.map (·.declarationRange) ++
    (getMainVersoModuleDocs env).snippets.toArray.map (·.declarationRange)
  -- Parse header to find where imports end
  let fil ← getFileName
  let (hdrStx, _) ← Parser.parseHeader
    { inputString := fm.source, fileName := fil, fileMap := fm }
  let hdrEndPos := hdrStx.raw.getTailPos?.getD default
  -- Skip re-export files: nothing after imports means nothing to document.
  let afterImports : Substring.Raw :=
    { str := fm.source, startPos := hdrEndPos, stopPos := fm.source.rawEndPos }
  if isOnlyWhitespace afterImports.toString then return
  if docRanges.isEmpty then
    -- No module docstring anywhere in the file.
    Linter.logLint linter.hazel.header.moduleDoc stx
      m!"Missing module docstring.  Please add a `/-! ... -/` comment after the imports."
  else
    -- There is a module docstring.  Check it's the first thing after imports.
    -- Mixing formats is an elaboration error, so the earliest range across
    -- both stores is the first module doc in the file.
    let mut docStartPos := fm.source.rawEndPos
    for r in docRanges do
      let p := fm.ofPosition r.pos
      if p < docStartPos then docStartPos := p
    -- Extract text between end of imports and start of first module doc.
    -- If there's any non-whitespace content, something comes before the doc.
    if docStartPos > hdrEndPos then
      let between : Substring.Raw := { str := fm.source, startPos := hdrEndPos, stopPos := docStartPos }
      unless isOnlyWhitespace between.toString do
        Linter.logLint linter.hazel.header.moduleDoc stx
          m!"Module docstring should be the first command after imports.  \
             Other commands appear before `/-! ... -/`."

initialize addLinter moduleDocLinter

end Hazel.Header.ModuleDoc

end -- meta section
