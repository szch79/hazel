/-
SPDX-FileCopyrightText: 2026 Mingtong Lin
SPDX-License-Identifier: MIT
-/
module

public meta import Lean
public meta import Lean.Linter

/-!
# Module docstring linter

Checks that every file has a `/-! ... -/` module docstring and that it comes
right after the imports.  Whole-module `set_option` commands may precede it:
that is where the stdlib puts them, and `doc.verso` only affects the
docstring's parsing when set before it.  Runs at `eoi` (end of input) so it
can see the full file structure.
-/

meta section

open Lean Elab Command Linter

/-- Require a module docstring (`/-! ... -/`) right after the imports, with
only `set_option` commands allowed in between. -/
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
  let inputCtx : Parser.InputContext := { inputString := fm.source, fileName := fil, fileMap := fm }
  let (hdrStx, parserState, _) ← Parser.parseHeader inputCtx
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
        -- Reparse the commands before the doc: `set_option` commands (and
        -- comments, which are trivia) are allowed there, anything else is a
        -- placement violation.
        let pmctx : Parser.ParserModuleContext := { env, options := ← getOptions }
        let mut ps := parserState
        let mut msgs : MessageLog := .empty
        while ps.pos < docStartPos do
          let (cmd, ps', msgs') := Parser.parseCommand inputCtx pmctx ps msgs
          ps := ps'
          msgs := msgs'
          if cmd.isOfKind ``Parser.Command.eoi then break
          if cmd.getPos?.getD docStartPos >= docStartPos then break
          unless cmd.isOfKind ``Parser.Command.set_option do
            Linter.logLint linter.hazel.header.moduleDoc stx
              m!"Module docstring should appear right after the imports; only \
                 `set_option` commands may precede it."
            break

initialize addLinter moduleDocLinter

end Hazel.Header.ModuleDoc

end -- meta section
