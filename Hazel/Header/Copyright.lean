/-
SPDX-FileCopyrightText: 2026 Mingtong Lin
SPDX-License-Identifier: MIT
-/
module

public meta import Lean
public meta import Lean.Linter
public meta import Hazel.Util

/-!
# Copyright and header linter

Checks copyright comment, module docstring presence, and duplicate imports.
The copyright check is controlled by a user-provided predicate (`copyrightCheckRef`).
-/

meta section

open Lean Elab Command Linter Hazel.Util

/-! ## Options -/

/-- Option to check the copyright header via `copyrightCheckRef`. -/
public register_option linter.hazel.header.copyright : Bool := {
  defValue := false
  descr := "check that a copyright comment precedes module"
}


/-- Option to check for duplicate imports. -/
public register_option linter.hazel.header.duplicateImports : Bool := {
  defValue := false
  descr := "check for duplicate imports"
}

/-! ## Helpers -/

namespace Hazel.Header.Copyright

/--
User-provided predicate for validating the copyright header comment.  The
argument is the leading text before the first syntax node (i.e. everything
before `module`).  Default: checks that a block comment (`/- ... -/`) exists.
-/
public initialize copyrightCheckRef : IO.Ref (String → Bool) ←
  IO.mkRef fun lead =>
    let s := lead.trimAscii.toString
    -- Check for block comment: starts with /- and contains -/ (no containsSubstr in stdlib).
    s.startsWith "/-" && (s.splitOn "-/").length > 1

/-- Return the first non-import command, or `none` if the file is import-only. -/
private def firstNonImport? : Syntax → Option Syntax
  | .node _ ``Lean.Parser.Module.module #[_header, .node _ `null args] => args[0]?
  | _ => some .missing

/-- Parse the current file from the beginning up to `pos`, optionally appending `post`. -/
private def parseUpToHere (pos : String.Pos.Raw) (post : String := "") :
    CommandElabM Syntax := do
  let fm ← getFileMap
  let upToHere : Substring.Raw :=
    { str := fm.source, startPos := ⟨0⟩, stopPos := pos }
  Parser.testParseModule (← getEnv) "linter.header" (upToHere.toString ++ post)

/-- Check for syntactically duplicate imports. -/
private def duplicateImportsCheck (imports : Array Syntax) : CommandElabM Unit := do
  let mut seen : Array Name := #[]
  for imp in imports do
    let ids := imp.getArgs.filter (·.isIdent)
    if let some modId := ids.back? then
      if seen.contains modId.getId then
        Linter.logLint linter.hazel.header.duplicateImports modId
          m!"Duplicate import: '{modId}' already imported"
      else
        seen := seen.push modId.getId

/-! ## Linter -/

/--
The header linter.  Checks are controlled by three independent options:
`linter.hazel.header.copyright`, `linter.hazel.header.moduleDoc`, and
`linter.hazel.header.duplicateImports`.
Module docstring check is in `Hazel/Header/ModuleDoc.lean`.
-/
def headerLinter : Lean.Linter where run := withSetOptionIn fun stx => do
  let opts ← getLinterOptions
  let checkCopyright := getLinterValue linter.hazel.header.copyright opts
  let checkDupImports := getLinterValue linter.hazel.header.duplicateImports opts
  unless checkCopyright || checkDupImports do return
  if (← MonadState.get).messages.hasErrors then return
  let fm ← getFileMap
  -- Parse only the header (module keyword + imports), not beyond.
  -- Going past imports risks hitting `@[expose]`, `section`, or other
  -- commands that `testParseModule` cannot handle.
  let fil ← getFileName
  let (hdrStx, _) ← Parser.parseHeader
    { inputString := fm.source, fileName := fil, fileMap := fm }
  let hdrEndPos := hdrStx.raw.getTailPos?.getD default
  -- Only run once: on commands whose start position is at or before the
  -- header end.  Later commands are past the import region.
  unless stx.getPos?.getD default ≤ hdrEndPos do return
  let upToStx ← parseUpToHere hdrEndPos "\nsection"
  -- Duplicate imports check.
  if checkDupImports then
    duplicateImportsCheck (getImports upToStx)
  -- Copyright check.
  if checkCopyright then
    let lead := match Syntax.getHeadInfo upToStx with
      | SourceInfo.original lead .. => lead.toString
      | _ => ""
    let check ← copyrightCheckRef.get
    unless check lead do
      Linter.logLint linter.hazel.header.copyright stx
        m!"Copyright header check failed.  Expected a comment block before `module`."

initialize addLinter headerLinter

end Hazel.Header.Copyright

end -- meta section
