/-
SPDX-FileCopyrightText: 2026 Mingtong Lin
SPDX-License-Identifier: MIT
-/
module

public meta import Lean
public meta import Lean.Linter
public meta import Hazel.Util

/-!
# Import restriction linters

- `linter.hazel.header.noImportAll`: flag `import all` usage
- `linter.hazel.header.noBroadImport`: flag imports of forbidden module prefixes
-/

meta section

open Lean Elab Command Linter Hazel.Util

/-- Flag `import all` usage. -/
public register_option linter.hazel.header.noImportAll : Bool := {
  defValue := false
  descr := "warn on `import all` usage"
}

/-- Flag imports of forbidden module prefixes. -/
public register_option linter.hazel.header.noBroadImport : Bool := {
  defValue := false
  descr := "warn on imports of forbidden module prefixes"
}

namespace Hazel.Header.ImportRestrict

/--
User-provided list of forbidden module name prefixes for `noBroadImport`.
Default: empty (user sets their own).
-/
public initialize broadImportForbiddenRef : IO.Ref (Array Name) ← IO.mkRef #[]

/-- The import restriction linter. -/
def importRestrictLinter : Lean.Linter where run := withSetOptionIn fun stx => do
  let opts ← getLinterOptions
  let chkAll := getLinterValue linter.hazel.header.noImportAll opts
  let chkBroad := getLinterValue linter.hazel.header.noBroadImport opts
  unless chkAll || chkBroad do return
  if (← MonadState.get).messages.hasErrors then return
  unless stx.isOfKind ``Parser.Command.eoi do return
  let fm ← getFileMap
  let fil ← getFileName
  let (hdrStx, _) ← Parser.parseHeader
    { inputString := fm.source, fileName := fil, fileMap := fm }
  let imports := getImports hdrStx
  for imp in imports do
    -- Check for `import all`: look for an `all` atom in the import's children
    if chkAll then
      let hasAll := imp.getArgs.any fun arg =>
        match arg with
        | .atom _ val => val == "all"
        | _ => false
      if hasAll then
        Linter.logLint linter.hazel.header.noImportAll imp
          m!"Avoid `import all`; prefer granular imports."
    -- Check for broad imports
    if chkBroad then
      let forbidden ← broadImportForbiddenRef.get
      let ids := imp.getArgs.filter (·.isIdent)
      if let some modId := ids.back? then
        let modName := modId.getId
        for pfx in forbidden do
          if modName == pfx || modName.getRoot == pfx then
            Linter.logLint linter.hazel.header.noBroadImport imp
              m!"Avoid importing top-level aggregator `{modName}`; use granular imports."
            break

initialize addLinter importRestrictLinter

end Hazel.Header.ImportRestrict

end -- meta section
