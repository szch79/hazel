/-
SPDX-FileCopyrightText: 2026 Mingtong Lin
SPDX-License-Identifier: MIT
-/
module

public meta import Lean
public meta import Lean.Linter
public meta import Lean.Meta.Tactic.TryThis
public meta import Hazel.Util

/-!
# Import ordering linter

Three independent checks on import structure:

- `linter.hazel.header.sortedImports`: alphabetical within each modifier group,
  with per-group sort suggestion
- `linter.hazel.header.importGroupOrder`: groups in correct order (warning only,
  no auto-fix since reordering across groups can change semantics)
- `linter.hazel.header.importGroupContiguity`: same-group imports must be adjacent
  (no interleaving), with blank lines between groups
-/

meta section

open Lean Elab Command Linter Hazel.Util

/-- Imports must be sorted alphabetically within each modifier group. -/
public register_option linter.hazel.header.sortedImports : Bool := {
  defValue := false
  descr := "check that imports are sorted alphabetically within each group"
}

/-- Import groups must be in the correct order. -/
public register_option linter.hazel.header.importGroupOrder : Bool := {
  defValue := false
  descr := "check that import groups are in the correct order"
}

/-- Same-group imports must be contiguous (not interleaved with other groups). -/
public register_option linter.hazel.header.importGroupContiguity : Bool := {
  defValue := false
  descr := "check that same-group imports are adjacent with blank lines between groups"
}

namespace Hazel.Header.ImportOrder

/--
Import group key: 0 = public meta, 1 = public, 2 = meta, 3 = private.
Lower number means the group should come first.

Checks syntax children for keyword atoms rather than string-matching
the reprinted text (which would false-positive on module names containing
"public" or "meta").
-/
private def importGroupKey (imp : Syntax) : Nat :=
  -- In the new module system, `public` and `meta` are syntax nodes
  -- (`Lean.Parser.Module.public`, `Lean.Parser.Module.meta`), not atoms.
  let hasPublic := (imp.find? (·.isOfKind `Lean.Parser.Module.«public»)).isSome
  let hasMeta := (imp.find? (·.isOfKind `Lean.Parser.Module.«meta»)).isSome
  if hasPublic && hasMeta then 0
  else if hasPublic then 1
  else if hasMeta then 2
  else 3

/-- Human-readable group name. -/
private def groupName (k : Nat) : String :=
  match k with
  | 0 => "public meta" | 1 => "public" | 2 => "meta" | _ => "private"

/-- Get the module name from an import syntax. -/
private def importModuleName (imp : Syntax) : Option Name :=
  let ids := imp.getArgs.filter (·.isIdent)
  ids.back?.map (·.getId)

/-- Get the source text of an import from the FileMap. -/
private def importSourceText (imp : Syntax) (fm : FileMap) : String :=
  match imp.getPos?, imp.getTailPos? with
  | some s, some e =>
    ({ str := fm.source, startPos := s, stopPos := e : Substring.Raw }).toString.trimAscii.toString
  | _, _ => (imp.reprint.getD "").trimAscii.toString

/-- Collect runs of same-group imports from the import array. -/
private def collectGroups (imports : Array Syntax) : Array (Nat × Array Syntax) := Id.run do
  let mut groups : Array (Nat × Array Syntax) := #[]
  let mut i := 0
  while i < imports.size do
    let key := importGroupKey imports[i]!
    let mut run : Array Syntax := #[]
    while i < imports.size && importGroupKey imports[i]! == key do
      run := run.push imports[i]!
      i := i + 1
    groups := groups.push (key, run)
  return groups

/-- The import ordering linter. -/
def importOrderLinter : Lean.Linter where run := withSetOptionIn fun stx => do
  let opts ← getLinterOptions
  let chkSort := getLinterValue linter.hazel.header.sortedImports opts
  let chkGroup := getLinterValue linter.hazel.header.importGroupOrder opts
  let chkContig := getLinterValue linter.hazel.header.importGroupContiguity opts
  unless chkSort || chkGroup || chkContig do return
  if (← MonadState.get).messages.hasErrors then return
  unless stx.isOfKind ``Parser.Command.eoi do return
  let fm ← getFileMap
  let fil ← getFileName
  let (hdrStx, _) ← Parser.parseHeader
    { inputString := fm.source, fileName := fil, fileMap := fm }
  let imports := getImports hdrStx
  if imports.size ≤ 1 then return
  -- 1. Check group ordering (warning only, no suggestion)
  if chkGroup then
    for i in [:imports.size - 1] do
      let gA := importGroupKey imports[i]!
      let gB := importGroupKey imports[i + 1]!
      if gA > gB then
        Linter.logLint linter.hazel.header.importGroupOrder imports[i + 1]!
          m!"{groupName gB} imports should come before {groupName gA} imports."
  -- 2. Check alphabetical order within each group, with per-group suggestion
  if chkSort then
    let groups := collectGroups imports
    for (_, group) in groups do
      if group.size ≤ 1 then continue
      -- Check if this group is sorted
      let mut needsSort := false
      for j in [:group.size - 1] do
        let some a := importModuleName group[j]! | continue
        let some b := importModuleName group[j + 1]! | continue
        if a.toString > b.toString then
          needsSort := true
          Linter.logLint linter.hazel.header.sortedImports group[j + 1]!
            m!"Import `{b}` should come before `{a}`."
      if needsSort then
        -- Sort this group and offer suggestion
        let sorted := group.qsort fun a b =>
          let nA := (importModuleName a).getD .anonymous
          let nB := (importModuleName b).getD .anonymous
          nA.toString < nB.toString
        let sortedText := "\n".intercalate (sorted.toList.map (importSourceText · fm))
        -- Span covers this group only
        let some firstPos := group[0]!.getPos? | continue
        let some lastEnd := group.back!.getTailPos? | continue
        let groupSpan := Syntax.mkLit `str "" (SourceInfo.synthetic firstPos lastEnd false)
        liftCoreM <| Lean.Meta.Tactic.TryThis.addSuggestion groupSpan
          { suggestion := .string sortedText
            toCodeActionTitle? := some fun _ => "Sort imports in this group" }
          (origSpan? := groupSpan)
          (header := "Sort imports:")
  -- 3. Check group contiguity
  if chkContig then
    -- Track which groups have been seen
    let mut seenGroups : Array Nat := #[]
    let mut lastGroup : Option Nat := none
    for imp in imports do
      let key := importGroupKey imp
      if let some last := lastGroup then
        if key != last then
          -- Switching groups: check if this group was seen before
          if seenGroups.contains key then
            Linter.logLint linter.hazel.header.importGroupContiguity imp
              m!"{groupName key} imports should be contiguous (group is split)."
      if !seenGroups.contains key then
        seenGroups := seenGroups.push key
      lastGroup := some key

initialize addLinter importOrderLinter

end Hazel.Header.ImportOrder

end -- meta section
