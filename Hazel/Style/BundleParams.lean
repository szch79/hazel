/-
SPDX-FileCopyrightText: 2026 Mingtong Lin
SPDX-License-Identifier: MIT
-/
module

public meta import Lean
public meta import Lean.Linter

/-!
# Bundle parameters linter

Checks that adjacent binders with the same type and binder kind are bundled
into a single multi-name binder.

```
-- Bad
theorem foo {a : Nat} {b : Nat} (h : a = b) : ...

-- Good
theorem foo {a b : Nat} (h : a = b) : ...
```

Purely syntactic — compares source type text, no MetaM needed.
-/

meta section

open Lean Elab Command Linter

/-- Adjacent same-type binders should be bundled. -/
public register_option linter.hazel.style.bundleParams : Bool := {
  defValue := false
  descr := "check that adjacent same-type binders are bundled"
}

namespace Hazel.Style.BundleParams

/-- Binder kinds we check (not instance binders). -/
private def isBundleableBinder (stx : Syntax) : Bool :=
  stx.isOfKind ``Parser.Term.explicitBinder ||
  stx.isOfKind ``Parser.Term.implicitBinder ||
  stx.isOfKind ``Parser.Term.strictImplicitBinder

/--
Extract the type syntax from a binder node.  The type is inside
a `binderType` child which has structure `":" >> termParser`.
We return the reprinted type text for comparison.
-/
private def getBinderTypeReprint (stx : Syntax) : Option String :=
  -- The binder structure is: bracket, names, binderType, ..., bracket
  -- binderType is at index [2] for all three kinds
  -- binderType has kind `null` or `Lean.Parser.Term.binderType`
  -- and contains ":" at [0] and the type term at [1]
  let binderType := stx[2]
  -- binderType might be a null node (when type is omitted: `{a b}`)
  if binderType.isMissing || binderType.getNumArgs == 0 then none
  else
    -- The type term is the last meaningful child of binderType
    -- For `binderType`, structure is ":" then term
    -- reprint the whole binderType for comparison (includes the colon)
    binderType.reprint

/--
Extract the names from a binder node.  Names are at index [1]
(a `null` node containing `binderIdent`s).
-/
private def getBinderNames (stx : Syntax) : Array String := Id.run do
  let namesNode := stx[1]
  let mut names : Array String := #[]
  for arg in namesNode.getArgs do
    if arg.isIdent then
      names := names.push arg.getId.toString
    else if let some r := arg.reprint then
      names := names.push r
  return names

/--
Check if a binder has a default value or tactic.
For `explicitBinder`, index [3] is the optional default/tactic.
-/
private def hasDefaultValue (stx : Syntax) : Bool :=
  if stx.isOfKind ``Parser.Term.explicitBinder then
    -- explicitBinder: ( names binderType optDefault )
    -- optDefault is at [3] if it exists and is not missing
    stx.getNumArgs > 4 && !stx[3].isMissing && stx[3].getNumArgs > 0
  else false

/--
Build the opening bracket for a binder kind.
-/
private def openBracket (stx : Syntax) : String :=
  if stx.isOfKind ``Parser.Term.explicitBinder then "("
  else if stx.isOfKind ``Parser.Term.implicitBinder then "{"
  else "⦃"

/--
Build the closing bracket for a binder kind.
-/
private def closeBracket (stx : Syntax) : String :=
  if stx.isOfKind ``Parser.Term.explicitBinder then ")"
  else if stx.isOfKind ``Parser.Term.implicitBinder then "}"
  else "⦄"

/-- The bundle parameters linter. -/
def bundleParamsLinter : Linter where run := withSetOptionIn fun stx => do
  unless getLinterValue linter.hazel.style.bundleParams (← getLinterOptions) do return
  if (← MonadState.get).messages.hasErrors then return
  unless stx.isOfKind ``Parser.Command.declaration do return
  let some sigStx := stx.find? fun s =>
    s.isOfKind ``Parser.Command.declSig ||
    s.isOfKind ``Parser.Command.optDeclSig
  | return
  let binders := sigStx[0]
  let args := binders.getArgs
  if args.size < 2 then return
  -- Check adjacent pairs
  let mut i := 0
  while i + 1 < args.size do
    let a := args[i]!
    let b := args[i + 1]!
    -- Both must be bundleable (not instance binders)
    unless isBundleableBinder a && isBundleableBinder b do
      i := i + 1
      continue
    -- Same binder kind
    unless a.getKind == b.getKind do
      i := i + 1
      continue
    -- Neither has default value
    if hasDefaultValue a || hasDefaultValue b then
      i := i + 1
      continue
    -- Same type (compare reprinted text)
    let some typeA := getBinderTypeReprint a | do i := i + 1; continue
    let some typeB := getBinderTypeReprint b | do i := i + 1; continue
    unless typeA == typeB do
      i := i + 1
      continue
    -- Found a bundleable pair — collect all consecutive binders with same type/kind
    let mut namesAll := getBinderNames a
    let mut j := i + 1
    while j < args.size do
      let c := args[j]!
      unless isBundleableBinder c && c.getKind == a.getKind && !hasDefaultValue c do break
      let some typeC := getBinderTypeReprint c | break
      unless typeC == typeA do break
      namesAll := namesAll ++ getBinderNames c
      j := j + 1
    -- Build suggestion
    let ob := openBracket a
    let cb := closeBracket a
    let nameList := " ".intercalate namesAll.toList
    let suggestion := s!"{ob}{nameList} {typeA}{cb}"
    Linter.logLint linter.hazel.style.bundleParams a
      m!"Adjacent binders could be bundled: `{suggestion}`"
    -- Skip past the group we just reported
    i := j
  return

initialize addLinter bundleParamsLinter

end Hazel.Style.BundleParams

end -- meta section
