/-
SPDX-FileCopyrightText: 2026 Mingtong Lin
SPDX-License-Identifier: MIT
-/
module

public meta import Lean
public meta import Lean.Linter
public meta import Lean.Meta.Tactic.TryThis

/-!
# Dot notation linter

Flags cases where dot notation could be used but isn't.  For example,
`List.length l` could be written as `l.length`.

The check: for each function application `Foo.bar x ...` in the `InfoTree`,
if `bar` is in the namespace `Foo` and some explicit argument has type with
head `Foo`, suggest rewriting to dot notation.
-/

meta section

open Lean Meta Elab Command Linter Server

/-- Suggest dot notation where applicable. -/
public register_option linter.hazel.style.preferDotNotation : Bool := {
  defValue := false
  descr := "suggest dot notation where applicable"
}

namespace Hazel.Style.PreferDotNotation

/--
Result of checking a function application for dot notation.
-/
private structure DotResult where
  shortName : String
  receiverStr : String

/--
Check if a function application could use dot notation.  If so, return the
short function name and the pretty-printed receiver.
-/
private def checkDotNotation (e : Expr) : MetaM (Option DotResult) := do
  let fn := e.getAppFn
  let .const fnName _ := fn | return none
  let shortName := fnName.getString!
  let ns := fnName.getPrefix
  if ns.isAnonymous then return none
  let fnInfo ← getFunInfo fn
  let args := e.getAppArgs
  -- Find the first explicit argument whose type head matches the namespace.
  let mut firstExplicitMatch : Option Nat := none
  for i in [:min fnInfo.paramInfo.size args.size] do
    let pi := fnInfo.paramInfo[i]!
    if pi.isImplicit || pi.isInstImplicit || pi.isStrictImplicit then continue
    let argType ← inferType args[i]!
    if let .const typeName _ := argType.getAppFn then
      -- Match namespace: either equal, or one is a suffix of the other
      -- (handles _private prefix from module system)
      if typeName == ns || ns.isSuffixOf typeName || typeName.isSuffixOf ns then
        firstExplicitMatch := some i
        break
  let some receiverIdx := firstExplicitMatch | return none
  -- Verify that no implicit argument before the receiver also matches
  -- the namespace.  If an implicit matches first, dot notation would
  -- fill that implicit instead, producing a type error.
  for i in [:receiverIdx] do
    let pi := fnInfo.paramInfo[i]!
    if !pi.isImplicit && !pi.isStrictImplicit then continue
    let argType ← inferType args[i]!
    if let .const typeName _ := argType.getAppFn then
      if typeName == ns || ns.isSuffixOf typeName || typeName.isSuffixOf ns then
        return none  -- implicit matches first, dot notation unsafe
  let receiver := args[receiverIdx]!
  -- Coercion detection: if receiver is not a bare FVar, the elaborator may
  -- have inserted a coercion (e.g., Subtype.val).  Dot notation resolves on
  -- the SOURCE type (pre-coercion), not the Expr type.  Unwrap to the inner
  -- FVar and verify its declared type matches the function namespace.
  if !receiver.isFVar then
    -- Find the innermost FVar by unwrapping applications
    let mut inner := receiver
    while inner.isApp do inner := inner.appArg!
    if inner.isFVar then
      -- Check inner FVar's declared type against the function namespace
      let innerType ← inferType inner
      let innerHead := innerType.getAppFn
      -- Also try whnf to see through abbrevs
      let innerTypeR ← whnf innerType
      let innerHeadR := innerTypeR.getAppFn
      let matchesNs := fun (head : Expr) =>
        if let .const tn _ := head then
          tn == ns || ns.isSuffixOf tn || tn.isSuffixOf ns
        else false
      unless matchesNs innerHead || matchesNs innerHeadR do
        return none  -- source type doesn't match — coercion involved
    -- Non-FVar, non-FVar-inner: complex expression, allow (might be (f x).method)
  -- Skip metavariables
  if receiver.isMVar then return none
  -- Skip hygienic FVars
  if receiver.isFVar then
    let ldecl ← receiver.fvarId!.getDecl
    if ldecl.userName.hasMacroScopes then return none
    if (ldecl.userName.toString.splitOn "✝").length > 1 then return none
  let receiverStr ← match receiver with
    | .fvar fvarId => pure (← fvarId.getDecl).userName.toString
    | e => pure (toString (← PrettyPrinter.ppExpr e))
  -- Skip if pp'd receiver contains hygienic markers or coercion arrow
  if (receiverStr.splitOn "✝").length > 1 then return none
  if receiverStr.startsWith "↑" then return none
  return some { shortName, receiverStr }

/--
Find the source ident that explicitly calls the function.  Returns the source
`Name` if found, or `none` if the call uses dot notation or isn't present.
Uses suffix matching for module-qualified names (e.g., source `Array.size`
matches Expr `Std.Data.Array.size`).  Only suffix-matches on qualified
idents (with namespace prefix) to avoid matching bare field names like `union`
inside dot notation `s.union`.
-/
private def findExplicitCall (stx : Syntax) (fnName : Name) : Option Name :=
  (stx.find? (fun s =>
    s.isIdent &&
    let id := s.getId
    if id == fnName then true
    else if !id.getPrefix.isAnonymous then
      id.isSuffixOf fnName || fnName.isSuffixOf id
    else false
  )).map (·.getId)

/--
Build the suggestion string from source text.  Replaces `Ns.fn ... receiver ...`
with `receiver.fn ...` by:
1. Splitting source at the function name to isolate args
2. Removing the first occurrence of ` receiver` (with leading space) from args
3. Prepending `receiver.shortName` to remaining args

**Limitation**: uses string matching on source text, which is fragile for:
- Receiver name appearing inside other tokens (mitigated by leading space)
- Multi-line expressions (source positions may span lines)
- Complex receiver expressions (e.g., `(List.filter p l).length` — the receiver
  is a parenthesized sub-expression, not a simple name)

These edge cases are rare in practice.  The suggestion may be wrong in those
cases but the lint warning itself is still correct.
-/
private def buildSuggestion (stx : Syntax) (shortName : String) (fnName : Name)
    (fm : FileMap) (receiverStr : String) : Option String := do
  let some startPos := stx.getPos? | failure
  let some endPos := stx.getTailPos? | failure
  let srcText : String :=
    { str := fm.source, startPos := startPos, stopPos := endPos : Substring.Raw }.toString
  let fnStr := fnName.toString
  -- Split at the function name to isolate the arguments portion.
  -- If the function name appears multiple times (e.g., `List.length (List.length l)`),
  -- `intercalate` restores inner occurrences, keeping only the outermost stripped.
  let fnParts := srcText.splitOn fnStr
  if fnParts.length < 2 then failure
  let argsText := fnStr.intercalate fnParts.tail!
  -- Remove the first occurrence of the receiver from the arguments.
  -- We match ` receiver` (with leading space) to avoid matching inside
  -- other tokens (e.g., receiver "l" inside "length").
  let needle := s!" {receiverStr}"
  -- Split source text at receiver to remove it from args (string surgery).
  let parts := argsText.splitOn needle
  if parts.length < 2 then failure
  let beforeReceiver := parts[0]!
  -- Rejoin remaining parts (restores later occurrences of the receiver)
  let afterReceiver := needle.intercalate (parts.drop 2)
  let gap := if parts.length > 1 then parts[1]! else ""
  let remainingArgs := s!"{beforeReceiver}{gap}{afterReceiver}".trimAscii.toString
  if remainingArgs.isEmpty then
    return s!"{receiverStr}.{shortName}"
  else
    return s!"{receiverStr}.{shortName} {remainingArgs}"

/-- The dot notation linter. -/
def dotNotationLinter : Lean.Linter where run := withSetOptionIn fun _stx => do
  unless getLinterValue linter.hazel.style.preferDotNotation (← getLinterOptions) &&
         (← getInfoState).enabled do
    return
  if (← MonadState.get).messages.hasErrors then return
  let trees ← getInfoTrees
  let fm ← getFileMap
  let mut termInfos : Array (ContextInfo × TermInfo) := #[]
  for tree in trees.toArray do
    termInfos := tree.foldInfo (init := termInfos) fun ctx info acc =>
      match info with
      | .ofTermInfo ti => acc.push (ctx, ti)
      | _ => acc
  for (ctx, ti) in termInfos do
    if ti.isBinder then continue
    let some _ := ti.stx.getPos? | continue
    -- Skip synthetic syntax (from macro expansion, pattern matching, etc.)
    match ti.stx.getHeadInfo with
    | .original .. => pure ()
    | _ => continue
    let fn := ti.expr.getAppFn
    let .const fnName _ := fn | continue
    let some srcFnName := findExplicitCall ti.stx fnName | continue
    -- Check if dot notation is applicable and get the receiver name
    let some result ← liftCoreM do
      try ti.runMetaM ctx (checkDotNotation ti.expr)
      catch _ => return none
      | continue
    -- Build suggestion using the SOURCE function name (not the fully-qualified
    -- Expr name) so that string splitting on source text works correctly.
    let suggestion? := buildSuggestion ti.stx result.shortName srcFnName fm result.receiverStr
    match suggestion? with
    | some suggestion =>
      Linter.logLint linter.hazel.style.preferDotNotation ti.stx
        m!"Use dot notation: `{suggestion}`"
      liftCoreM <| Lean.Meta.Tactic.TryThis.addSuggestion ti.stx
        { suggestion := .string suggestion
          toCodeActionTitle? := some fun s => s!"Use dot notation: {s}" }
        (origSpan? := ti.stx)
        (header := "Try this:")
    | none =>
      Linter.logLint linter.hazel.style.preferDotNotation ti.stx
        m!"Use dot notation: `{result.receiverStr}.{result.shortName}`"

initialize addLinter dotNotationLinter

end Hazel.Style.PreferDotNotation

end -- meta section
