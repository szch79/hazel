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
# Dot notation linter

Flags prefix calls `Ns.f ... x ...` that could be written `x.f ...`.  For
example, `List.length l` could be written as `l.length`.

A call is flagged when `x.f` would elaborate to the same term.  The check
mirrors the two rules Lean applies to dot notation:

- `x.f` looks up `f` in the namespace of the head of the type of `x`,
  unfolding definitions until some namespace has it (`resolveLVal`).  The
  linter uses the type of `x` as written, before any coercion the call
  inserted.
- `x.f` passes `x` to the first parameter whose declared type is headed by
  that namespace, skipping parameters bound by named arguments
  (`addLValArg`).  The linter requires this to be the explicit parameter
  that `x` fills in the call.

Only calls written in prefix form are checked: pipelines (`|>`, `<|`, `$`),
`@f` calls and other notations are not.  `x.f` elaborates `x` without an
expected type, which the `InfoTree` cannot show, so receivers whose syntax
kind is in `skippedReceiverKindsRef` are never flagged.  By default these are
the forms that need an expected type, such as `do` blocks and anonymous
constructors.  For the same reason, a local variable bound without a type
annotation is never flagged: its type may have been inferred from the call.
-/

meta section

open Lean Meta Elab Command Linter Server Hazel.Util

/-- Suggest dot notation where applicable. -/
public register_option linter.hazel.style.preferDotNotation : Bool := {
  defValue := false
  descr := "suggest dot notation where applicable"
}

namespace Hazel.Style.PreferDotNotation

/-! ## Configuration -/

/--
Syntax kinds of receivers that are never flagged.  `x.f` elaborates `x`
without an expected type, so a receiver that needs one cannot be moved in
front of the dot.  The default lists every such form: `do`, `by`, `fun`,
`nofun` and `nomatch` blocks, anonymous constructors, `.ctor` shorthand,
structure instances, coercion arrows, holes, `sorry`, and numeric literals
(which default to `Nat`).  Parentheses around a receiver are looked through,
and an application headed by one of these kinds, such as `.some 1`, is
skipped too.  Extend in your project's init module:

```
meta initialize
  Hazel.Style.PreferDotNotation.skippedReceiverKindsRef.modify
    (· ++ #[``termIfThenElse, ``termDepIfThenElse, ``Lean.Parser.Term.match])
```
-/
public initialize skippedReceiverKindsRef : IO.Ref (Array SyntaxNodeKind) ←
  IO.mkRef #[``Parser.Term.do, ``Parser.Term.byTactic, ``Parser.Term.fun,
    ``Parser.Term.nofun, ``Parser.Term.nomatch, ``Parser.Term.anonymousCtor,
    ``Parser.Term.dotIdent, ``Parser.Term.structInst, ``coeNotation, ``coeFunNotation,
    ``coeSortNotation, ``Parser.Term.hole, ``Parser.Term.syntheticHole, ``Parser.Term.sorry,
    numLitKind, scientificLitKind]

/-! ## Syntax -/

/-- A prefix call `Ns.f a₁ ... aₙ` as written in the source. -/
private structure Call where
  /-- The function identifier. -/
  fn : Syntax
  /-- The positional arguments, in order. -/
  positional : Array Syntax
  /-- The parameter names bound by named arguments. -/
  named : Array Name

/--
Split `stx` into a `Call` if it is a prefix application, as parsed, of an
identifier naming `fnName`.  A partially qualified identifier matches by
suffix, but a bare one (such as `length` under `open List`) only by equality.
Wrapper nodes (parentheses, type ascriptions), applications built by macros
(`|>`, `<|`, `$`, notations) and `@f` calls do not have this shape.  A call
with `..` is rejected, since its arguments cannot be counted.
-/
private def callParts? (stx : Syntax) (fnName : Name) : Option Call := do
  let .node .none kind #[fn, argsNode] := stx | failure
  guard (kind == ``Parser.Term.app && fn.isIdent)
  guard (fn.getHeadInfo matches .original ..)
  let id := fn.getId
  guard (id == fnName ||
    !id.getPrefix.isAnonymous && (id.isSuffixOf fnName || fnName.isSuffixOf id))
  let mut positional := #[]
  let mut named := #[]
  for arg in argsNode.getArgs do
    if arg.isOfKind ``Parser.Term.namedArgument then
      named := named.push arg[1].getId
    else if arg.isOfKind ``Parser.Term.ellipsis then
      failure
    else
      positional := positional.push arg
  return { fn, positional, named }

/-- Strip enclosing parentheses. -/
private partial def unparen (stx : Syntax) : Syntax :=
  if stx.isOfKind ``Parser.Term.paren then unparen stx[1] else stx

/--
Whether `recv`, with parentheses stripped, has a kind in `kinds`, or is an
application whose head has one.
-/
private def isSkippedReceiver (kinds : Array SyntaxNodeKind) (recv : Syntax) : Bool :=
  let recv := unparen recv
  kinds.contains recv.getKind ||
    recv.isOfKind ``Parser.Term.app && kinds.contains recv[0].getKind

/--
The rewrite of `stx`, the call `call`, to `recv.short rest`, where `rest` is
the source text of the call after the function identifier, minus `recv`.
Slicing the source keeps the arguments exactly as written.  No
parenthesization is needed: an argument is already a maximum-precedence
term, which is what the receiver of dot notation must be.
-/
private def suggestion? (src : String) (stx : Syntax) (call : Call) (recv : Syntax)
    (short : String) : Option String := do
  let slice (b e : String.Pos.Raw) : String :=
    { str := src, startPos := b, stopPos := e : Substring.Raw }.toString
  let recvText ← sourceText? recv
  let before := (slice (← call.fn.getTailPos?) (← recv.getPos?)).trimAsciiEnd.toString
  let rest := (before ++ slice (← recv.getTailPos?) (← stx.getTailPos?)).trimAscii.toString
  return if rest.isEmpty then s!"{recvText}.{short}" else s!"{recvText}.{short} {rest}"

/-! ## Semantics -/

/--
Whether `type` is headed by a type whose name, without its private prefix,
is `ns`, possibly after unfolding reducible definitions.  This is the test
`typeMatchesBaseName` applies to each parameter in `addLValArg`.
-/
private partial def typeHeadedBy (type : Expr) (ns : Name) : MetaM Bool :=
  withReducibleAndInstances do
    let headIsNs (e : Expr) : Bool :=
      e.getAppFn.constName?.any (privateToUserName · == ns)
    if headIsNs type.cleanupAnnotations then return true
    let type ← whnfCore type
    if headIsNs type then return true
    match ← unfoldDefinition? type with
    | some type => typeHeadedBy type ns
    | none => return false

/--
The index, among the positional arguments of a call to `fn`, of the argument
that `x.f` would replace with `x`.  Following `addLValArg`, this is the first
parameter not bound by a named argument whose declared type is headed by
`ns`.  `none` if that parameter is implicit (`x.f` would pass `x` by name, so
no positional argument is the receiver) or has no positional argument.
-/
private def receiverIndex? (fn : Expr) (ns : Name) (named : Array Name)
    (numPositional : Nat) : MetaM (Option Nat) := do
  forallTelescopeReducing (← inferType fn) fun xs _ => do
    let mut named := named
    let mut idx := 0
    for x in xs do
      let decl ← x.fvarId!.getDecl
      if named.contains decl.userName then
        named := named.erase decl.userName
        continue
      if ← typeHeadedBy decl.type ns then
        return if decl.binderInfo.isExplicit && idx < numPositional then some idx else none
      if decl.binderInfo.isExplicit then idx := idx + 1
    return none

/--
The declaration that `x.short` finds in the namespace `typeName`, following
`resolveLValAux`: a structure field of `typeName` or one of its parents, or
else a declaration `S.short` for the first `S` in the structure resolution
order of `typeName` that has one.  `none` if nothing is found or the name is
ambiguous.
-/
private def findMember? (typeName : Name) (short : String) : MetaM (Option Name) := do
  let env ← getEnv
  if isStructure env typeName then
    if let some base := findField? env typeName (.mkSimple short) then
      return some (base ++ .mkSimple short)
  let order ←
    if isStructure env typeName then getStructureResolutionOrder typeName
    else pure #[typeName]
  for s in order do
    -- As in `findMethod?`, resolve without the current namespace.
    let candidates ← withTheReader Core.Context ({ · with currNamespace := .anonymous }) do
      resolveGlobalName (privateToUserName s ++ .mkSimple short)
    match candidates.filter (·.2.isEmpty) with
    | [] => continue
    | [(n, _)] => return some n
    | _ => return none
  return none

/--
Whether `x.short`, for `x : type`, resolves to `fnName`.  Following
`resolveLVal`, look the name up in the namespace of the head of `type`,
unfolding one definition at a time until some namespace has it.
-/
private partial def resolvesTo (type : Expr) (short : String) (fnName : Name) :
    MetaM Bool := do
  let type ← whnfCore (← instantiateMVars type)
  let .const head _ := type.getAppFn | return false
  if let some n ← findMember? head short then return n == fnName
  match ← unfoldDefinition? type with
  | some type => resolvesTo type short fnName
  | none => return false

/--
Whether `x.short` resolves to `fnName`, where `recv` is `x` as elaborated in
the call.  A local bound without a type annotation (`{x}` in a signature, an
auto-bound implicit, `∀ x`, `fun x`) is recorded with a metavariable type
that something assigned later, possibly the call itself, which `x.f` cannot
use.  Such a receiver is rejected, even though a binder whose type comes from
an expected type (as in `fun x` passed as an argument) would have worked.
-/
private def receiverResolvesTo (recv : Expr) (short : String) (fnName : Name) :
    MetaM Bool := do
  let type ← inferType recv
  if recv.isFVar && type.consumeMData.getAppFn.isMVar then return false
  resolvesTo type short fnName

/-! ## Linter -/

/-- The dot notation linter. -/
def dotNotationLinter : Lean.Linter where run := withSetOptionIn fun _stx => do
  unless getLinterValue linter.hazel.style.preferDotNotation (← getLinterOptions) &&
         (← getInfoState).enabled do
    return
  if (← MonadState.get).messages.hasErrors then return
  let skippedKinds ← skippedReceiverKindsRef.get
  let trees ← getInfoTrees
  let src := (← getFileMap).source
  let mut termInfos : Array (ContextInfo × TermInfo) := #[]
  for tree in trees.toArray do
    termInfos := tree.foldInfo (init := termInfos) fun ctx info acc =>
      match info with
      | .ofTermInfo ti => if ti.isBinder then acc else acc.push (ctx, ti)
      | _ => acc
  -- The receiver's own `TermInfo`, keyed by source range and kind, holds its
  -- type before any coercion the call inserted.
  let rangeKey (stx : Syntax) : Option (Nat × Nat × SyntaxNodeKind) := do
    return ((← stx.getPos?).byteIdx, (← stx.getTailPos?).byteIdx, stx.getKind)
  let mut bySyntax : Std.HashMap (Nat × Nat × SyntaxNodeKind) (ContextInfo × TermInfo) := {}
  for (ctx, ti) in termInfos do
    if let some key := rangeKey ti.stx then
      bySyntax := bySyntax.insertIfNew key (ctx, ti)
  let mut reported : Std.HashSet (Nat × Nat × SyntaxNodeKind) := {}
  for (ctx, ti) in termInfos do
    let .const fnName _ := ti.expr.getAppFn | continue
    let some call := callParts? ti.stx fnName | continue
    let some key := rangeKey ti.stx | continue
    if reported.contains key then continue
    let userName := privateToUserName fnName
    let ns := userName.getPrefix
    if ns.isAnonymous then continue
    let short := userName.getString!
    let some idx ← liftCoreM do
      try ti.runMetaM ctx (receiverIndex? ti.expr.getAppFn ns call.named call.positional.size)
      catch _ => return none
      | continue
    let recv := call.positional[idx]!
    if isSkippedReceiver skippedKinds recv then continue
    let some (recvCtx, recvInfo) := rangeKey recv >>= bySyntax.get? | continue
    let resolves ← liftCoreM do
      try recvInfo.runMetaM recvCtx (receiverResolvesTo recvInfo.expr short fnName)
      catch _ => return false
    unless resolves do continue
    let some suggestion := suggestion? src ti.stx call recv short | continue
    reported := reported.insert key
    Linter.logLint linter.hazel.style.preferDotNotation ti.stx
      m!"Use dot notation: `{suggestion}`"
    liftCoreM <| Lean.Meta.Tactic.TryThis.addSuggestion ti.stx
      { suggestion := .string suggestion
        toCodeActionTitle? := some fun s => s!"Use dot notation: {s}" }
      (origSpan? := ti.stx)
      (header := "Try this:")

initialize addLinter dotNotationLinter

end Hazel.Style.PreferDotNotation

end -- meta section
