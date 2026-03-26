/-
SPDX-FileCopyrightText: 2026 Mingtong Lin
SPDX-License-Identifier: MIT
-/
module

public meta import Lean
public meta import Lean.Linter
public meta import Hazel.Util

/-!
# No string elaboration linter

Flags the anti-pattern of constructing Lean code as strings then parsing them.
Use quasiquotations instead.
-/

meta section

open Lean Elab Command Linter Hazel.Util

/-- Flag string-to-syntax elaboration anti-patterns. -/
public register_option linter.hazel.meta.noStringElaboration : Bool := {
  defValue := false
  descr := "warn on constructing Lean code via string parsing"
}

namespace Hazel.Meta.NoStringElab

/--
Known function names that parse strings into syntax.  If a call to one of these
contains a string literal or interpolation argument, the linter flags it.
-/
private def parserFnNames : Array Name := #[
  `Lean.Parser.runParserCategory,
  `Lean.Elab.runFrontend,
  `Lean.Parser.testParseModule
]

/-- Check if a syntax node is a string literal or string interpolation. -/
private def isStringLike (stx : Syntax) : Bool :=
  stx.isStrLit?.isSome ||
  stx.isOfKind `interpolatedStr ||
  (match stx with
   | .node _ kind _ => kind.toString.startsWith "interpolatedStr"
   | _ => false)

/-- The string elaboration linter. -/
def noStringElabLinter : Lean.Linter where run := withSetOptionIn fun stx => do
  unless getLinterValue linter.hazel.meta.noStringElaboration (← getLinterOptions) do return
  if (← MonadState.get).messages.hasErrors then return
  -- Find applications where a known parser function is called with a string arg
  let apps := findAll stx fun s =>
    match s with
    | .node _ ``Parser.Term.app _ => true
    | _ => false
  for app in apps do
    let fn := app[0]
    let fnName := if fn.isIdent then fn.getId else .anonymous
    if parserFnNames.any (· == fnName) then
      -- Check if any argument is a string literal or interpolation
      let args := app.getArgs
      for arg in args do
        let allNodes := findAll arg isStringLike
        if !allNodes.isEmpty then
          Linter.logLint linter.hazel.meta.noStringElaboration app
            m!"Avoid constructing Lean code as strings; use quasiquotations instead."
          break

initialize addLinter noStringElabLinter

end Hazel.Meta.NoStringElab

end -- meta section
