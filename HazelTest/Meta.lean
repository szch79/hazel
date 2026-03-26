/-
Tests for meta linters.
-/
module

meta import Hazel
import Lean.Meta.Basic

set_option linter.unusedVariables false

/-! # noStringElaboration -/

section noStringElaboration
set_option linter.hazel.meta.noStringElaboration true

-- Passing: using quasiquotations is fine
#guard_msgs in
open Lean in
def meta_pass_quotation : MetaM Syntax := do
  `(term| 1 + 2)

-- Passing: string literals not in parser context are fine
#guard_msgs in
def meta_pass_string : String := "hello world"

-- Passing: string interpolation not in parser context is fine
#guard_msgs in
def meta_pass_interp (n : Nat) : String := s!"value: {n}"

-- NOTE: A failing test for noStringElaboration would require calling
-- `Parser.runParserCategory` with a string literal, which needs complex
-- setup (environment, parser state).  The linter is best-effort for
-- detecting this anti-pattern in metaprogramming code.

end noStringElaboration

/-! # requireSuppressionComment -/

section requireSuppressionComment
set_option linter.hazel.meta.requireSuppressionComment true

-- Failing: file-wide suppression without comment
/--
warning: Suppression of `linter.hazel.style.preferDotNotation` should have a `--` comment explaining why.

Note: This linter can be disabled with `set_option linter.hazel.meta.requireSuppressionComment false`
-/
#guard_msgs in
set_option linter.hazel.style.preferDotNotation false

-- Passing: file-wide suppression with inline comment
#guard_msgs in
set_option linter.hazel.style.preferDotNotation false -- generated code

-- Passing: file-wide suppression with comment on line above
#guard_msgs in
-- Dot notation breaks due to coercion
set_option linter.hazel.style.preferDotNotation false

-- Passing: enabling a linter (not suppression)
#guard_msgs in
set_option linter.hazel.style.preferDotNotation true

-- Passing: non-hazel option
#guard_msgs in
set_option linter.unusedVariables false

-- Failing: scoped suppression without comment
/--
warning: Suppression of `linter.hazel.style.preferDotNotation` should have a `--` comment explaining why.

Note: This linter can be disabled with `set_option linter.hazel.meta.requireSuppressionComment false`
-/
#guard_msgs in
set_option linter.hazel.style.preferDotNotation false in
def _scoped_fail := 42

-- Passing: scoped suppression with inline comment
#guard_msgs in
set_option linter.hazel.style.preferDotNotation false in -- generated code
def _scoped_pass_inline := 42

-- Passing: scoped suppression with comment on line above
#guard_msgs in
-- Dot notation breaks due to coercion
set_option linter.hazel.style.preferDotNotation false in
def _scoped_pass_above := 42

-- Passing: scoped with inline comment before `in` on next line
#guard_msgs in
set_option linter.hazel.style.preferDotNotation false -- generated code
  in def _scoped_pass_inline_before_in := 42

-- Failing: block comment does not count (only `--` line comments)
/--
warning: Suppression of `linter.hazel.style.preferDotNotation` should have a `--` comment explaining why.

Note: This linter can be disabled with `set_option linter.hazel.meta.requireSuppressionComment false`
-/
#guard_msgs in
/- This is a block comment, not a line comment -/
set_option linter.hazel.style.preferDotNotation false

-- Failing: comment two lines above (blank line gap) does not count
/--
warning: Suppression of `linter.hazel.style.preferDotNotation` should have a `--` comment explaining why.

Note: This linter can be disabled with `set_option linter.hazel.meta.requireSuppressionComment false`
-/
#guard_msgs in
-- This comment is too far away

set_option linter.hazel.style.preferDotNotation false

end requireSuppressionComment
