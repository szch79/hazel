/-
Tests for docstring linters.  Each linter scoped to its own section.
-/
module

meta import Hazel

set_option linter.unusedVariables false

/-! # doubleSpace -/

section doubleSpace
set_option linter.hazel.docstring.doubleSpace true

#guard_msgs in
/-- This is a sentence.  This is another. -/
def ds_pass_double := true

#guard_msgs in
/-- This is a sentence. -/
def ds_pass_period_end := true

/--
warning: Use two spaces after sentence-ending punctuation in docstrings.

Note: This linter can be disabled with `set_option linter.hazel.docstring.doubleSpace false`
-/
#guard_msgs in
/-- This is a sentence. This is another. -/
def ds_fail_single_space := true

#guard_msgs in
/-- See `Foo.bar` for details. -/
def ds_pass_backtick := true

end doubleSpace

/-! # noUnicodeProse -/

section noUnicodeProse
set_option linter.hazel.docstring.noUnicodeProse true

-- Single backtick: unicode inside code span is fine
#guard_msgs in
/-- The term `φ` is a formula. -/
def ds_pass_unicode_backtick := true

-- Double backtick: unicode inside is fine
#guard_msgs in
/-- Use ``φ ∧ ψ`` for conjunction. -/
def ds_pass_unicode_double_backtick := true

-- Single dollar: unicode in math span is fine
#guard_msgs in
/-- We have $φ ∧ ψ$ here. -/
def ds_pass_unicode_math := true

-- Double dollar: unicode in display math is fine
#guard_msgs in
/-- Display: $$∀ x, φ(x) → ψ(x)$$ is valid. -/
def ds_pass_unicode_double_dollar := true

-- Multiple code spans in one docstring
#guard_msgs in
/-- Both `φ` and `ψ` are formulas, and $α ∧ β$ holds. -/
def ds_pass_unicode_multi_span := true

-- Unicode in prose (not in any span) should fail
/--
warning: Avoid non-ASCII characters in docstring prose; use backtick spans for code.

Note: This linter can be disabled with `set_option linter.hazel.docstring.noUnicodeProse false`
-/
#guard_msgs in
/-- The formula φ is valid. -/
def ds_fail_unicode_prose := true

-- Unicode after closing code span should fail
/--
warning: Avoid non-ASCII characters in docstring prose; use backtick spans for code.

Note: This linter can be disabled with `set_option linter.hazel.docstring.noUnicodeProse false`
-/
#guard_msgs in
/-- The term `φ` has type α. -/
def ds_fail_unicode_after_span := true

-- Escaped backtick should not start a code span
/--
warning: Avoid non-ASCII characters in docstring prose; use backtick spans for code.

Note: This linter can be disabled with `set_option linter.hazel.docstring.noUnicodeProse false`
-/
#guard_msgs in
/-- Not a code span: \`φ\` is prose. -/
def ds_fail_escaped_backtick := true

-- Two code spans with prose unicode BETWEEN them: should fail
/--
warning: Avoid non-ASCII characters in docstring prose; use backtick spans for code.

Note: This linter can be disabled with `set_option linter.hazel.docstring.noUnicodeProse false`
-/
#guard_msgs in
/-- Both `φ` and α and `ψ` here. -/
def ds_fail_unicode_between_spans := true

-- Triple backtick code block: unicode inside is fine
#guard_msgs in
/--
Some text.
```lean
def foo (φ : Type) := φ
```
More text.
-/
def ds_pass_triple_backtick := true

-- Triple backtick with unicode AFTER the block: should fail
/--
warning: Avoid non-ASCII characters in docstring prose; use backtick spans for code.

Note: This linter can be disabled with `set_option linter.hazel.docstring.noUnicodeProse false`
-/
#guard_msgs in
/--
Code:
```lean
def foo := 1
```
The type α is important.
-/
def ds_fail_after_triple_backtick := true

-- Mixed spans: backtick and dollar in same docstring
#guard_msgs in
/-- We use `φ` in code and $ψ$ in math. -/
def ds_pass_mixed_spans := true

end noUnicodeProse

/-! # capitalStart -/

section capitalStart
set_option linter.hazel.docstring.capitalStart true

#guard_msgs in
/-- This starts with uppercase. -/
def ds_pass_capital := true

#guard_msgs in
/-- `foo` is a function. -/
def ds_pass_backtick_start := true

/--
warning: Docstrings should start with an uppercase letter.

Note: This linter can be disabled with `set_option linter.hazel.docstring.capitalStart false`
-/
#guard_msgs in
/-- this starts lowercase. -/
def ds_fail_lowercase := true

end capitalStart

/-! # multilineFormat -/

section multilineFormat
set_option linter.hazel.docstring.multilineFormat true

#guard_msgs in
/--
This is properly formatted.
Multiple lines are fine.
-/
def ds_pass_multiline := true

#guard_msgs in
/-- Single line is fine. -/
def ds_pass_single := true

/--
warning: Nothing should follow the opening delimiter on its line.

Note: This linter can be disabled with `set_option linter.hazel.docstring.multilineFormat false`
-/
#guard_msgs in
/-- This text follows
the opening delimiter.
-/
def ds_fail_text_after_open := true

end multilineFormat

/-! # collapsible -/

section collapsible
set_option linter.hazel.docstring.collapsible true

/--
warning: Single-line docstring should use `/-- ... -/` format.

Note: This linter can be disabled with `set_option linter.hazel.docstring.collapsible false`
-/
#guard_msgs in
/--
This could be one line.
-/
def ds_fail_collapsible := true

#guard_msgs in
/--
First line.
Second line.
-/
def ds_pass_not_collapsible := true

end collapsible

/-! # Module docstrings -/

section moduleDocstrings
set_option linter.hazel.docstring.noUnicodeProse true
set_option linter.hazel.docstring.capitalStart true

set_option linter.hazel.docstring.multilineFormat false in
set_option linter.hazel.docstring.collapsible false in
/--
warning: Avoid non-ASCII characters in module docstring prose.

Note: This linter can be disabled with `set_option linter.hazel.docstring.noUnicodeProse false`
-/
#guard_msgs in
/-! The formula φ appears here. -/

set_option linter.hazel.docstring.multilineFormat false in
set_option linter.hazel.docstring.collapsible false in
/--
warning: Module docstrings should start with an uppercase letter.

Note: This linter can be disabled with `set_option linter.hazel.docstring.capitalStart false`
-/
#guard_msgs in
/-! lower start. -/

set_option linter.hazel.docstring.multilineFormat false in
set_option linter.hazel.docstring.collapsible false in
#guard_msgs in
/-! # Proper heading -/

end moduleDocstrings

/-! # Edge cases -/

section edgeCases
set_option linter.hazel.docstring.multilineFormat true

#guard_msgs in
/--
The syntax `/--` opens and `-/` closes.
This should not cause issues.
-/
def ds_pass_delimiters_in_body := true

end edgeCases

/-! # missingDocstring -/

section missingDocstring
set_option linter.hazel.docstring.missingDocstring true
set_option linter.hazel.docstring.multilineFormat false
set_option linter.hazel.docstring.collapsible false

#guard_msgs in
/-- A documented definition. -/
def md_pass_def := true

#guard_msgs in
/-- A documented theorem. -/
theorem md_pass_theorem : True := trivial

#guard_msgs in
/-- A documented structure. -/
structure MdPassStruct where
  x : Nat

#guard_msgs in
/-- A documented inductive. -/
inductive MdPassInd where
  | mk

#guard_msgs in
private def md_pass_private := true

/--
warning: Public declaration is missing a docstring.

Note: This linter can be disabled with `set_option linter.hazel.docstring.missingDocstring false`
-/
#guard_msgs in
def md_fail_def := true

/--
warning: Public declaration is missing a docstring.

Note: This linter can be disabled with `set_option linter.hazel.docstring.missingDocstring false`
-/
#guard_msgs in
theorem md_fail_theorem : True := trivial

/--
warning: Public declaration is missing a docstring.

Note: This linter can be disabled with `set_option linter.hazel.docstring.missingDocstring false`
-/
#guard_msgs in
structure MdFailStruct where
  x : Nat

#guard_msgs in
instance : Inhabited MdPassStruct where
  default := ⟨0⟩

end missingDocstring
