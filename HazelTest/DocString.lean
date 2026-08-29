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

-- Numbered list markers should not trigger the doubleSpace check.
#guard_msgs in
/--
A list:
1. First item.
2. Second item.
-/
def ds_pass_numbered_list := true

-- URLs are not prose: a sentence-ending period after a URL cannot be
-- distinguished from a period inside the URL, so no check fires there.
#guard_msgs in
/-- See https://example.com/spec. Section two has details. -/
def ds_pass_url := true

-- A violation elsewhere in the prose is still caught.
/--
warning: Use two spaces after sentence-ending punctuation in docstrings.

Note: This linter can be disabled with `set_option linter.hazel.docstring.doubleSpace false`
-/
#guard_msgs in
/-- See https://example.com/spec. Details follow. Second sentence. -/
def ds_fail_url_elsewhere := true

-- Markdown link labels are not prose: citation-style labels contain
-- initials and abbreviations.
#guard_msgs in
/-- See [A. Author, *On a generic topic*][author99] for background. -/
def ds_pass_link_label := true

-- An inline link target is skipped along with its label.
#guard_msgs in
/-- Read [the D. Knuth interview](https://example.com/interview) today. -/
def ds_pass_inline_link := true

-- Reference-style definitions: bracketed label, then a URL.
#guard_msgs in
/--
Details in [E. Writer, *A survey*][writer00].

[writer00]: https://example.com/survey
-/
def ds_pass_link_reference := true

-- Prose after a link is still checked.
/--
warning: Use two spaces after sentence-ending punctuation in docstrings.

Note: This linter can be disabled with `set_option linter.hazel.docstring.doubleSpace false`
-/
#guard_msgs in
/-- See [A. Author, *Title*][a99] for this. Also for that. -/
def ds_fail_link_then_prose := true

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

-- Unicode inside a URL is fine (IRIs may contain non-ASCII).
#guard_msgs in
/-- See https://example.com/φ-notes for details. -/
def ds_pass_unicode_url := true

-- Unicode inside a link label is fine.
#guard_msgs in
/-- See [Kőnig's theorem][k36] for the bipartite case. -/
def ds_pass_unicode_link := true

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

-- A URL is not prose; no capitalization to demand.
#guard_msgs in
/-- https://example.com hosts the project page. -/
def ds_pass_url_start := true

-- Likewise for a leading markdown link.
#guard_msgs in
/-- [a-tool guide](https://example.com/guide) covers the setup. -/
def ds_pass_link_start := true

/--
warning: Docstrings should start with an uppercase letter.

Note: This linter can be disabled with `set_option linter.hazel.docstring.capitalStart false`
-/
#guard_msgs in
/-- this starts lowercase. -/
def ds_fail_lowercase := true

-- Without `doc.verso`, braces are ordinary prose: a role header is not
-- recognized, so this docstring starts with a lowercase letter.
/--
warning: Docstrings should start with an uppercase letter.

Note: This linter can be disabled with `set_option linter.hazel.docstring.capitalStart false`
-/
#guard_msgs in
/-- {lean}`1 + 1` is a sum. -/
def ds_fail_role_without_verso := true

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

/-! # Non-declaration commands -/

section nonDeclDocstrings

-- Regression: docstrings on syntax/macro commands were previously not linted.

set_option linter.hazel.docstring.capitalStart true

/--
warning: Docstrings should start with an uppercase letter.

Note: This linter can be disabled with `set_option linter.hazel.docstring.capitalStart false`
-/
#guard_msgs in
/-- lowercase start on syntax. -/
syntax "ds_test_syn_cap" : command

#guard_msgs in
/-- Correct start on syntax. -/
syntax "ds_test_syn_ok" : command

set_option linter.hazel.docstring.capitalStart false
set_option linter.hazel.docstring.multilineFormat true

/--
warning: Nothing should follow the opening delimiter on its line.

Note: This linter can be disabled with `set_option linter.hazel.docstring.multilineFormat false`
-/
#guard_msgs in
/-- Text after opener
on syntax.
-/
syntax "ds_test_syn_ml" : command

set_option linter.hazel.docstring.multilineFormat false
set_option linter.hazel.docstring.collapsible true

/--
warning: Single-line docstring should use `/-- ... -/` format.

Note: This linter can be disabled with `set_option linter.hazel.docstring.collapsible false`
-/
#guard_msgs in
/--
Collapsible on syntax.
-/
syntax "ds_test_syn_coll" : command

end nonDeclDocstrings

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

/-! # doc.verso docstrings -/

section versoDocstrings
set_option doc.verso true

section
set_option linter.hazel.docstring.multilineFormat true

-- Regression: `Syntax.reprint` on a Verso docstring is not source-faithful
-- (its body is a markup tree), which made well-formed docstrings fail the
-- closing-delimiter check.
#guard_msgs in
/--
This is properly formatted.
Multiple lines are fine.

Even a second paragraph is fine.
-/
def ds_verso_pass_multiline := true

#guard_msgs in
/-- Single line is fine. -/
def ds_verso_pass_single := true

/--
warning: Nothing should follow the opening delimiter on its line.

Note: This linter can be disabled with `set_option linter.hazel.docstring.multilineFormat false`
-/
#guard_msgs in
/-- This text follows
the opening delimiter.
-/
def ds_verso_fail_text_after_open := true

end

section
set_option linter.hazel.docstring.collapsible true

/--
warning: Single-line docstring should use `/-- ... -/` format.

Note: This linter can be disabled with `set_option linter.hazel.docstring.collapsible false`
-/
#guard_msgs in
/--
This could be one line.
-/
def ds_verso_fail_collapsible := true

#guard_msgs in
/--
First line.
Second line.
-/
def ds_verso_pass_not_collapsible := true

end

section
-- Regression: `getDocStringText` throws on Verso docstrings, which silently
-- disabled all prose checks under `doc.verso`.
set_option linter.hazel.docstring.doubleSpace true
set_option linter.hazel.docstring.capitalStart true

#guard_msgs in
/-- This is a sentence.  This is another. -/
def ds_verso_pass_prose := true

/--
warning: Use two spaces after sentence-ending punctuation in docstrings.

Note: This linter can be disabled with `set_option linter.hazel.docstring.doubleSpace false`
-/
#guard_msgs in
/-- This is a sentence. This is another. -/
def ds_verso_fail_single_space := true

/--
warning: Docstrings should start with an uppercase letter.

Note: This linter can be disabled with `set_option linter.hazel.docstring.capitalStart false`
-/
#guard_msgs in
/-- this starts lowercase. -/
def ds_verso_fail_lowercase := true

-- URLs are not prose; the period after the URL does not trigger doubleSpace.
#guard_msgs in
/-- See https://example.com/spec. Section two has details. -/
def ds_verso_pass_url := true

-- Link labels are not prose under Verso either.
#guard_msgs in
/-- See [J. Doe's notes](https://example.com/notes) for more. -/
def ds_verso_pass_link := true

-- A Verso role header before the opening code span is not prose; there is no
-- capitalization to demand.
#guard_msgs in
/-- {lean}`1 + 1` is a sum. -/
def ds_verso_pass_role_start := true

-- Nor is a role header with arguments.
#guard_msgs in
/-- {lean type:="Nat"}`1 + 1` is a sum of type natural numbers. -/
def ds_verso_pass_role_args_start := true

end

section
set_option linter.hazel.docstring.noUnicodeProse true
-- Verso emits "Code element could be more specific" hints for backtick code
-- elements; disable them so the guards only capture linter output.
set_option doc.verso.suggestions false

#guard_msgs in
/-- The term `φ` is a formula. -/
def ds_verso_pass_unicode_backtick := true

/--
warning: Avoid non-ASCII characters in docstring prose; use backtick spans for code.

Note: This linter can be disabled with `set_option linter.hazel.docstring.noUnicodeProse false`
-/
#guard_msgs in
/-- The formula φ is valid. -/
def ds_verso_fail_unicode_prose := true

end

section
-- Regression: docstring presence must be detected structurally; a Verso
-- docstring counts as documented.
set_option linter.hazel.docstring.missingDocstring true

#guard_msgs in
/-- A documented definition under Verso. -/
def ds_verso_md_pass := true

/--
warning: Public declaration is missing a docstring.

Note: This linter can be disabled with `set_option linter.hazel.docstring.missingDocstring false`
-/
#guard_msgs in
def ds_verso_md_fail := true

end

-- Module docstrings under Verso cannot be tested here: a file cannot mix
-- Verso-format module docs with the Markdown-format ones used throughout
-- this file.  See the `HazelTest/ModuleDoc/VersoDoc.lean` fixture.

end versoDocstrings

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
