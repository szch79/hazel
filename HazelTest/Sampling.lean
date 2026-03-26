/-
Sampling tests: run changed linters against stdlib-style patterns.
Verifies no false positives from F1-F6 fixes.
-/
module

meta import Hazel

set_option linter.unusedVariables false

/-! # F1: InlineBy / InlineDo / KeywordAlign — no false positives -/

section inlineByDo
set_option linter.hazel.style.inlineBy true
set_option linter.hazel.style.inlineDo true

-- Passing: by on same line as :=
#guard_msgs in
theorem sampling_by_inline (n : Nat) : n = n := by rfl

-- Passing: by on same line as =>
#guard_msgs in
theorem sampling_by_match (n : Nat) : n = n := by
  match n with
  | 0 => rfl
  | n + 1 => rfl

-- Passing: do on same line as :=
#guard_msgs in
def sampling_do_inline : IO Unit := do
  pure ()

-- Passing: multiple by in nested context
#guard_msgs in
theorem sampling_nested_by (n m : Nat) : n + m = n + m := by
  have : n = n := by rfl
  rfl

end inlineByDo

section keywordAlign
set_option linter.hazel.style.keywordAlign.where true
set_option linter.hazel.style.keywordAlign.deriving true

-- Passing: where aligned with def
#guard_msgs in
class SamplingClass (a : Type) where
  val : a

-- Passing: deriving aligned with structure
#guard_msgs in
structure SamplingStruct where
  x : Nat
  y : Nat
deriving Repr

end keywordAlign

/-! # F2: NumericProjDepth — Linter.logLint format -/

section numericProj
set_option linter.hazel.style.numericProj true
set_option linter.hazel.style.numericProjDepth 2

-- Passing: depth <= 2
#guard_msgs in
def sampling_proj_ok (x : Nat × (Nat × Nat)) : Nat := x.2.1

-- Failing: depth 3, uses Linter.logLint format
/--
warning: Numeric projection chain `.2.2.1` is 3 deep (max 2).  Use named field access or destructuring instead.

Note: This linter can be disabled with `set_option linter.hazel.style.numericProj false`
-/
#guard_msgs in
def sampling_proj_deep (x : Nat × (Nat × (Nat × Nat))) : Nat := x.2.2.1

end numericProj

/-! # F3/F4: PreferRintro / PreferCombined — syntax-based matching -/

section preferRintro
set_option linter.hazel.tactic.preferRintro true

-- Passing: no intro+rcases pattern
#guard_msgs in
example (h : ∃ n : Nat, n = 0) : True := by
  obtain ⟨n, _⟩ := h
  trivial

-- Passing: intro of multiple vars (not single var)
#guard_msgs in
example : Nat → Nat → True := by
  intro a b
  trivial

end preferRintro

section preferCombined
set_option linter.hazel.tactic.preferSimpA true
set_option linter.hazel.tactic.preferRwA true

-- Passing: simpa already used
set_option linter.unnecessarySimpa false in
#guard_msgs in
example (h : 1 + 1 = 2) : 2 = 2 := by
  simpa using h

-- Passing: rw not followed by assumption
#guard_msgs in
example (h : 1 = 1) : 1 = 1 := by
  rw [show 1 = 1 from rfl]

end preferCombined

/-! # F5: StrongPostCond — safe back? -/

-- StrongPostCond only fires when Std.Do.Triple is imported.
-- Just verify it doesn't crash on normal declarations.
section strongPostCond
set_option linter.hazel.do.strongPostCond true

#guard_msgs in
def sampling_normal_def : Nat := 42

#guard_msgs in
theorem sampling_normal_thm : 1 = 1 := rfl

end strongPostCond

/-! # F6: Prose — capital start with # -/

section prose
set_option linter.hazel.docstring.capitalStart true

-- Passing: docstring starting with #
#guard_msgs in
/-- # Section header -/
def sampling_hash_start := 42

-- Passing: docstring starting with backtick
#guard_msgs in
/-- `foo` is a function. -/
def sampling_backtick_start := 42

-- Passing: normal uppercase start
#guard_msgs in
/-- Returns the value. -/
def sampling_normal_start := 42

end prose
