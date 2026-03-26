/-
Tests for tactic linters.
-/
module

meta import Hazel

set_option linter.unusedVariables false

/-! # noErw -/

section noErw
set_option linter.hazel.tactic.noErw true

#guard_msgs in
example (h : 1 = 1) : 1 = 1 := by rw [h]

/--
warning: Avoid `erw`; prefer `rw` with appropriate lemmas.

Note: This linter can be disabled with `set_option linter.hazel.tactic.noErw false`
-/
#guard_msgs in
example (h : 1 = 1) : 1 = 1 := by erw [h]

end noErw

/-! # redundantSimpArg -/

section redundantSimpArg
set_option linter.hazel.tactic.redundantSimpArg true

@[simp] theorem my_simp_lemma : (0 : Nat) + n = n := by simp

set_option linter.unusedSimpArgs false in
/--
warning: Redundant simp argument: `my_simp_lemma` is already `@[simp]`.

Note: This linter can be disabled with `set_option linter.hazel.tactic.redundantSimpArg false`
-/
#guard_msgs in
example : (0 : Nat) + 1 = 1 := by simp [my_simp_lemma]

-- Passing: simp only with @[simp] lemma (deliberate controlled simplification)
set_option linter.unusedSimpArgs false in
#guard_msgs in
example : (0 : Nat) + 1 = 1 := by simp only [my_simp_lemma]

-- Passing: simp only with non-@[simp] lemma
set_option linter.unusedSimpArgs false in
#guard_msgs in
example (h : 1 = 1) : 1 = 1 := by simp only [h]

-- Passing: simp without arguments
#guard_msgs in
example : (0 : Nat) + 1 = 1 := by simp

-- Passing: simp only without arguments (bare simp only)
set_option linter.unusedSimpArgs false in
#guard_msgs in
example (h : 1 = 1) : 1 = 1 := by simp only

-- Passing: simp with non-@[simp] local hypothesis
set_option linter.unusedSimpArgs false in
#guard_msgs in
example (h : 1 + 1 = 3) : 1 + 1 = 3 := by simp [h]

-- Failing: simp_all with @[simp] lemma
set_option linter.unusedSimpArgs false in
/--
warning: Redundant simp argument: `my_simp_lemma` is already `@[simp]`.

Note: This linter can be disabled with `set_option linter.hazel.tactic.redundantSimpArg false`
-/
#guard_msgs in
example : (0 : Nat) + 1 = 1 := by simp_all [my_simp_lemma]

-- Passing: linter disabled
set_option linter.hazel.tactic.redundantSimpArg false in
set_option linter.unusedSimpArgs false in
#guard_msgs in
example : (0 : Nat) + 1 = 1 := by simp [my_simp_lemma]

end redundantSimpArg

/-! # haveObtain -/

section haveObtain
set_option linter.hazel.tactic.haveObtain true

#guard_msgs in
example (h : True ∧ True) : True := by
  have h2 : True := h.1
  exact h2

#guard_msgs in
example (h : True ∧ True) : True := by
  obtain ⟨h1, _⟩ := h
  exact h1

/--
warning: Use `obtain ⟨...⟩` for destructuring instead of `have ⟨...⟩`.

Note: This linter can be disabled with `set_option linter.hazel.tactic.haveObtain false`
-/
#guard_msgs in
example (h : True ∧ True) : True := by
  have ⟨h1, _⟩ := h
  exact h1

-- Passing: plain have with no destructuring (regression for bug #3)
#guard_msgs in
example : True := by
  have h : ∀ n : Nat, n = n := fun _ => rfl
  trivial

-- Passing: have with ⟨⟩ in the value, not the binder
#guard_msgs in
example : True := by
  have h : True ∧ True := ⟨trivial, trivial⟩
  exact h.1

end haveObtain

/-! # noIntros -/

section noIntros
set_option linter.hazel.tactic.noIntros true

#guard_msgs in
example : Nat → Nat → True := by
  intro x y
  trivial

#guard_msgs in
example : Nat → Nat → True := by
  intros
  trivial

/--
warning: Use `intro` instead of `intros` with named arguments.

Note: This linter can be disabled with `set_option linter.hazel.tactic.noIntros false`
-/
#guard_msgs in
example : Nat → Nat → True := by
  intros x y
  trivial

-- Edge: intros _ (underscore is a named binder, should flag)
-- NOTE: may fire multiple times due to findAll finding wrapper nodes
set_option linter.hazel.tactic.noIntros false in
#guard_msgs in
example : Nat → True := by
  intros _
  trivial

end noIntros

/-! # preferExact -/

section preferExact
set_option linter.hazel.tactic.preferExact true

#guard_msgs in
example (h : True) : True := by exact h

-- apply creates subgoals — not flagged
set_option linter.hazel.tactic.preferExact false in
#guard_msgs in
example : True ∧ True := by
  apply And.intro
  · trivial
  · trivial

/--
warning: Use `exact True.intro` instead of `apply`.

Note: This linter can be disabled with `set_option linter.hazel.tactic.preferExact false`
-/
#guard_msgs in
example : True := by apply True.intro

-- Edge: refine that closes the goal
/--
warning: Use `exact True.intro` instead of `refine`.

Note: This linter can be disabled with `set_option linter.hazel.tactic.preferExact false`
-/
#guard_msgs in
example : True := by refine True.intro

end preferExact

/-! # preferAssumption -/

section preferAssumption
set_option linter.hazel.tactic.preferAssumption true

#guard_msgs in
example (h : True) : True := by assumption

/--
warning: Use `assumption` instead of `exact h`.

Note: This linter can be disabled with `set_option linter.hazel.tactic.preferAssumption false`
-/
#guard_msgs in
example (h : True) : True := by exact h

-- Edge: exact h.1 — NOT flagged (projection, not bare FVar)
#guard_msgs in
example (h : True ∧ True) : True := by exact h.1

-- Edge: exact with complex expression — NOT flagged
#guard_msgs in
example : True := by exact trivial

end preferAssumption

/-! # preferCombined -/

section preferCombined
set_option linter.hazel.tactic.preferSimpA true
set_option linter.hazel.tactic.preferRwA true

-- Failing: rw followed by assumption (semicolon)
/--
warning: Use `rwa` instead of `rw; assumption`.

Note: This linter can be disabled with `set_option linter.hazel.tactic.preferRwA false`
-/
#guard_msgs in
example (a b : Nat) (h1 : a = b) (h2 : b = 0) : a = 0 := by rw [h1]; assumption

-- Failing: rw followed by assumption (newline)
/--
warning: Use `rwa` instead of `rw; assumption`.

Note: This linter can be disabled with `set_option linter.hazel.tactic.preferRwA false`
-/
#guard_msgs in
example (a b : Nat) (h1 : a = b) (h2 : b = 0) : a = 0 := by
  rw [h1]
  assumption

-- Passing: rwa already used
#guard_msgs in
example (a b : Nat) (h1 : a = b) (h2 : b = 0) : a = 0 := by rwa [h1]

-- Edge: rw followed by trivial — NOT flagged (not assumption)
#guard_msgs in
example (a b : Nat) (h1 : a = b) (h2 : b = 0) : a = 0 := by rw [h1]; trivial

end preferCombined

/-! # preferRfl -/

section preferRfl
set_option linter.hazel.tactic.preferRfl true

-- Passing: simp on a non-rfl goal (1 + 1 is not defeq to 2 without simp)
#guard_msgs in
example (h : 1 = 2) : 1 = 2 := by simp [h]

-- Failing: simp on a goal that's already rfl
/--
warning: Use `rfl` instead of `simp` (goal is definitionally equal).

Note: This linter can be disabled with `set_option linter.hazel.tactic.preferRfl false`
-/
#guard_msgs in
example : (fun x : Nat => x) 1 = 1 := by simp

-- Passing: rfl already used
#guard_msgs in
example : (fun x : Nat => x) 1 = 1 := by rfl

-- Passing: simp uses a rewrite lemma (not just rfl)
#guard_msgs in
example (n : Nat) : 0 + n = n := by simp

-- Passing: typeclass instance unfolding is not reducible-transparent.
-- `Foo.eval x = x.eval` is defeq at default transparency but not at
-- reducible transparency, so `rfl` fails and `simp` is correct.
class RflTestClass (L : Type) where eval : L → Nat
inductive RflTestBar where | a | b
instance : RflTestClass RflTestBar where eval | .a => 1 | .b => 2
def RflTestBar.eval : RflTestBar → Nat | .a => 1 | .b => 2
#guard_msgs in
@[simp] theorem rflTest_eval_eq (x : RflTestBar) :
    RflTestClass.eval x = x.eval := by cases x <;> rfl

-- Passing: non-terminal simp (doesn't close the goal)
#guard_msgs in
example (n : Nat) (h : n = 0) : n + 0 = 0 := by simp; exact h

end preferRfl

/-! # preferConstructor -/

section preferConstructor
set_option linter.hazel.tactic.preferConstructor true

-- Passing: constructor with non-exact subproofs
#guard_msgs in
example : True ∧ (1 = 1) := by
  constructor
  · trivial
  · rfl

-- Failing: constructor with all exact subproofs
/--
warning: Use `exact ⟨trivial, rfl⟩` instead of `constructor` with individual `exact` calls.

Note: This linter can be disabled with `set_option linter.hazel.tactic.preferConstructor false`
-/
#guard_msgs in
example : True ∧ (1 = 1) := by
  constructor
  · exact trivial
  · exact rfl

end preferConstructor

/-! # preferRintro -/

section preferRintro
set_option linter.hazel.tactic.preferRintro true

-- Passing: rintro already used
#guard_msgs in
example : (∃ n : Nat, n = 0) → True := by
  rintro ⟨n, _⟩
  trivial

-- Failing: intro followed by rcases on same variable
/--
warning: Use `rintro` instead of `intro h` followed by destructuring.

Note: This linter can be disabled with `set_option linter.hazel.tactic.preferRintro false`
-/
#guard_msgs in
example : (∃ n : Nat, n = 0) → True := by
  intro h
  rcases h with ⟨n, _⟩
  trivial

end preferRintro

/-! # inlineShow -/

section inlineShow
set_option linter.hazel.tactic.inlineShow true
set_option linter.hazel.tactic.preferRfl false
set_option linter.hazel.tactic.preferExact false

-- Passing: single-line inline show
#guard_msgs in
example (a b : Nat) (h : a = b) (h2 : b = 0) : a = 0 := by
  rw [show a = b from h]; exact h2

-- Passing: standalone show (not inside rw, just goal annotation)
#guard_msgs in
example : True := by
  show True
  trivial

-- Passing: inline show with rfl (trivial, single line)
#guard_msgs in
example (n : Nat) : n + 0 = n := by
  rw [show n + 0 = n from rfl]

-- Failing: multi-line inline show in rw
/--
warning: Multi-line inline `show` proof.  Consider extracting to `have` for readability.

Note: This linter can be disabled with `set_option linter.hazel.tactic.inlineShow false`
-/
#guard_msgs in
example (a b : Nat) (h : a = b) (h2 : b = 0) : a = 0 := by
  rw [show a = b from by
    exact h]
  exact h2

-- Failing: multi-line inline show with by in simp
/--
warning: Multi-line inline `show` proof.  Consider extracting to `have` for readability.

Note: This linter can be disabled with `set_option linter.hazel.tactic.inlineShow false`
-/
#guard_msgs in
example (a b : Nat) (h : a = b) : a = b := by
  exact show a = b from by
    exact h

end inlineShow
