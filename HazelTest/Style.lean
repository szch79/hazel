/-
Tests for all style linters.  Each linter is scoped to its own section to
avoid cross-contamination.
-/
module

meta import Hazel

set_option linter.unusedVariables false

/-! # Variable Naming -/

section varNaming
set_option linter.hazel.style.varNaming true

@[suggested_var_names "ω"]
abbrev MyWorld := Nat → Bool

@[suggested_var_names "φ" "ψ"]
inductive MyFormula where
  | var (x : Nat) : MyFormula
  | neg (φ : MyFormula) : MyFormula

suggest_var_names "f" "g" "h" for MyWorld → Bool

#guard_msgs in
def pass_world (ω : MyWorld) : Bool := ω 0

#guard_msgs in
def pass_world_subscript (ω₁ ω₂ : MyWorld) : Bool := ω₁ 0 || ω₂ 0

#guard_msgs in
def pass_formula (φ : MyFormula) : Bool := true

#guard_msgs in
def pass_formula_psi (ψ : MyFormula) : Bool := true

#guard_msgs in
def pass_structural (f : MyWorld → Bool) : Bool := f (fun _ => true)

#guard_msgs in
def pass_underscore (_ : MyWorld) : Bool := true

/--
warning: Suggested names of type `MyWorld`: ω

Note: This linter can be disabled with `set_option linter.hazel.style.varNaming false`
-/
#guard_msgs in
def fail_world (x : MyWorld) : Bool := x 0

/--
warning: Suggested names of type `MyFormula`: φ ψ

Note: This linter can be disabled with `set_option linter.hazel.style.varNaming false`
-/
#guard_msgs in
def fail_formula (n : MyFormula) : Bool := true

/--
warning: Suggested names of type `MyWorld → Bool`: f g h

Note: This linter can be disabled with `set_option linter.hazel.style.varNaming false`
-/
#guard_msgs in
def fail_structural (x : MyWorld → Bool) : Bool := x (fun _ => true)

class MyLang (L : Type) where
  eval : L → MyWorld → Bool

#guard_msgs in
def pass_typeclass [MyLang φ] (x : φ) : MyWorld → Bool := MyLang.eval x

/--
warning: Suggested names of type `MyFormula`: φ ψ

Note: This linter can be disabled with `set_option linter.hazel.style.varNaming false`
-/
#guard_msgs in
def fail_typeclass (n : MyFormula) : Bool := true

/-! ### Wildcard and dependent type patterns -/

-- Wildcard: match a dependent type applied to any argument
structure DepType (n : Nat) where
  val : Nat

suggest_var_names "d" for DepType _

-- Passing: d matches wildcard
#guard_msgs in
def vn_pass_wildcard {n : Nat} (d : DepType n) : Nat := d.val

-- Failing: x doesn't match wildcard
/--
warning: Suggested names of type `DepType n`: d

Note: This linter can be disabled with `set_option linter.hazel.style.varNaming false`
-/
#guard_msgs in
def vn_fail_wildcard {n : Nat} (x : DepType n) : Nat := x.val

-- Nested wildcard
structure Wrapper (α : Type) where
  inner : α

suggest_var_names "w" for Wrapper _

-- Failing: x doesn't match
/--
warning: Suggested names of type `Wrapper Nat`: w

Note: This linter can be disabled with `set_option linter.hazel.style.varNaming false`
-/
#guard_msgs in
def vn_fail_nested_wild (x : Wrapper Nat) : Nat := x.inner

-- Passing: w matches
#guard_msgs in
def vn_pass_nested_wild (w : Wrapper Nat) : Nat := w.inner

/-! ### Structural matching with nested wildcards -/

-- Nested type: Container applied to a specific inner type with wildcard arg
structure VnInner (n : Nat) where val : Nat
structure VnOuter (α : Type) where inner : α

-- Match VnOuter applied to VnInner with any arg
suggest_var_names "q" for VnOuter (VnInner _)

-- Failing: y doesn't match q
/--
warning: Suggested names of type `VnOuter (VnInner n)`: q

Note: This linter can be disabled with `set_option linter.hazel.style.varNaming false`
-/
#guard_msgs in
def vn_fail_struct {n : Nat} (y : VnOuter (VnInner n)) : Nat := y.inner.val

-- Passing: q matches
#guard_msgs in
def vn_pass_struct {n : Nat} (q : VnOuter (VnInner n)) : Nat := q.inner.val

-- Passing: VnOuter Nat does NOT match VnOuter (VnInner _)
#guard_msgs in
def vn_pass_no_struct_match (z : VnOuter Nat) : Nat := z.inner

-- Passing: VnInner n alone does NOT match VnOuter (VnInner _)
#guard_msgs in
def vn_pass_wrong_outer {n : Nat} (z : VnInner n) : Nat := z.val

-- Concrete nested pattern (separate type to avoid overlap with wildcard rule)
structure VnBox (α : Type) where box : α

suggest_var_names "b0" for VnBox (VnInner 0)

-- Failing: x doesn't match b0
/--
warning: Suggested names of type `VnBox (VnInner 0)`: b0

Note: This linter can be disabled with `set_option linter.hazel.style.varNaming false`
-/
#guard_msgs in
def vn_fail_concrete_nested (x : VnBox (VnInner 0)) : Nat := x.box.val

-- Passing: b0 matches
#guard_msgs in
def vn_pass_concrete_nested (b0 : VnBox (VnInner 0)) : Nat := b0.box.val

-- Passing: VnBox (VnInner 1) does NOT match VnBox (VnInner 0)
#guard_msgs in
def vn_pass_diff_concrete (z : VnBox (VnInner 1)) : Nat := z.box.val

/-! ### Body-level binders (lambda, let) -/

-- Failing: lambda with wrong name (type inferred)
/--
warning: Suggested names of type `MyWorld`: ω

Note: This linter can be disabled with `set_option linter.hazel.style.varNaming false`
-/
#guard_msgs in
def vn_fail_lambda : MyWorld → Bool := fun x => true

-- Passing: lambda with correct name
#guard_msgs in
def vn_pass_lambda : MyWorld → Bool := fun ω => true

-- Failing: annotated lambda with wrong name
/--
warning: Suggested names of type `MyFormula`: φ ψ

Note: This linter can be disabled with `set_option linter.hazel.style.varNaming false`
-/
#guard_msgs in
def vn_fail_lambda_ann : MyFormula → Bool := fun (x : MyFormula) => true

-- Passing: unannotated lambda with _ prefix (skipped)
#guard_msgs in
def vn_pass_lambda_underscore : MyWorld → Bool := fun _ => true

/-! ### Universe-polymorphic types in `suggest_var_names` -/

-- Regression test: `suggest_var_names` for types whose elaboration produces
-- universe metavariables (e.g., `Finset Nat`).  Previously the linter crashed
-- with "unknown universe metavariable" because the stored Expr contained
-- uninstantiated universe metavars.

suggest_var_names "S" "T" for Array Nat

-- Passing: S matches
#guard_msgs in
def vn_pass_array_rule (S : Array Nat) : Nat := S.size

-- Failing: x doesn't match
/--
warning: Suggested names of type `Array Nat`: S T

Note: This linter can be disabled with `set_option linter.hazel.style.varNaming false`
-/
#guard_msgs in
def vn_fail_array_rule (x : Array Nat) : Nat := x.size

-- The linter must not crash on subsequent declarations in the same file.
#guard_msgs in
def vn_pass_after_finset_rule (n : Nat) : Nat := n + 1

end varNaming

/-! # Parameter Naming -/

section paramNaming
set_option linter.hazel.style.paramNaming true

@[suggested_param_names (L "φ" "ψ")]
class MyLang₂ (L : Type) where
  eval : L → (Nat → Bool) → Bool

#guard_msgs in
def pass_param [MyLang₂ φ] (x : φ) : (Nat → Bool) → Bool := MyLang₂.eval x

#guard_msgs in
def pass_param_psi [MyLang₂ ψ] (x : ψ) : (Nat → Bool) → Bool := MyLang₂.eval x

/--
warning: Suggested names for parameter `L`: φ ψ

Note: This linter can be disabled with `set_option linter.hazel.style.paramNaming false`
-/
#guard_msgs in
def fail_param [MyLang₂ N] (x : N) : (Nat → Bool) → Bool := MyLang₂.eval x

end paramNaming

/-! # Prefer Dot Notation -/

section preferDotNotation
set_option linter.hazel.style.preferDotNotation true

#guard_msgs in
def dn_pass_dot (l : List Nat) : Nat := l.length

#guard_msgs in
def dn_pass_no_ns (n : Nat) : Nat := n + 1

/--
warning: Use dot notation: `l.length`

Note: This linter can be disabled with `set_option linter.hazel.style.preferDotNotation false`
---
info: Try this:
  [apply] l.length
-/
#guard_msgs in
def dn_fail_length (l : List Nat) : Nat := List.length l

/--
warning: Use dot notation: `l.map (· + 1)`

Note: This linter can be disabled with `set_option linter.hazel.style.preferDotNotation false`
---
info: Try this:
  [apply] l.map (· + 1)
-/
#guard_msgs in
def dn_fail_map (l : List Nat) : List Nat := List.map (· + 1) l

/--
warning: Use dot notation: `l₁.append l₂`

Note: This linter can be disabled with `set_option linter.hazel.style.preferDotNotation false`
---
info: Try this:
  [apply] l₁.append l₂
-/
#guard_msgs in
def dn_fail_append (l₁ l₂ : List Nat) : List Nat := List.append l₁ l₂

/--
warning: Use dot notation: `l.reverse`

Note: This linter can be disabled with `set_option linter.hazel.style.preferDotNotation false`
---
info: Try this:
  [apply] l.reverse
-/
#guard_msgs in
def dn_fail_reverse (l : List Nat) : List Nat := List.reverse l

-- Passing: implicit arg of same type before explicit arg.
-- `DnTestLemma.mem_union_left` has implicit `{s : DnTestSet}` before
-- explicit `(t : DnTestSet)`, so dot notation on `t` would fill `s`
-- incorrectly.
structure DnTestSet where vals : List Nat
def DnTestSet.union (s t : DnTestSet) : DnTestSet := ⟨s.vals ++ t.vals⟩
def DnTestSet.mem (v : Nat) (s : DnTestSet) : Prop := v ∈ s.vals
theorem DnTestSet.mem_union_left {s : DnTestSet} (t : DnTestSet)
    (h : s.mem v) : (s.union t).mem v := by
  simp only [DnTestSet.mem, DnTestSet.union, List.mem_append]
  exact Or.inl h

#guard_msgs in
example (s t : DnTestSet) (v : Nat) (hv : s.mem v) :
    (s.union t).mem v :=
  DnTestSet.mem_union_left t hv

-- Passing: already using dot notation
#guard_msgs in
def dn_pass_already_dot (l : List Nat) : Nat := l.length

/-! ### Qualified name matching (module-qualified Expr names) -/

-- Structure + method defined in same file (inside public section)
structure DnQualFoo where
  val : Nat

namespace DnQualFoo
def isPos (f : DnQualFoo) : Prop := f.val > 0
end DnQualFoo

-- Failing: qualified call DnQualFoo.isPos → φ.isPos
/--
warning: Use dot notation: `φ.isPos`

Note: This linter can be disabled with `set_option linter.hazel.style.preferDotNotation false`
---
info: Try this:
  [apply] φ.isPos
-/
#guard_msgs in
def dn_fail_qualified (φ : DnQualFoo) : Prop := DnQualFoo.isPos φ

-- Passing: already using dot notation on same-file type
#guard_msgs in
def dn_pass_qualified_dot (φ : DnQualFoo) : Prop := φ.isPos

-- Failing: qualified call in binder type
/--
warning: Use dot notation: `φ.isPos`

Note: This linter can be disabled with `set_option linter.hazel.style.preferDotNotation false`
---
info: Try this:
  [apply] φ.isPos
-/
#guard_msgs in
theorem dn_fail_qualified_binder {φ : DnQualFoo}
    (h : DnQualFoo.isPos φ) : True := trivial

-- Passing: dot notation inside binder (not flagged)
#guard_msgs in
theorem dn_pass_dot_binder {φ : DnQualFoo}
    (h : φ.isPos) : True := trivial

/-! ### Coercion edge cases -/

-- Subtype: receiver is coerced, source type doesn't match namespace
structure DnBase where val : Nat

def DnBase.isGood (b : DnBase) : Prop := b.val > 0

abbrev DnSub := { b : DnBase // b.val > 0 }

-- Passing: φ : DnSub, call DnBase.isGood φ — coercion involved, don't flag
#guard_msgs in
theorem dn_pass_coercion (φ : DnSub) : DnBase.isGood φ → True := fun _ => trivial

-- Passing: coercion in instance field body
def DnBase.toNat (b : DnBase) : Nat := b.val

class DnHasVal (α : Type) where
  toNat : α → Nat

#guard_msgs in
instance : DnHasVal DnSub where
  toNat φ := DnBase.toNat φ

-- Passing: explicit coercion ↑φ in term
#guard_msgs in
def dn_pass_explicit_coe (φ : DnSub) : Nat := DnBase.toNat (↑φ)

-- Failing: direct type match (no coercion)
/--
warning: Use dot notation: `φ.isGood`

Note: This linter can be disabled with `set_option linter.hazel.style.preferDotNotation false`
---
info: Try this:
  [apply] φ.isGood
-/
#guard_msgs in
theorem dn_fail_no_coercion (φ : DnBase) : DnBase.isGood φ → True := fun _ => trivial

end preferDotNotation

/-! # Prefer Notation -/

section preferNotation
set_option linter.hazel.style.preferNotation true
set_option linter.hazel.style.preferDotNotation false

@[expose] public section

def myAdd (a b : Nat) : Nat := a + b

infixl:65 " ⊕ " => myAdd

#guard_msgs in
def un_pass_notation (a b : Nat) : Nat := a ⊕ b

#guard_msgs in
def un_pass_no_notation (a b : Nat) : Nat := a + b

/--
warning: Use notation: `a ⊕ b`

Note: This linter can be disabled with `set_option linter.hazel.style.preferNotation false`
---
info: Try this:
  [apply] a ⊕ b
-/
#guard_msgs in
def un_fail_explicit (a b : Nat) : Nat := myAdd a b

end -- @[expose] public section

/--
warning: Use notation: `¬p`

Note: This linter can be disabled with `set_option linter.hazel.style.preferNotation false`
---
info: Try this:
  [apply] ¬p
-/
#guard_msgs in
def un_fail_not (p : Prop) : Prop := Not p

/--
warning: Use notation: `a + b`

Note: This linter can be disabled with `set_option linter.hazel.style.preferNotation false`
---
info: Try this:
  [apply] a + b
-/
#guard_msgs in
def un_fail_add (a b : Nat) : Nat := HAdd.hAdd a b

/--
warning: Use notation: `(a, b)`

Note: This linter can be disabled with `set_option linter.hazel.style.preferNotation false`
---
info: Try this:
  [apply] (a, b)
-/
#guard_msgs in
def un_fail_pair (a b : Nat) : Nat × Nat := Prod.mk a b

/--
warning: Use notation: `p ∧ q`

Note: This linter can be disabled with `set_option linter.hazel.style.preferNotation false`
---
info: Try this:
  [apply] p ∧ q
-/
#guard_msgs in
def un_fail_and (p q : Prop) : Prop := And p q

#guard_msgs in
def un_pass_not (p : Prop) : Prop := ¬p

#guard_msgs in
def un_pass_add (a b : Nat) : Nat := a + b

#guard_msgs in
def un_pass_and (p q : Prop) : Prop := p ∧ q

#guard_msgs in
def un_pass_ite (c : Bool) (a b : Nat) : Nat := if c then a else b

-- Universe-polymorphic typeclass with custom notation
@[expose] public section

universe u
set_option quotPrecheck false

class UnTestOp (α : Type u) where
  unOp : α → α → α

notation "UNOP(" a ", " b ")" => UnTestOp.unOp a b

instance : UnTestOp Nat where unOp := Nat.add

end

-- Failing: concrete call, universe-polymorphic class
/--
warning: Use notation: `UNOP(a, b)`

Note: This linter can be disabled with `set_option linter.hazel.style.preferNotation false`
---
info: Try this:
  [apply] UNOP(a, b)
-/
#guard_msgs in
def un_fail_univ (a b : Nat) : Nat := UnTestOp.unOp a b

-- Failing: polymorphic call
/--
warning: Use notation: `UNOP(a, b)`

Note: This linter can be disabled with `set_option linter.hazel.style.preferNotation false`
---
info: Try this:
  [apply] UNOP(a, b)
-/
#guard_msgs in
def un_fail_poly [UnTestOp α] (a b : α) : α := UnTestOp.unOp a b

-- Passing: already using notation
#guard_msgs in
def un_pass_univ (a b : Nat) : Nat := UNOP(a, b)

-- Scoped notation
@[expose] public section
namespace UnTestNs
scoped notation "SNOP(" a ", " b ")" => UnTestOp.unOp a b
end UnTestNs
end

-- Failing: scoped notation available via open
/--
warning: Use notation: `SNOP(a, b)`

Note: This linter can be disabled with `set_option linter.hazel.style.preferNotation false`
---
info: Try this:
  [apply] SNOP(a, b)
-/
#guard_msgs in
open UnTestNs in
def un_fail_scoped (a b : Nat) : Nat := UnTestOp.unOp a b

-- Passing: using scoped notation
#guard_msgs in
open UnTestNs in
def un_pass_scoped (a b : Nat) : Nat := SNOP(a, b)

-- Failing: namespaced function (suffix matching)
@[expose] public section
namespace UnTestNs2
def myFn (a b : Nat) : Nat := a + b
notation "MYFN(" a ", " b ")" => UnTestNs2.myFn a b
end UnTestNs2
end

/--
warning: Use notation: `MYFN(a, b)`

Note: This linter can be disabled with `set_option linter.hazel.style.preferNotation false`
---
info: Try this:
  [apply] MYFN(a, b)
-/
#guard_msgs in
open UnTestNs2 in
def un_fail_ns (a b : Nat) : Nat := myFn a b

-- Passing: lambda body — delab may use `↦` vs `=>` but these are
-- syntactic variants, not notation differences
#guard_msgs in
def un_pass_lambda (f : Nat → Nat) : Nat → Nat := fun x => f x

-- Passing: do block — delab desugars the do body, producing multi-line
-- output that is not a useful notation suggestion
#guard_msgs in
def un_pass_do : IO Nat := do
  let x ← pure 42
  pure x

-- Passing: match expression — delab may restructure
#guard_msgs in
def un_pass_match (n : Nat) : Nat := match n with
  | 0 => 1
  | n + 1 => n

end preferNotation

/-! # Inline By -/

section inlineBy
set_option linter.hazel.style.inlineBy true

#guard_msgs in
theorem fmt_pass_inline : True := by trivial

#guard_msgs in
theorem fmt_pass_term_by : True := (by trivial)

/--
warning: `by` should not start a new line

Note: This linter can be disabled with `set_option linter.hazel.style.inlineBy false`
-/
#guard_msgs in
theorem fmt_fail_newline_by : True :=
  by trivial

end inlineBy

/-! # Inline Do -/

section inlineDo
set_option linter.hazel.style.inlineDo true

#guard_msgs in
def fmt_pass_inline_do : IO Unit := do
  return ()

/--
warning: `do` should be on the same line as the preceding token

Note: This linter can be disabled with `set_option linter.hazel.style.inlineDo false`
-/
#guard_msgs in
def fmt_fail_newline_do : IO Unit :=
  do return ()

end inlineDo

/-! # Keyword Align -/

section keywordAlign
set_option linter.hazel.style.keywordAlign.where true
set_option linter.hazel.style.keywordAlign.deriving true
set_option linter.hazel.style.keywordAlign.terminationBy true
set_option linter.hazel.style.keywordAlign.decreasingBy true

#guard_msgs in
instance : Inhabited Nat where
  default := 0

#guard_msgs in
inductive MyBool where
  | t | f
deriving Repr

#guard_msgs in
def fib : Nat → Nat
  | 0 => 0
  | 1 => 1
  | n + 2 => fib (n + 1) + fib n
termination_by n => n

/--
warning: `termination_by` should align with its declaration (column 0)

Note: This linter can be disabled with `set_option linter.hazel.style.keywordAlign.terminationBy false`
-/
#guard_msgs in
def fib2 : Nat → Nat
  | 0 => 0
  | 1 => 1
  | n + 2 => fib2 (n + 1) + fib2 n
  termination_by n => n

-- Negative: indented `where`
/--
warning: `where` should align with its declaration (column 0)

Note: This linter can be disabled with `set_option linter.hazel.style.keywordAlign.where false`
-/
#guard_msgs in
instance : ToString Bool
  where toString b := if b then "yes" else "no"

-- Negative: indented `decreasing_by`
/--
warning: `decreasing_by` should align with its declaration (column 0)

Note: This linter can be disabled with `set_option linter.hazel.style.keywordAlign.decreasingBy false`
-/
#guard_msgs in
def fib3 : Nat → Nat
  | 0 => 0
  | 1 => 1
  | n + 2 => fib3 (n + 1) + fib3 n
termination_by n => n
  decreasing_by all_goals omega

end keywordAlign

/-! # Section No Indent -/

section sectionNoIndent
set_option linter.hazel.style.sectionNoIndent true

#guard_msgs in
def sni_pass_toplevel := true

#guard_msgs in
section SniSection

#guard_msgs in
def sni_pass_in_section := true

#guard_msgs in
end SniSection

-- Negative: indented definition inside section
section SniIndented
/--
warning: Command should not be indented (column 2, expected 0)

Note: This linter can be disabled with `set_option linter.hazel.style.sectionNoIndent false`
-/
#guard_msgs in
  def sni_fail_indented := true
end SniIndented

end sectionNoIndent

/-! # Numeric Projection Depth -/

section numericProjDepth
set_option linter.hazel.style.numericProj true
set_option linter.hazel.style.numericProjDepth 1

-- Passing: single numeric projection
#guard_msgs in
def npd_pass_single (x : Nat × Nat) : Nat := x.1

-- Passing: named projections (any depth)
#guard_msgs in
def npd_pass_named (x : Nat × (Nat × Nat)) : Nat := x.snd.fst

-- Passing: mixed, named resets chain
#guard_msgs in
def npd_pass_mixed (x : (Nat × Nat) × (Nat × Nat)) : Nat := x.snd.1

-- Failing: depth 2 numeric chain
/--
warning: Numeric projection chain `.2.1` is 2 deep (max 1).  Use named field access or destructuring instead.

Note: This linter can be disabled with `set_option linter.hazel.style.numericProj false`
-/
#guard_msgs in
def npd_fail_depth2 (x : Nat × (Nat × Nat)) : Nat := x.2.1

-- Failing: depth 3 numeric chain
/--
warning: Numeric projection chain `.2.2.1` is 3 deep (max 1).  Use named field access or destructuring instead.

Note: This linter can be disabled with `set_option linter.hazel.style.numericProj false`
-/
#guard_msgs in
def npd_fail_depth3 (x : Nat × (Nat × (Nat × Nat))) : Nat := x.2.2.1

-- Passing with higher threshold
set_option linter.hazel.style.numericProjDepth 2 in
#guard_msgs in
def npd_pass_threshold2 (x : Nat × (Nat × Nat)) : Nat := x.2.1

-- Failing at threshold 2 with depth 3
/--
warning: Numeric projection chain `.2.2.1` is 3 deep (max 2).  Use named field access or destructuring instead.

Note: This linter can be disabled with `set_option linter.hazel.style.numericProj false`
-/
#guard_msgs in
set_option linter.hazel.style.numericProjDepth 2 in
def npd_fail_threshold2 (x : Nat × (Nat × (Nat × Nat))) : Nat := x.2.2.1

-- Disabled with Bool
#guard_msgs in
set_option linter.hazel.style.numericProj false in
def npd_pass_disabled (x : Nat × (Nat × (Nat × Nat))) : Nat := x.2.2.1

end numericProjDepth

/-! # byIndent -/

section byIndent
set_option linter.hazel.style.byIndent true

-- Passing: single-line by (no indentation to check)
#guard_msgs in
theorem bi_pass_inline : True := by trivial

-- Passing: correct 2-space indent from command (col 0)
#guard_msgs in
theorem bi_pass_basic : True := by
  trivial

-- Passing: multi-line signature, by on continuation line
#guard_msgs in
theorem bi_pass_multiline
    (h : True) : True := by
  exact h

-- Passing: def with by
#guard_msgs in
def bi_pass_def : Nat := by
  exact 42

-- Passing: instance with by
#guard_msgs in
instance bi_pass_instance : Inhabited Nat := by
  exact ⟨0⟩

-- Failing: 4-space indent (expected 2)
/--
warning: Tactic proof after `by` is not indented correctly (expected 2 spaces from enclosing declaration).

Note: This linter can be disabled with `set_option linter.hazel.style.byIndent false`
-/
#guard_msgs in
theorem bi_fail_overindent : True := by
    trivial

-- Failing: 1-space indent (under-indented)
/--
warning: Tactic proof after `by` is not indented correctly (expected 2 spaces from enclosing declaration).

Note: This linter can be disabled with `set_option linter.hazel.style.byIndent false`
-/
#guard_msgs in
theorem bi_fail_underindent : True := by
 trivial

-- Passing: nested have with by (not checked — only top-level by)
#guard_msgs in
theorem bi_pass_nested_have : True := by
  have h : True := by
      trivial  -- wrong indent, but nested — not checked
  exact h

-- Passing: fun ... => by (not checked — inline by)
#guard_msgs in
theorem bi_pass_fun_by : True := by
  have h : True → True := fun _ => by
        trivial  -- deeply indented, but nested — not checked
  exact h trivial

-- Passing: show ... from by (not checked — inline by)
#guard_msgs in
theorem bi_pass_show_by : 1 + 0 = 1 := by
  rw [show 1 + 0 = 1 from by rfl]

-- Passing: by inside where clause
#guard_msgs in
structure BiTestStruct where
  val : Nat
  prop : val = val := by rfl

-- Passing: focusing dots
#guard_msgs in
theorem bi_pass_focus : True ∧ True := by
  constructor
  · trivial
  · trivial

end byIndent

/-! # preferBinder -/

section preferBinder
set_option linter.hazel.style.preferBinder true

-- Passing: already explicit binder
#guard_msgs in
theorem pb_pass_binder (h : True) : True := h

-- Passing: Nat is not Prop
#guard_msgs in
def pb_pass_data : Nat → Nat := fun n => n

-- Passing: arrow inside parens (higher-order function type)
#guard_msgs in
def pb_pass_higher (f : Nat → Nat) : Nat := f 0

-- Failing: Prop-valued arrow
/--
warning: `True` could be an explicit argument instead.

Note: This linter can be disabled with `set_option linter.hazel.style.preferBinder false`
-/
#guard_msgs in
theorem pb_fail_arrow : True → True := fun h => h

-- Failing: two Prop-valued arrows
/--
warning: `True` could be an explicit argument instead.

Note: This linter can be disabled with `set_option linter.hazel.style.preferBinder false`
---
warning: `False` could be an explicit argument instead.

Note: This linter can be disabled with `set_option linter.hazel.style.preferBinder false`
-/
#guard_msgs in
theorem pb_fail_two : True → False → True := fun h _ => h

-- Failing: Prop arrow in return type after explicit binder
/--
warning: `True` could be an explicit argument instead.

Note: This linter can be disabled with `set_option linter.hazel.style.preferBinder false`
-/
#guard_msgs in
theorem pb_fail_partial (h : True) : True → True := fun _ => h

-- Failing: forall with Prop
/--
warning: `True` could be an explicit argument instead.

Note: This linter can be disabled with `set_option linter.hazel.style.preferBinder false`
-/
#guard_msgs in
theorem pb_fail_forall : ∀ _ : True, True := fun h => h

-- Edge: mixed Prop and non-Prop arrows — only Prop flagged
/--
warning: `True` could be an explicit argument instead.

Note: This linter can be disabled with `set_option linter.hazel.style.preferBinder false`
-/
#guard_msgs in
def pb_fail_mixed_arrows : Nat → True → True := fun _ h => h

-- Edge: abbrev with Prop arrow
/--
warning: `True` could be an explicit argument instead.

Note: This linter can be disabled with `set_option linter.hazel.style.preferBinder false`
-/
#guard_msgs in
abbrev pb_fail_abbrev : True → True := fun h => h

-- Edge: chained arrows with Prop
/--
warning: `True` could be an explicit argument instead.

Note: This linter can be disabled with `set_option linter.hazel.style.preferBinder false`
---
warning: `True` could be an explicit argument instead.

Note: This linter can be disabled with `set_option linter.hazel.style.preferBinder false`
-/
#guard_msgs in
theorem pb_fail_multi_arrow : True → True → True := fun h _ => h

-- Edge: no type annotation (def foo := ...) — should not crash
#guard_msgs in
def pb_pass_no_type := 42

end preferBinder

/-! # redundantImplicit -/

section redundantImplicit
set_option linter.hazel.style.redundantImplicit true
set_option autoImplicit true

-- Passing: not implicit (explicit binder)
#guard_msgs in
def ri_pass_explicit (α : Type) (x : α) : α := x

-- Passing: not Type/Sort ({n : Nat})
#guard_msgs in
def ri_pass_nat {n : Nat} (x : Fin n) : Fin n := x

-- Passing: autoImplicit off
#guard_msgs in
set_option autoImplicit false in
def ri_pass_auto_off {α : Type} (x : α) : α := x

-- Passing: instance binder
#guard_msgs in
def ri_pass_instance [inst : Inhabited α] : α := inst.default

-- Passing: strict implicit
#guard_msgs in
def ri_pass_strict ⦃α : Type⦄ (x : α) : α := x

-- Passing: non-Type implicit ({x : α} alone, no Type binder)
-- Note: {α : Type} WOULD be flagged, but {x : α} should NOT be
/--
warning: Implicit binder `α : Type` could be omitted, `autoImplicit` would bind it.  Note: removing may widen the universe level.

Note: This linter can be disabled with `set_option linter.hazel.style.redundantImplicit false`
-/
#guard_msgs in
theorem ri_pass_nontype {α : Type} {x : α} (h : x = x) : True := trivial

-- Failing: basic {α : Type}
/--
warning: Implicit binder `α : Type` could be omitted, `autoImplicit` would bind it.  Note: removing may widen the universe level.

Note: This linter can be disabled with `set_option linter.hazel.style.redundantImplicit false`
-/
#guard_msgs in
def ri_fail_basic {α : Type} (x : α) : α := x

-- Failing: multiple {α : Type} {β : Type}
/--
warning: Implicit binder `α : Type` could be omitted, `autoImplicit` would bind it.  Note: removing may widen the universe level.

Note: This linter can be disabled with `set_option linter.hazel.style.redundantImplicit false`
---
warning: Implicit binder `β : Type` could be omitted, `autoImplicit` would bind it.  Note: removing may widen the universe level.

Note: This linter can be disabled with `set_option linter.hazel.style.redundantImplicit false`
-/
#guard_msgs in
def ri_fail_two {α : Type} {β : Type} (f : α → β) (x : α) : β := f x

-- Failing: theorem
/--
warning: Implicit binder `α : Type` could be omitted, `autoImplicit` would bind it.  Note: removing may widen the universe level.

Note: This linter can be disabled with `set_option linter.hazel.style.redundantImplicit false`
-/
#guard_msgs in
theorem ri_fail_theorem {α : Type} {x : α} {y : α} (h : x = y) : y = x := h.symm

end redundantImplicit

/-! ### redundantImplicit level 2 -/

section redundantImplicitL2
set_option linter.hazel.style.redundantImplicit true
set_option linter.hazel.style.redundantImplicitLevel 2

-- Passing at level 1 (non-Sort), but failing at level 2: {n : Nat}
/--
warning: Implicit binder `n : Nat` could be omitted, `autoImplicit` would infer the same type from usage.

Note: This linter can be disabled with `set_option linter.hazel.style.redundantImplicit false`
-/
#guard_msgs in
theorem ri2_fail_nat {n : Nat} (h : n > 0) : n ≥ 1 := h

-- Failing at level 2: {l : List α}
/--
warning: Implicit binder `l : List α` could be omitted, `autoImplicit` would infer the same type from usage.

Note: This linter can be disabled with `set_option linter.hazel.style.redundantImplicit false`
-/
#guard_msgs in
theorem ri2_fail_list {l : List α} (h : l ≠ []) : l.length > 0 := by
  cases l with
  | nil => contradiction
  | cons _ _ => simp

-- Failing at level 2: {a : α} and {l : List α} (both flagged)
/--
warning: Implicit binder `a : α` could be omitted, `autoImplicit` would infer the same type from usage.

Note: This linter can be disabled with `set_option linter.hazel.style.redundantImplicit false`
---
warning: Implicit binder `l : List α` could be omitted, `autoImplicit` would infer the same type from usage.

Note: This linter can be disabled with `set_option linter.hazel.style.redundantImplicit false`
-/
#guard_msgs in
theorem ri2_fail_elem {a : α} {l : List α} (h : a ∈ l) : l ≠ [] := by
  cases h <;> simp

-- Passing at level 2: explicit binder (not implicit)
#guard_msgs in
theorem ri2_pass_explicit (n : Nat) (h : n > 0) : n ≥ 1 := h

-- Passing at level 2: instance binder
#guard_msgs in
theorem ri2_pass_inst [Inhabited α] (x : α) : True := trivial

-- Passing at level 2: auto-implicit (no binder at all)
#guard_msgs in
theorem ri2_pass_auto (h : n > 0) : n ≥ 1 := h

-- Passing at level 2: name shadows something in scope
namespace ri2_shadow
def n := 42
-- n resolves to ri2_shadow.n, auto-implicit won't bind it
end ri2_shadow

-- Sort binder still gets the universe widening message at level 2
/--
warning: Implicit binder `α : Type` could be omitted, `autoImplicit` would bind it.  Note: removing may widen the universe level.

Note: This linter can be disabled with `set_option linter.hazel.style.redundantImplicit false`
-/
#guard_msgs in
theorem ri2_fail_sort {α : Type} (x : α) : True := trivial

-- Level 1 does NOT flag non-Sort binders
/--
warning: Implicit binder `α : Type` could be omitted, `autoImplicit` would bind it.  Note: removing may widen the universe level.

Note: This linter can be disabled with `set_option linter.hazel.style.redundantImplicit false`
-/
#guard_msgs in
set_option linter.hazel.style.redundantImplicitLevel 1 in
theorem ri2_level1_only_sort {α : Type} {n : Nat} (h : n > 0) (x : α) : True := trivial

-- Passing at level 2: dependent forall type (auto-implicit can't reconstruct)
#guard_msgs in
theorem ri2_pass_dependent_forall
    {P : (f : Nat → Bool) → (n : Nat) → f n = true → Prop}
    (h : P (fun _ => true) 0 rfl) : True := trivial

-- Passing at level 2: another dependent forall
#guard_msgs in
def ri2_pass_dependent_pred {P : (n : Nat) → n > 0 → Prop}
    (h : P 1 (by omega)) : True := trivial

-- Passing at level 2: predicate over multiple typed args with dependencies
-- (predicate over multiple typed args with dependencies)
#guard_msgs in
theorem ri2_pass_complex_pred
    {P : (f : Nat → Bool) → (V : List Nat) → (∀ n ∈ V, f n = true) → Prop}
    (h : P (fun _ => true) [0, 1] (by simp)) : True := trivial

-- Passing at level 2: dependent pair type
#guard_msgs in
theorem ri2_pass_sigma {p : (n : Nat) → Fin n → Prop}
    (h : p 3 ⟨1, by omega⟩) : True := trivial

/-! ### Function position vs argument position -/

-- Passing: function-typed binder only used in function position (applied)
-- Auto-implicit can't infer function types from application alone.
#guard_msgs in
theorem ri2_pass_applied_only {f : Nat → Nat → Bool} (h : f 0 1 = true) : True := trivial

-- Passing: higher-order binder only applied (the VarOrder P pattern)
#guard_msgs in
theorem ri2_pass_higher_order {P : Nat → Nat → Prop} (h : ∀ n, P n 0) : P 1 0 := h 1

-- Passing: P applied inside forall only
#guard_msgs in
theorem ri2_pass_applied_in_forall {P : Nat → Prop} (h : ∀ n, P n) : P 0 := h 0

-- Failing: function-typed binder used as ARGUMENT to a known function
-- List.map constrains f's type, so auto-implicit works.
/--
warning: Implicit binder `f : Nat → Nat` could be omitted, `autoImplicit` would infer the same type from usage.

Note: This linter can be disabled with `set_option linter.hazel.style.redundantImplicit false`
-/
#guard_msgs in
theorem ri2_fail_func_as_arg {f : Nat → Nat} (h : List.map f [1] = [2]) : True := trivial

-- Failing: f used as argument via Function.Injective
/--
warning: Implicit binder `f : Nat → Nat` could be omitted, `autoImplicit` would infer the same type from usage.

Note: This linter can be disabled with `set_option linter.hazel.style.redundantImplicit false`
-/
#guard_msgs in
theorem ri2_fail_injective {f : Nat → Nat} (h : Function.Injective f) : True := trivial

-- Failing: f used as argument via @Eq (type annotation constrains it)
/--
warning: Implicit binder `f : Nat → Bool` could be omitted, `autoImplicit` would infer the same type from usage.

Note: This linter can be disabled with `set_option linter.hazel.style.redundantImplicit false`
-/
#guard_msgs in
theorem ri2_fail_eq_constraint {f : Nat → Bool} (h : @Eq (Nat → Bool) f f) : True := trivial

-- Failing: f applied AND used as argument — argument-position constrains type
/--
warning: Implicit binder `f : Nat → Nat` could be omitted, `autoImplicit` would infer the same type from usage.

Note: This linter can be disabled with `set_option linter.hazel.style.redundantImplicit false`
-/
#guard_msgs in
theorem ri2_fail_mixed {f : Nat → Nat} (h1 : Function.Injective f) (h2 : f 0 = 1) :
    True := trivial

/-! ### Dot notation edge cases -/

structure RIFoo where
  val : Nat
  prop : val > 0 := by omega

-- Passing: binder used ONLY via dot notation — surely can't be inferred
#guard_msgs in
theorem ri2_pass_dot_only {φ : RIFoo} (h : φ.val > 0) : φ.prop = φ.prop := rfl

-- Passing: binder used only via dot notation in both binder types and return type
#guard_msgs in
theorem ri2_pass_dot_all {φ : RIFoo} (h : φ.val > 0) : φ.val > 0 := h

-- Failing: binder used via explicit call (not dot notation) — inferable
/--
warning: Implicit binder `φ : RIFoo` could be omitted, `autoImplicit` would infer the same type from usage.

Note: This linter can be disabled with `set_option linter.hazel.style.redundantImplicit false`
-/
#guard_msgs in
theorem ri2_fail_explicit_call {φ : RIFoo} (h : RIFoo.val φ > 0) : True := trivial

-- Failing: binder used both via dot notation AND as function arg — inferable
/--
warning: Implicit binder `φ : RIFoo` could be omitted, `autoImplicit` would infer the same type from usage.

Note: This linter can be disabled with `set_option linter.hazel.style.redundantImplicit false`
-/
#guard_msgs in
theorem ri2_fail_mixed_dot {φ : RIFoo} (h : φ.val > 0) (g : RIFoo.val φ > 0) : True := trivial

-- Passing: numeric projection (also Term.proj) — can't infer
#guard_msgs in
theorem ri2_pass_numeric_proj {p : Nat × Nat} (h : p.1 > 0) : p.1 > 0 := h

end redundantImplicitL2

/-! # argumentOrder -/

section argumentOrder
set_option linter.hazel.style.paramOrder true

-- Passing: correct order (α used first)
#guard_msgs in
def ao_pass_order {α : Type} {β : Type} (f : α → β) (x : α) : β := f x

-- Passing: dependency forces order (β depends on α)
/-- warning: declaration uses `sorry` -/
#guard_msgs in
def ao_pass_dep {α : Type} {β : α → Type} (x : α) : β x := sorry

-- Passing: single binder
#guard_msgs in
def ao_pass_single {α : Type} (x : α) : α := x

-- Passing: both used at same position
#guard_msgs in
def ao_pass_same {α : Type} {β : Type} (p : α × β) : α := p.1

-- Passing: β has more uses but first occurrence ties — don't flag
#guard_msgs in
def ao_pass_tied {α : Type} {β : Type} (f : β → α) (x : β) : α := f x

-- Failing: explicit binders misordered
-- Passing: tied first-use (both used at h) — keep declaration order
#guard_msgs in
def ao_pass_tied_data (y : Nat) (x : Nat) (h : x < y) : Nat := x

-- Passing: Product type α × β — both used at same binder, α first in expr
#guard_msgs in
def ao_pass_prod {α : Type} {β : Type} (p : α × β) : β := p.2

-- Passing: reversed product β × α — β first in expr, matches declaration order
#guard_msgs in
def ao_pass_prod_rev {β : Type} {α : Type} (p : β × α) : α := p.2

-- Passing: product β × α — both first used at same binder, no 2nd use for α
#guard_msgs in
def ao_pass_prod_noswap {α : Type} {β : Type} (p : β × α) : α := p.2

-- Passing: instance binder — Inhabited depends on α, order forced
#guard_msgs in
def ao_pass_inst {α : Type} [Inhabited α] : α := default

-- Passing: strict implicit
#guard_msgs in
def ao_pass_strict ⦃α : Type⦄ ⦃β : Type⦄ (f : α → β) : α → β := f

-- Failing: α first used at binder 2 (g), β first used at binder 1 (f)
/--
warning: `α` is declared before `β` but used later.  Consider reordering.

Note: This linter can be disabled with `set_option linter.hazel.style.paramOrder false`
-/
#guard_msgs in
def ao_fail_separate {α : Type} {β : Type} (f : β → Nat) (g : α → Nat) (b : β) (a : α) : Nat := f b + g a

-- Failing: strict implicit misordered (different first-use binders)
/--
warning: `α` is declared before `β` but used later.  Consider reordering.

Note: This linter can be disabled with `set_option linter.hazel.style.paramOrder false`
-/
#guard_msgs in
def ao_fail_strict ⦃α : Type⦄ ⦃β : Type⦄ (f : β → Nat) (g : α → Nat) (b : β) (a : α) : Nat := f b + g a

-- Passing: mixed implicit + explicit, correct order
#guard_msgs in
def ao_pass_mixed {α : Type} (x : α) {β : Type} (f : α → β) : β := f x

-- Passing: three binders, all correctly ordered (no arrow in return type)
#guard_msgs in
def ao_pass_three {α : Type} {β : Type} {γ : Type}
    (f : α → β) (g : β → γ) (x : α) : γ := g (f x)

-- Passing: unused binders have equal score (no flag)
#guard_msgs in
def ao_pass_unused {α : Type} {β : Type} : Nat := 0

-- Passing: theorem with correct order
#guard_msgs in
theorem ao_pass_thm {α : Type} {x y : α} (h : x = y) : y = x := h.symm

-- Passing: bundled {x y : α} not split even when y is used first
#guard_msgs in
theorem ao_pass_bundled {α : Type} {x y : α} (h : y = x) : x = y := h.symm

-- Passing: split binders {x} {y} — tied first-use (both in h)
#guard_msgs in
theorem ao_pass_split_tied {α : Type} {x : α} {y : α} (h : y = x) : x = y := h.symm

-- Passing: function type (Nat → Nat) as binder type — inner arrow doesn't affect ordering
#guard_msgs in
def ao_pass_higher {α : Type} (f : Nat → Nat) (x : α) : α := x

-- Passing: dependency chain: γ depends on β depends on α
/-- warning: declaration uses `sorry` -/
#guard_msgs in
def ao_pass_chain {α : Type} {β : α → Type} {γ : (x : α) → β x → Type}
    (x : α) (y : β x) : γ x y := sorry

-- Edge case: return-type arrow creates phantom binder (forallTelescope opens it)
-- Should NOT flag — both α and β first used at same binder (f), both Sort
#guard_msgs in
def ao_pass_return_arrow {α : Type} {β : Type} (f : α → β) : α → β := f

-- Edge case: ∀ in return type (preferBinder territory, not ours)
#guard_msgs in
theorem ao_pass_forall_return {α : Type} : ∀ x : α, x = x := fun _ => rfl

-- Edge case: multi-name binder group (P Q R : Prop) all used at same binder
/-- warning: declaration uses `sorry` -/
#guard_msgs in
theorem ao_pass_multi_name (P Q R : Prop) (h : P → Q → R) : R := sorry

-- Edge case: instance between types — instance body-only, skip
#guard_msgs in
def ao_pass_inst_between {α : Type} [Inhabited α] (x : α) : α := x

-- Edge case: Prop binders (not Sort) — tiebreaker should apply
-- Passing: bundled (P Q : Prop) not split
/--
warning: declaration uses `sorry`
-/
#guard_msgs in
theorem ao_pass_bundled_prop (P Q : Prop) (h : Q ∧ P) : P := sorry

-- Passing: split (P) (Q) — tied first-use (both in h)
/--
warning: declaration uses `sorry`
-/
#guard_msgs in
theorem ao_pass_split_prop_tied (P : Prop) (Q : Prop) (h : Q ∧ P) : P := sorry

-- Passing: mixed Sort and non-Sort, tied first-use — keep declaration order
/--
warning: declaration uses `sorry`
-/
#guard_msgs in
def ao_pass_mixed_sort {α : Type} {n : Nat} (f : Fin n → α) : α := f ⟨0, sorry⟩

-- Passing: bundled (z y x : Nat) not split
#guard_msgs in
def ao_pass_bundled_three (z y x : Nat) (h : x < y) (g : y < z) : Nat := x

-- Failing: split (z) (y) (x) — only first pair flags (z used later than y)
-- y and x are tied (both first used at h) so no flag for that pair
/--
warning: `z` is declared before `y` but used later.  Consider reordering.

Note: This linter can be disabled with `set_option linter.hazel.style.paramOrder false`
-/
#guard_msgs in
def ao_fail_three_split (z : Nat) (y : Nat) (x : Nat) (h : x < y) (g : y < z) : Nat := x

-- Edge: no binders (should not crash)
#guard_msgs in
def ao_pass_no_binders : Nat := 0

/-! ### Binder grouping -/

-- Passing: bundled {a b : α} {l : List α} — group {a,b} ties with {l}
#guard_msgs in
theorem ao_pass_bundled_list {a b : α} {l : List α} (h1 : a ∈ l) (h2 : b ∈ l) : True := trivial

-- Passing: bundled {a b : α} with both used in return type
#guard_msgs in
theorem ao_pass_bundled_return {a b : α} {l l' : List α} :
    a :: l = b :: l' ↔ a = b ∧ l = l' := by
  constructor
  · intro h; exact ⟨List.head_eq_of_cons_eq h, List.tail_eq_of_cons_eq h⟩
  · rintro ⟨rfl, rfl⟩; rfl

-- Passing: bundled (z y x : Nat) — entire group moves together
#guard_msgs in
def ao_pass_bundled_nat (z y x : Nat) (h : x < y) (g : y < z) : Nat := x

-- Passing: bundled (P Q : Prop) — tied first-use
/--
warning: declaration uses `sorry`
-/
#guard_msgs in
theorem ao_pass_bundled_prop2 (P Q : Prop) (h : Q ∧ P) : P := sorry

-- Passing: stdlib interleaved pattern {l l'} (h) {i} (w)
#guard_msgs in
theorem ao_pass_interleaved {l l' : List α} (h : l = l') {i : Nat} (w : i < l.length) :
    l'[i]'(h ▸ w) = l[i] := by subst h; rfl

-- Passing: {a : α} {l : List α} — tied first-use in same hypothesis
#guard_msgs in
theorem ao_pass_elem_list {a : α} {l : List α} (h : a ∈ l) : True := trivial

-- Passing: {n m : Nat} — bundled, tied
#guard_msgs in
theorem ao_pass_nat_pair {n m : Nat} (h : n < m) : n ≤ m := Nat.le_of_lt h

-- Failing: g first used at h2 (later), f first used at h1 (earlier)
/--
warning: `g` is declared before `f` but used later.  Consider reordering.

Note: This linter can be disabled with `set_option linter.hazel.style.paramOrder false`
-/
#guard_msgs in
def ao_fail_clear_order (g : Nat → Nat) (f : Nat → Nat) (h1 : f 0 = 0) (h2 : g 0 = 0) : True :=
  trivial

-- Failing: R (Type) before v (Var) — R used much later
/--
warning: declaration uses `sorry`
---
warning: `R` is declared before `v` but used later.  Consider reordering.

Note: This linter can be disabled with `set_option linter.hazel.style.paramOrder false`
-/
#guard_msgs in
theorem ao_fail_type_before_data {R : Type} {v : Nat} {V : List Nat}
    (hv : v ∉ V) (α : Nat → R) : True := sorry

-- Passing: L used immediately in instance binder [Inhabited L]
#guard_msgs in
theorem ao_pass_inst_usage {L : Type} [Inhabited L] (x : L) : True := trivial

-- Passing: α used in [BEq α] right after declaration
#guard_msgs in
theorem ao_pass_inst_beq {α : Type} [BEq α] (a b : α) (h : a == b) : True := trivial

end argumentOrder

/-! ## bundleParams -/

section bundleParams
set_option linter.hazel.style.bundleParams true

-- Failing: same type, same kind (implicit)
/--
warning: Adjacent binders could be bundled: `{a b : Nat}`

Note: This linter can be disabled with `set_option linter.hazel.style.bundleParams false`
-/
#guard_msgs in
theorem bp_fail_implicit {a : Nat} {b : Nat} (h : a = b) : b = a := h.symm

-- Failing: same type, same kind (explicit)
/--
warning: Adjacent binders could be bundled: `(x y : Bool)`

Note: This linter can be disabled with `set_option linter.hazel.style.bundleParams false`
-/
#guard_msgs in
def bp_fail_explicit (x : Bool) (y : Bool) : Bool := x && y

-- Failing: three adjacent
/--
warning: declaration uses `sorry`
---
warning: Adjacent binders could be bundled: `{a b c : α}`

Note: This linter can be disabled with `set_option linter.hazel.style.bundleParams false`
-/
#guard_msgs in
theorem bp_fail_three {a : α} {b : α} {c : α} (h : a = b) : True := sorry

-- Passing: already bundled
#guard_msgs in
theorem bp_pass_bundled {a b : Nat} (h : a = b) : b = a := h.symm

-- Passing: different types
#guard_msgs in
def bp_pass_diff_type {a : Nat} {b : Bool} : Nat := a

-- Passing: different binder kinds
#guard_msgs in
def bp_pass_diff_kind {a : Nat} (b : Nat) : Nat := a + b

-- Passing: instance binders
#guard_msgs in
def bp_pass_inst [Inhabited Nat] [ToString Nat] : Nat := default

-- Passing: no type annotation (short form {a} {b})
#guard_msgs in
theorem bp_pass_no_type {a} {b} (h : @Eq Nat a b) : True := trivial

end bundleParams
