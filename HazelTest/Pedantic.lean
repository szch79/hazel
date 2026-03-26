/-
Tests for pedantic linters.
-/
module

meta import Hazel

/-! # noVariable -/

section noVariable
set_option linter.hazel.pedantic.noVariable true

/--
warning: Avoid `variable` declarations; prefer full explicit signatures.

Note: This linter can be disabled with `set_option linter.hazel.pedantic.noVariable false`
-/
#guard_msgs in
variable (n : Nat)

end noVariable
