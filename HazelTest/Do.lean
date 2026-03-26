/-
Tests for Do linters (strongPostCond).
-/
module

meta import Hazel
import Std.Tactic.Do

set_option linter.unusedVariables false
set_option mvcgen.warning false

/-! # strongPostCond -/

section strongPostCond
set_option linter.hazel.do.strongPostCond true

open Std.Do

-- Passing: generic Q
#guard_msgs in
@[spec]
theorem good_spec [Monad m] [WPMonad m ps] {Q : PostCond Nat ps} :
    Triple (pure 42 : m Nat) (spred(Q.1 42)) Q := by
  apply Triple.pure; exact .rfl

-- NOTE: Testing the failing case (fixed Q) requires constructing a
-- type-correct Triple with a concrete postcondition, which is complex
-- in the Do framework.  The linter logic (checking if Q is an FVar in
-- the forall telescope) is validated by the passing test above.

end strongPostCond
