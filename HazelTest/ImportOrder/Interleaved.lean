/-
Test: interleaved groups (same group split by another).
Expected warning: group contiguity violation.
-/
module

public meta import Hazel
import Init.Data.Array.Basic
public meta import Hazel.Util

set_option linter.hazel.header.importGroupContiguity true
-- The linter should flag `public meta import Hazel.Util` because
-- the public meta group is split by a private import.
