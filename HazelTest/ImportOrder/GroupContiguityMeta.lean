/-
Test: meta group split by a private import.
Expected warning: meta imports should be contiguous.
-/
module

meta import Hazel
import Init.Data.Array.Basic
meta import Init.Core

set_option linter.hazel.header.importGroupContiguity true
