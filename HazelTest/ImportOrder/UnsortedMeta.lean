/-
Test: unsorted within meta group.
Expected warning: sorted import violation within meta group.
-/
module

meta import Init.Core
meta import Hazel

set_option linter.hazel.header.sortedImports true
