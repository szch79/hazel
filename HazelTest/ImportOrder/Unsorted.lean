/-
Test: unsorted imports within the same group.
Expected warning: Import Finset should come before List.
Expected suggestion: reorder imports.
-/
module

meta import Hazel
import Init.Data.List.Basic
import Init.Data.Array.Basic

set_option linter.hazel.header.sortedImports true
-- The linter fires on the import line above and at eoi.
-- Cannot use #guard_msgs because the warning is on the import,
-- not on a command we can wrap.
