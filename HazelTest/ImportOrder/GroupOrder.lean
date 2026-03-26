/-
Test: wrong group order (private before meta).
Expected warning: meta imports should come before private imports.
Expected suggestion: reorder imports.
-/
module

import Init.Data.Array.Basic
meta import Hazel

set_option linter.hazel.header.importGroupOrder true
-- The linter fires on the import line and at eoi.
-- Cannot use #guard_msgs because the warning is on the import.
