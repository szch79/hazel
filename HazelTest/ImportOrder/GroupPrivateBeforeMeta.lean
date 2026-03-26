/-
Test: private before meta (wrong order).
Expected warning: meta imports should come before private imports.
Groups: private (3) then meta (2) — wrong.
-/
module

import Init.Data.Array.Basic
meta import Hazel

set_option linter.hazel.header.importGroupOrder true
