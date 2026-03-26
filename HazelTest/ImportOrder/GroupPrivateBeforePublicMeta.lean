/-
Test: private before public meta (wrong order).
Expected warning: public meta imports should come before private imports.
Groups: private (3) then public meta (0) — wrong.
-/
module

import Init.Data.Array.Basic
public meta import Hazel

set_option linter.hazel.header.importGroupOrder true
