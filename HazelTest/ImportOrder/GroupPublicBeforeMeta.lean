/-
Test: public (non-meta) before meta — correct order.  No warnings expected.
Groups: public (1) then meta (2).
-/
module

public import Init.Data.Array.Basic
meta import Hazel

set_option linter.hazel.header.importGroupOrder true
set_option linter.hazel.header.importGroupContiguity true
