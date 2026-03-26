/-
Test: all four groups in correct order.  No warnings expected.
Groups: public meta (0) > public (1) > meta (2) > private (3).
-/
module

public meta import Hazel
public import Init.Data.Array.Basic
meta import Init.Core
import Init.Data.List.Basic

set_option linter.hazel.header.sortedImports true
set_option linter.hazel.header.importGroupOrder true
set_option linter.hazel.header.importGroupContiguity true
