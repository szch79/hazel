/-
Test: public meta imports sorted and grouped correctly.  No warnings expected.
Groups: public meta (0) then meta (2) then private (3).
-/
module

public meta import Hazel
public meta import Hazel.Util
meta import Init.Core
import Init.Data.Array.Basic

set_option linter.hazel.header.sortedImports true
set_option linter.hazel.header.importGroupOrder true
set_option linter.hazel.header.importGroupContiguity true
