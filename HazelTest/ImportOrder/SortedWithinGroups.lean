/-
Test: sorted within each group, across multiple groups.  No warnings expected.
-/
module

public meta import Hazel
public meta import Hazel.Util
meta import Init.Core
import Init.Data.Array.Basic
import Init.Data.List.Basic

set_option linter.hazel.header.sortedImports true
set_option linter.hazel.header.importGroupOrder true
set_option linter.hazel.header.importGroupContiguity true
