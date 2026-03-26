/-
Test: already sorted imports.  No warnings expected.
-/
module

meta import Hazel
import Init.Data.Array.Basic
import Init.Data.List.Basic

set_option linter.hazel.header.sortedImports true
set_option linter.hazel.header.importGroupOrder true
