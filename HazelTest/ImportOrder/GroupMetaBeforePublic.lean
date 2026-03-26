/-
Test: meta before public (wrong order).
Expected warning: public imports should come before meta imports.
Groups: meta (2) then public (1) — wrong, should be public first.
-/
module

meta import Hazel
public import Init.Data.Array.Basic

set_option linter.hazel.header.importGroupOrder true
