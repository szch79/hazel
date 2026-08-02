/-
Test: a non-`set_option` command before the module docstring SHOULD trigger
the placement warning, even when `set_option` commands also appear there.
-/
module

meta import Hazel

set_option linter.hazel.header.moduleDoc true

def commandBeforeDocTest := true

/-!
A module docstring that comes after a definition.
-/
