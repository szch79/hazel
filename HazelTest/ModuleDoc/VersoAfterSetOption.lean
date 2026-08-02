/-
Test: Verso module docstring preceded by `set_option` commands should NOT
trigger the placement warning: whole-module options conventionally sit
between the imports and the docstring, and `doc.verso` only takes effect
on the docstring when set before it.
-/
module

meta import Hazel

set_option doc.verso true
set_option linter.hazel.header.moduleDoc true

/-!
A well-formed module docstring under Verso,
preceded only by whole-module option commands.
-/

def versoAfterSetOptionTest := true
