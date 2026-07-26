/-
Test: Verso module docstring preceded by `set_option` commands SHOULD
trigger the placement warning.
Regression: before the Verso store was consulted, this case was misreported
as "Missing module docstring" instead of a placement violation.
-/
module

meta import Hazel

set_option doc.verso true
set_option linter.hazel.header.moduleDoc true

/-!
A well-formed module docstring under Verso,
but not the first command after imports.
-/

def versoAfterSetOptionTest := true
