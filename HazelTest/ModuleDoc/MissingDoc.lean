/-
Test: file with content but no module docstring SHOULD trigger warning.
Expected: "Missing module docstring" warning.
-/
module

meta import Hazel

set_option linter.hazel.header.moduleDoc true
set_option linter.unusedVariables false

def missingDocTest := 42
