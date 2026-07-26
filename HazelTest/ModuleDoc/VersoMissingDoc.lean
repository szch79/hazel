/-
Test: no module docstring with `doc.verso` on SHOULD still trigger the
missing-docstring warning (both format stores are empty).
-/
-- lean-args: -D doc.verso=true -D linter.hazel.header.moduleDoc=true
module

meta import Hazel

def versoMissingDocTest := 42
