/-
Test: Verso module docstring first after imports SHOULD pass.
Regression: `header.moduleDoc` only consulted the Markdown store
(`getMainModuleDoc`), so a Verso module doc was reported as missing.

`doc.verso` must be on before the module doc is parsed, so it is passed via
`lean-args` rather than an in-file `set_option` (which would itself be a
command before the doc and trip the placement check).
-/
-- lean-args: -D doc.verso=true -D linter.hazel.header.moduleDoc=true
module

meta import Hazel

/-!
A well-formed module docstring
under Verso, first after imports.
-/

def versoFirstTest := true
