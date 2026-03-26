/-
Tests for header linters.

NOTE: Header linters inspect the file's own header at parse time, so we
cannot use `#guard_msgs` to test copyright/moduleDoc/duplicateImports
directly.  We verify the options exist and don't error.
-/
module

meta import Hazel

set_option linter.unusedVariables false

/-! # noImportAll -/

section noImportAll
set_option linter.hazel.header.noImportAll true

#guard_msgs in
def header_pass_no_import_all := true

end noImportAll

/-! # noBroadImport -/

section noBroadImport
set_option linter.hazel.header.noBroadImport true

#guard_msgs in
def header_pass_no_broad_import := true

end noBroadImport
