/-
Test: re-export file.  When moduleDoc is enabled project-wide, this file
should NOT trigger a warning because it only contains imports.  Since we
cannot set linter options before imports in a test file, this test only
verifies the file compiles.  The actual re-export skip is validated by
building kclib (which sets the option in its lakefile).
-/
module

meta import Hazel
import Init.Data.List.Basic
import Init.Data.Array.Basic
