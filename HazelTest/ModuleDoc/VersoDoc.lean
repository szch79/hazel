/-
Test: docstring linters under `doc.verso`.

Verso module docs cannot be tested in `HazelTest/DocString.lean` because a
file cannot mix Verso-format and Markdown-format module docs.  The
closing-delimiter warning also lives here: its text contains an unbalanced
closer, so it cannot appear inside a `#guard_msgs` docstring.
-/
module

meta import Hazel

set_option doc.verso true
set_option linter.hazel.docstring.multilineFormat true
set_option linter.hazel.docstring.capitalStart true
set_option linter.hazel.docstring.doubleSpace true
set_option linter.hazel.docstring.noUnicodeProse true

/-!
A well-formed module docstring spanning
multiple lines under Verso.
-/

-- Text precedes the closer: multilineFormat warning.
/--
Text precedes
the closer. -/
def versoBadCloser := true

-- Lowercase module doc: capitalStart warning.
/-! lowercase module doc. -/

-- Single space after sentence in module doc: doubleSpace warning.
/-! First sentence. Second sentence. -/

-- Unicode in module doc prose: noUnicodeProse warning.
/-! The formula φ appears in module prose. -/

-- URL in module doc prose: sentence punctuation adjacent to a URL is part
-- of the URL span, so no doubleSpace warning.
/-! See https://example.com/spec. Section two has details. -/
