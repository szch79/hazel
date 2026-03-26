# Hazel

A configurable linter library for Lean 4 projects.

## Quick Start

Add Hazel as a dependency:

```lean
-- lakefile.lean
require hazel from git "https://github.com/szch79/hazel.git" @ "main"
```

Import and enable the full set:

```lean
-- lakefile.lean
package myProject where
  leanOptions := #[
    ⟨`linter.hazel, true⟩
  ]
```

```lean
-- MyProject/Init.lean
meta import Hazel
```

Override individual rules in the lakefile or per-file:

```lean
-- Disable one rule project-wide
⟨`linter.hazel.style.preferBinder, false⟩

-- Disable per-declaration
set_option linter.hazel.tactic.preferRfl false in
theorem foo : ...
```

## Categories

### Header

Checks on file-level structure: copyright headers, module docstrings, and
import organization.

#### `linter.hazel.header.copyright`

Checks that a block comment exists before the `module` keyword.  The
content check is configurable via `IO.Ref`:

```lean
-- Default: just checks a /- ... -/ block exists.
-- Override in your Init.lean:
meta initialize Hazel.Header.Copyright.copyrightCheckRef.set fun lead =>
  (lead.splitOn "SPDX-License-Identifier:").length > 1
```

#### `linter.hazel.header.moduleDoc`

Every file must have a `/-! ... -/` module docstring after imports.

```lean
-- Bad: no module docstring
module
import Lean

def foo := 1

-- Good
module
import Lean

/-! # My Module -/

def foo := 1
```

#### `linter.hazel.header.duplicateImports`

Flags identical import statements.

```lean
-- Bad
import Lean
import Lean

-- Good
import Lean
```

#### `linter.hazel.header.sortedImports`

Imports must be sorted alphabetically within each modifier group
(`public meta`, `public`, `meta`, plain).  Provides a clickable
"Sort imports" code action.

```lean
-- Bad
import Lean.Elab
import Lean.Data

-- Good
import Lean.Data
import Lean.Elab
```

#### `linter.hazel.header.importGroupOrder`

Public imports must come before private imports.  The expected order is:
`public meta` > `public` > `meta` > plain.

```lean
-- Bad
import Lean.Data
public import Lean.Elab

-- Good
public import Lean.Elab
import Lean.Data
```

#### `linter.hazel.header.importGroupContiguity`

Imports of the same modifier group must be contiguous (not interleaved
with other groups).

```lean
-- Bad
public import A
import B
public import C

-- Good
public import A
public import C
import B
```

#### `linter.hazel.header.noImportAll`

Flags `import all` statements.

```lean
-- Bad
import all Lean

-- Good
import Lean.Elab.Command
```

#### `linter.hazel.header.noBroadImport`

Flags imports of broad top-level aggregator modules.  Configurable via
`IO.Ref`:

```lean
-- Default: flags `import Std`
-- Override:
meta initialize Hazel.Header.ImportRestrict.broadImportCheckRef.set
  fun name => name == `Std || name == `Mathlib
```

---

### Style

Formatting, naming, and syntactic preferences.

#### `linter.hazel.style.varNaming`

Type-based variable naming conventions.  Register rules via the
`@[suggested_var_names]` attribute:

```lean
@[suggested_var_names "l"]
abbrev MyList := List Nat

-- Bad: x doesn't start with l
def head (x : MyList) : Nat := x.head!

-- Good
def head (l : MyList) : Nat := l.head!
```

For type expressions without a named alias, use the `suggest_var_names`
command:

```lean
suggest_var_names "f" "g" "h" for Nat → Bool
```

`suggest_var_names` can match types structurally, and we can use `_` as a wildcard to match any argument:

```lean
-- Match MyState applied to any argument
suggest_var_names "s" for MyState _

-- Match MyState applied to a specific argument
suggest_var_names "s" for MyState Nat

-- Nested wildcards
suggest_var_names "w" for Wrapper _
```

#### `linter.hazel.style.paramNaming`

Naming rules for typeclass parameters.  Register via
`@[suggested_param_names]`:

```lean
@[suggested_param_names (α "l")]
class Container (α : Type) where
  size : α → Nat

-- Bad: x doesn't start with l
theorem foo [Container X] (x : X) : ...

-- Good
theorem foo [Container α] (l : α) : ...
```

#### `linter.hazel.style.preferDotNotation`

Flags explicit namespace-qualified calls that could use dot notation.
Provides a clickable "Try this" code action.

```lean
-- Bad
def foo (l : List Nat) : Nat := List.length l

-- Good
def foo (l : List Nat) : Nat := l.length
```

#### `linter.hazel.style.preferNotation`

Flags explicit function calls when a registered notation exists.  Works
with any syntax that has a delaborator.

```lean
-- Bad
def foo (p : Prop) : Prop := Not p

-- Good
def foo (p : Prop) : Prop := ¬p
```

Other examples: `HAdd.hAdd a b` (suggest `a + b`), `And p q` (suggest
`p ∧ q`), `Prod.mk a b` (suggest `(a, b)`), etc.

#### `linter.hazel.style.inlineBy`

`by` must appear on the same line as `:=`.

```lean
-- Bad
theorem foo : True :=
  by trivial

-- Good
theorem foo : True := by
  trivial
```

#### `linter.hazel.style.inlineDo`

`do` must appear on the same line as `:=`.

```lean
-- Bad
def main : IO Unit :=
  do pure ()

-- Good
def main : IO Unit := do
  pure ()
```

#### `linter.hazel.style.sectionNoIndent`

Content inside `section`/`namespace` must not be indented relative to the
`section`/`namespace` keyword.

```lean
-- Bad
section
  def foo := 1

-- Good
section
def foo := 1
```

#### `linter.hazel.style.keywordAlign.deriving`
#### `linter.hazel.style.keywordAlign.terminationBy`
#### `linter.hazel.style.keywordAlign.decreasingBy`
#### `linter.hazel.style.keywordAlign.where`

These keywords must align with their parent declaration.

```lean
-- Bad
inductive MyBool where
  | t | f
  deriving Repr

-- Good
inductive MyBool where
  | t | f
deriving Repr
```

#### `linter.hazel.style.numericProj` / `numericProjDepth`

Flags long chains of numeric projections (`.1.2.1`).  The `numericProj`
Bool enables the check; `numericProjDepth` (default 2) sets the maximum
allowed depth.

```lean
-- OK (depth 2)
def foo (x : Nat × (Nat × Nat)) : Nat := x.2.1

-- Bad (depth 3)
def bar (x : Nat × (Nat × (Nat × Nat))) : Nat := x.2.2.1
```

Named projections (`.fst`, `.snd`) are not counted.

#### `linter.hazel.style.byIndent`

Tactic body after a top-level `:= by` must be indented exactly 2 spaces
from the declaration keyword's column.  Only checks the outermost `by` in
each declaration — nested `by` blocks (inside `have`, `fun`, `show`, etc.)
are not checked.

```lean
-- Bad: 4-space indent from theorem
theorem foo : True := by
    trivial

-- Good: 2-space indent from theorem
theorem foo : True := by
  trivial
```

#### `linter.hazel.style.preferBinder`

Prop-valued arrow domains in type signatures should be explicit binder
arguments.

```lean
-- Bad
theorem foo : P → Q → P := fun h _ => h

-- Good
theorem foo (h : P) (_ : Q) : P := h
```

Only flags `Prop`-typed domains.  `Type`-typed arrows (e.g., `∀ α, ...`)
are not flagged.

#### `linter.hazel.style.redundantImplicit` / `redundantImplicitLevel`

When `autoImplicit` is on, flags explicit implicit binders that auto-implicit
would introduce automatically.  The `redundantImplicitLevel` option (default
1) controls the scope:

- **Level 1**: only flag `Sort`/`Type` binders (`{α : Type}`).  Warns that
  removing may widen the universe level.
- **Level 2**: flag all implicit binders (`{n : Nat}`, `{l : List α}`,
  etc.).  For non-Sort binders, auto-implicit infers the exact same type
  from usage — no semantic change.

```lean
-- Level 1 flags this (Sort binder):
theorem foo {α : Type} (x : α) : α := x

-- Level 2 additionally flags this (non-Sort binder):
theorem bar {n : Nat} (h : n > 0) : n ≥ 1 := h

-- Good (both levels):
theorem foo (x : α) : α := x
theorem bar (h : n > 0) : n ≥ 1 := h
```

To enable level 2 in the lakefile:

```lean
⟨`linter.hazel.style.redundantImplicitLevel, .ofNat 2⟩
```

#### `linter.hazel.style.paramOrder`

Binder declaration order should match first-use order in the type
signature.  Binders should be declared close to where they are used.

```lean
-- Bad: α is used only at binder 3, β at binder 2
def foo {α : Type} {β : Type} (g : β → Nat) (f : α → Nat) : Nat := g 0 + f 0

-- Good: β first (used at binder 2), then α (used at binder 3)
def foo {β : Type} {α : Type} (g : β → Nat) (f : α → Nat) : Nat := g 0 + f 0
```

Type/Sort binders that are first used in the same later binder are not
reordered relative to each other (e.g., `{α} {β}` when both appear in
`f : β → α`).

#### `linter.hazel.style.bundleParams`

Adjacent binders with the same type and binder kind should be bundled into
a single multi-name binder.

```lean
-- Bad
theorem foo {a : Nat} {b : Nat} (h : a = b) : b = a := h.symm

-- Good
theorem foo {a b : Nat} (h : a = b) : b = a := h.symm
```

Does not flag instance binders, binders with default values, or binders
with different types or binder kinds.

---

### DocString

Checks on documentation comments (`/-- ... -/` and `/-! ... -/`).

#### `linter.hazel.docstring.doubleSpace`

Sentences must be followed by two spaces in docstrings.

```lean
-- Bad
/-- Returns the size. This includes tombstoned entries. -/

-- Good
/-- Returns the size.  This includes tombstoned entries. -/
```

#### `linter.hazel.docstring.noUnicodeProse`

Non-ASCII characters in docstring prose are flagged.  Unicode inside
backtick code spans (`` `...` ``), double backtick spans, triple backtick
fenced blocks, and `$...$` math spans is allowed.

```lean
-- Bad
/-- The type α represents a variable. -/

-- Good
/-- The type `α` represents a variable. -/
```

To allow specific Unicode characters (e.g., em-dash) in prose:

```lean
-- In your Init.lean
meta initialize Hazel.DocString.Prose.allowedUnicodeRef.modify (· ++ #['—', '–', '…'])
```

#### `linter.hazel.docstring.capitalStart`

Docstrings must start with an uppercase letter, a backtick, or `#`
(for markdown headers like `# Section`).

```lean
-- Bad
/-- returns the length. -/

-- Good
/-- Returns the length. -/
/-- `List.length` returns the length. -/
/-- # Overview -/
```

#### `linter.hazel.docstring.multilineFormat`

Multi-line docstrings must have opening and closing delimiters on their own
lines.

```lean
-- Bad
/-- Returns the size.
This includes tombstoned entries. -/

-- Good
/--
Returns the size.  This includes tombstoned entries.
-/
```

#### `linter.hazel.docstring.collapsible`

Single-line docstring content should not be split across three lines.

```lean
-- Bad
/--
Returns the length.
-/

-- Good
/-- Returns the length. -/
```

#### `linter.hazel.docstring.missingDocstring`

Public `def`, `theorem`, `class`, `structure`, and `inductive` declarations
must have a docstring.

---

### Tactic

Checks on tactic proof style.

#### `linter.hazel.tactic.preferSimpA`

`simp [...]; assumption` should be `simpa [...]`.

```lean
-- Bad
example (h : a = b) (h2 : b = 0) : a = 0 := by
  simp [h]; assumption

-- Good
example (h : a = b) (h2 : b = 0) : a = 0 := by
  simpa [h]
```

#### `linter.hazel.tactic.preferRwA`

`rw [...]; assumption` should be `rwa [...]`.

```lean
-- Bad
example (h : a = b) (h2 : b = 0) : a = 0 := by
  rw [h]; assumption

-- Good
example (h : a = b) (h2 : b = 0) : a = 0 := by
  rwa [h]
```

#### `linter.hazel.tactic.preferRfl`

`simp` on a goal that is already definitionally equal (provable by `rfl`)
should use `rfl` instead.  Uses reducible transparency to avoid false
positives on goals that require unfolding.

```lean
-- Bad
theorem foo (n : Nat) : n + 0 = n := by simp

-- Good
theorem foo (n : Nat) : n + 0 = n := by rfl
```

#### `linter.hazel.tactic.preferConstructor`

`constructor` followed by `exact` on every subgoal should use anonymous
constructor syntax.

```lean
-- Bad
example (h : P) (h2 : Q) : P ∧ Q := by
  constructor
  · exact h
  · exact h2

-- Good
example (h : P) (h2 : Q) : P ∧ Q := by
  exact ⟨h, h2⟩
```

#### `linter.hazel.tactic.preferRintro`

`intro x; rcases x with ⟨a, b⟩` should be `rintro ⟨a, b⟩`.

```lean
-- Bad
example : (P ∧ Q) → P := by
  intro h
  rcases h with ⟨hp, _⟩
  exact hp

-- Good
example : (P ∧ Q) → P := by
  rintro ⟨hp, _⟩
  exact hp
```

#### `linter.hazel.tactic.haveObtain`

`have ⟨...⟩` for destructuring should use `obtain ⟨...⟩` instead.

```lean
-- Bad
example (h : ∃ n, n > 0) : True := by
  have ⟨_, _⟩ := h
  trivial

-- Good
example (h : ∃ n, n > 0) : True := by
  obtain ⟨_, _⟩ := h
  trivial
```

Non-destructuring `have` (without angle brackets) is not flagged.

#### `linter.hazel.tactic.noErw`

Flags uses of `erw`.  Extended rewrite uses weaker definitional equality
and usually indicates a missing lemma.

#### `linter.hazel.tactic.noIntros`

Flags `intros` with named arguments.  Use `intro` instead.  Bare `intros`
(without arguments) is not flagged.

```lean
-- Bad
example : P → Q → P := by intros h _; exact h

-- Good
example : P → Q → P := by intro h _; exact h
```

#### `linter.hazel.tactic.redundantSimpArg`

Flags `simp [foo]` arguments that are already in the default `@[simp]` set.
`simp only` is not flagged — it is a deliberate choice for controlled
simplification, and plain `simp` may over-simplify and break the proof.

```lean
@[simp] theorem foo_eq : foo = bar := ...

-- Bad: foo_eq is already @[simp]
example : foo = bar := by simp [foo_eq]

-- Good
example : foo = bar := by simp

-- OK: simp only is intentional (controlled simplification)
example : foo = bar := by simp only [foo_eq]
```

#### `linter.hazel.tactic.preferExact`

Flags `apply` or `refine` that closes the goal completely (zero remaining
subgoals).  Use `exact` instead.

#### `linter.hazel.tactic.preferAssumption`

Flags `exact h` where `h` is a local hypothesis.  Use `assumption`
instead for robustness against renaming.

#### `linter.hazel.tactic.inlineShow`

Flags multi-line inline `show` proofs inside `rw [...]`, `simp [...]`,
etc.  Suggest extracting to `have` for readability.

```lean
-- Bad
rw [show a = b from by
  simp [some_long_lemma]]

-- Good
have h : a = b := by simp [some_long_lemma]
rw [h]
```

Single-line inline `show` (e.g., `rw [show a = b from rfl]`) is not
flagged.

---

### Meta

Checks on metaprogramming hygiene.

#### `linter.hazel.meta.noStringElaboration`

Flags known string-to-syntax anti-patterns in metaprogramming: calls to
`Lean.Parser.runParserCategory` or `Lean.Elab.Term.elabTermStr`.  Use
quasiquotations (`` `(...) ``) instead of constructing Lean code as
strings.

#### `linter.hazel.meta.requireSuppressionComment`

When disabling a hazel linter via `set_option`, a `--` comment explaining
the reason is required.  Following the conventions of ESLint and Clippy,
every suppression should document the rationale.

```lean
-- Bad: suppression without comment
set_option linter.hazel.style.preferDotNotation false

-- Good: inline comment
set_option linter.hazel.style.preferDotNotation false -- generated code

-- Good: comment on the line above
-- Dot notation breaks due to coercion
set_option linter.hazel.style.preferDotNotation false
```

Works for both file-wide `set_option` and scoped `set_option ... in`.
Only checks options under `linter.hazel.*` set to `false` or `0`.

---

### Do

Checks related to the `mvcgen` verification framework.

#### `linter.hazel.do.strongPostCond`

Flags `@[spec]` lemmas where the postcondition is a specific proposition
rather than a universally quantified `Q`.  Only active when
`Std.Do.Triple` is in the environment (i.e., the `mvcgen` framework is
imported).

---

### Pedantic

Opinionated rules not included in the default set.

#### `linter.hazel.pedantic.noVariable`

Flags `variable` commands.  The rationale: every declaration should have a
self-contained signature.  Enable explicitly if desired:

```lean
⟨`linter.hazel.pedantic.noVariable, true⟩
```

---

## Configuration

### Full set

Enable all default linters at once:

```lean
⟨`linter.hazel, true⟩
```

This enables all linters listed above except `noVariable`.

### Individual overrides

```lean
package myProject where
  leanOptions := #[
    ⟨`linter.hazel, true⟩,
    -- Disable specific rules
    ⟨`linter.hazel.style.preferBinder, false⟩,
    ⟨`linter.hazel.tactic.preferAssumption, false⟩,
    -- Adjust numeric projection depth
    ⟨`linter.hazel.style.numericProjDepth, .ofNat 3⟩,
  ]
```

### Per-file / per-declaration

```lean
-- Disable for an entire file
set_option linter.hazel.style.preferDotNotation false

-- Disable for one declaration
set_option linter.hazel.tactic.noErw false in
theorem foo : ... := by erw [h]
```

### Custom copyright check

```lean
-- In your Init.lean:
meta initialize Hazel.Header.Copyright.copyrightCheckRef.set fun lead =>
  (lead.splitOn "SPDX-License-Identifier:").length > 1
```

### Variable naming rules

Register via attributes on type definitions:

```lean
@[suggested_var_names "l"]
abbrev MyList := List Nat

@[suggested_param_names (α "l" "l'")]
class Container (α : Type) where
  size : α → Nat

suggest_var_names "f" "g" "h" for Nat → Bool
```

### Broad import restrictions

```lean
meta initialize Hazel.Header.ImportRestrict.broadImportCheckRef.set
  fun name => name == `Std || name == `Mathlib
```

## Compatibility

Hazel has no external dependencies beyond Lean's core library.  It works
with any Lean 4 project regardless of whether Mathlib is used.

## License

MIT
