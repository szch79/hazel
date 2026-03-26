/-
SPDX-FileCopyrightText: 2026 Mingtong Lin
SPDX-License-Identifier: MIT
-/
import Lean

/-!
# Header-fixture test driver

Walks header-level fixture files under `HazelTest/ImportOrder/` and
`HazelTest/ModuleDoc/`, runs each through the `lean` binary, and diffs
captured diagnostics against a sibling `.expected.out` file.  Fixtures
here cannot use `#guard_msgs` because their warnings fire on the file's
import header, before any command runs.

Mirrors the Lean stdlib `tests/lean/test_single.sh` pattern, adapted to
run as a `lake_exe` test driver.

Usage:
- `lake test`                   — diff mode; nonzero exit on any mismatch
- `lake exe hazelTest --update` — rewrite `.expected.out` files from current output
-/

open Lean

namespace HazelTest.Driver

/-- One fixture: source file, sibling expected-output file, derived module name. -/
structure Fixture where
  src      : System.FilePath
  expected : System.FilePath
  modName  : Name
  deriving Inhabited

/-- Convert a path like `HazelTest/ImportOrder/Foo.lean` to module name `HazelTest.ImportOrder.Foo`. -/
def pathToModName (path : System.FilePath) : Name := Id.run do
  let s := (path.toString.dropEnd ".lean".length).toString
  let parts := s.splitOn "/"
  parts.foldl (fun acc p => Name.mkStr acc p) Name.anonymous

/-- Recursively collect `.lean` files under a directory. -/
partial def collectLean (root : System.FilePath) : IO (Array System.FilePath) := do
  let mut out := #[]
  if !(← root.isDir) then return out
  for entry in (← root.readDir) do
    let p := entry.path
    if ← p.isDir then
      out := out ++ (← collectLean p)
    else if p.extension == some "lean" then
      out := out.push p
  return out

/-- Discover all fixtures under the header-fixture roots. -/
def discover : IO (Array Fixture) := do
  let mut out := #[]
  for dir in #["HazelTest/ImportOrder", "HazelTest/ModuleDoc"] do
    for src in (← collectLean dir) do
      out := out.push {
        src,
        expected := src.withExtension "expected.out",
        modName := pathToModName src
      }
  -- Stable order for deterministic diffs.
  return out.qsort (fun a b => a.src.toString < b.src.toString)

/-- Run one fixture through the `lean` binary and capture its diagnostics.

Mirrors the Lean stdlib `tests/lean/test_single.sh` pattern.  We spawn
`lean` as a subprocess (rather than calling `Lean.Elab.runFrontend`
in-process) because module-system files (`module` + `meta import`) need a
populated `ModuleSetup.importArts`, which the `lean` shell builds from
its `--setup` flag but third-party callers can't easily reconstruct. -/
def runFixture (f : Fixture) : IO String := do
  let out ← IO.Process.output {
    cmd := "lean", args := #["--", f.src.toString]
  }
  return out.stdout ++ out.stderr

/-- Read an expected-output file, or return empty if missing. -/
def readExpected (path : System.FilePath) : IO String := do
  if ← path.pathExists then IO.FS.readFile path else pure ""

/-- Diff actual vs expected; return true on match. -/
def passes (actual expected : String) : Bool := actual == expected

end HazelTest.Driver

open HazelTest.Driver in
def main (args : List String) : IO UInt32 := do
  let update := args.contains "--update"
  let fixtures ← discover
  if fixtures.isEmpty then
    IO.eprintln "hazel-test: no fixtures found (run from the hazel/ package root)"
    return 1
  let mut failed : Nat := 0
  let mut updated : Nat := 0
  for f in fixtures do
    let actual ← runFixture f
    let expected ← readExpected f.expected
    if passes actual expected then
      continue
    if update then
      IO.FS.writeFile f.expected actual
      IO.println s!"updated {f.expected}"
      updated := updated + 1
    else
      failed := failed + 1
      IO.eprintln s!"FAIL {f.src}"
      IO.eprintln "--- expected"
      IO.eprint expected
      IO.eprintln "--- actual"
      IO.eprint actual
      IO.eprintln "---"
  if update then
    IO.println s!"hazel-test: updated {updated} / {fixtures.size} fixture(s)"
    return 0
  if failed == 0 then
    IO.println s!"hazel-test: {fixtures.size} fixture(s) passed"
    return 0
  else
    IO.eprintln s!"hazel-test: {failed} / {fixtures.size} fixture(s) failed"
    return 1
