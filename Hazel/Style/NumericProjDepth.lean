/-
SPDX-FileCopyrightText: 2026 Mingtong Lin
SPDX-License-Identifier: MIT
-/
module

public meta import Lean
public meta import Lean.Linter
public meta import Hazel.Util

/-!
# Numeric projection depth linter

Flags chains of numeric projections (`.1.2.1`) that exceed a configurable
depth.  Long numeric chains are unreadable; prefer named field access
(`.fst`, `.snd`, etc.) or destructuring (`let ⟨a, b, c⟩ := x`).

Named projections (`.fst`, `.foo`) do not count and reset the chain.
-/

meta section

open Lean Elab Command Linter Hazel.Util

/-- Enable the numeric projection depth linter.  Included in `linter.hazel`. -/
public register_option linter.hazel.style.numericProj : Bool := {
  defValue := false
  descr := "enable numeric projection depth linter"
}

/-- Max depth of consecutive numeric projections (default 2). -/
public register_option linter.hazel.style.numericProjDepth : Nat := {
  defValue := 2
  descr := "max depth of consecutive numeric projections"
}

namespace Hazel.Style.NumericProjDepth

/-- Check if a `Term.proj` node uses a numeric field index (`.1`, `.2`). -/
private def isNumericProj (stx : Syntax) : Bool :=
  stx.isOfKind ``Parser.Term.proj &&
  stx.getNumArgs >= 3 &&
  stx[2].isOfKind `fieldIdx

/--
Count the depth of consecutive numeric projections starting from `stx`.
Recurses into child `[0]` (the base expression) as long as it's also
a numeric projection.
-/
private def numericProjDepth (stx : Syntax) : Nat := Id.run do
  let mut depth := 0
  let mut cur := stx
  while isNumericProj cur do
    depth := depth + 1
    cur := cur[0]
  return depth

/--
Check if this numeric proj node is a child of another numeric proj in the
same chain.  If so, it's an inner node and should not be flagged separately
(the outermost node will be flagged instead).

Works by checking: is `stx` the `[0]` child (base) of any other numeric
proj?  We use tail position to distinguish — if any outer proj ends after
this one, this one is inner.
-/
private def isInnerNumericProj (stx : Syntax) (allProjs : Array Syntax) : Bool :=
  allProjs.any fun other =>
    isNumericProj other &&
    -- `other` is a strictly larger proj containing `stx`: same start, later end
    other.getPos? == stx.getPos? &&
    match (other.getTailPos?, stx.getTailPos?) with
    | (some otherEnd, some thisEnd) => otherEnd > thisEnd
    | _ => false

/-- The numeric projection depth linter. -/
def numericProjDepthLinter : Lean.Linter where run := withSetOptionIn fun stx => do
  unless getLinterValue linter.hazel.style.numericProj (← getLinterOptions) do return
  let maxDepth := linter.hazel.style.numericProjDepth.get (← getOptions)
  if (← MonadState.get).messages.hasErrors then return
  -- Find all Term.proj nodes with numeric field index
  let projs := findAll stx fun s => isNumericProj s
  for proj in projs do
    -- Only flag the outermost in each chain
    if isInnerNumericProj proj projs then continue
    let depth := numericProjDepth proj
    if depth > maxDepth then
      -- Build the chain string for the message (e.g., ".1.2.1")
      let chain := Id.run do
        let mut s := ""
        let mut cur := proj
        while isNumericProj cur do
          -- Use the atom value directly, not reprint (which includes trivia)
          let idx := match cur[2] with
            | .atom _ val => val
            | .node _ _ #[.atom _ val] => val
            | _ => "?"
          s := s!".{idx}{s}"
          cur := cur[0]
        return s
      Linter.logLint linter.hazel.style.numericProj proj
        m!"Numeric projection chain `{chain}` is {depth} deep (max {maxDepth}).  \
           Use named field access or destructuring instead."

initialize addLinter numericProjDepthLinter

end Hazel.Style.NumericProjDepth

end -- meta section
