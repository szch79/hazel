/-
SPDX-FileCopyrightText: 2026 Mingtong Lin
SPDX-License-Identifier: MIT
-/
module

public meta import Lean

/-!
# Shared helpers for Hazel linters
-/

meta section

open Lean

namespace Hazel.Util

/-- Find all syntax nodes in a tree matching a predicate. -/
public partial def findAll (stx : Syntax) (p : Syntax → Bool) : Array Syntax :=
  let found := if p stx then #[stx] else #[]
  match stx with
  | .node _ _ args => found ++ (args.flatMap (findAll · p))
  | _ => found

/-- Collect all import syntax nodes from a module syntax. -/
public partial def getImports (s : Syntax) : Array Syntax :=
  let rest : Array Syntax := (s.getArgs.map getImports).flatten
  if s.isOfKind `Lean.Parser.Module.import then rest.push s else rest

/-! ## Docstring span-aware iteration

Utilities for iterating over prose characters in docstrings, skipping
backtick code spans (with correct count matching), escaped characters,
and `$`/`$$` math spans.
-/

/--
Skip a backtick-delimited code span starting at index `i` (which points to the
first backtick).  Counts opening backticks and finds the matching closing
sequence.  Returns the index after the closing backticks.
-/
public def skipBacktickSpan (chars : Array Char) (i : Nat) : Nat := Id.run do
  let len := chars.size
  let mut j := i
  let mut count := 0
  while j < len && chars[j]! == '`' do
    j := j + 1
    count := count + 1
  let mut run := 0
  while j < len do
    if chars[j]! == '`' then
      run := run + 1
      if run == count then return j + 1
    else
      run := 0
    j := j + 1
  return j

/-- Skip a `$`-delimited math span starting at index `i`.  Handles both `$...$` and `$$...$$`. -/
public def skipMathSpan (chars : Array Char) (i : Nat) : Nat := Id.run do
  let len := chars.size
  let mut j := i
  let mut count := 0
  while j < len && chars[j]! == '$' do
    j := j + 1
    count := count + 1
  let mut run := 0
  while j < len do
    if chars[j]! == '$' then
      run := run + 1
      if run == count then return j + 1
    else
      run := 0
    j := j + 1
  return j

/--
Iterate over prose characters in a docstring, skipping code spans, math spans,
and escaped characters.  Calls `f` with `(index, char, chars)` for each prose
character.  Returns `some a` on the first `f` that returns `some`.
-/
public def forProse (s : String) (f : Nat → Char → Array Char → Option α) :
    Option α := Id.run do
  let chars := s.toList.toArray
  let len := chars.size
  let mut i := 0
  while i < len do
    let c := chars[i]!
    if c == '\\' then
      i := i + 2
      continue
    if c == '`' then
      i := skipBacktickSpan chars i
      continue
    if c == '$' then
      i := skipMathSpan chars i
      continue
    if let some result := f i c chars then
      return some result
    i := i + 1
  return none

/-! ## Tactic sequence helpers -/

/--
Collect tactic-level children from a tactic sequence, flattening wrapper
nodes.  The Lean parser wraps tactic sequences in several layers
(`tacticSeq` > `tacticSeq1Indented` > `null` > tactic).  This recurses
through all wrapper kinds and collects leaf tactic nodes.
-/
public partial def collectTactics (stx : Syntax) : Array Syntax :=
  let kind := stx.getKind
  if kind == ``Parser.Tactic.tacticSeq1Indented ||
     kind == ``Parser.Tactic.seq1 ||
     kind == ``Parser.Tactic.tacticSeq ||
     kind == `null then
    stx.getArgs.foldl (init := #[]) fun acc arg =>
      if arg.isAtom || arg.isMissing then acc
      else
        let sub := collectTactics arg
        if sub.isEmpty then acc.push arg else acc ++ sub
  else #[]

end Hazel.Util

end -- meta section
