/-
SPDX-FileCopyrightText: 2026 Mingtong Lin
SPDX-License-Identifier: MIT
-/
module

public meta import Hazel.Do
public meta import Hazel.DocString
public meta import Hazel.Header
public meta import Hazel.Meta
public meta import Hazel.Pedantic
public meta import Hazel.Style
public meta import Hazel.Tactic

/-!
# Hazel

A collection of configurable linters for Lean 4 projects.  Import `Hazel`
and enable the set via `linter.hazel` or toggle individual options.
-/

meta section

open Lean Linter

register_linter_set linter.hazel :=
  -- Header
  linter.hazel.header.copyright
  linter.hazel.header.moduleDoc
  linter.hazel.header.duplicateImports
  linter.hazel.header.sortedImports
  linter.hazel.header.importGroupOrder
  linter.hazel.header.importGroupContiguity
  linter.hazel.header.noImportAll
  linter.hazel.header.noBroadImport
  -- Style
  linter.hazel.style.varNaming
  linter.hazel.style.paramNaming
  linter.hazel.style.preferDotNotation
  linter.hazel.style.preferNotation
  linter.hazel.style.inlineBy
  linter.hazel.style.inlineDo
  linter.hazel.style.sectionNoIndent
  linter.hazel.style.keywordAlign.deriving
  linter.hazel.style.keywordAlign.terminationBy
  linter.hazel.style.keywordAlign.decreasingBy
  linter.hazel.style.keywordAlign.where
  linter.hazel.style.numericProj
  linter.hazel.style.byIndent
  linter.hazel.style.preferBinder
  linter.hazel.style.redundantImplicit
  linter.hazel.style.paramOrder
  linter.hazel.style.bundleParams
  -- DocString
  linter.hazel.docstring.doubleSpace
  linter.hazel.docstring.noUnicodeProse
  linter.hazel.docstring.capitalStart
  linter.hazel.docstring.multilineFormat
  linter.hazel.docstring.collapsible
  linter.hazel.docstring.missingDocstring
  -- Tactic
  linter.hazel.tactic.preferSimpA
  linter.hazel.tactic.preferRwA
  linter.hazel.tactic.preferRfl
  linter.hazel.tactic.preferConstructor
  linter.hazel.tactic.preferRintro
  linter.hazel.tactic.haveObtain
  linter.hazel.tactic.noErw
  linter.hazel.tactic.noIntros
  linter.hazel.tactic.redundantSimpArg
  linter.hazel.tactic.preferExact
  linter.hazel.tactic.preferAssumption
  linter.hazel.tactic.inlineShow
  -- Meta
  linter.hazel.meta.noStringElaboration
  linter.hazel.meta.requireSuppressionComment
  -- Do
  linter.hazel.do.strongPostCond

  -- Pedantic (not included by default)
  -- linter.hazel.pedantic.noVariable (too opinionated)

end -- meta section
