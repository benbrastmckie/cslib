# Implementation Summary: Naming / Notation Uniformity Sweep

- **Task**: 544 - unify_validity_derivability_naming_notation
- **Status**: [COMPLETED]
- **Started**: 2026-07-23T00:00:00Z
- **Completed**: 2026-07-23T00:00:00Z
- **Effort**: ~4.5 hours
- **Dependencies**: None
- **Artifacts**: plans/01_naming-notation-uniformity.md, reports/01_naming-notation-uniformity-sweep.md
- **Standards**: summary-format.md, status-markers.md, artifact-management.md

## Overview

Mechanical naming/notation uniformity sweep across the four logic families under
`Cslib/Logics/{Propositional,Modal,Temporal,Bimodal}`. All six items from the research report
landed as pure renames plus one scoped-notation addition and one deprecated alias -- zero
`sorry`, zero new axioms, zero proof changes. The full 7-step CSLib CI pipeline is green.

## What Changed

- **Item 1 (Temporal validity vocabulary)**: `Valid`/`ValidSerial`/`ValidDense`/`ValidDiscrete`/
  `SemanticConsequence`/`Satisfiable`/`FormulaSatisfiable` renamed to lowercase `valid*` forms in
  `Temporal/Semantics/Validity.lean`, matching Bimodal's existing convention. Updated the
  module-header ASCII hierarchy block, reduction-lemma docstrings, and consumer references in
  `DenseSoundness.lean`, `DenseCompleteness.lean` (an additional consumer found during the
  sweep beyond the plan's file list), `Tableau/Completeness.lean`, and the one qualified
  `Temporal.Satisfiable` reference in `LTL/EmbeddingSemantics.lean`. The guarded English "Valid"
  prose at `ProofSystem/Axioms.lean:216,221` and the unrelated `ValidChronicle` structure names
  were left untouched.
- **Item 2 (turnstile notation)**: Added a `scoped` `⊨`/`Γ ⊨ φ` notation pair to
  `Temporal/Semantics/Validity.lean` and converted Bimodal's existing (previously unscoped) pair
  to `scoped` in `Bimodal/Semantics/Validity.lean`, avoiding a latent global-notation conflict.
  All 4 Bimodal code use-sites of `⊨` already had a bare `open Cslib.Logic.Bimodal` (which
  activates scoped notation too in Lean 4), so no `open scoped` additions were needed.
- **Item 4 (`NIKTheorem` → `NIKDerivable`)**: Renamed across all 15 sites in
  `Modal/Metalogic/Constructive/Labelled/{Deduction,Soundness,Completeness}.lean`.
- **Item 5 (S5 `ModalAxiom` → `S5Axiom`, Option A)**: Renamed the `abbrev` in place in
  `DerivationTree.lean` (no relocation to `Instances/S5.lean`), added a
  `@[deprecated] alias ModalAxiom := S5Axiom`, reworded the stale docstring task-number
  mentions to durable anchors, and migrated all standalone references across 14 downstream
  files (Soundness, MCS, Completeness, Systems/S5/*, InterSystem/*, Bimodal
  ModalConservativity, ProofSystem/Instances). Migration turned out to be complete: the
  deprecated alias is unused outside its own declaration.
- **Item 6 (conservativity naming)**: Standardized 17 `<sys>_conservative_extension` theorems
  (15 Modal `Systems/*/ConservativeExtension.lean` files + Bimodal + Temporal) to
  `<sys>_conservative_over_cpl`, including the bare `modal_conservative_extension` outlier in
  `Systems/K/ConservativeExtension.lean` → `k_conservative_over_cpl`. The research report's "18"
  count appears to be a minor overcount -- only 17 distinct theorem declarations exist. The
  shared `modal_conservative_extension_param` helper and the pre-existing generic
  `conservative_over_cpl` combinator (a distinct declaration in `ConservativityLift.lean`) were
  left untouched.
- **Item 3 (Algebra completeness suffix)**: Renamed the six genuine Algebra-layer completeness
  theorems (`hilbert_alg_complete`, `conjImp_brouwerian_complete`, `imp_hilbert_complete`,
  `conjImpBot_pointedBrouwerian_complete`, `conjImpBotMin_brouwerianBot_complete`,
  `brouwerianBot_complete`) to their `_completeness` forms across 18 files (wider than the
  plan's 5-file estimate, since references extend through the fragment-conservativity network).
  Rewrapped 3 docstring lines that exceeded the 100-char longLine limit due to the longer
  suffix. The `*negation_complete` property family (174 occurrences, verified unchanged),
  `propositions_complete`, and local `big_complete`/`small_complete` have-names were verified
  untouched.

## Decisions

- Notation scoping (item 2): both Temporal and Bimodal turnstile notations made `scoped`, per
  the autonomous-run directive, rather than leaving Bimodal's unscoped.
- S5 axiom relocation (item 5): Option A (in-place rename + alias) chosen over Option B
  (relocation to `Instances/S5.lean`), per the autonomous-run directive, to avoid inverting a
  dependency edge across ~13 files.
- Item 5/6 migration completeness treated as opportunistic-but-thorough: rather than stopping
  at "low-churn" sites and leaving heavy use of the deprecated alias, the full standalone
  reference set was migrated in both items since the mechanical word-boundary rename made this
  low-risk and left zero deprecation-warning residue.
- Two derived lemma names containing "ModalAxiom" as a compound substring
  (`S4Axiom_implies_ModalAxiom`, `TBAxiom_implies_ModalAxiom`) were left unrenamed (their type
  signatures now correctly read `S5Axiom`, but the lemma names themselves were judged out of
  scope for item 5, which targets the `ModalAxiom`/`S5Axiom` predicate itself, not every
  identifier that mentions it).

## Impacts

- 58 files changed (renames + one notation addition + alias), zero proof-logic changes.
- Full CSLib CI pipeline green: `lake build` (3253 jobs), `lake test` (9245 jobs),
  `lake exe checkInitImports` (clean), `lake exe lint-style` (exit 0), `lake exe mk_all --module`
  (no update necessary), `lake shake` (pre-existing baseline findings only -- none reference an
  added/removed import, since no `import` line was touched anywhere in this task).
- Downstream consumers of the renamed identifiers should use the new lowercase/`_completeness`/
  `_over_cpl`/`S5Axiom`/`NIKDerivable` forms; `ModalAxiom` remains available via the deprecated
  alias for any external code not yet migrated.

## Follow-ups

- None required for this task. Potential future work (explicitly out of scope per the plan's
  Non-Goals): renaming the Tableau-layer `_complete` theorems, renaming Propositional
  `Tautology`, relocating `S5Axiom` into `Instances/S5.lean`, and adding NOTATION.md
  documentation for the new Temporal turnstile.

## References

- specs/544_unify_validity_derivability_naming_notation/plans/01_naming-notation-uniformity.md
- specs/544_unify_validity_derivability_naming_notation/reports/01_naming-notation-uniformity-sweep.md
