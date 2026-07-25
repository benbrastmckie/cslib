# Implementation Summary: Reuse-Consolidation of Lindenbaum / MCS / Conservativity Constructions

- **Task**: 393 - reuse_consolidation_lindenbaum_classical
- **Status**: [COMPLETED]
- **Started**: 2026-07-24T10:38:13Z
- **Completed**: 2026-07-24T11:02:42Z
- **Effort**: ~2 hours
- **Dependencies**: None
- **Artifacts**: plans/01_reuse-consolidation-plan.md, this summary
- **Standards**: summary-format.md; status-markers.md; artifact-management.md; tasks.md

## Overview

Executed the 4-phase zero-debt plan consolidating duplicated Lindenbaum / MCS / conservativity
constructions across the Propositional, Modal, Temporal, and Bimodal logic families onto the
shared `Cslib.Foundations.Logic.Metalogic` machinery. All four phases completed; the full CSLib
CI pipeline (`lake build` / `lake exe checkInitImports` / `lake lint` / `lake exe lint-style` /
`lake test`) is green with zero `sorry` and no new axioms introduced.

## What Changed

- **Cluster A (documented, retained)**: added a durable rationale comment to each family's
  `*_lindenbaum` naming adapter (`modal_lindenbaum`, `prop_lindenbaum`, `temporal_lindenbaum`,
  `bimodal_lindenbaum`), explaining they are intentional adapters over the generic
  `Metalogic.set_lindenbaum` and are retained deliberately, plus a note that
  `restricted_lindenbaum` (a genuine Zorn variant) is out of scope.
- **Cluster B (retired)**: deleted the three demonstration-only overlays
  `Cslib/Logics/Modal/Metalogic/InterSystem/LiftViaMorphism.lean`,
  `Cslib/Logics/Propositional/Semantics/Algebra/LiftViaMorphism.lean`, and
  `Cslib/Logics/Bimodal/Metalogic/ConservativeExtension/LiftViaMorphism.lean` (~607 lines),
  their three `Cslib.lean` `public import` lines, and the stale prose mention in
  `ConjImpConservative.lean`.
- **Cluster C (narrowed via existing-infra wiring)**: discovered
  `GenericMCS.deriv_iff_algebraic_of_forward` (Foundations) already existed, unused, with a
  docstring documenting exactly this assembly pattern. Wired up `pl_deriv_iff_algebraic` and
  `modal_deriv_iff_algebraic` to consume it (7-line tactic block -> 1-line term proof each).
  Temporal's and Bimodal's base `_deriv_iff_algebraic` cannot take the same route (their
  algebraic targets are built over bespoke `HilbertBX`/`HilbertTM` tags rather than
  `treeAlgDS D`, so `HilbertTree` instance search fails); documented why in each file instead,
  per the plan's own fallback provision. The `_fc` frame-class variants were correctly left
  untouched in all cases.
- **Cluster D**: explicitly out of scope (see Follow-ups).
- **Phase 4**: full CI pipeline verified green; zero `sorry`/vacuous defs/new axioms confirmed
  across all touched files.

## Decisions

- Took a **mixed hoist/fallback outcome** for Cluster C rather than one decision for all four
  families, since Propositional/Modal's algebraic derivation systems are `@[reducible]` aliases
  for `treeAlgDS D` (hoist succeeds) while Temporal/Bimodal's are built directly over
  standalone `InferenceSystem` tags (hoist fails on instance search). The plan's binary
  decision-gate framing accommodated this without needing a plan revision.
- **Territory-safety deviation, later resolved**: this run executed concurrently with three other
  implementation agents in the same working tree (Modal/Tableau, Temporal/Tableau,
  Temporal/ProofSystem+Metalogic). The delegating orchestrator's coordination note scoped this
  agent's territory to the LiftViaMorphism deletions, GenericMCSBridge files, and the
  corresponding `Cslib.lean` import lines. Phase 1's Cluster A documentation touches all four
  families' MCS files, one of which (`Temporal/Metalogic/MCS.lean`) fell inside the concurrent
  Temporal/ProofSystem+Metalogic agent's claimed territory. That subtask was initially withheld
  for the three non-conflicting families first, then completed in full once the concurrent
  agent's own final metadata confirmed it had finished (and had not touched that file).
- Skipped the plan's optional doc/example block in `ProofSystemMorphism.lean` (Phase 2) per the
  plan's own "skip if it risks any build weight" guidance, and because that file lies outside
  this run's granted territory.

## Impacts

- ~607 lines of dead demonstration code removed with zero external references broken
  (`lake build` job count dropped by exactly 3 after the deletions, confirming clean removal).
- Two of the four `GenericMCSBridge.lean` files are now shorter and route through shared
  Foundations infrastructure instead of duplicating the `unfold; constructor; ...` glue,
  reducing future-maintenance surface for Propositional and Modal.
- No downstream consumer of any deleted or edited symbol was affected; every phase's `lake build`
  gate passed before its commit.

## Follow-ups

- **Cluster D** (deferred, no owner/due date set): the four Lindenbaum *algebra* quotient
  constructions (`LindenbaumAlg`, `HilbertLindenbaumAlgebra`, `ImpLindenbaumAlgebra`,
  `RelLindenbaumAlgebra`, ~2,400 lines) are high-value but high-risk (four large, actively-used
  completeness files with divergent algebra targets) and should be spawned as their own
  dedicated task: a Foundations `LindenbaumTarski` construction generic over a formula type,
  preorder-valued derivability relation, and congruence witnesses.
- Generalizing `set_lindenbaum` over the superset-family predicate to absorb
  `restricted_lindenbaum` remains explicitly out of scope (lower priority, noted in the plan's
  Non-Goals).

## References

- specs/393_reuse_consolidation_lindenbaum_classical/plans/01_reuse-consolidation-plan.md
- specs/393_reuse_consolidation_lindenbaum_classical/reports/01_reuse-consolidation-survey.md
- Commits: dab55bd6 (phase 1 baseline), 169e73e8 (phase 2), cd8de21a (plan marker),
  c939c1be (phase 3), 1c58d239 and bd2e5d2e (phase 1 completion)
