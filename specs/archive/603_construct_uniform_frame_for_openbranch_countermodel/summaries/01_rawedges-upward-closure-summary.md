# Implementation Summary: Uniform frame for `openBranch_countermodel` conjunct 1

- **Task**: 603 - Construct a uniform frame for openBranch_countermodel and discharge the upward-closure conjunct
- **Status**: [COMPLETED]
- **Started**: 2026-08-09T21:13:43Z
- **Completed**: 2026-08-09T21:36:27Z
- **Effort**: ~2 hours (plan estimate: 6.5 hours)
- **Dependencies**: None
- **Artifacts**: plans/01_rawedges-upward-closure.md
- **Standards**: summary-format.md, status-markers.md, artifact-management.md, tasks.md

## Overview

Discharged conjunct 1 (upward closure of `intExtractValuation b` along `intAccessPreorder edges`)
for a uniformly-constructed `edges := rawEdges`, by adding a new standalone, sorry-free lemma
`openBranch_rawEdges_upward_closed` to `Cslib/Logics/Propositional/Tableau/Intuitionistic/Scheme.lean`.
`edges` is reused verbatim from `intExpandBranches_openBranch_sat`'s existing `rawEdges` witness
(the tree-only parent-child edge list, previously discarded as `_rawEdges` by
`openBranch_countermodel`). The proof composes the already-sorry-free `IPosPersistRaw` with a new
`IWorldsPlanted` corollary of `IWorldHist`, chained over `Relation.ReflTransGen` by plain
`induction`. All six phases of the plan were executed in the plan's declared order; no plan
deviations.

## What Changed

All changes confined to
`Cslib/Logics/Propositional/Tableau/Intuitionistic/Scheme.lean` (169 insertions, 9 deletions):

- **`isAccessible_target_mem_edges`** (new, private): a non-reflexive `isAccessible` success
  means the target is a child endpoint of some edge -- proved by unfolding `isAccessible.go`'s
  DFS, no invariant hypotheses needed.
- **`edges_shape_of_worldHist`** (strengthened, sole existing caller `IWorldHist_forestComparable`
  updated): now returns the `1 ≤ c < nw` bound it already computed internally and previously
  discarded.
- **`IWorldsPlanted`, `IWorldsPlanted_mono`, `IWorldHist_worldsPlanted`** (new, private): the
  provenance half of `IPosPersistRaw`'s side-condition gap -- every raw edge-list child already
  has a planted branch entry -- derived as a pure corollary of `IWorldHist`/`IWorldHistCounter`,
  mirroring the existing `ForestComparable` derivation pattern exactly.
- **`intExpandBranches_openBranch_sat`** (widened, atomic-batch): added `IWorldsPlanted rawEdges b`
  as a sixth conjunct to its existential conclusion (both the outer statement and the inner
  `suffices key`), computed at the existing induction exit site alongside `hfc`.
  `openBranch_countermodel`'s `obtain` pattern grew one discarded `_hwp` binder to match; its
  statement and its own `sorry` are otherwise untouched.
- **`openBranch_rawEdges_upward_closed`** (new, public lemma): the target deliverable. States and
  proves `∃ edges, ∀ {w w'} p, w ≤ w' (over intAccessPreorder edges) → intExtractValuation b w p
  → intExtractValuation b w' p` for any `b` from an `intExpandBranches` run, witnessed by
  `rawEdges`. Proof: reuse the `intExpandBranches_openBranch_sat` obtain block verbatim (as in
  `openBranch_countermodel`), then `induction` over the `ReflTransGen` chain, applying
  `isAccessible_target_mem_edges` + `IWorldsPlanted` to establish `IPosPersistRaw`'s side
  condition at each step.

## Decisions

- Followed the plan's Phase 5 correction over the research report's original sketch: used plain
  `induction hle` (tail-peeling, via `| @tail y w2 hchain hstep ih`) rather than
  `Relation.ReflTransGen.head_induction_on` -- it unified directly and needed no fallback.
- Kept the new lemma fully decoupled from `openBranch_countermodel`'s own `sorry`, per the
  delegation's scope: conjunct 2 and the reconciliation of the two conjuncts under one `edges`
  are explicitly out of scope (successor task).
- Did not re-attempt the maximal atom-inclusion frame `⊑`, per the delegation's explicit
  exclusion (ruled out by task 591's probes for `phiRef1`/`phiRef3`).

## Impacts

- `openBranch_countermodel`'s two pre-existing sorries (at `truthLemma` and at its own conjunct-1
  site) are unchanged in count, location (modulo line drift from the additions above them: now
  at lines 693 and 8051), and semantics.
- No other file was touched; no new axioms were introduced anywhere in the repository diff.
- `intExpandBranches_openBranch_sat` is private and has exactly one real call site
  (`openBranch_countermodel`), confirmed unaffected beyond the destructuring-pattern update.

## Follow-ups

- Successor task: reconcile conjunct 1 (this lemma, over `rawEdges`) and conjunct 2
  (`¬ IForces ...`, currently `sorry` in `openBranch_countermodel`) under one uniform `edges` --
  either by showing `rawEdges` also supports `IFimpAccess`/`truthLemma`, or by finding a
  genuinely uniform construction. Flagged by the supporting research report as likely equivalent
  to the tableau completeness theorem itself.

## References

- `specs/603_construct_uniform_frame_for_openbranch_countermodel/plans/01_rawedges-upward-closure.md`
- `specs/603_construct_uniform_frame_for_openbranch_countermodel/reports/01_uniform-frame-construction.md`
- `Cslib/Logics/Propositional/Tableau/Intuitionistic/Scheme.lean`
