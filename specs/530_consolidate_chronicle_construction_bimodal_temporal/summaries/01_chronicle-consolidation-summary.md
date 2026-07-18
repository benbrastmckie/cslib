# Implementation Summary: Consolidate Bimodal & Temporal Chronicle Trees (Partial)

- **Task**: 530 - Consolidate chronicle construction (Bimodal/Temporal)
- **Plan**: plans/01_chronicle-consolidation.md
- **Status**: PARTIAL -- Phases 0-1 of 9 completed and committed; Phases 2-5 remain.

## What Was Done

### Phase 0: `ChronicleInterface F` skeleton (commit `20d80ec4`)

Landed `Cslib/Foundations/Logic/Metalogic/Chronicle/ChronicleInterface.lean`: a `structure
ChronicleInterface (F : Type*)` bundling the abstract formula operators (`bot`, `imp`,
`and`, `or`, `untl`, `snce`, `somePast`, `allPast`, `allFuture`, `someFuture`), a
`Type*`-valued derivation family `Deriv`, low-level derivation combinators
(`assumption`, `modusPonens`, `weakening`, `deductionTheorem`, `identity'`, `impTrans`,
`lceImp`, `rceImp`, `pairing`, `efq`, `pastNecessitation`), and MCS-apparatus
statement-only fields (`mcsClosedUnderDerivation`, `theoremInMcs`, `negationComplete`,
`negExcludes`, `cudContainsTheorems`) needed by the Phase 1 lift. Reuses
`SinceSeedConsistency.lean`'s generic definitional-notion `def`s (`isSetConsistent`,
`isSetMaximalConsistent`, `isClosedUnderDerivation`, `rBurgessOf`, etc.) directly rather
than duplicating them, via `ci`-prefixed thin wrappers to avoid namespace collision.
Deliberately a separate structure from `SinceSeedInterface` (no changes to
`SinceSeedConsistency.lean`).

Two fields originally planned (`untlLeftMonoDeriv`, `combineImpConj`) were removed after
discovering their only proofs live downstream of `ChronicleTypes.lean` (in each tree's own
`PointInsertion/Burgess.lean`), which would create an import cycle. Both are deferred to
Phase 2.

### Phase 1: Generic `Types.lean` + both trees re-export (commit `0677ee68`)

Landed `Cslib/Foundations/Logic/Metalogic/Chronicle/Types.lean`: the DCS infrastructure
(`SetDeductivelyClosed`, `mcs_is_dcs`, `cud_*`/`dcs_*`), r-relations (`rRelation`,
`rRelationSince`, `r3Relation`, `r3RelationSince`), r-maximality (`rMaximal`,
`rMaximalSince`, `R3Maximal`, `R3MaximalSince`), and basic subset/intersection theorems
(including bimodal's `dcs_inter_*`/`three_way_inter_consistent`), generic over a
`ChronicleInterface` value.

Both trees' `ChronicleTypes.lean` now:
- Define an interface instance (`bimodalChronicleInterface : FrameClass →
  ChronicleInterface (Formula Atom)`, an `fc`-indexed family; `temporalChronicleInterface
  : ChronicleInterface (Formula Atom)`, a single value).
- Re-export the generic DCS/r-relation/r-maximality/Burgess-relation layer under their
  existing names via thin `abbrev`/`theorem` wrappers (downstream files unperturbed).
- Keep the `Chronicle` structure and its conditions (c0-c5', `ValidChronicle`,
  `ChronicleInvariant`, C3 consequences) **logic-local, unchanged** -- see Deviations
  below.

**Verification performed**: scoped `lake build` green for both `ChronicleTypes.lean`
files, both `RRelation.lean` files, all `CounterexampleElimination/*.lean` files in both
trees, both `ChronicleConstruction.lean` files, `ChronicleToCountermodel(Basic).lean`
(bimodal), and `Logics/Temporal/Metalogic/DenseCompleteness.lean` (`completeness_dense`
confirmed still sorry-free and provable). Zero new sorries, zero new axioms in all touched
files. Bimodal's `ChronicleToCountermodel.lean` sorry count unchanged (17, pre-existing,
untouched, not imported by any generic module).

## Plan Deviations

1. **Chronicle structure/conditions stay logic-local** (Phase 1 task items 3-4, marked
   "altered" in the plan file). An initial draft bridged the local `Chronicle` structure
   to the generic one via a `toGeneric : Chronicle Atom → Cslib.Foundations....Chronicle
   (Formula Atom)` conversion, routing `Chronicle.c0`-`.c5'` through it. This compiled
   standalone but broke `rcases`/`simp` proofs in downstream
   `CounterexampleElimination/*.lean` files (both trees) that pattern-match on
   Finset-membership subterms nested inside condition statements -- the extra `.toGeneric`
   projection layer, while defeq, is not eagerly reduced by `rcases`, producing "is not an
   inductive datatype" failures. Reverted: `Chronicle`/`c0`-`c5'`/`ValidChronicle`/
   `ChronicleInvariant`/C3-consequences are verbatim per-tree (matching pre-task content),
   per the plan's own sanctioned contingency for proof bodies that resist generic
   abstraction. The DCS/r-relation/r-maximality/Burgess layer (which does not touch the
   `Chronicle` structure) remains fully generic.
2. **`untlLeftMonoDeriv` and `combineImpConj` dropped from `ChronicleInterface`** (noted in
   Phase 0 already landed, documented again here for visibility). Both lemmas' only
   proofs live in each tree's `PointInsertion/Burgess.lean`, downstream of
   `ChronicleTypes.lean`; importing them at the `ChronicleInterface`/`Types.lean` layer
   would create an import cycle. Neither is used by any Phase 1 proof. Deferred to Phase 2
   (`RRelation.lean`), which sits at the correct layer (temporal's `RRelation.lean` already
   imports `WitnessSeed`/downstream modules) to supply them.

## Why Stopped at Phase 1 (Not a Blocker -- a Scoping Decision)

Phase 2 (lift `RRelation.lean`'s ~38-lemma shared core) was surveyed but not attempted
this run. Reading both trees' `RRelation.lean` files (Temporal: 746 lines; Bimodal: 1694
lines) showed the shared core is substantially deeper than `ChronicleTypes.lean`: it
relies on ~15 additional MCS/axiom-level primitives not yet in `ChronicleInterface`
(`temporal_implication_property`/bimodal equivalent, `theoremInMcs`'s callers, and
critically many named per-logic `Axiom.*` lemmas used directly via `DerivationTree.axiom`
-- `until_F`, `self_accum_until`, `since_P`, `absorb_until`, `absorb_since`,
`left_mono_until_G`, `left_mono_since_H`, `enrichment_until`, `enrichment_since`,
`connect_future`, `connect_past`, `right_mono_since`, `right_mono_until`,
`allPast_to_classic`, `allFuture_to_classic`, plus `contraposition`, `doubleNegation`,
`dni`, `tempKDistDerived`/`pastKDist`, and the `someFuture_allFuture_neg_absurd`/
`somePast_allPast_neg_absurd` absurdity lemmas). Each of these needs careful per-logic
name/signature verification before it can become a interface field, and several appear in
long proof chains (e.g. `burgessR_implies_burgessRSince`, ~35 lines) where an abstraction
mistake would be easy to miss without dedicated verification time. Given this task's
"zero-debt, no proof changes" mandate, rushing this lift risked either an incomplete/buggy
abstraction or leaving mid-phase uncommitted work. Stopping at the Phase 1 checkpoint
(fully green, fully committed) was judged the safer choice within this run's remaining
budget.

## Modified Files

- `Cslib/Foundations/Logic/Metalogic/Chronicle/ChronicleInterface.lean` (new)
- `Cslib/Foundations/Logic/Metalogic/Chronicle/Types.lean` (new)
- `Cslib/Logics/Bimodal/Metalogic/BXCanonical/Chronicle/ChronicleTypes.lean` (rewritten:
  instance + re-export)
- `Cslib/Logics/Temporal/Metalogic/Chronicle/ChronicleTypes.lean` (rewritten: instance +
  re-export)
- `Cslib.lean` (barrel: two new Foundations imports)
- `specs/530_consolidate_chronicle_construction_bimodal_temporal/plans/01_chronicle-consolidation.md`
  (phase markers + deviation annotations)

## Verification Results

- `sorry_count` (new): 0
- `vacuous_count` (new): 0
- `axiom_count` (new): 0
- Scoped `lake build`: green across all files touched/downstream of this task
- Full-project `lake build`: **currently fails** on
  `Cslib/Logics/Modal/Tableau/LoopChecking.lean`, an unrelated file mid-edit by a
  concurrent session (task 511, uncommitted at session start per initial `git status`;
  confirmed via `git log --oneline -1` showing it last touched by a different task's
  commit). Not caused by, or related to, this task's changes.
- `Logics/Temporal/Metalogic/DenseCompleteness.lean` `completeness_dense`: confirmed
  sorry-free and provable (built green).
- Bimodal `ChronicleToCountermodel.lean`: 17 pre-existing sorries, unchanged; not imported
  by any generic module.

## Continuation

See `.orchestrator-handoff.json` for the structured resume point. In short: resume at
Phase 2 (`RRelation.lean`), starting with a research pass that maps each of the ~15
axiom-level primitives listed above to its Bimodal and Temporal counterpart (name,
signature, and whether it is `fc`-independent like the Phase-1 Burgess relations or needs
per-`fc` provision like `ClosedUnderDerivation`), before extending `ChronicleInterface`
and porting `RRelation.lean`'s shared ~38-lemma core.
