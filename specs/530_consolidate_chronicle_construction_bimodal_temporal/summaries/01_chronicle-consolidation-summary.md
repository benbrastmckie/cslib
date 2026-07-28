# Implementation Summary: Consolidate Bimodal & Temporal Chronicle Trees (Partial)

- **Task**: 530 - Consolidate chronicle construction (Bimodal/Temporal)
- **Plan**: plans/01_chronicle-consolidation.md
- **Status**: PARTIAL -- Phases 0-3a of 9 completed and committed; Phase 3b BLOCKED
- **Started**: TBD
- **Completed**: TBD
- **Artifacts**: TBD
- **Standards**: TBD
  (architectural finding, needs plan-owner decision); Phases 3c-5 not attempted pending
  that decision.

## Update (this run, 4th dispatch): Phase 3a completed (commit `c7493875`); Phase 3b BLOCKED

**Phase 3a landed** (see plan file for the full deviation writeup): the fresh-rational
Finset helpers (`exists_rat_gt_finset`/`exists_rat_lt_finset`/`exists_rat_between_not_in_finset`,
zero `ChronicleInterface`/`Formula` dependency) and the three `BurgessR3Maximal_g_content_sub`/
`_sdc`/`_bot_not_mem` MCS-level lemmas are now generic in
`Cslib/Foundations/Logic/Metalogic/Chronicle/CounterexampleElimination/Structures.lean`, with
both trees re-exporting under existing names. No new `ChronicleInterface` fields were needed --
`until_implies_F_in_mcs` (Phase 2), `futureNecessitation`, `futureKDist`,
`someFutureAllFutureNegAbsurd`, and `dcs_modus_ponens ∘ mcs_is_dcs` (for
`implication_property`) already covered every primitive. `C5Counterexample`/
`C5'Counterexample`, `c2'_preserved_on_old_adjacent`, and `burgessR3Maximal_from_h_content_sub`
stayed logic-local per the Phase 3a survey's own recommendation. `lake shake` flagged
`PointInsertion`/`CanonicalModel` imports (and the `CanonicalModel` `open`) as newly-unused in
Bimodal's `BurgessHelpers.lean` after the lift; removed both. Full `lake build`
(3242 jobs)/`lake lint`/`lake exe lint-style`/`lake exe checkInitImports`/`lake test` all green;
zero new sorries/axioms.

### Phase 3b: BLOCKED -- major architectural finding (see plan file's Phase 3b blocker for the
full writeup; summarized here for the next dispatch)

Read Temporal's `CounterexampleElimination/RecursiveWalks.lean` in full (1125 lines) and
Bimodal's `CounterexampleElimination/Interface.lean` signatures (3048 lines;
`c5ForwardWalk`/`c5BackwardWalk` at lines 224/810). **Finding**: `C5ForwardWalkResult`/
`C5BackwardWalkResult` (both trees) are `structure`s indexed by `χ : Chronicle Atom` --
each tree's own **local** `Chronicle` structure (confirmed via `ChronicleTypes.lean`: `structure
Chronicle (Atom : Type*) where f : Rat → Set (Formula Atom) ...`), NOT the generic
`Cslib.Foundations.Logic.Metalogic.Chronicle.Types.Chronicle F`. The walk proof bodies are
saturated with `rcases`/`simp only [χ', Finset.mem_insert] at ha hb`-style pattern-matching on
Chronicle-structure-literal-derived Finset-membership subterms -- exactly the failure signature
Phase 1's own docstring already named and rejected a `toGeneric` bridge over ("the extra (defeq
but not eagerly-reduced) `.toGeneric` projection layer caused `rcases`/`simp` to no longer
recognize the term as a Finset").

**This entanglement was also confirmed to extend to Phase 3c and Phase 4a/4b**: Phase 3c's
`EliminationResult` (both trees) is likewise indexed by `Chronicle Atom`, and Phase 4a/4b's
`ChronicleConstruction.lean` core functions (`singletonChronicle`, `omegaChain`, `limitG`,
`chronicle_model_exists`, etc.) all consume/produce `Chronicle Atom` directly -- confirmed via
signature grep, not a full read, but the pattern is unambiguous (these files exist specifically
to build/manipulate Chronicle values).

**Why this is a BLOCKED escalation, not a "keep logic-local and continue" annotation**: Phase
3a's logic-local carve-outs were small (2 structures, 2 lemmas, ~15-100 lines each) within a
phase whose main deliverable (3 lemmas + 3 helpers) *did* land generically. Phase 3b's
resistant content is the phase's *entire* primary deliverable, and the same root cause
(confirmed, not hypothesized) propagates through the *rest of the plan*. Per
`plan-compliance.md`, a deviation of this scope on `.lean` files must be raised as a blocker for
plan-owner decision, not silently descoped.

**What is needed to unblock** (see plan file for full text): a `/revise` decision between (a)
formally descoping Phases 3b-4b to "surveyed, confirmed blocked by Chronicle-locality, no
generic lift" and moving straight to Phase 5 cleanup, accepting that only `ChronicleTypes`/
`RRelation`/the small Phase-3a lemmas end up shared (the ~5000-line CEE/Construction dedup the
plan's Phase 3c description anticipated does not happen); or (b) a deeper architectural retry --
replacing each tree's local `Chronicle` with a true reducible type alias to the generic
`Chronicle F` (`abbrev` rather than a projection function) to see whether that specific
technique avoids Phase 1's `.toGeneric`-layer breakage. Option (b) reopens Phase 1's closed
decision and is materially riskier/larger than continuing the current phase-by-phase lift, so it
needs explicit sign-off rather than opportunistic mid-phase attempt.

**No lean files were changed for Phase 3b** (nothing was found safe to lift); only the plan file
was updated to mark it `[BLOCKED]` with the full writeup above.

## Update (3rd dispatch): Phase 2 completed (commit `cb61119a`)

Landed the ~37-lemma shared core of `RRelation.lean` as a generic Foundations module,
extending `ChronicleInterface` with 21 new statement-only fields (13 raw axiom-Deriv facts
-- `untilF`/`selfAccumUntil`/`sinceP`/`absorbUntil`/`absorbSince`/`leftMonoUntilG`/
`leftMonoSinceH`/`rightMonoUntil`/`rightMonoSince`/`enrichmentUntil`/`enrichmentSince`/
`connectFuture`/`connectPast`; `futureNecessitation`; `doubleNegation`; `futureKDist`/
`pastKDist`; and 6 MCS-level duality-bridge facts --
`someFutureAllFutureNegAbsurd`/`somePastAllPastNegAbsurd`/`negAllPastNegToSomePast`/
`negAllFutureNegToSomeFuture`/`someFutureHNegGPAbsurd`/`somePastGNegHFAbsurd`). Also added
`ciNeg`/`ciTop` convenience defs (`neg φ := imp φ bot`, `top := imp bot bot`, matching the
`PropositionalConnectives` Lukasiewicz defaults both `Formula.neg`/`Formula.top` delegate
to -- confirmed defeq for both logics).

Landed `Cslib/Foundations/Logic/Metalogic/Chronicle/RRelation.lean` with the full shared
core (deductive-closure infra, Zorn maximal-extension existence for r/r3-relations,
`burgess*_absorption`, `mcs_contrapositive_mem`, `BurgessR3Maximal` existence, left-mono
helpers, the 4 Lemma-2.3 duality-bridge theorems as thin field wrappers, deductive-closure
singleton propagation, and `burgessR3Maximal_exists_from_seed`). Rewired both trees'
`RRelation.lean` to instance + re-export over it; Bimodal's ~23 logic-local extras
(Since-mirrored maximal-extension variants, `BurgessR3Maximal` accessor suite,
conjunction-guard machinery, c4/c4' hard cases, Xu's Lemma 3.2.1, gContent-seed
construction) stay verbatim, only rewiring their internal calls to the now-generic
`chain_finite_subset_in_element`/`mcs_contrapositive_mem`/etc.

**Findings that corrected the plan's premises**:
1. `burgessR3Maximal_from_g_content_sub` is a **false-positive name match**: Temporal's
   version (in the pre-Phase-2 file) is a trivial restatement of
   `burgessR3Maximal_extension_exists` with no `gContent` hypothesis at all, while
   Bimodal's is a substantially richer lemma taking `gContent A ⊆ C` and constructing its
   own seed via `Formula.top`. Kept logic-local in BOTH trees rather than merged.
2. No genuine "primed variant" divergence exists for `deductiveClosure_singleton_imp`:
   Bimodal's non-primed and Temporal's primed (`_imp'`) versions are the SAME lemma
   (Bimodal `fc`-generic, Temporal fixed at `FrameClass.Base`). Lifted as one generic
   `deductiveClosure_singleton_imp'`, re-exported under each tree's own existing name.

**Verification performed**: full `lake build` (3241 jobs, green -- only pre-existing
unrelated warnings in `Modal/Tableau/FrameSoundness.lean` from a concurrent session),
`lake exe checkInitImports` (clean), `lake lint` (0 errors repo-wide after fixing one
missing docstring on `derivationFromSingletonList`), `lake exe lint-style` (clean), `lake
test` (all `CslibTests/` green). Zero new sorries (grep-confirmed on all 6 touched/new
files), zero new axioms (the one `grep "^axiom "` hit is a false positive inside a doc
comment). `Logics/Temporal/Metalogic/DenseCompleteness.lean` `completeness_dense` and
Bimodal `ChronicleToCountermodel.lean` (17 pre-existing sorries) both confirmed unchanged.

## Phase 3a Survey (not started -- architectural wrinkle found, documented for continuation)

Read Bimodal's `CounterexampleElimination/{Structures,BurgessHelpers}.lean` and Temporal's
`CounterexampleElimination/Structures.lean` to scope Phase 3a. Found:

- `exists_rat_gt_finset`/`exists_rat_lt_finset`/`exists_rat_between_not_in_finset` (fresh-
  rational helpers) have **zero** `Formula`/`Chronicle` dependency -- pure `Finset Rat`
  lemmas, identical in both trees, trivially liftable to a completely
  interface-independent generic lemma. Easy, low-risk first step.
- `BurgessR3Maximal_g_content_sub`/`BurgessR3Maximal_sdc`/`BurgessR3Maximal_bot_not_mem`
  (Bimodal's `BurgessHelpers.lean` / Temporal's `Structures.lean`) operate on
  `Set (Formula Atom)` via the Burgess apparatus already in `ChronicleInterface` after
  Phase 2 -- liftable the same way as `RRelation.lean`'s shared core, likely needing 0-2
  more fields for the BX12-style `F_until_equiv`/`P_since_equiv` facts used inside
  `BurgessR3Maximal_g_content_sub`'s proof (need to verify Bimodal's exact axiom names
  match before adding fields).
- **Architectural wrinkle**: `C5Counterexample`/`C5'Counterexample` (the two structures
  Phase 3a's own task list names as its primary deliverable) are `structure ... (χ :
  Chronicle Atom)` -- they reference the `Chronicle` structure's `.f`/`.dom` fields
  directly. Since Phase 1 deliberately kept `Chronicle`/`ValidChronicle` **logic-local**
  (a `toGeneric` bridge broke downstream `rcases`/`simp` proofs -- see
  `ChronicleTypes.lean`'s "Chronicle Structure" section), `C5Counterexample`/
  `C5'Counterexample` cannot be transparently genericized without either (a) inventing a
  new abstract "chronicle-shape" structure/typeclass as a second bridge layer (real risk
  of the identical `rcases`/`simp` breakage that blocked Phase 1's attempt, since these
  structures are pattern-matched constantly in the walk/elimination proofs Phase 3b/3c
  target), or (b) accepting they stay **logic-local in both trees, verbatim, unmerged**
  -- the plan's own sanctioned contingency ("if a specific lemma resists generic
  abstraction, keep it logic-local"), extended here to two small structures. Recommend
  (b): the two structures are ~15 lines each and identical modulo `Chronicle Atom` vs
  `Chronicle F` -- not worth the bridge-layer risk for near-zero duplication savings.
  `c2'_preserved_on_old_adjacent` (Bimodal `BurgessHelpers.lean`) has the same
  `Chronicle`-locality issue and should likewise stay logic-local in both trees.
- `burgessR3Maximal_from_h_content_sub` (Temporal `Structures.lean`, `private`) depends on
  `h_content_sub_imp_g_content_sub'`, a duality theorem the plan's Phase 4b text already
  earmarks as logic-local (`g_content_sub_imp_h_content_sub`/
  `h_content_sub_imp_g_content_sub`, "add to temporal only if the same axioms are
  available there -- otherwise leave temporal without them"). This creates a forward
  dependency from Phase 3a onto a Phase 4b decision; simplest resolution is to also keep
  `burgessR3Maximal_from_h_content_sub` logic-local (it is `private`, so no cross-tree
  naming conflict risk either way).

**Recommendation for the next dispatch**: do the two low-risk lifts first (fresh-rational
helpers; the 3 `BurgessR3Maximal_*` MCS-level lemmas), explicitly mark
`C5Counterexample`/`C5'Counterexample`/`c2'_preserved_on_old_adjacent`/
`burgessR3Maximal_from_h_content_sub` as logic-local deviations in the plan file (not a
blocker -- a scoping decision within the plan's own contingency), then proceed to 3b/3c.

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

- `Cslib/Foundations/Logic/Metalogic/Chronicle/ChronicleInterface.lean` (Phase 0; +21
  fields in Phase 2)
- `Cslib/Foundations/Logic/Metalogic/Chronicle/Types.lean` (Phase 1)
- `Cslib/Foundations/Logic/Metalogic/Chronicle/RRelation.lean` (new, Phase 2)
- `Cslib/Logics/Bimodal/Metalogic/BXCanonical/Chronicle/ChronicleTypes.lean` (Phase 1
  instance + re-export; +21 field values in Phase 2)
- `Cslib/Logics/Bimodal/Metalogic/BXCanonical/Chronicle/RRelation.lean` (rewritten Phase 2:
  instance + re-export for the shared core; ~23 extras verbatim)
- `Cslib/Logics/Temporal/Metalogic/Chronicle/ChronicleTypes.lean` (Phase 1 instance +
  re-export; +21 field values in Phase 2)
- `Cslib/Logics/Temporal/Metalogic/Chronicle/RRelation.lean` (rewritten Phase 2: full
  instance + re-export)
- `Cslib.lean` (barrel: three new Foundations imports total)
- `specs/530_consolidate_chronicle_construction_bimodal_temporal/plans/01_chronicle-consolidation.md`
  (phase markers + deviation annotations)

## Verification Results

- `sorry_count` (new): 0
- `vacuous_count` (new): 0
- `axiom_count` (new): 0
- Full-project `lake build`: **green** (3241 jobs; the earlier LoopChecking.lean
  concurrent-session conflict noted in the Phase 0-1 summary resolved itself upstream)
- `lake exe checkInitImports`: clean
- `lake lint`: clean (0 errors repo-wide)
- `lake exe lint-style`: clean
- `lake test`: green (`CslibTests/` full suite)
- `Logics/Temporal/Metalogic/DenseCompleteness.lean` `completeness_dense`: confirmed
  sorry-free and provable (built green)
- Bimodal `ChronicleToCountermodel.lean`: 17 pre-existing sorries, unchanged; not imported
  by any generic module

## Continuation

See `.orchestrator-handoff.json` for the structured resume point. In short: Phase 3a is
complete and committed (`c7493875`). Phase 3b is `[BLOCKED]` on a plan-owner decision -- **do
not attempt further generic lifting of `c5ForwardWalk`/`c5BackwardWalk` (or Phase 3c's
elimination driver, or Phase 4a/4b's `ChronicleConstruction`) without first reading the Phase
3b blocker writeup** in both this file and the plan file, and without an explicit `/revise`
decision on the two paths documented there (descope 3b-4b to logic-local and skip to Phase 5
cleanup, vs. a deeper `Chronicle`-type-alias architectural retry). Resuming with a plain
`/implement` re-dispatch should re-surface this blocker for user review rather than silently
retrying the same doomed bridge.
