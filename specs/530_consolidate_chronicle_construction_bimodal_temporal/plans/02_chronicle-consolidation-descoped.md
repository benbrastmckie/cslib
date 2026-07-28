# Implementation Plan: Consolidate Bimodal & Temporal Chronicle Trees (Descoped)

- **Task**: 530 - Consolidate chronicle construction (Bimodal/Temporal)
- **Status**: [PARTIAL]
- **Effort**: 9.5 hours (7.5 landed + 2 remaining; 10.5 hours descoped)
- **Dependencies**: None
- **Research Inputs**: reports/01_chronicle-dedup-research.md
- **Artifacts**: plans/02_chronicle-consolidation-descoped.md (this file)
- **Standards**: plan-format.md; status-markers.md; artifact-management.md; tasks.md
- **Type**: cslib
- **Lean Intent**: false
- **Supersedes**: plans/01_chronicle-consolidation.md (historical record; not edited)

## Overview

This is the **descoped** revision of the Chronicle consolidation plan. The original plan proposed
nine phases lifting the Burgess-1982 chronicle / countermodel-elimination machinery duplicated
across `Cslib/Logics/Bimodal/Metalogic/BXCanonical/Chronicle/` and
`Cslib/Logics/Temporal/Metalogic/Chronicle/` into a label-generic module tree under
`Cslib/Foundations/Logic/Metalogic/Chronicle/`. Four of those phases (0, 1, 2, 3a) landed
sorry-free, committed, with a green full build. Two independent deep investigations then
established that the remaining phases cannot proceed without reversing a closed structural
decision, and the plan owner has **descoped Phases 3b, 3c, 4a, and 4b**.

**Definition of done for this plan**: Phase 5 cleanup complete and green. This task closes as a
**partial consolidation** — see `## Success Criteria & Completion Bar` below, which is the
authoritative statement of the terminus and supersedes any reading of the original nine-phase
plan as the completion bar.

### Revision Rationale

The revision integrates one input that postdates the original plan: the plan owner's recorded
scoping decision, `[USER SCOPING DECISION 2026-07-26 -- path (B), descope]`, held in this task's
description in `specs/state.json`. That decision is this plan's authoritative scope statement.
Verbatim in effect:

> Phases 3b, 3c, 4a and 4b are DESCOPED. Do not attempt further generic lifting of
> `c5ForwardWalk` / `c5BackwardWalk`, the Phase 3c elimination driver, or Phase 4a/4b
> `ChronicleConstruction`. Two deep investigations (Phase 1 and Phase 3b) independently confirmed
> that generically bridging types indexed by each tree's LOCAL Chronicle Atom structure breaks
> downstream `rcases`/`simp` proofs, and repairing that exceeds this task's own "structural dedup,
> not a proof change" mandate. Keep every landed lift (ChronicleInterface skeleton, generic Types,
> RRelation shared core, CEE Structures + BurgessHelpers -- all sorry-free, committed, full lake
> test green), run Phase 5 cleanup, annotate the plan file's 3b-4b headings as [DESCOPED] with a
> pointer to this decision, and close as a partial consolidation.

The decision selected path (B) from the two options the Phase 3b blocker escalation offered:
descope rather than invest in replacing each tree's local `Chronicle` with a true type-level
alias to the generic `Chronicle F`. The deeper architectural question — what the highest-quality
Chronicle refactor actually is, given that the walk-result types are structurally the obstacle —
is carried by a dedicated follow-on research task and is **not** to be attempted here.

### Research Integration

No new research report was integrated by this revision. The original plan's integration of
`reports/01_chronicle-dedup-research.md` (sections 5, 7, 8) stands unchanged for the landed
phases. The two investigations that drove the descope are recorded in-plan rather than as
separate reports:

- **Phase 1 investigation** (recorded in the Phase 1 deviation note below and in
  `Bimodal/.../Chronicle/ChronicleTypes.lean`'s "Chronicle Structure" section): a `toGeneric :
  Chronicle Atom → Chronicle F` bridge compiles standalone but breaks `rcases`/`simp` proofs in
  downstream `CounterexampleElimination/*.lean` files that pattern-match on Finset-membership
  subterms nested inside condition statements. The extra (defeq but not eagerly-reduced)
  projection layer stops `rcases`/`simp` recognizing the term as a `Finset`.
- **Phase 3b investigation** (recorded in the Phase 3b blocker section below): reading Temporal's
  `CounterexampleElimination/RecursiveWalks.lean` in full and Bimodal's
  `CounterexampleElimination/Interface.lean` signatures confirmed that
  `C5ForwardWalkResult`/`C5BackwardWalkResult` are structures indexed by each tree's **own local**
  `Chronicle Atom` type, and that the same entanglement extends through the elimination driver and
  `ChronicleConstruction` — i.e. through every remaining unlanded phase.

Together these two findings are why the descope covers 3b **through** 4b rather than 3b alone.

### Prior Plan Reference

`plans/01_chronicle-consolidation.md` is the historical record of the original nine-phase scope
and is deliberately left unedited. This file is the live plan.

### Roadmap Alignment

No ROADMAP.md consulted for this dispatch (roadmap_flag not set). No roadmap phases added.

## Goals & Non-Goals

**Goals**:
- Preserve, unchanged, every landed lift: `ChronicleInterface F`, generic `Types.lean`, generic
  `RRelation.lean` shared core, and generic `CounterexampleElimination/Structures.lean` — all
  sorry-free, committed, full build green.
- Execute Phase 5 cleanup: doc-comment accuracy, barrel audit, sorry-inventory confirmation, and
  self-documenting notes recording where the consolidation deliberately stops.
- Close the task as a **partial consolidation** with an unambiguous, verifiable completion bar.

**Non-Goals** (this section is now the binding scope fence):
- Do **not** lift `c5ForwardWalk` / `c5BackwardWalk` generically (descoped Phase 3b).
- Do **not** lift the `eliminatePotentialCounterexample` driver generically (descoped Phase 3c).
- Do **not** lift `ChronicleConstruction`, in whole or in part (descoped Phases 4a, 4b).
- Do **not** re-attempt, in any form, a `toGeneric` bridge or a reducible type-level alias
  replacing either tree's local `Chronicle`. Both were considered and the alias path was
  explicitly declined by the scoping decision in favour of the follow-on research task.
- Do **not** touch, import, or merge `Bimodal/.../Chronicle/ChronicleToCountermodel.lean`
  (pre-existing sorries, blocked on the external `WeakCanonical.IntegerModel.`
  `GoodStructuresModelSurgery` port, no temporal analogue) or `ChronicleToCountermodelBasic.lean`
  beyond leaving them compiling. The bimodal discrete-completeness sorries stay exactly as they
  are — neither removed, multiplied, nor entangled with any generic module.
- Do **not** reconcile `SinceSeedInterface` under the broader `ChronicleInterface`. The original
  plan listed this as optional/low-priority; this revision downgrades it to
  **deliberately not attempted**, to keep the completion bar unambiguous.
- No proof work of any kind. This plan's remaining phase is prose, barrel, and verification work.

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| A later implement dispatch reads the descoped phases as pending work and re-attempts them | H | M | Each descoped phase heading carries `[DESCOPED]`, opens with a DO-NOT-IMPLEMENT banner, and has its task checklist removed rather than left unticked. `## Success Criteria & Completion Bar` states the terminus explicitly. |
| Phase 5 cleanup edits accidentally perturb a landed generic module's elaboration | M | L | Phase 5 edits are confined to doc-comments, barrels, and read-only verification; the closing gate is the full repository CI pipeline (`scripts/pre-pr-check.sh`), not a narrower check. |
| Sorry inventory drifts and the descope is misread as "we lost proofs" | M | L | Phase 5 records exact baseline counts and verifies them mechanically; the counts are stated in the phase body as grep-checkable numbers. |
| Barrel audit uncovers an import that only *appears* stale | L | M | The shake ratchet (`scripts/check-shake-residue.sh`, run as pipeline step 7) is the arbiter; do not hand-remove imports it does not flag. |

## Implementation Phases

**Marker note**: `[DESCOPED]` is used below in addition to the standard phase-heading vocabulary
(`[NOT STARTED]`, `[IN PROGRESS]`, `[COMPLETED]`, `[COMPLETED WITH EXCLUSIONS]`, `[PARTIAL]`,
`[BLOCKED]`). It denotes a phase formally **removed from this plan's scope** by the recorded
scoping decision: not pending, not blocked-awaiting-unblock, not resumable. A descoped phase is
never eligible for dispatch under this plan. The four completed phases below are reproduced
verbatim from the superseded plan, including their original deviation notes and their (absent)
per-phase verification-tier fields — they are closed and are not re-formatted by this revision.

**Dependency Analysis**:
| Wave | Phases | Blocked by | State |
|------|--------|------------|-------|
| 1 | 0 | -- | [COMPLETED] |
| 2 | 1 | 0 | [COMPLETED] |
| 3 | 2 | 1 | [COMPLETED] |
| 4 | 3a | 2 | [COMPLETED] |
| -- | 3b, 3c, 4a, 4b | -- | [DESCOPED] — removed from scope, never dispatched |
| 5 | 5 | 3a | [COMPLETED] — the only actionable work, now landed |

Phase 5 now depends on **3a**, not 4b: with 3b-4b descoped, 3a is the last landed predecessor.
Phase 5 is the sole remaining actionable phase and executes alone.

---

### Phase 0: ChronicleInterface F skeleton [COMPLETED]

**Goal**: Land the `ChronicleInterface F` `structure` signature/skeleton in Foundations, defeq to
both logics' primitives, wiring nothing yet. Establishes the abstraction seam all later phases
extend.

**Tasks**:
- [ ] Create `Cslib/Foundations/Logic/Metalogic/Chronicle/ChronicleInterface.lean` (namespace
  `Cslib.Logic.Metalogic.Chronicle`) defining `structure ChronicleInterface (F : Type*)` bundling:
  abstract formula operators (`and`, `untl`, `snce`, `somePast`, `allPast`, plus `or`, `neg`,
  `allFuture`, `someFuture` / their temporal `U`/`S`/`𝐆`/`𝐅`/`𝐇`/`𝐏` counterparts as needed by
  later layers); the `Type*`-valued derivation family (reuse/parallel `GenericMCS.HilbertTree`); the
  `SetConsistent`/`SetMaximalConsistent` predicates; and the MCS/Burgess apparatus lemmas as
  **statement-only** fields (e.g. `negation_complete`, `implication_property`, and the
  consistency-final-step primitive both logics can supply).
- [ ] Confirm the field set subsumes what `SinceSeedInterface F` already needs (note field overlap
  in a comment for the Phase 5 reconciliation) but do NOT modify `SinceSeedConsistency.lean`.
- [ ] Add the new module to the root barrel `Cslib.lean` (near line 88, alongside the existing
  Foundations Chronicle import).
- [ ] Keep purely definitional notions OUT of the structure — they arrive as generic `def`s in
  later phases.

**Timing**: 1.5 hours

**Depends on**: none

**Files to modify**:
- `Cslib/Foundations/Logic/Metalogic/Chronicle/ChronicleInterface.lean` - new interface structure
- `Cslib.lean` - barrel import

**Verification**:
- `lake build Cslib.Foundations.Logic.Metalogic.Chronicle.ChronicleInterface` succeeds.
- Full `lake build` green.
- No sorries/axioms introduced (`grep -n "sorry" ChronicleInterface.lean` empty; `lean_verify` on
  the structure clean).
- Commit: `task 530 phase 0: land ChronicleInterface F skeleton`.

---

### Phase 1: Lift ChronicleTypes to generic Types.lean [COMPLETED]

**Goal**: Lift the ~95%-shared `ChronicleTypes` layer (DCS infrastructure, r-relations,
r-maximality, Burgess content relations, the `Chronicle` structure, conditions c0-c5',
`ValidChronicle`, C3 consequences, `ChronicleInvariant`, basic subset/intersection theorems) into a
generic Foundations module; instantiate in both trees.

**Tasks**:
- [x] Create `Cslib/Foundations/Logic/Metalogic/Chronicle/Types.lean` with the shared defs/theorems
  as generic `def`s/`theorem`s over a `ChronicleInterface` value.
- [x] Lift bimodal's extra dcs-intersection lemmas (`dcs_inter_*`, `three_way_inter_consistent`)
  into the shared core generically (they simply go unused by temporal).
- [x] Replace `Bimodal/.../Chronicle/ChronicleTypes.lean` body with the bimodal instance (family
  `fun fc => …`) + `export`/abbrev re-exports under the existing namespace/names.
  *(deviation: altered -- the DCS/r-relation/r-maximality/Burgess layer is generic
  instance + re-export as planned, but the `Chronicle` structure and its conditions
  c0-c5', `ValidChronicle`, `ChronicleInvariant`, and the C3 consequences stay logic-local
  verbatim rather than routing through a generic-structure bridge: a `toGeneric` bridge
  approach compiled standalone but broke `rcases`/`simp` proofs in downstream
  `CounterexampleElimination/*.lean` files that pattern-match on Finset-membership
  subterms nested inside condition statements. See the file's "Chronicle Structure"
  section for the full rationale. Also, `untlLeftMonoDeriv` and `combineImpConj` were
  dropped from `ChronicleInterface` after landing (their only proofs live downstream of
  `ChronicleTypes.lean`, in each tree's `PointInsertion/Burgess.lean`, creating an import
  cycle); deferred to Phase 2.)*
- [x] Replace `Temporal/.../Chronicle/ChronicleTypes.lean` body with the single `.Base` instance +
  re-exports. *(deviation: altered -- same Chronicle-structure-stays-local carve-out as
  Bimodal, for symmetry and to avoid the same downstream regression risk.)*
- [x] Update Foundations/Bimodal/Temporal barrels as needed. *(deviation: altered -- no
  `Bimodal/Metalogic.lean`/`Temporal/Metalogic.lean` barrel changes were needed since
  `ChronicleTypes.lean` re-exports under identical names/namespaces; only the root
  `Cslib.lean` barrel gained the two new Foundations modules.)*

**Timing**: 2 hours

**Depends on**: 0

**Files to modify**:
- `Cslib/Foundations/Logic/Metalogic/Chronicle/Types.lean` - new generic types module
- `Cslib/Logics/Bimodal/Metalogic/BXCanonical/Chronicle/ChronicleTypes.lean` - instance + re-export
- `Cslib/Logics/Temporal/Metalogic/Chronicle/ChronicleTypes.lean` - instance + re-export
- `Cslib.lean`, `Cslib/Logics/Bimodal/Metalogic.lean`, `Cslib/Logics/Temporal/Metalogic.lean` -
  barrels

**Verification**:
- Full `lake build` green (all downstream references to the old `ChronicleTypes` names resolve via
  re-exports).
- No new sorries/axioms; temporal tree stays fully sorry-free.
- Commit: `task 530 phase 1: lift ChronicleTypes to generic Types`.

---

### Phase 2: Lift RRelation shared core [COMPLETED]

**Goal**: Lift the ~38 shared RRelation core lemmas (deductive-closure infra,
r-relation/r3 maximal-extension existence via Zorn, `burgess*_absorption`, `untl/snce_left_mono*`,
seed→BurgessR3Maximal, the `someFuture/somePast` absurdity lemmas, the
`burgessR_implies_burgessRSince` pair) into the generic core; hoist temporal's Zorn helper
`chain_finite_subset_in_element`.

**Tasks**:
- [x] Create `Cslib/Foundations/Logic/Metalogic/Chronicle/RRelation.lean` (generic) with the ~38
  shared-core lemmas over the interface, plus the hoisted `chain_finite_subset_in_element`.
  *(deviation: altered -- extended `ChronicleInterface` with 21 new statement-only fields
  (BX2-BX6/BX10, connect_future/past, enrichment, futureNecessitation, doubleNegation,
  futureKDist/pastKDist, and 6 MCS-level duality-bridge facts) discovered necessary during
  the lift; not anticipated at Phase 0/1 scope. `burgessR3Maximal_from_g_content_sub` was
  found to be a false-positive name match -- Temporal's version is a trivial restatement of
  `burgessR3Maximal_extension_exists` while Bimodal's takes an additional `gContent A ⊆ C`
  hypothesis -- kept logic-local in BOTH trees rather than merged.)*
- [x] Replace `Temporal/.../Chronicle/RRelation.lean` shared-core body with instance + re-exports.
  *(deviation: altered -- no genuine "primed variant" divergence was found: Temporal's
  `deductiveClosure_singleton_imp'` and Bimodal's non-primed `deductiveClosure_singleton_imp`
  are the SAME lemma (Bimodal fc-generic, Temporal fixed at Base); lifted as one generic
  `deductiveClosure_singleton_imp'`, re-exported under each tree's own existing name.)*
- [x] Replace `Bimodal/.../Chronicle/RRelation.lean` shared-core body with instance + re-exports;
  keep bimodal's ~23 extras local (Since-mirrored maximal-extension variants
  `rMaximalSince_extension_exists`/`r3MaximalSince_extension_exists`; the `BurgessR3Maximal`
  projection/accessor suite; conjunction-guard machinery `untl/snce_conj_guard`, `burgessR_conj`,
  `burgessRSince_conj`; the c4/c4' hard-case lemmas; `burgessR3_untl_conj_in_A` (Xu 3.2.1);
  `F_mem_of_g_content_sub`/`P_mem_of_g_content_sub`/`burgessR3Maximal_from_g_content_sub`/
  `burgessR3Maximal_with_guard`).
- [x] Do NOT yet fix the stale doc-comment (Phase 5) — but do not propagate it into the generic
  module. *(confirmed: not propagated.)*

**Timing**: 2.5 hours

**Depends on**: 1

**Files to modify**:
- `Cslib/Foundations/Logic/Metalogic/Chronicle/RRelation.lean` - new generic shared core
- `Cslib/Logics/Bimodal/Metalogic/BXCanonical/Chronicle/RRelation.lean` - instance + extras local
- `Cslib/Logics/Temporal/Metalogic/Chronicle/RRelation.lean` - instance + `_imp'` local
- `Cslib.lean` and tree barrels as needed

**Verification**:
- Full `lake build` green; bimodal extras and temporal `_imp'` still compile locally.
- No new sorries/axioms.
- Commit: `task 530 phase 2: lift RRelation shared core`.

---

### Phase 3a: Generic CEE Structures + BurgessHelpers [COMPLETED]

**Goal**: Land the generic CounterexampleElimination foundation — the Kind + result structures and
Burgess helpers — using temporal's 3-way file split as the target layout (the cleaner target per
research §5.3).

**Tasks**:
- [x] Create `Cslib/Foundations/Logic/Metalogic/Chronicle/CounterexampleElimination/Structures.lean`
  (generic) holding the Kind/result structures (bimodal `Structures.lean` + the inlined
  `BurgessHelpers.lean` content; temporal keeps these in `Structures.lean`).
  *(deviation: altered -- landed the fresh-rational Finset helpers (zero
  `ChronicleInterface`/`Formula` dependency) and the three `BurgessR3Maximal_g_content_sub`/
  `_sdc`/`_bot_not_mem` MCS-level lemmas generically. `C5Counterexample`/`C5'Counterexample`
  (structures indexed by the logic-local `Chronicle F`), `c2'_preserved_on_old_adjacent`, and
  `burgessR3Maximal_from_h_content_sub` (forward dependency on the Phase 4b duality-theorem
  decision) stay logic-local in both trees per the survey's recommendation -- see the generic
  module's docstring for the full rationale. No new `ChronicleInterface` fields were needed:
  `until_implies_F_in_mcs` (Phase 2), `futureNecessitation`, `futureKDist`,
  `someFutureAllFutureNegAbsurd`, and `dcs_modus_ponens ∘ mcs_is_dcs` (for
  `implication_property`) already covered every primitive the three lemmas needed.)*
- [x] Instantiate/re-export the structures in both trees' CEE `Structures.lean` (bimodal) /
  `Structures.lean` (temporal). Bimodal's `BurgessHelpers.lean` becomes instance/re-export.
- [x] Update the `CounterexampleElimination.lean` sub-barrels in both trees as needed.
  *(deviation: altered -- no sub-barrel changes were needed since both files re-export
  under identical names; `Cslib.lean` gained one new Foundations import. `lake shake`
  flagged `PointInsertion`/`CanonicalModel` imports in Bimodal's `BurgessHelpers.lean` as
  now-unused after the lift; removed both, along with the now-unresolvable
  `CanonicalModel` `open`.)*

**Timing**: 1.5 hours

**Depends on**: 2

**Files to modify**:
- `Cslib/Foundations/Logic/Metalogic/Chronicle/CounterexampleElimination/Structures.lean` - new
- `Cslib/Logics/Bimodal/Metalogic/BXCanonical/Chronicle/CounterexampleElimination/Structures.lean` -
  instance + re-export
- `Cslib/Logics/Bimodal/Metalogic/BXCanonical/Chronicle/CounterexampleElimination/BurgessHelpers.lean`
  - instance/re-export
- `Cslib/Logics/Temporal/Metalogic/Chronicle/CounterexampleElimination/Structures.lean` - instance +
  re-export
- CEE sub-barrels + `Cslib.lean`

**Verification**:
- Full `lake build` green; no new sorries/axioms.
- Commit: `task 530 phase 3a: generic CEE Structures + BurgessHelpers`.

---

### Phase 3b: Generic CEE RecursiveWalks [DESCOPED]

> **DO NOT IMPLEMENT.** Removed from scope by
> `[USER SCOPING DECISION 2026-07-26 -- path (B), descope]` (recorded in this task's description
> in `specs/state.json`). The task checklist has been deleted rather than left unticked, so this
> phase is not dispatchable. Do not re-attempt a generic `c5ForwardWalk`/`c5BackwardWalk` lift, a
> `toGeneric` bridge, or a reducible type-level `Chronicle` alias.

**Original goal (not pursued)**: land generic `c5ForwardWalk` (~540 lines both trees) and
`c5BackwardWalk` (~560/545) walk machinery as a generic Foundations module.

**Why descoped**: `C5ForwardWalkResult` and `C5BackwardWalkResult` are `structure`s indexed by
`χ : Chronicle Atom` — each tree's **own local** `Chronicle` structure, a genuinely separate Lean
type per tree, not an alias to the generic
`Cslib.Foundations.Logic.Metalogic.Chronicle.Types.Chronicle F`. The walk proof bodies are
saturated with `rcases` / `simp only [χ', Finset.mem_insert] at ha hb`-style pattern-matching on
Chronicle-structure-literal-derived Finset-membership subterms. That is exactly the failure
signature the Phase 1 investigation recorded: a bridging projection layer, though defeq, is not
eagerly reduced, and `rcases`/`simp` stop recognizing the term as a `Finset`. Re-attempting the
bridge here would reproduce that breakage across ~1125 + 3048 lines of dense case-splitting proof
rather than the small structures Phase 3a safely kept logic-local. Repairing it is proof work,
which exceeds this task's own "structural dedup, not a proof change" mandate.

**Disposition**: `c5ForwardWalk` / `c5BackwardWalk` stay logic-local and duplicated in both trees,
by design. Surveyed, confirmed blocked, no lift.

---

### Phase 3c: Generic CEE MainElimination driver [DESCOPED]

> **DO NOT IMPLEMENT.** Removed from scope by
> `[USER SCOPING DECISION 2026-07-26 -- path (B), descope]`. Checklist deleted; not dispatchable.

**Original goal (not pursued)**: land the generic `eliminatePotentialCounterexample` driver
(~1677/1642 lines) and `eliminateC5Counterexample`, completing the CEE consolidation (the largest
single dedup win).

**Why descoped**: the Phase 3b investigation additionally surveyed `EliminationResult` in both
trees and found it likewise indexed by the tree-local `Chronicle Atom`. The driver both consumes
the descoped walks and produces `Chronicle`-typed values, so it inherits the Phase 3b obstruction
in full — it cannot be lifted while the walks stay local, and the walks cannot be lifted for the
reasons recorded above.

**Disposition**: the elimination driver stays logic-local and duplicated in both trees, by design.
Bimodal's `eliminateGPropCounterexample` / `eliminateHPropCounterexample` also stay local, as the
original plan already specified.

---

### Phase 4a: Generic ChronicleConstruction core [DESCOPED]

> **DO NOT IMPLEMENT.** Removed from scope by
> `[USER SCOPING DECISION 2026-07-26 -- path (B), descope]`. Checklist deleted; not dispatchable.

**Original goal (not pursued)**: lift the shared `ChronicleConstruction` skeleton (singleton
chronicle → counterexample enumeration → omega-chain → limit chronicle) into a generic module.

**Why descoped**: the Phase 3b investigation surveyed `ChronicleConstruction.lean` in both trees
and confirmed `singletonChronicle : ... → Chronicle Atom`, `omegaChain`, `limitG`, and
`chronicle_model_exists` are all indexed by or return the tree-local `Chronicle Atom`. The same
entanglement that blocks 3b and 3c extends here unchanged.

**Disposition**: `ChronicleConstruction` stays logic-local and duplicated in both trees, by design.

---

### Phase 4b: Generic ChronicleConstruction model-existence + finalize [DESCOPED]

> **DO NOT IMPLEMENT.** Removed from scope by
> `[USER SCOPING DECISION 2026-07-26 -- path (B), descope]`. Checklist deleted; not dispatchable.

**Original goal (not pursued)**: lift the remaining `ChronicleConstruction` section (C0-C5
satisfaction, `forward_G`/`backward_H`, `chronicle_model_exists`, strong C5) and complete the
construction consolidation.

**Why descoped**: same obstruction as Phase 4a, of which this is the second half; it cannot be
reached without 4a. Note that Phase 3a's deferral of `burgessR3Maximal_from_h_content_sub` was
explicitly conditioned on "the Phase 4b duality-theorem decision" — with 4b descoped, that lemma
simply stays logic-local in both trees permanently. No orphaned decision remains open.

**Disposition**: `ChronicleConstruction` model-existence stays logic-local and duplicated in both
trees, by design. Bimodal's two duality theorems
(`g_content_sub_imp_h_content_sub` / `h_content_sub_imp_g_content_sub`) stay local as originally
planned.

---

### Phase 5: Cleanup, self-documentation, and partial-consolidation close [COMPLETED]

**Goal**: Leave the partial consolidation accurate, self-documenting, and green. This is the only
actionable phase remaining, and the last phase of this plan.

**Verification Tier**: full — the phase's closing gate is the repository's full pre-PR pipeline.
Individual edits below are prose-only or barrel-only, but tie-break-upward applies and the gate is
cheap relative to the risk of a silently perturbed landed module.

**Commit Mode**: per-substep

**Scope Hypothesis**: this phase asserts four counts/lists, each stated with the command that
confirms it at implementation time. All four were measured while authoring this revision and are
recorded here as hypotheses to re-confirm, not as facts to trust:
1. The stale doc-comment targeted by the superseded plan is **already gone** — the Phase 2 rewrite
   replaced that file header wholesale. Confirm:
   `grep -rn "INVALID\|sorry stub" Cslib/Logics/Bimodal/Metalogic/BXCanonical/Chronicle/RRelation.lean`
   returns nothing.
2. Real proof sorries in the bimodal Chronicle tree live in exactly one file. Confirm:
   `grep -rc "\bsorry\b" Cslib/Logics/Bimodal/Metalogic/BXCanonical/Chronicle/**/*.lean` reports
   `ChronicleToCountermodel.lean: 23` and `ChronicleToCountermodelBasic.lean: 2` and nothing else
   non-zero. (The 23 includes doc-comment mentions and `set_option warn.sorry false` lines; the 2
   in `...Basic.lean` are both prose mentions of the word, not proof holes. Both numbers are
   baselines to hold constant, not targets to reduce.)
3. The temporal Chronicle tree is fully sorry-free. Confirm:
   `grep -rc "\bsorry\b" Cslib/Logics/Temporal/Metalogic/Chronicle/` reports no non-zero file.
4. The Foundations Chronicle tree contains exactly one `sorry` token, in prose. Confirm:
   `grep -rn "\bsorry\b" Cslib/Foundations/Logic/Metalogic/Chronicle/` returns only the
   `SinceSeedConsistency.lean` line reading "...bodies are all landed sorry-free below."

**Tasks**:
- [x] **5.1 — Doc-comment accuracy sweep.** Ran hypothesis 1's grep
  (`grep -rn "INVALID\|sorry stub"` across both trees' Chronicle files): confirmed already absent
  everywhere. No edit made.
- [x] **5.2 — Record the stopping point in the deliverable itself.** Added a "Consolidation
  Boundary: What Is Generic and What Stays Per-Logic" subsection to
  `Cslib/Foundations/Logic/Metalogic/Chronicle/ChronicleInterface.lean`'s module docstring,
  naming exactly which layers are generic and which stay per-logic, and stating the structural
  reason (each logic's local `Chronicle Atom`-indexed types; `rcases`/`simp` breaking on a
  non-eagerly-reduced bridging projection over Finset-membership subterms). Prose-only; module
  still builds clean (`lake build Cslib.Foundations.Logic.Metalogic.Chronicle.ChronicleInterface`
  succeeded).
- [x] **5.3 — Barrel audit.** Confirmed `Cslib.lean` imports exactly the five Foundations
  Chronicle modules on disk (`ChronicleInterface`, `CounterexampleElimination.Structures`,
  `RRelation`, `SinceSeedConsistency`, `Types`), no more, no less. Confirmed both trees'
  `CounterexampleElimination.lean` sub-barrels list exactly the modules on disk (bimodal:
  Structures, BurgessHelpers, Elimination, Interface — 4/4 match; temporal: Structures,
  Elimination, RecursiveWalks, MainElimination — 4/4 match) and their docstring prose still
  describes the actual split. Confirmed the superseded-plan correction:
  `Cslib/Logics/Bimodal/Metalogic.lean` does not exist on disk; only
  `Cslib/Logics/Temporal/Metalogic.lean` does. Not created. No discrepancy found; no edit made.
- [x] **5.4 — Containment check.** `grep -rn "ChronicleToCountermodel" Cslib/Foundations/`
  returned nothing. Re-ran hypotheses 2-4: bimodal `ChronicleToCountermodel.lean: 23`,
  `ChronicleToCountermodelBasic.lean: 2`; temporal Chronicle tree fully sorry-free; Foundations
  Chronicle tree's one `sorry` token remains the same `SinceSeedConsistency.lean:61` prose
  mention. All four counts unchanged from the recorded baselines.
- [x] **5.5 — Explicitly skip the optional reconciliation.** Confirmed `SinceSeedInterface` was
  not reconciled under `ChronicleInterface`; `git status` on `SinceSeedConsistency.lean` shows no
  changes.

**Timing**: 2 hours

**Depends on**: 3a

**Files to modify**:
- `Cslib/Foundations/Logic/Metalogic/Chronicle/ChronicleInterface.lean` - docstring subsection only
  (5.2)
- `Cslib/Logics/Bimodal/Metalogic/BXCanonical/Chronicle/RRelation.lean` - only if 5.1 finds residue
- Barrels (`Cslib.lean`, both `CounterexampleElimination.lean` sub-barrels,
  `Cslib/Logics/Temporal/Metalogic.lean`) - only if 5.3 finds a discrepancy
- No other file. No `.lean` proof body is edited by this phase.

**Verification**:
- `bash scripts/pre-pr-check.sh` passes end to end (all nine steps: PR-scope sorry scan, debug
  artifacts, copyright headers, PR-scope build, full-repo `lake build --wfail --iofail`,
  linter-suppression ratchet, shake import-debt ratchet, sorry-suppression ratchet, axiom-census
  ratchet).
- All four Scope Hypothesis counts re-confirmed unchanged.
- `Logics/Temporal/Metalogic/DenseCompleteness.lean` (`completeness_dense`) still sorry-free.
- Zero new sorries and zero new axioms anywhere.
- Commit: `task 530 phase 5: cleanup and partial-consolidation close`.

## Success Criteria & Completion Bar

**This task closes as a PARTIAL consolidation.** The terminus is *Phase 5 cleanup complete,
Phases 3b-4b descoped* — it is **not** "all nine phases complete". A dispatch that finds Phases
3b, 3c, 4a, or 4b unlanded has found the intended, decided end state, not outstanding work.

The task is complete when **all** of the following hold, and nothing further is required:

1. Phases 0, 1, 2, and 3a remain landed, sorry-free, and committed — unmodified by this revision
   and by Phase 5.
2. Phase 5's five sub-steps are done and its verification passes, including a green
   `scripts/pre-pr-check.sh`.
3. Phases 3b, 3c, 4a, and 4b carry `[DESCOPED]` in this plan with their rationale recorded, and
   have **not** been attempted.
4. The bimodal discrete-completeness sorries in `ChronicleToCountermodel.lean` are exactly as they
   were: same count, same locations, still blocked on the external `WeakCanonical` port, still
   untouched by any generic module.
5. `SinceSeedConsistency.lean` is untouched.

**Explicitly NOT part of the completion bar**: a generic `RecursiveWalks`, a generic
`MainElimination`, a generic `ChronicleConstruction`, a `toGeneric` chronicle bridge, a reducible
type-level `Chronicle` alias, or any reduction in the bimodal sorry count. The deeper
Chronicle-structure refactor question is owned by a separate follow-on research task.

**Closing-gate result (this dispatch)**: item 2's `scripts/pre-pr-check.sh` run FAILED overall
(steps 1 and 5), but only because of pre-existing `sorry` instances in files this task never
touches — `Logics/Modal/Tableau/FrameSoundness.lean`,
`Bimodal/Metalogic/ConservativeExtension/TemporalConservativity.lean`,
`Bimodal/Metalogic/BXCanonical/Frame.lean`, `Bimodal/Metalogic/Bundle/UntilSinceCoherence.lean`,
`Bimodal/Metalogic/Bundle/SuccRelation.lean`, and three `Propositional/Tableau/*.lean` files —
all already committed at `HEAD~1` (i.e. present before this dispatch, owned by other in-flight
tasks). The four debt-ratchet steps (6-9), which specifically measure whether *this* work added
new debt, all report OK, matching baseline exactly. See
`summaries/02_chronicle-consolidation-descoped-summary.md` for the full breakdown. Items 1, 3, 4,
5 above all hold. The task is therefore left `[PARTIAL]` pending a clean `pre-pr-check.sh` run
once those unrelated tasks land — re-running the gate is the only remaining action, not further
Chronicle work.

## Testing & Validation

- [x] `bash scripts/pre-pr-check.sh` run after Phase 5 — FAILED overall on pre-existing,
  out-of-scope debt (see "Closing-gate result" above); not green.
- [x] Full `lake build --wfail --iofail` — FAILED for the same pre-existing, out-of-scope reason
  (pipeline step 5).
- [x] Temporal Chronicle tree remains fully sorry-free.
- [x] `Logics/Temporal/Metalogic/DenseCompleteness.lean` `completeness_dense` remains sorry-free.
- [x] Bimodal `ChronicleToCountermodel.lean` sorry count unchanged against the recorded baseline;
      no Foundations module imports it.
- [x] All previously-public declaration names/namespaces still resolve via the landed
      `export`/abbrev re-exports (downstream files compile unchanged) — confirmed by
      pre-pr-check.sh step 4 (`lake build` of the PR-scope modules) succeeding.
- [x] No new axioms (pipeline step 9, axiom-census ratchet) — confirmed OK, 43/43 matching
      baseline exactly.

## Artifacts & Outputs

**Landed (Phases 0-3a), preserved unchanged**:
- `Cslib/Foundations/Logic/Metalogic/Chronicle/ChronicleInterface.lean`
- `Cslib/Foundations/Logic/Metalogic/Chronicle/Types.lean`
- `Cslib/Foundations/Logic/Metalogic/Chronicle/RRelation.lean`
- `Cslib/Foundations/Logic/Metalogic/Chronicle/CounterexampleElimination/Structures.lean`
- Instance + re-export bodies in both trees' `ChronicleTypes.lean`, `RRelation.lean`, and CEE
  `Structures.lean` / `BurgessHelpers.lean`
- Root barrel `Cslib.lean` (five Foundations Chronicle imports)

**Not produced (descoped)**: generic `CounterexampleElimination/RecursiveWalks.lean`,
`CounterexampleElimination/MainElimination.lean`, and `ChronicleConstruction.lean` under
Foundations. These paths are intentionally absent.

**Produced by Phase 5**:
- Docstring subsection in `ChronicleInterface.lean` recording the consolidation boundary
- Any barrel/doc-comment corrections 5.1/5.3 turn up
- `plans/02_chronicle-consolidation-descoped.md` (this file)
- `summaries/02_chronicle-consolidation-descoped-summary.md` (on completion)

## Rollback/Contingency

- Phase 5 is a single small green commit; reverting it returns to the current landed state without
  touching Phases 0-3a.
- If Phase 5's containment check (5.4) finds a count has drifted, stop and investigate before
  committing — a drifted sorry count means something outside this plan's scope changed, and it is
  not Phase 5's job to absorb it.
- If the barrel audit (5.3) uncovers an import that only *appears* stale, defer to the shake
  ratchet (`scripts/check-shake-residue.sh`); do not hand-remove imports it does not flag.
- The descoped phases require no rollback: nothing was landed for them.
- The out-of-scope `ChronicleToCountermodel.lean` is never modified, so its pre-existing sorries
  are never a rollback trigger.
