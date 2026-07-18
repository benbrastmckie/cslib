# Implementation Plan: Consolidate Bimodal & Temporal Chronicle Trees

- **Task**: 530 - Consolidate chronicle construction (Bimodal/Temporal)
- **Status**: [IMPLEMENTING]
- **Effort**: 20 hours
- **Dependencies**: None
- **Research Inputs**: reports/01_chronicle-dedup-research.md
- **Artifacts**: plans/01_chronicle-consolidation.md (this file)
- **Standards**: plan-format.md; status-markers.md; artifact-management.md; tasks.md
- **Type**: cslib
- **Lean Intent**: false

## Overview

Factor the near-duplicate Burgess-1982 chronicle / countermodel-elimination machinery duplicated
across `Cslib/Logics/Bimodal/Metalogic/BXCanonical/Chronicle/` and
`Cslib/Logics/Temporal/Metalogic/Chronicle/` (~89% overlap) into a label-generic module tree
under `Cslib/Foundations/Logic/Metalogic/Chronicle/`, then have both logics instantiate it. This
is a **structural move only**: no proof changes, zero new sorries, zero new axioms, and every
landed sorry-free result preserved. Divergence between the two trees is almost entirely mechanical
(fc-threading, connective spelling, namespace/helper names), so the work is abstracting existing
green proofs over an interface value — not discovering new proofs. Definition of done: both trees
re-export generic declarations under their existing names, a full `lake build` is green after every
phase, and `Logics/Temporal/Metalogic/DenseCompleteness.lean` (`completeness_dense`) remains
sorry-free.

### Research Integration

The plan directly implements the phased strategy in `reports/01_chronicle-dedup-research.md`
(sections 5, 7, 8). Key integrated findings:
- The consolidation **extends the already-landed `SinceSeedInterface F` precedent** in
  `Foundations/.../Chronicle/SinceSeedConsistency.lean` (built on `GenericMCS.HilbertTree`) with a
  broader `ChronicleInterface F`. Reuse-first is satisfied by building on this, not inventing a new
  abstraction.
- The interface **must be a `structure`, not a `class`**: Bimodal needs an instance family indexed
  by `fc : FrameClass` (prefix connectives `Formula.untl/snce/...`); Temporal needs exactly one
  `.Base` instance (notation `U`/`S`/`𝐆`/`𝐅`/`𝐇`/`𝐏`). Explicit passing (as with `HilbertTree`) is
  clearer than instance resolution across several live `fc`.
- Purely definitional notions (`SetDeductivelyClosed`, `rRelation`, `burgessR*`, `Chronicle`,
  conditions c0-c5', `ValidChronicle`, etc.) become generic `def`s parameterized by an interface
  value; only the MCS/Burgess apparatus lemmas that each logic proves differently become interface
  **statement fields**.
- **Task-premise correction (honored):** the "watch the bimodal RRelation sorry" premise is STALE.
  `RRelation.lean` is sorry-free; its only "sorry" is a stale doc-comment (verified at
  `Bimodal/.../RRelation.lean` ~line 40: "Several lemmas in this file are INVALID and marked with
  sorry stubs"). This comment is corrected in the cleanup phase.
- **Out of scope (honored):** `Bimodal/.../Chronicle/ChronicleToCountermodel.lean` is genuinely
  divergent, carries the only real proof sorries in either tree (blocked on the external
  `WeakCanonical.IntegerModel.GoodStructuresModelSurgery` port), and has no temporal counterpart.
  It MUST NOT be consolidated, imported into, or entangled with any generic module.

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

No ROADMAP.md consulted for this dispatch (roadmap_flag not set). No roadmap phases added.

## Goals & Non-Goals

**Goals**:
- Land `ChronicleInterface F` (a `structure`) in Foundations, defeq to both logics' primitives.
- Lift the four shared layers — `ChronicleTypes`, `RRelation` shared core, the
  `CounterexampleElimination` pipeline, and `ChronicleConstruction` — into generic Foundations
  modules, instantiated by both trees.
- Both trees re-export generic declarations under their **existing** namespaces/names (via
  `export`/abbrev aliases) so downstream files are minimally perturbed.
- Keep `lake build` green and produce one commit at every phase boundary.
- Preserve every landed sorry-free result; introduce zero new sorries and zero new axioms.

**Non-Goals**:
- Do **not** touch, import, or merge `Bimodal/.../Chronicle/ChronicleToCountermodel.lean`
  (pre-existing sorries, external-port-blocked, no temporal analogue) or
  `ChronicleToCountermodelBasic.lean` beyond leaving it compiling.
- Do **not** consolidate temporal-only model-building glue (`TruthLemma`, `Frame`,
  `CanonicalChain`, `OrderedSeedConsistency`) — no bimodal counterpart.
- Do **not** attempt to unify the logic-specific divergent declarations (bimodal's 2 duality
  theorems, 2 GProp/HProp eliminators, ~24 RRelation extras; temporal's `_imp'` variant) — they
  stay logic-local.
- Do **not** disturb the landed `SinceSeedConsistency.lean` until the final cleanup phase, and only
  then optionally (reconciliation is low-priority and must not risk re-verifying the green Since
  path).
- No new mathematical content; if a proof body resists generic abstraction, keep that lemma
  logic-local rather than introducing a sorry — never defer with a sorry.

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| A proof body resists generic abstraction over the interface | M | M | Keep that lemma logic-local (do NOT sorry it); note it in the phase summary. The interface exposes whichever primitive both logics can supply (e.g. `set_consistent_not_both` vs `mcs_not_mem_of_neg`), or both as fields. |
| Downstream files reference declarations by old name/namespace and break | H | M | Use `export`/abbrev aliases so the generic move is transparent; run a full `lake build` at each phase before commit. |
| Accidentally entangling the out-of-scope `ChronicleToCountermodel.lean` sorries | H | L | Explicit non-goal; generic modules never import it. Verify no new import edge is introduced into it. |
| Interface field set is wrong/incomplete, discovered late in a big phase | M | M | Phase 0 lands the skeleton defeq to both logics' primitives and compiles before any lifting; expand fields conservatively per-phase as the next layer needs them. |
| Long/heavy builds (`RRelation`, CEE `Interface`) slow iteration | M | H | Budget time; build incrementally; commit each green sub-phase so no rework is lost. |
| Touching `SinceSeedConsistency.lean` re-verifies the already-green Since path (churn) | M | M | Defer any reconciliation to the optional Phase 5 tail; skip if it risks the green Since path. |
| A phase exceeds one agent run | M | M | The two large layers (CEE, ChronicleConstruction) are pre-split into agent-run-sized sub-phases (3a/3b/3c, 4a/4b) along temporal's natural file boundaries. |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 0 | -- |
| 2 | 1 | 0 |
| 3 | 2 | 1 |
| 4 | 3a | 2 |
| 5 | 3b | 3a |
| 6 | 3c | 3b |
| 7 | 4a | 3c |
| 8 | 4b | 4a |
| 9 | 5 | 4b |

Phases within the same wave can execute in parallel. This plan is fully sequential: each layer
depends on the generic modules landed by the prior layer (RRelation uses generic Types; CEE uses
generic Types + RRelation; ChronicleConstruction uses CEE; cleanup follows all), and phases share
the same barrel files, so serialized execution also avoids territory conflicts.

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

### Phase 3a: Generic CEE Structures + BurgessHelpers [NOT STARTED]

**Goal**: Land the generic CounterexampleElimination foundation — the Kind + result structures and
Burgess helpers — using temporal's 3-way file split as the target layout (the cleaner target per
research §5.3).

**Tasks**:
- [ ] Create `Cslib/Foundations/Logic/Metalogic/Chronicle/CounterexampleElimination/Structures.lean`
  (generic) holding the Kind/result structures (bimodal `Structures.lean` + the inlined
  `BurgessHelpers.lean` content; temporal keeps these in `Structures.lean`).
- [ ] Instantiate/re-export the structures in both trees' CEE `Structures.lean` (bimodal) /
  `Structures.lean` (temporal). Bimodal's `BurgessHelpers.lean` becomes instance/re-export.
- [ ] Update the `CounterexampleElimination.lean` sub-barrels in both trees as needed.

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

### Phase 3b: Generic CEE RecursiveWalks [NOT STARTED]

**Goal**: Land the generic `c5ForwardWalk` (~540 lines both) and `c5BackwardWalk` (~560/545) walk
machinery as a generic module.

**Tasks**:
- [ ] Create
  `Cslib/Foundations/Logic/Metalogic/Chronicle/CounterexampleElimination/RecursiveWalks.lean`
  (generic) porting the two walk defs over the interface (axis-only divergence, verified near
  line-for-line in research §5.3).
- [ ] Re-export the walks into both trees (temporal `RecursiveWalks.lean`; bimodal these live inside
  the monolithic `Interface.lean` — replace that portion with instance/re-export).

**Timing**: 2.5 hours

**Depends on**: 3a

**Files to modify**:
- `Cslib/Foundations/Logic/Metalogic/Chronicle/CounterexampleElimination/RecursiveWalks.lean` - new
- `Cslib/Logics/Temporal/Metalogic/Chronicle/CounterexampleElimination/RecursiveWalks.lean` -
  instance + re-export
- `Cslib/Logics/Bimodal/Metalogic/BXCanonical/Chronicle/CounterexampleElimination/Interface.lean` -
  replace walk portion with instance/re-export
- CEE sub-barrels

**Verification**:
- Full `lake build` green; no new sorries/axioms.
- Commit: `task 530 phase 3b: generic CEE RecursiveWalks`.

---

### Phase 3c: Generic CEE MainElimination driver [NOT STARTED]

**Goal**: Land the generic `eliminatePotentialCounterexample` driver (~1677/1642 lines) and
`eliminateC5Counterexample` (line-for-line near-duplicate modulo axes); complete the CEE
consolidation (the largest single dedup win, ~5000 lines collapsing to one pipeline). Keep bimodal's
2 GProp/HProp eliminators local.

**Tasks**:
- [ ] Create
  `Cslib/Foundations/Logic/Metalogic/Chronicle/CounterexampleElimination/MainElimination.lean`
  (generic) with the driver + `eliminateC5Counterexample` over the interface.
- [ ] Re-export the driver into both trees (temporal `MainElimination.lean`; bimodal replace the
  remaining `Interface.lean`/`Elimination.lean` driver portion with instance/re-export).
- [ ] Keep bimodal's `eliminateGPropCounterexample` / `eliminateHPropCounterexample` (~80 lines)
  **logic-local**; do not lift them.
- [ ] Finalize the CEE sub-barrels so both trees expose the same public names as before.

**Timing**: 3 hours

**Depends on**: 3b

**Files to modify**:
- `Cslib/Foundations/Logic/Metalogic/Chronicle/CounterexampleElimination/MainElimination.lean` - new
- `Cslib/Logics/Temporal/Metalogic/Chronicle/CounterexampleElimination/MainElimination.lean` and
  `Elimination.lean` - instance + re-export
- `Cslib/Logics/Bimodal/Metalogic/BXCanonical/Chronicle/CounterexampleElimination/Interface.lean`,
  `Elimination.lean` - instance/re-export; GProp/HProp eliminators stay local
- CEE sub-barrels + `Cslib.lean`

**Verification**:
- Full `lake build` green; bimodal GProp/HProp eliminators still compile locally.
- No new sorries/axioms; temporal tree stays fully sorry-free.
- Commit: `task 530 phase 3c: generic CEE MainElimination driver`.

---

### Phase 4a: Generic ChronicleConstruction core [NOT STARTED]

**Goal**: Lift the first half of the shared `ChronicleConstruction` skeleton (singleton chronicle →
counterexample enumeration → omega-chain → limit chronicle) into a generic module. ~59 shared decls
total across 4a+4b, 1:1 in the same order, proof bodies identical modulo axes + helper-rename table.

**Tasks**:
- [ ] Create `Cslib/Foundations/Logic/Metalogic/Chronicle/ChronicleConstruction.lean` (generic) and
  port the construction-core section (singleton → enumeration → omega-chain → limit chronicle) over
  the interface.
- [ ] Wire both trees' `ChronicleConstruction.lean` to the generic core for this section via
  instance + re-export (partial re-export; the C0-C5/model-existence section follows in 4b).

**Timing**: 2.5 hours

**Depends on**: 3c

**Files to modify**:
- `Cslib/Foundations/Logic/Metalogic/Chronicle/ChronicleConstruction.lean` - new generic module
  (core section)
- `Cslib/Logics/Bimodal/Metalogic/BXCanonical/Chronicle/ChronicleConstruction.lean` - partial
  instance + re-export
- `Cslib/Logics/Temporal/Metalogic/Chronicle/ChronicleConstruction.lean` - partial instance +
  re-export
- `Cslib.lean` and tree barrels

**Verification**:
- Full `lake build` green (both trees compile with the core section lifted, remainder still local).
- No new sorries/axioms.
- Commit: `task 530 phase 4a: generic ChronicleConstruction core`.

---

### Phase 4b: Generic ChronicleConstruction model-existence + finalize [NOT STARTED]

**Goal**: Lift the remaining shared `ChronicleConstruction` section (C0-C5 satisfaction,
`forward_G`/`backward_H`, `chronicle_model_exists`, strong C5) into the generic module and complete
the ChronicleConstruction consolidation. Keep the 2 bimodal-only duality theorems local.

**Tasks**:
- [ ] Extend the generic `ChronicleConstruction.lean` with the C0-C5 satisfaction lemmas,
  `forward_G`/`backward_H`, `chronicle_model_exists`, and strong C5, over the interface.
- [ ] Complete both trees' re-exports so all 59 shared decls resolve to the generic module under
  their existing names.
- [ ] Keep bimodal's `g_content_sub_imp_h_content_sub` / `h_content_sub_imp_g_content_sub` (~100
  lines, rely on BX4/BX4' connect_future/connect_past) **logic-local** (add to temporal only if the
  same axioms are available there — otherwise leave temporal without them, as today).

**Timing**: 2.5 hours

**Depends on**: 4a

**Files to modify**:
- `Cslib/Foundations/Logic/Metalogic/Chronicle/ChronicleConstruction.lean` - model-existence section
- `Cslib/Logics/Bimodal/Metalogic/BXCanonical/Chronicle/ChronicleConstruction.lean` - complete
  instance + re-export; 2 duality theorems local
- `Cslib/Logics/Temporal/Metalogic/Chronicle/ChronicleConstruction.lean` - complete instance +
  re-export
- tree barrels

**Verification**:
- Full `lake build` green; all 59 shared decls resolve via the generic module; bimodal duality
  theorems still compile locally.
- `Logics/Temporal/Metalogic/DenseCompleteness.lean` (`completeness_dense`) still sorry-free.
- No new sorries/axioms.
- Commit: `task 530 phase 4b: generic ChronicleConstruction model-existence`.

---

### Phase 5: Cleanup and optional reconciliation [NOT STARTED]

**Goal**: Finalize barrels, correct the stale doc-comment, and optionally reconcile the interfaces.

**Tasks**:
- [ ] Fix the stale sorry doc-comment in `Bimodal/.../Chronicle/RRelation.lean` (~line 40, "Several
  lemmas in this file are INVALID and marked with sorry stubs") — the file is sorry-free.
- [ ] Audit and tidy all affected barrels (`Cslib.lean`, `Bimodal/Metalogic.lean`,
  `Temporal/Metalogic.lean`, CEE sub-barrels) for import correctness and ordering.
- [ ] **Optional / low-priority**: reconcile `SinceSeedInterface` under the broader
  `ChronicleInterface` (have Since reuse the broader interface) ONLY if it does not risk
  re-verifying the already-green Since path; otherwise leave `SinceSeedConsistency.lean` untouched.
- [ ] **Optional**: note (do not necessarily execute) that `OrderedSeedConsistency` (the Until
  analog of the Since-seed extraction) is a possible future follow-up — out of scope here.
- [ ] Confirm no import edge into `ChronicleToCountermodel.lean` was introduced anywhere.

**Timing**: 1.5 hours

**Depends on**: 4b

**Files to modify**:
- `Cslib/Logics/Bimodal/Metalogic/BXCanonical/Chronicle/RRelation.lean` - stale comment fix
- Barrels as needed
- (Optional) `Cslib/Foundations/Logic/Metalogic/Chronicle/SinceSeedConsistency.lean` /
  `ChronicleInterface.lean` - only if reconciliation is safe

**Verification**:
- Full `lake build` green.
- Repo-wide `grep` confirms no new `sorry`/`axiom` anywhere in the touched trees; temporal Chronicle
  tree fully sorry-free; bimodal `ChronicleToCountermodel.lean` sorries neither removed nor
  multiplied.
- Commit: `task 530 phase 5: cleanup and barrel finalization`.

## Testing & Validation

- [ ] Full `lake build` is green after every phase (0, 1, 2, 3a, 3b, 3c, 4a, 4b, 5).
- [ ] Temporal Chronicle tree remains fully sorry-free after every phase.
- [ ] `Logics/Temporal/Metalogic/DenseCompleteness.lean` `completeness_dense` remains sorry-free and
  provable.
- [ ] Zero new sorries and zero new axioms introduced (verify via `grep`/`lean_verify` on each new
  generic module and on both trees' touched files).
- [ ] Bimodal `ChronicleToCountermodel.lean` sorry count is unchanged (pre-existing sorries neither
  removed nor multiplied); no generic module imports it.
- [ ] All previously-public declaration names/namespaces still resolve (downstream files compile
  unchanged) via `export`/abbrev re-exports.

## Artifacts & Outputs

- `plans/01_chronicle-consolidation.md` (this file)
- New generic modules under `Cslib/Foundations/Logic/Metalogic/Chronicle/`:
  `ChronicleInterface.lean`, `Types.lean`, `RRelation.lean`,
  `CounterexampleElimination/{Structures,RecursiveWalks,MainElimination}.lean`,
  `ChronicleConstruction.lean`
- Rewritten (instance + re-export) bodies in both trees' Chronicle files
- Updated barrels: `Cslib.lean`, `Bimodal/Metalogic.lean`, `Temporal/Metalogic.lean`, CEE
  sub-barrels
- `summaries/01_chronicle-consolidation-summary.md` (on completion)

## Rollback/Contingency

- Each phase is an isolated green commit; revert the offending commit to return to the last green
  state without losing earlier phases.
- If a specific lemma resists generic abstraction, keep it logic-local (never sorry it) and record
  the deviation in the phase summary — the plan already reserves logic-local status for the known
  divergent declarations, so extending that set is a controlled contingency, not a failure.
- If interface reconciliation (Phase 5, optional) threatens the green Since path, skip it entirely;
  it is explicitly non-essential.
- The out-of-scope `ChronicleToCountermodel.lean` is never modified, so its pre-existing sorries are
  never a rollback trigger for this task.
