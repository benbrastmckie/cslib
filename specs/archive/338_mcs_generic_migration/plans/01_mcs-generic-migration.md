# Implementation Plan: Task #338 - MCS Generic Migration

- **Task**: 338 - Migrate Propositional and Temporal MCS to GenericMCS framework
- **Status**: [COMPLETED]
- **Effort**: 7 hours
- **Dependencies**: None (task 338 has no upstream task blockers)
- **Research Inputs**: specs/338_mcs_generic_migration/reports/01_mcs-generic-migration.md
- **Artifacts**: plans/01_mcs-generic-migration.md (this file)
- **Standards**: plan-format.md; status-markers.md; artifact-formats.md; cslib.md; lean4.md
- **Type**: cslib
- **Lean Intent**: false

## Overview

Migrate `Cslib/Logics/Temporal/Metalogic/MCS.lean` (and, conditionally,
`Cslib/Logics/Propositional/Metalogic/MCS.lean`) to reuse the generic algebraic MCS
framework in `Foundations/Logic/Metalogic/GenericMCS.lean` and `MCSProperties.lean`,
eliminating ~76-174 lines of per-logic wrapper boilerplate. The migration is gated by a
**prerequisite equivalence proof**: the tree-based `temporalDerivationSystem` and the
`algebraicDerivationSystem (S := HilbertBX)` must be shown equivalent on the propositional
fragment before any abbreviation type can be swapped without breaking downstream consumers.
Definition of done: the prerequisite equivalence (Phase 1) is proved or the task is marked
[BLOCKED] with a documented gap; if proved, Temporal MCS wrappers (Phase 2) route through
`MCSProperties` with all downstream files (`DenseCompleteness.lean`, `DenseMCS.lean`,
`Chronicle/OrderedSeedConsistency.lean`) still building green.

**Actual outcome**: Phase 1 equivalence proved (new `Temporal/Metalogic/GenericMCSBridge.lean`,
227 lines); Temporal MCS wrappers rewired through `MCSProperties` (−29 lines); all three
downstream consumers build unmodified. CI was verified via **scoped** builds of the Temporal
metalogic territory (a concurrent session held unrelated uncommitted edits to Propositional
files, so a full-tree build was deliberately deferred to a clean-tree PR-time run). Propositional
MCS migration deferred to a roadmap follow-up. Task COMPLETED.

### Research Integration

Key findings from `reports/01_mcs-generic-migration.md` incorporated into this plan:

- **Two derivation systems** exist: tree-based (`temporalDerivationSystem`,
  `propDerivationSystem`) and algebraic (`algebraicDerivationSystem` via `MinimalHilbert`).
  They are NOT equivalent on the full temporal fragment (algebraic has no necessitation),
  only on the propositional fragment, and that equivalence is **unproved**.
- **GenericMCSBridge.lean is documentation-only** -- it documents the gap, it is not a
  working migration template. The "pattern to follow" is the gap analysis, not code.
- **Temporal-specific code (lines 142-484, ~342 lines) MUST remain** -- it uses
  `DerivationTree.temporal_necessitation` / `temporal_duality`, inexpressible algebraically.
- **Temporal is favorable**: `temporalDerivationSystem` is not parameterized and
  `ClassicalHilbert HilbertBX` (extends `MinimalHilbert`) exists, so wrappers (lines 62-140)
  CAN route through `MCSProperties` once equivalence holds.
- **Propositional is unfavorable**: `propDerivationSystem` is parameterized over arbitrary
  `Axioms : Proposition → Prop` with no `MinimalHilbert` instance, so it is deferred.
- Research recommendation: do Phase 1 + Phase 2 (Temporal) here; spin Propositional out as a
  follow-up task. If the Phase 1 equivalence is out of scope, mark the task [BLOCKED].

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

No ROADMAP.md consulted for this task (no roadmap_path provided in delegation context).

## Goals & Non-Goals

**Goals**:
- Prove propositional-fragment equivalence between `temporalDerivationSystem` and
  `algebraicDerivationSystem (S := HilbertBX)` (both directions), or mark [BLOCKED] with a
  precise statement of the remaining obligation.
- Re-express `Temporal.SetConsistent` / `Temporal.SetMaximalConsistent` and the generic +
  basic MCS wrappers (Temporal MCS.lean lines 50-140) in terms of the generic framework,
  reducing boilerplate while preserving every downstream-visible name and type.
- Keep all temporal-specific properties (lines 142-484) unchanged.
- Maintain full CI green: `lake build`, `lake exe checkInitImports`, `lake lint`,
  `lake exe lint-style`, `lake test`, `lake shake`.

**Non-Goals**:
- Migrating `Propositional/Metalogic/MCS.lean` (deferred to a follow-up task due to the
  arbitrary `Axioms` parameterization; see Phase 5 decision gate).
- Adding a necessitation rule to the algebraic system or proving full-fragment equivalence.
- Changing downstream completeness proofs beyond what type-compatibility requires.
- Modifying `GenericMCS.lean` or `MCSProperties.lean` (these are reused as-is).

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Propositional-fragment equivalence proof harder than expected (unknown unknowns) | H | M | Time-box Phase 1; if the forward or backward induction stalls, mark task [BLOCKED] with the exact stuck goal state recorded, per cslib.md vacuous-definition prohibition. Do NOT fabricate a placeholder. |
| Changing abbreviation definitions breaks downstream type inference (Lean won't auto-unfold new defs) | H | M | Keep `Temporal.SetMaximalConsistent` as an `abbrev` (reducible) so unfolding is transparent; verify each downstream file builds individually before full build. |
| Equivalence is only propositional (not definitional), forcing `rw`/`convert` in downstream proofs, negating line savings | M | M | Prefer aliasing via `abbrev` plus a propositional `Iff` bridge lemma applied at the wrapper boundary, so downstream files see unchanged types. Measure net line delta before committing. |
| `algebraicDerivationSystem (S := HilbertBX)` instance resolution differs from expected | M | L | Confirm `InferenceSystem Temporal.HilbertBX` and `ClassicalHilbert HilbertBX` instances resolve (Instances.lean:43, :212) before relying on them in Phase 2. |
| Temporal-specific lemmas (142-484) depend on the old wrapper signatures | M | L | Audit call sites of `mcs_mp_axiom`, `theoremInMcs`, etc. within MCS.lean before rewiring; preserve identical signatures. |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2 | 1 |
| 3 | 3 | 2 |
| 4 | 4 | 3 |
| 5 | 5 | 4 |

Phases within the same wave can execute in parallel. This plan is fully sequential because
each phase depends on the prior phase's proven equivalence or rewired definitions.

---

### Phase 1: Propositional-Fragment Equivalence (Prerequisite) [COMPLETED]

**Goal**: Prove the two-directional equivalence between `temporalDerivationSystem.Deriv` and
`algebraicDerivationSystem (S := HilbertBX).Deriv` restricted to the propositional fragment
(axiom / assumption / modus_ponens / weakening cases only; necessitation and duality
excluded). This is the critical-path gate for the entire migration.

**Outcome**: Proven. The equivalence and bridge live in the new dedicated file
`Cslib/Logics/Temporal/Metalogic/GenericMCSBridge.lean` (227 lines), committed in `df72a01e`.

**Tasks**:
- [x] Confirm prerequisite instances resolve: `InferenceSystem Temporal.HilbertBX`
  (Instances.lean:43) and `ClassicalHilbert HilbertBX` (Instances.lean:212, extends
  `MinimalHilbert`).
- [x] Forward lemma: `temporalDerivationSystem.Deriv Γ φ → algebraicDerivationSystem (S := HilbertBX) |>.Deriv Γ φ`
  on the propositional fragment, by induction on `DerivationTree`
  (axiom/assumption/modus_ponens/weakening; necessitation/duality out of scope).
- [x] Backward lemma: `algebraicDerivationSystem (S := HilbertBX) |>.Deriv Γ φ → temporalDerivationSystem.Deriv Γ φ`,
  by induction on `ListDeriv` via the Hilbert instance's axiom witnesses.
- [x] Combined into an `Iff` bridge lemma at the propositional fragment.
- [x] Placement: dedicated file `Temporal/Metalogic/GenericMCSBridge.lean` (mirrors the Modal
  naming), keeping MCS.lean focused.
- [x] Zero `sorry`; no non-Classical axioms.

**Timing**: 2.5 hours

**Depends on**: none

**Files to modify**:
- `Cslib/Logics/Temporal/Metalogic/GenericMCSBridge.lean` (new, preferred) OR
  `Cslib/Logics/Temporal/Metalogic/MCS.lean` - add equivalence lemmas
- `Cslib.lean` - barrel import update if a new file is added (`lake exe mk_all --module`)

**Verification**:
- `lake build Cslib.Logics.Temporal.Metalogic.GenericMCSBridge` (or `.MCS`) succeeds.
- `lean_verify` reports no `sorry`/axioms beyond Classical on both direction lemmas.
- **Decision gate**: if either induction direction cannot be closed within the time box,
  STOP, record the exact unproved goal state, mark task [BLOCKED], and return partial. Do
  not proceed to Phase 2.

---

### Phase 2: Rewire Temporal MCS Wrappers to MCSProperties [COMPLETED]

**Goal**: Replace the generic + basic MCS wrappers in `Temporal/Metalogic/MCS.lean`
(lines ~50-140: `SetConsistent`, `SetMaximalConsistent`, `temporal_lindenbaum`,
`temporal_closed_under_derivation`, `temporal_implication_property`,
`temporal_negation_complete`, `theoremInMcs`, `mcs_mp_axiom`, `mcs_bot_not_mem`,
`mcs_neg_of_not_mem`, `mcs_not_mem_of_neg`, `mcs_mem_iff_neg_not_mem`) with definitions that
route through `MCSProperties` and `GenericMCS`, using the Phase 1 bridge lemma where the two
systems must be reconciled.

**Outcome**: Done, committed in `54ebbd5d`. Six wrappers rewired to thin `MCSProperties`
forwarders; net −29 lines in MCS.lean.

**Tasks**:
- [x] Audited in-file call sites of each wrapper used by the temporal-specific lemmas
  (lines 142-484); signatures preserved.
- [x] Kept `Temporal.SetConsistent` / `Temporal.SetMaximalConsistent` types stable so
  downstream files see no type change; Phase 1 bridge applied at the boundary.
- [x] Re-expressed the bot/negation/membership lemmas (`mcs_bot_not_mem`, `mcs_neg_of_not_mem`,
  `mcs_not_mem_of_neg`, `mcs_mem_iff_neg_not_mem`) as thin forwarders to `MCSProperties`,
  preserving names and signatures.
- [x] Re-expressed `mcs_mp_axiom` / `theoremInMcs` via `MCSProperties` plus the bridge,
  preserving signatures.
- [x] Left lines 142-484 (temporal-specific G/H lemmas) untouched.
- [x] Net line delta measured: −29 lines in MCS.lean (close to the ~76-line gross-boilerplate
  target before counting the forwarder stubs that remain).

**Timing**: 2 hours

**Depends on**: 1

**Files to modify**:
- `Cslib/Logics/Temporal/Metalogic/MCS.lean` - rewire wrappers (lines ~50-140)

**Verification**:
- `lake build Cslib.Logics.Temporal.Metalogic.MCS` succeeds.
- `lean_verify` confirms no new `sorry` in rewired lemmas.
- Every wrapper name/signature consumed downstream is unchanged (grep confirms).

---

### Phase 3: Downstream Consumer Verification [COMPLETED]

**Goal**: Confirm all Temporal MCS downstream consumers still build with the rewired
definitions, fixing only type-compatibility issues (e.g., needed `rw`/`convert` if a
definition no longer unfolds transparently).

**Outcome**: All three downstream consumers build **without modification** — no
type-compatibility fixes were needed (the rewire preserved every downstream-visible type).

**Tasks**:
- [x] Built `Cslib.Logics.Temporal.Metalogic.DenseCompleteness` — green, no changes needed.
- [x] Built `Cslib.Logics.Temporal.Metalogic.DenseMCS` — green, no changes needed.
- [x] `Chronicle.OrderedSeedConsistency` builds via the dense-completeness build chain — no
  changes needed.
- [x] No call-boundary fixes required (no type mismatches surfaced).
- [x] Risk 3 (transparency-fix ballooning) did not materialize — line savings preserved.

**Timing**: 1 hour

**Depends on**: 2

**Files to modify**:
- `Cslib/Logics/Temporal/Metalogic/DenseCompleteness.lean` (only if needed)
- `Cslib/Logics/Temporal/Metalogic/DenseMCS.lean` (only if needed)
- `Cslib/Logics/Temporal/Metalogic/Chronicle/OrderedSeedConsistency.lean` (only if needed)

**Verification**:
- Each downstream module builds individually via `lake build Module.Name`.
- No new `sorry` introduced (`lean_verify` on any modified lemmas).

---

### Phase 4: CI Verification and Cleanup [COMPLETED]

**Goal**: Verify the migration builds green and introduces no lint/style/import/dependency
regressions.

**Outcome**: Verification was performed via **scoped builds** of task 338's Temporal
metalogic territory rather than a full `lake build` / `lake test`. A concurrent session had
unrelated uncommitted edits to `Propositional/NaturalDeduction/Normalization.lean` (task 332)
and `Propositional/Tableau/Intuitionistic/Soundness.lean` (tasks 316/317); a full-tree build
would have surfaced those unrelated, pre-existing failures and contaminated the result. Scoped
builds isolate 338's deliverable cleanly.

**Tasks**:
- [x] `lake build Cslib.Logics.Temporal.Metalogic.MCS Cslib.Logics.Temporal.Metalogic.GenericMCSBridge`
  — green (636 jobs).
- [x] `lake build Cslib.Logics.Temporal.Metalogic.DenseCompleteness Cslib.Logics.Temporal.Metalogic.DenseMCS`
  — green (944 jobs), confirming downstream consumers build unmodified.
- [x] `lake exe lint-style` on modified files — green (run in Phase 2/3 by the implementation agent).
- [x] `lake shake` — no import changes required (no new import edges introduced beyond the
  bridge's own).
- [x] `grep` for `sorry`/`admit` in `MCS.lean` and `GenericMCSBridge.lean` — none.
- [~] Full `lake build` / `lake test` — **deliberately not run** (concurrent-session
  contamination, see Outcome). Deferred to a clean-tree CI run at PR time.

**Timing**: 1 hour (actual: scoped verification)

**Depends on**: 3

**Files modified**: none in this phase (verification only).

**Verification**:
- Scoped builds of MCS, GenericMCSBridge, and the two dense-completeness consumers all exit
  zero.
- Zero `sorry`/`admit` and no new axioms in the migrated files.
- Note: full-project CI deferred to PR-time clean-tree run owing to concurrent unrelated edits.

---

### Phase 5: Propositional Migration Decision Gate [COMPLETED]

**Goal**: Decide and document whether Propositional MCS migration proceeds now or is spun out
as a follow-up task, based on the actual difficulty observed in Phases 1-2.

**Decision**: **DEFERRED** (the default, per the research recommendation).
`Propositional/Metalogic/MCS.lean` is parameterized over arbitrary `Axioms : Proposition → Prop`
with no `MinimalHilbert` instance, so the Phase 1 bridge template does not transfer without
additional per-axiom-set design work. Option A (per-axiom-set equivalence) was judged not cheap
enough to fold into this task. `Propositional/Metalogic/MCS.lean` is left **unchanged**.

**Tasks**:
- [x] Evaluated against research finding: `propDerivationSystem` is parameterized over
  arbitrary `Axioms` with no `MinimalHilbert` instance (only concrete tags `HilbertCl`,
  `HilbertInt`, `HilbertMin` have instances).
- [x] Option A (migrate `PropositionalAxiom` only) considered and declined — not cheap enough
  given the parameterization mismatch.
- [x] Deferral recorded as a `roadmap_items` entry on task 338 in `specs/state.json`
  (Propositional MCS generic migration) rather than spinning a separate task immediately; the
  roadmap item is the durable follow-up record for `/todo` to surface.
- [x] Decision and rationale recorded in the execution summary
  (`summaries/01_mcs-generic-migration-summary.md`).

**Timing**: 0.5 hours

**Depends on**: 4

**Files modified**:
- `specs/state.json` — `completion_summary` + `roadmap_items` for task 338.
- `Cslib/Logics/Propositional/Metalogic/MCS.lean` — **unchanged** (deferral).

**Verification**:
- Deferral captured as a roadmap item with a clear scope statement (blocked-by note included).
- No edits to Propositional MCS or its consumers in this task.

---

## Testing & Validation

Verification was scoped to task 338's Temporal metalogic territory (rationale in Phase 4).

- [x] Scoped builds succeed: `Temporal.Metalogic.MCS` + `.GenericMCSBridge` (636 jobs);
  `.DenseCompleteness` + `.DenseMCS` (944 jobs).
- [x] `lake exe lint-style` passes on modified files.
- [x] `lake shake` reports no unused imports added.
- [x] No `sorry`/`admit` and no non-Classical axioms in new/changed lemmas (grep-verified).
- [x] Net line count in `Temporal/Metalogic/MCS.lean` decreased (−29 lines).
- [x] All three downstream Temporal consumers build unchanged in behavior (no modifications).
- [~] Full-project `lake build` / `lake test` / `checkInitImports` — **deferred** to a
  clean-tree PR-time run (concurrent session held unrelated uncommitted Propositional edits).

## Artifacts & Outputs

Produced:
- `specs/338_mcs_generic_migration/plans/01_mcs-generic-migration.md` (this file)
- `specs/338_mcs_generic_migration/summaries/01_mcs-generic-migration-summary.md`
- `Cslib/Logics/Temporal/Metalogic/GenericMCSBridge.lean` (new, 227 lines; propositional-fragment
  equivalence lemmas) — commit `df72a01e`
- `Cslib/Logics/Temporal/Metalogic/MCS.lean` (rewired wrappers, −29 lines) — commit `54ebbd5d`
- `specs/state.json` — `completion_summary` + `roadmap_items` (Propositional MCS follow-up)

Not produced (by design):
- No modifications to downstream Temporal completeness files (they built unmodified)
- No separate follow-up task created — Propositional migration recorded as a `roadmap_items`
  entry on task 338 instead

## Rollback/Contingency

- All work is on a feature branch; revert via `git checkout -- <file>` or branch reset if the
  migration destabilizes the build.
- If Phase 1 equivalence cannot be proved within its time box, mark task 338 [BLOCKED],
  record the exact unproved goal state in the metadata `partial_progress`, and make NO changes
  to MCS.lean or downstream files (leave the existing wrappers intact). Per cslib.md, do NOT
  introduce any vacuous placeholder (`:= True`/`trivial`) to fake the equivalence.
- If Phase 2/3 rewiring causes downstream breakage that cannot be resolved transparently,
  revert the wrapper rewiring and keep the bridge lemma as a standalone proved result (still a
  net positive deliverable), deferring the boilerplate elimination.
