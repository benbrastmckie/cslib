# Implementation Plan: Task #338 - MCS Generic Migration

- **Task**: 338 - Migrate Propositional and Temporal MCS to GenericMCS framework
- **Status**: [NOT STARTED]
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
`Chronicle/OrderedSeedConsistency.lean`) still building green under full CI.

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

**Tasks**:
- [ ] Confirm prerequisite instances resolve: `InferenceSystem Temporal.HilbertBX`
  (Instances.lean:43) and `ClassicalHilbert HilbertBX` (Instances.lean:212, extends
  `MinimalHilbert`). Use `lean_hover_info` / `#check` to verify.
- [ ] State forward lemma: `temporalDerivationSystem.Deriv Γ φ → algebraicDerivationSystem (S := HilbertBX) |>.Deriv Γ φ`
  for the propositional fragment. Prove by induction on `DerivationTree`, mapping
  axiom/assumption/modus_ponens/weakening to the corresponding `ListDeriv` constructions.
  Necessitation/duality cases are out of scope (fragment restriction).
- [ ] State backward lemma: `algebraicDerivationSystem (S := HilbertBX) |>.Deriv Γ φ → temporalDerivationSystem.Deriv Γ φ`.
  Prove by induction on `ListDeriv`, mapping each constructor to a `DerivationTree`
  constructor via the Hilbert instance's axiom witnesses.
- [ ] Combine into an `Iff` bridge lemma at the propositional fragment.
- [ ] Decide placement: new section in `Temporal/Metalogic/MCS.lean` or a small dedicated
  file `Temporal/Metalogic/GenericMCSBridge.lean` (mirroring the Modal naming). Prefer a
  dedicated file to keep MCS.lean focused.
- [ ] Use `lean_goal` continuously and `lean_multi_attempt` before edits; ensure zero `sorry`
  via `lean_verify` on each new lemma.

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

**Tasks**:
- [ ] Audit in-file call sites of each wrapper used by the temporal-specific lemmas
  (lines 142-484): `mcs_mp_axiom`, `theoremInMcs`, `temporal_closed_under_derivation`,
  `temporal_negation_complete`, etc. Record exact signatures that must be preserved.
- [ ] Keep `Temporal.SetConsistent` / `Temporal.SetMaximalConsistent` as `abbrev`s with
  identical types so downstream files see no type change; if routed through
  `AlgebraicMCS (S := HilbertBX)`, insert the Phase 1 `Iff` bridge at the boundary.
- [ ] Re-express the bot/negation/membership lemmas (`mcs_bot_not_mem`, `mcs_neg_of_not_mem`,
  `mcs_not_mem_of_neg`, `mcs_mem_iff_neg_not_mem`) as thin forwarders to the corresponding
  `MCSProperties` lemmas, preserving names and signatures.
- [ ] Re-express `mcs_mp_axiom` / `theoremInMcs` via `MCSProperties.mcs_mp_axiom` /
  `mcs_theorem_in_mcs` plus the bridge, preserving signatures.
- [ ] Leave lines 142-484 (temporal-specific G/H lemmas) untouched.
- [ ] Measure net line delta; confirm boilerplate reduction (~76 lines target).

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

**Tasks**:
- [ ] Build `Cslib.Logics.Temporal.Metalogic.DenseCompleteness` and resolve any type
  mismatches introduced by the rewire.
- [ ] Build `Cslib.Logics.Temporal.Metalogic.DenseMCS`.
- [ ] Build `Cslib.Logics.Temporal.Metalogic.Chronicle.OrderedSeedConsistency`.
- [ ] For each failure, prefer a localized `show`/`rw [Temporal.SetMaximalConsistent]` fix at
  the call boundary over altering proof structure; record any change.
- [ ] If transparency fixes balloon beyond the line savings (Risk 3 materializes), reconsider
  keeping the wrappers as plain aliases (no algebraic routing) and document the trade-off.

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

### Phase 4: Full CI Verification and Cleanup [NOT STARTED]

**Goal**: Run the full CSLib CI pipeline and resolve lint/style/import/dependency issues
introduced by the migration.

**Tasks**:
- [ ] `lake exe cache get` (fetch Mathlib cache if needed on this branch).
- [ ] `lake build` (full project).
- [ ] `lake exe checkInitImports` (all files import `Cslib.Init`).
- [ ] `lake lint` (environment linters; fix any docBlame/dupNamespace introduced).
- [ ] `lake exe lint-style` (text linters; `--fix` if safe).
- [ ] `lake test` (CslibTests suite).
- [ ] `lake exe mk_all --module` if a new file was added in Phase 1.
- [ ] `lake shake --add-public --keep-implied --keep-prefix` (import minimization).

**Timing**: 1 hour

**Depends on**: 3

**Files to modify**:
- Any file flagged by lint/shake (minimal, mechanical fixes only).
- `Cslib.lean` (barrel) if a new file was added.

**Verification**:
- All CI commands exit zero (or with only pre-existing, unrelated warnings).
- `lake test` passes.

---

### Phase 5: Propositional Migration Decision Gate [NOT STARTED]

**Goal**: Decide and document whether Propositional MCS migration proceeds now or is spun out
as a follow-up task, based on the actual difficulty observed in Phases 1-2.

**Tasks**:
- [ ] Evaluate against research finding: `propDerivationSystem` is parameterized over
  arbitrary `Axioms` with no `MinimalHilbert` instance (only concrete tags `HilbertCl`,
  `HilbertInt`, `HilbertMin` have instances).
- [ ] If a per-axiom-set equivalence (Option A) is cheap given the Phase 1 proof template,
  optionally migrate `Propositional/Metalogic/MCS.lean` for `PropositionalAxiom` only and
  verify `StrongCompleteness.lean`, `IntStrongCompleteness.lean`, `IntLindenbaum.lean`.
- [ ] Otherwise (default, per research recommendation): create a follow-up task
  `propositional_mcs_generic_migration` via `/task`, link it to 338, and leave Propositional
  MCS.lean unchanged.
- [ ] Record the decision and rationale in the execution summary.

**Timing**: 0.5 hours

**Depends on**: 4

**Files to modify**:
- `Cslib/Logics/Propositional/Metalogic/MCS.lean` (only if Option A is chosen)
- `specs/state.json` + `specs/TODO.md` (only if a follow-up task is created)

**Verification**:
- If migrated: `lake build` of Propositional consumers green.
- If deferred: follow-up task exists in TODO.md with a clear scope statement.

---

## Testing & Validation

- [ ] `lake build` (full project) succeeds.
- [ ] `lake exe checkInitImports` passes.
- [ ] `lake lint` reports no new warnings attributable to this change.
- [ ] `lake exe lint-style` passes (or `--fix` applied).
- [ ] `lake test` passes.
- [ ] `lake shake --add-public --keep-implied --keep-prefix` reports no unused imports added.
- [ ] `lean_verify` confirms no `sorry` and no non-Classical axioms in new/changed lemmas.
- [ ] Net line count in `Temporal/Metalogic/MCS.lean` decreased (boilerplate eliminated).
- [ ] All three downstream Temporal consumers build unchanged in behavior.

## Artifacts & Outputs

- `specs/338_mcs_generic_migration/plans/01_mcs-generic-migration.md` (this file)
- `specs/338_mcs_generic_migration/summaries/01_mcs-generic-migration-summary.md` (on completion)
- `Cslib/Logics/Temporal/Metalogic/GenericMCSBridge.lean` (new; equivalence lemmas) OR
  added section in `Cslib/Logics/Temporal/Metalogic/MCS.lean`
- Modified `Cslib/Logics/Temporal/Metalogic/MCS.lean` (rewired wrappers)
- Possibly modified downstream Temporal completeness files
- Possibly a follow-up task for Propositional migration

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
