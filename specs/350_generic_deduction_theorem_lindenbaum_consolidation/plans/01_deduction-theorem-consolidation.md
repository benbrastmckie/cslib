# Implementation Plan: Task #350

- **Task**: 350 - generic_deduction_theorem_lindenbaum_consolidation
- **Status**: [IMPLEMENTING]
- **Effort**: 7 hours
- **Dependencies**: None
- **Research Inputs**: reports/01_generic-dt-lindenbaum-consolidation.md
- **Artifacts**: plans/01_deduction-theorem-consolidation.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: cslib
- **Lean Intent**: false

## Overview

Consolidate the Type-valued deduction theorem of the Temporal and Bimodal logics through the
Foundations generic layer (`algebraic_has_deduction_theorem` + `list_deduction_theorem`),
eliminating the hand-written well-founded-recursion bodies and the `deductionWithMem` helpers
while preserving the public signature of each `deductionTheorem` def so the ~18 raw
`DerivationTree`-producer call sites and all downstream consumers (MCS, Completeness, Chronicle,
TruthLemma, Bundle) keep compiling sorry-free. Temporal reuses its existing pointwise-equivalence
bridge (`temporal_deriv_iff_algebraic`); Bimodal gets a new temporal-style bridge built at
`HilbertTM` / `FrameClass.Base`. Modal and Propositional are explicitly deferred to a follow-up
task because routing them requires new "predicate -> InferenceSystem + MinimalHilbert"
infrastructure (a genuine new abstraction, not a reuse). Definition of done: each phase ends with
the relevant scoped build green and the final phase passes the full CI pipeline (lake build, lake
test, lake exe checkInitImports, lake exe lint-style, lake shake) with zero new axioms and zero
`sorry`.

### Research Integration

This plan is built directly on `reports/01_generic-dt-lindenbaum-consolidation.md`, which corrects
several premises of the original task description:

- **Lindenbaum is already consolidated.** All plain `*_lindenbaum` lemmas (`prop_lindenbaum`,
  `modal_lindenbaum`, `temporal_lindenbaum`, `temporal_lindenbaum_fc`, `bimodal_lindenbaum`)
  already delegate one-line to `Metalogic.set_lindenbaum`. No Lindenbaum work is in scope. The
  remaining `zorn_subset` uses in `Logics/` carry extra structure (R-maximal DCS, restricted/closure
  MCS, prime exclusion) and are correctly out of scope.
- The deduction theorem has **two layers**: a trivial `Prop`-level `HasDeductionTheorem` wrapper,
  and a bulk **Type-valued `deductionTheorem` def** (~150-230 lines, WF recursion on tree height)
  consumed *directly as a raw `DerivationTree` producer* at ~40 call sites. The bulk def **cannot be
  deleted** — it must be re-implemented with the **same signature**, its body delegating to a bridge
  plus the generic `algebraic_has_deduction_theorem`, with `deductionWithMem` removed.
- The generic `algebraic_has_deduction_theorem` only proves the `Prop`-level predicate for
  `algebraicDerivationSystem` (ListDeriv). Transferring it to a logic's tree-based
  `DerivationSystem` requires a pointwise equivalence bridge `treeDS.Deriv Γ φ ↔ algDS.Deriv Γ φ`.
- **Temporal** already has a real, reusable bridge that is independent of the hand proof.
  **Bimodal** at `FrameClass.Base` maps cleanly and can get a temporal-style bridge. Both use fixed
  systems with `InferenceSystem` + `MinimalHilbert` instances in place.
- **Modal/Propositional** are blocked by `Axioms : Proposition -> Prop` predicate polymorphism vs
  `MinimalHilbert` type-keying; recommended scope defers them to a follow-up task.
- Zero-debt is achievable: the bridge round-trip uses `Nonempty.some` (Classical choice) on
  already-`noncomputable` defs — no new axiom, no `sorry`.

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

No roadmap context (`roadmap_path` / `roadmap_flag`) was provided to this planning invocation;
`specs/ROADMAP.md` was not consulted or modified. This task advances the Foundations
generic-metalogic consolidation begun in task 338.

## Goals & Non-Goals

**Goals**:
- Re-implement the Temporal Type-valued `deductionTheorem` (`Temporal/Metalogic/DeductionTheorem.lean:119`)
  via the existing `temporal_deriv_iff_algebraic` bridge, preserving its signature; delete
  `deductionWithMem` (:72) and the WF body; re-prove `temporal_has_deduction_theorem` (:167) through
  the bridge.
- Build a new Bimodal bridge `Cslib/Logics/Bimodal/Metalogic/Core/GenericMCSBridge.lean`
  (`bimodal_deriv_iff_algebraic` + consistency/max-consistency equivalences) at `HilbertTM` /
  `FrameClass.Base`, mirroring the temporal bridge and independent of the bimodal hand proof.
- Re-implement the Bimodal Type-valued `deductionTheorem` (`Bimodal/Metalogic/Core/DeductionTheorem.lean:161`)
  via that bridge, preserving its signature; delete `deductionWithMem` (:83); re-prove
  `bimodalHasDeductionTheorem` (:225).
- Keep all ~18 raw call sites and downstream consumers (Temporal Chronicle/DenseCompleteness;
  Bimodal BXCanonical/TruthLemma, Bundle/WitnessSeed, Frame, Completeness, MaximalConsistent)
  compiling sorry-free.
- End every phase with the relevant scoped build green; end the final phase with the full CI
  pipeline green and zero new axioms / `sorry`.
- Explicitly defer Modal & Propositional to a follow-up task and emit a clear spec for the
  orchestrator to spawn it.

**Non-Goals**:
- No Lindenbaum work (already consolidated; out of scope per research §3).
- No consolidation of Modal or Propositional `deductionTheorem` in this task (deferred; requires new
  `predicate -> InferenceSystem` infrastructure per research §5).
- No change to the `temporal_has_deduction_theorem_fc` / `deductionTheoremFc` variant in
  `DenseMCS.lean` unless a bridge at arbitrary `fc` is trivially available — left as-is (extra
  structure); only verified to still compile.
- No change to the extra-structured Zorn constructions (RestrictedMCS, RRelation R-maximal DCS,
  Min/Int prime extensions).
- No refactor of the Foundations generic layer itself (`ListDeduction`, `GenericMCS`, `Consistency`
  are reused as-is).

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Import cycle: re-implementing `deductionTheorem` to call the bridge while the bridge imports `DeductionTheorem` | H | H | Temporal bridge's `import ...DeductionTheorem` is non-load-bearing (research §4.1); drop it first, then `DeductionTheorem` may import the bridge. For Bimodal, author the new bridge so it never imports `Core/DeductionTheorem.lean` (derive the equivalence from the `InferenceSystem`/`MinimalHilbert` instances directly). |
| Forward direction of bridge fails to reconstruct non-propositional constructors (`necessitation`, `temporal_necessitation`, `temporal_duality`) | H | M | These fire only at empty context; mirror the temporal `deriv_tree_to_list` cases (research §4.1, §6) that bottom out at the inference system. Verify the bridge compiles standalone before deleting any hand body. |
| A raw `deductionTheorem` consumer uses `fc ≠ Base` in Bimodal | M | M | Audit all raw consumers (TruthLemma, WitnessSeed, Frame, Completeness, MaximalConsistent) before deletion; if any use other `fc`, scope deletion to `Base` and keep the general body for those (research §5 subtlety). |
| Signature drift breaks a downstream proof obligation | H | M | Preserve the exact public type signature of each `deductionTheorem`; only the body and `deductionWithMem` change. Re-verify named downstream files per phase. |
| Classical-choice round-trip perceived as new debt | L | L | All four `deductionTheorem` defs are already `noncomputable`; `Nonempty.some` introduces no new axiom or `sorry` (research §8). Confirm with `lean_verify` / `#print axioms` on re-implemented defs. |
| `lake shake` flags now-unused imports after body deletion | M | M | After deleting WF bodies / `deductionWithMem`, run `lake shake --add-public --keep-implied --keep-prefix` and remove imports it reports as unused. |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1, 2 | -- |
| 2 | 3 | 1, 2 |
| 3 | 4 | 1, 2, 3 |

Phases within the same wave can execute in parallel. Phases 1 (Temporal) and 2 (Bimodal bridge
build) touch disjoint directories and may run concurrently.

### Phase 1: Temporal deduction theorem re-implementation via existing bridge [COMPLETED]

**Goal**: Replace the Temporal Type-valued `deductionTheorem` body with a bridge round-trip
(signature preserved), delete `deductionWithMem` and the WF body, and re-prove
`temporal_has_deduction_theorem` through the bridge — Temporal Metalogic and downstream green.

**Tasks**:
- [ ] In `Cslib/Logics/Temporal/Metalogic/GenericMCSBridge.lean`, confirm the
  `import ...Temporal.Metalogic.DeductionTheorem` (line 9) is non-load-bearing for the equivalence,
  then drop it (verify no transitive need) to break the future cycle.
- [ ] Reorder wiring so `Temporal/Metalogic/DeductionTheorem.lean` can import the bridge.
- [ ] Re-implement `deductionTheorem` (`DeductionTheorem.lean:119`) with the **same signature**, body
  = bridge round-trip: `⟨d⟩ -> temporal_deriv_iff_algebraic -> algebraic_has_deduction_theorem
  -> .mpr -> Nonempty.some` (or the def-appropriate shape returning the raw `DerivationTree`).
- [ ] Delete `deductionWithMem` (`DeductionTheorem.lean:72`) and the WF-recursion body.
- [ ] Re-prove `temporal_has_deduction_theorem` (`DeductionTheorem.lean:167`) via
  `rw [temporal_deriv_iff_algebraic] ...; exact algebraic_has_deduction_theorem ...`.
- [ ] Confirm the ~2 raw call sites in `Temporal/Metalogic/Chronicle/Frame.lean:{153,200}` still
  type-check against the preserved signature.
- [ ] Leave `temporal_has_deduction_theorem_fc` / `deductionTheoremFc` in `DenseMCS.lean` unchanged;
  verify it still compiles.
- [ ] `#print axioms` (or `lean_verify`) on the re-implemented `deductionTheorem` to confirm no new
  axiom beyond Classical choice already present.

**Timing**: 2 hours

**Depends on**: none

**Files to modify**:
- `Cslib/Logics/Temporal/Metalogic/GenericMCSBridge.lean` - drop non-load-bearing import.
- `Cslib/Logics/Temporal/Metalogic/DeductionTheorem.lean` - re-implement `deductionTheorem` body,
  delete `deductionWithMem`, re-prove `temporal_has_deduction_theorem`.

**Verification**:
- `lake build Cslib.Logics.Temporal.Metalogic` green.
- Downstream green: `lake build` of Temporal `Completeness`, `Chronicle`, `DenseCompleteness`.
- No `sorry`, no new axiom in re-implemented defs.

---

### Phase 2: Build Bimodal temporal-style bridge [COMPLETED]

**Goal**: Create a new, hand-proof-independent pointwise-equivalence bridge for Bimodal at
`HilbertTM` / `FrameClass.Base`, with consistency/max-consistency equivalences — compiles standalone
with no deletions yet.

**Tasks**:
- [ ] Create `Cslib/Logics/Bimodal/Metalogic/Core/GenericMCSBridge.lean` mirroring the temporal
  bridge structure: forward `deriv_tree_to_list`, backward helpers, and the pointwise
  `bimodal_deriv_iff_algebraic` at `S := Bimodal.HilbertTM` (`InferenceSystem` at
  `Bimodal/ProofSystem/Instances.lean:47`).
- [ ] In the forward direction, reconstruct the non-propositional constructors at empty context:
  `necessitation`, `temporal_necessitation`, `temporal_duality` (7-constructor tree; research §6).
- [ ] Add `bimodal_setConsistent_iff_algebraic` and `bimodal_setMaxConsistent_iff_algebraic`
  mirroring the temporal equivalences.
- [ ] Ensure this new file does **NOT** import `Core/DeductionTheorem.lean` (derive the equivalence
  from the `InferenceSystem`/`MinimalHilbert` instances directly), so Phase 3 can have
  `DeductionTheorem` import the bridge without a cycle.
- [ ] Confirm imports are minimal (anticipate `lake shake`).

**Timing**: 2 hours

**Depends on**: none (independent file; mirrors the *existing* temporal bridge — Wave 1, parallel
with Phase 1).

**Files to modify**:
- `Cslib/Logics/Bimodal/Metalogic/Core/GenericMCSBridge.lean` - **new file**.

**Verification**:
- `lake build Cslib.Logics.Bimodal.Metalogic.Core.GenericMCSBridge` green.
- The bridge file compiles without importing `Core/DeductionTheorem.lean`.
- No `sorry` in the new bridge.

---

### Phase 3: Bimodal deduction theorem re-implementation via new bridge [IN PROGRESS]

**Goal**: Audit `fc = Base` usage, re-implement the Bimodal `deductionTheorem` via the new bridge
(signature preserved), delete `deductionWithMem`, re-prove `bimodalHasDeductionTheorem` — Bimodal
Metalogic + BXCanonical + Bundle green.

**Tasks**:
- [ ] Audit every raw `deductionTheorem` consumer to confirm `fc = Base`:
  `BXCanonical/TruthLemma.lean:102`, `BXCanonical/Completeness/Dense.lean:80`,
  `Core/MaximalConsistent.lean:153`, `Bundle/WitnessSeed.lean:{177,294,412,487}`,
  `Metalogic/Completeness.lean:{92,200,201}`, `BXCanonical/Frame.lean:{210,260,321,...}`.
  If any use `fc ≠ Base`, scope deletion to `Base` and keep the general body for those.
- [ ] Re-implement `deductionTheorem` (`Core/DeductionTheorem.lean:161`) with the **same signature**,
  body = bridge round-trip through `bimodal_deriv_iff_algebraic` + `algebraic_has_deduction_theorem`.
- [ ] Have `Core/DeductionTheorem.lean` import the new bridge (cycle-free per Phase 2).
- [ ] Delete `deductionWithMem` (`Core/DeductionTheorem.lean:83`) and the WF body.
- [ ] Re-prove `bimodalHasDeductionTheorem` (`Core/DeductionTheorem.lean:225`) through the bridge.
- [ ] `#print axioms` / `lean_verify` on the re-implemented def — confirm no new axiom / `sorry`.

**Timing**: 2 hours

**Depends on**: 1, 2

**Files to modify**:
- `Cslib/Logics/Bimodal/Metalogic/Core/DeductionTheorem.lean` - re-implement `deductionTheorem`,
  delete `deductionWithMem`, re-prove `bimodalHasDeductionTheorem`, import the bridge.

**Verification**:
- `lake build Cslib.Logics.Bimodal.Metalogic` green.
- Downstream green: `lake build` of Bimodal `BXCanonical` (TruthLemma, Completeness/Dense, Frame),
  `Bundle` (WitnessSeed), `Metalogic/Completeness`, `Core/MaximalConsistent`.
- No `sorry`, no new axiom in re-implemented defs.

---

### Phase 4: Modal/Propositional deferral, doc correction, follow-up spec, and full CI [NOT STARTED]

**Goal**: Correct the Modal bridge gap-analysis comment, record an explicit follow-up task spec for
the orchestrator to spawn, and pass the full CI pipeline repo-wide with all downstream consumers
sorry-free.

**Tasks**:
- [ ] Update the gap-analysis comment in `Cslib/Logics/Modal/Metalogic/GenericMCSBridge.lean` to note
  that the temporal-style equivalence **is** buildable (the `□(φ→φ)` "counterexample" is derivable in
  `algDS` at `[]`; research §4.2), and point at the follow-up task. Do not add a theorem here.
- [ ] Record the follow-up task spec in the summary / handoff (see "Follow-up task to spawn" below)
  so the orchestrator can spawn it: new `predicate -> InferenceSystem + MinimalHilbert` infrastructure
  (`HilbertOf Axioms` wrapper) + per-predicate bridges to consolidate Modal & Propositional
  `deductionTheorem` (~25 raw call sites must keep compiling).
- [ ] Run `lake shake --add-public --keep-implied --keep-prefix`; remove any imports it reports as
  unused after the Phase 1/3 body deletions.
- [ ] Run full CI: `lake build`, `lake test`, `lake exe checkInitImports`, `lake exe lint-style`,
  `lake shake --add-public --keep-implied --keep-prefix`.
- [ ] Explicitly re-verify the downstream sorry-free consumers listed in research §9: Temporal/Bimodal
  `Completeness`, Bimodal `BXCanonical/TruthLemma` + `Chronicle`, Temporal `Chronicle` +
  `DenseCompleteness`. (Modal/Propositional remain on their existing hand proofs — unchanged.)

**Timing**: 1 hour

**Depends on**: 1, 2, 3

**Files to modify**:
- `Cslib/Logics/Modal/Metalogic/GenericMCSBridge.lean` - correct gap-analysis comment, reference
  follow-up (comment-only; no Lean decls).

**Verification**:
- Full CI pipeline green: `lake build`, `lake test`, `lake exe checkInitImports`,
  `lake exe lint-style`, `lake shake --add-public --keep-implied --keep-prefix`.
- All named downstream consumers compile sorry-free.
- Follow-up task spec captured for the orchestrator.

---

## Follow-up task to spawn (Modal & Propositional)

Note for the orchestrator: spawn a follow-up task after this one completes. Modal and Propositional
`deductionTheorem` cannot be routed through the generic layer without new infrastructure because they
are polymorphic over an `Axioms : Proposition -> Prop` predicate, whereas `algebraicDerivationSystem`
is keyed on a type `S` with `[InferenceSystem S] [MinimalHilbert S]` (research §5).

Proposed follow-up scope:
- Build a `HilbertOf Axioms` wrapper type whose `derivation` is `DerivationTree Axioms []`, with
  `MinimalHilbert` synthesised from the `implyK`/`implyS` witnesses.
- Build per-predicate bridges `propDerivationSystem Axioms .Deriv ↔ algebraicDerivationSystem
  (S := HilbertOf Axioms) .Deriv` (and the modal analogue).
- Re-implement both `deductionTheorem` defs (signatures preserved) and delete the two
  `deductionWithMem`; ~25 raw call sites across Modal `Completeness`/`MCS`/`Systems/{K,D}` and
  Propositional `StrongCompleteness`/`Min,IntLindenbaum`/`NaturalDeduction` must keep compiling.

## Testing & Validation

- [ ] Phase 1: `lake build Cslib.Logics.Temporal.Metalogic` + Temporal Completeness/Chronicle/DenseCompleteness green.
- [ ] Phase 2: `lake build` of the new Bimodal bridge green, standalone, no cycle.
- [ ] Phase 3: `lake build Cslib.Logics.Bimodal.Metalogic` + BXCanonical/Bundle/Completeness/MaximalConsistent green.
- [ ] Phase 4 full CI: `lake build`; `lake test`; `lake exe checkInitImports`; `lake exe lint-style`;
  `lake shake --add-public --keep-implied --keep-prefix`.
- [ ] `#print axioms` on re-implemented `deductionTheorem` defs shows no new axiom beyond pre-existing
  Classical choice; no `sorry` anywhere in changed files.
- [ ] Named downstream consumers (research §9) compile sorry-free.

## Artifacts & Outputs

- `Cslib/Logics/Temporal/Metalogic/DeductionTheorem.lean` (re-implemented def, `deductionWithMem` removed).
- `Cslib/Logics/Temporal/Metalogic/GenericMCSBridge.lean` (import dropped).
- `Cslib/Logics/Bimodal/Metalogic/Core/GenericMCSBridge.lean` (new bridge file).
- `Cslib/Logics/Bimodal/Metalogic/Core/DeductionTheorem.lean` (re-implemented def, `deductionWithMem` removed).
- `Cslib/Logics/Modal/Metalogic/GenericMCSBridge.lean` (corrected gap-analysis comment).
- `specs/350_generic_deduction_theorem_lindenbaum_consolidation/summaries/01_deduction-theorem-consolidation-summary.md` (on implementation).
- Follow-up task spec for Modal/Propositional consolidation (for orchestrator to spawn).

## Rollback/Contingency

- Work is additive-then-subtractive per logic; each phase is an isolated git commit. To revert,
  restore the deleted WF body + `deductionWithMem` from git history and re-add the dropped import —
  the public signatures are unchanged, so reverting a phase does not disturb downstream consumers.
- If the Bimodal bridge forward direction cannot reconstruct a non-propositional constructor, keep the
  hand `deductionTheorem` body for Bimodal (skip Phase 3 deletion), ship Temporal-only consolidation,
  and fold Bimodal into the Modal/Propositional follow-up task.
- If the `fc ≠ Base` audit finds general-`fc` consumers, scope Bimodal deletion to `FrameClass.Base`
  and retain the polymorphic body for other frame classes (no signature change).
- If any phase cannot reach CI-green within one agent run, mark the phase `[PARTIAL]` with the failing
  build target recorded; the next `/implement` resumes from that phase.
