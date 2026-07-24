# Implementation Plan: Bespoke Keyed S4 Driver — Restructured Phases 3-5 (v2)

- **Task**: 535 - Abstract termination-measure interface for S4/B loop lemma (task 511 Phase 7 follow-on)
- **Status**: [IMPLEMENTING]
- **Effort**: 24 hours remaining (range 18-32); Phases 1-2 (~4h) already landed and committed. Total ~28h.
- **Dependencies**: None (parent 511 Phases 1-6 are landed, frozen, and consumed read-only)
- **Research Inputs**:
  - specs/535_abstract_termination_measure_interface_s4b_loop/reports/01_termination-interface-survey.md
  - specs/535_abstract_termination_measure_interface_s4b_loop/handoffs/01_phase3-5-continuation.md (authoritative technical map for the restructure)
- **Artifacts**: plans/02_keyed-s4-driver-restructured.md (this file)
- **Standards**: plan-format.md; status-markers.md; artifact-management.md; tasks.md
- **Type**: cslib
- **Lean Intent**: true

## Overview

This is a revision (v2) of `plans/01_keyed-s4-driver-plan.md`. Phases 1-2 of v1 landed green
(the `keys`-threaded fuel driver `modalExpandBranchesS4Keyed`/`modalTableauS4Keyed` and the crux
`hintikka_congr_S4`, proved unconditionally — no saturation hypothesis) and are committed on
`main` in `Cslib/Logics/Modal/Tableau/LoopChecking.lean`. They are preserved verbatim below as
`[COMPLETED]`.

The v1 Phases 3-5 were found unimplementable at their estimated size. In-depth source reading
(recorded in the v1 blocker notes and the continuation handoff) established a single structural
obstacle: every landed generic top-loop lemma these phases were modeled on
(`modalExpandBranchesHintikka` in `CompletenessLoop.lean`, `modalExpandBranchesGen_closed_unsatIn`
in `FrameSoundness.lean`) is hard-wired to a **single fixed** `apply : RuleApply Atom` used
identically at every step of its fuel induction, whereas the keyed S4 rule
`modalApplyOneS4Keyed φ₀ keys` genuinely varies per step (`keys` grows monotonically). None of the
generic machinery can be *instantiated* for the keyed driver — a bespoke, keys-threaded analogue
of each apparatus must be built. Additionally, **no** S4 soundness lemma exists anywhere in the
codebase, and `modalFuel φ₀` (K's fuel, v1 Phase 1's provisional choice) is confirmed *not*
provably sufficient for the S4 keyed loop. Remaining work is ~1500-2500 new lines.

This revision restructures the remaining work into the continuation handoff's decomposition,
sized to one agent run per phase (H8-style, ~100-500 lines output each). The two oversized handoff
rows are split: the handoff's `3d` (invariant bundle + step-preservation, ~400-700 lines) becomes
Phases 6 and 7; the handoff's `4` (soundness lemma + top-loop, ~300-500 lines) becomes Phases 9
and 10. Phase labels retain the handoff's `3a`-`3e`/`4`/`5` cross-references in parentheses.

**Definition of done** (unchanged from v1): `instDecidableS4Valid` is a sorry-free, axiom-clean
instance; every new public declaration is `lean_verify`-clean; the live `modalTableauS4`, S5's
`ModalLoopAuxS5w`/`modalExpandBranchesHintikka`, and B's `modalExpandBranchesB` are unchanged and
unregressed; frozen task-511 Phase 1-6 deliverables are byte-unchanged except for consuming
references.

### Research Integration

This revision integrates `handoffs/01_phase3-5-continuation.md` in full as the phase-by-phase
technical map, and carries forward the v1 integration of `reports/01_termination-interface-survey.md`.
The handoff supersedes the survey's Open Question 3 (fuel sufficiency): the survey left it open;
the handoff confirms by direct arithmetic (`modalComplexity φ₀ = 0`:
`modalWorldBoundS4 φ₀ = 2^(2·|Sf|) ≤ 4` exceeds K's `modalWorldBound φ₀ = 1`) that a fresh
`modalFuelS4` is mandatory. The handoff also supersedes the survey's Open Question 1 (crux
provability): the crux `hintikka_congr_S4` was proved unconditionally in Phase 2, easier than the
survey feared. The remaining Open Question 2 (direct keyed-driver soundness) is adopted and split
across Phases 9-10.

### Prior Plan Reference

Supersedes `plans/01_keyed-s4-driver-plan.md`. Phases 1-2 are carried over verbatim as
`[COMPLETED]`; Phases 3-5 of v1 are replaced by Phases 3-11 here. Task 511 Phases 1-6 remain the
landed, frozen assets this plan wires against.

## Goals & Non-Goals

**Goals**:
- Re-derive the four generic combinatorial measure primitives as territory-local `private` lemmas.
- Establish the three per-call measure obligations for `modalApplyOneS4Keyed φ₀ keys`, ∀ `keys`.
- Define `modalFuelS4 φ₀` and prove entry-measure sufficiency; repoint `modalTableauS4Keyed`'s fuel.
- Build the keys-threaded Hintikka-tracking invariant bundle and its single-step preservation lemma.
- Assemble the termination top-loop `modalExpandBranchesS4Keyed_hintikka`.
- Prove the S4 blocked-mint-redirect soundness lemma and the keys-threaded soundness top-loop
  `modalTableauS4Keyed_sound`.
- Land `modalTableauS4Keyed_complete`, `s4Valid_decides`, and `instDecidableS4Valid`, closing
  `Decidable (s4Valid φ)`.

**Non-Goals**:
- Path (a): generalizing `GenericDriver.lean`/`CompletenessLoop.lean`/`Saturation.lean` to thread
  opaque state (explicitly deprioritized by the survey; out of scope).
- Editing `FmpMeasure.lean` — its combinatorial primitives are `private` and out of this task's
  additive-only territory; they are re-derived locally, not called.
- Redefining or replacing the live `modalTableauS4` — it stays as the reference artifact.
- Any edit to frozen Phase 1-6 deliverables beyond consuming them; any change to S5's
  `ModalLoopAuxS5w`/`modalExpandBranchesHintikka` call site or B's `modalExpandBranchesB`.

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Per-call measure obligations (Phase 4) for the non-mint case need new T/S4Rules-dispatch lemmas not yet identified | M | M | Mirror `modalStepBranchS4_preserves_bClosure`'s non-mint branch (landed template); the outputs-subset half is already covered by `modalApplyOneS4Keyed_nonMint_universe_S4` (`LoopChecking.lean:2456`). If a sub-lemma resists, `[BLOCKED]` with the exact `lean_goal`. |
| `modalFuelS4` entry-measure inequality (Phase 5) harder than the `modalExpMeasure_entry_le_fuel` template | M | M | Follow `FmpMeasure.lean:208-247`'s proof shape against `modalWork`'s `|U\b|+|U\e|` form; keep the fuel closed form simple (`3^(2·(modalUniverseS4 φ₀).length + 1)`). |
| Keys-threaded invariant preservation (Phase 7) accumulates more fields than the K/S5/B precedent | M | M | `modalHintikkaClauseGen` carves out ALL box/diamond shapes as vacuous `True`, shrinking the real tracking burden to propositional monotonicity + witness-permanence (both landed arguments). Phase 6 defines the bundle before Phase 7 proves preservation, isolating scope. |
| Soundness mint-redirect lemma (Phase 9) is genuinely new semantic content | H | M | Build from `S4LoopInv.keyLowerBd`/`keysDistinct` (birth key lower-bounds the live relevant set) + the reflexive-transitive frame condition; gate it as its own phase before the soundness top-loop (Phase 10) so the novel content is isolated and `[BLOCKED]`-eligible. |
| A phase cannot close and is tempted toward a `sorry`/placeholder | H | L | Hard constraint: never insert `sorry`/`admit`/vacuous placeholder or an under-scoped theorem statement. Mark the phase `[BLOCKED]` with the exact reached `lean_goal` and stop. |
| Accidental edit/regression of a frozen Phase 1-6 or S5/B deliverable | H | L | Additive-only by construction; run `lean_verify` on `instDecidableS5Valid`, `modalTableauB`, and each frozen lemma after Phases 8 and 11. |
| New public declaration pulls a non-standard axiom | M | L | `lean_verify` each new public declaration; require `propext`/`Classical.choice`/`Quot.sound` only. |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1, 2 | -- |
| 2 | 3, 4, 5, 6, 9 | 1, 2 |
| 3 | 7 | 6 |
| 4 | 8, 10 | 3, 4, 5, 7 (P8); 3, 4, 5, 9 (P10) |
| 5 | 11 | 8, 10, 2 |

Phases within the same wave can execute in parallel. Wave 2 bundles the independent
infrastructure (measure primitives, per-call obligations, fuel, invariant definitions, and the
standalone soundness lemma), each consuming only landed assets. Phases 1-2 are already
`[COMPLETED]` (Wave 1).

### Phase 1: Keyed S4 driver definitions [COMPLETED]

- **Goal:** Define the `keys`-threaded fuel driver and its entry point; compile green with no
  proof obligations discharged yet.
- **Tasks:**
  - [x] Define `modalExpandBranchesS4Keyed` in `LoopChecking.lean`: a `processNext`-style fuel loop
        threading `keys` (plus the `keysWorldsKnown`/`worldsContiguousS4` aux invariants) as extra
        worklist columns alongside `(branch, expanded, acc)`, structurally mirroring
        `modalExpandBranchesGen`/`processNext` (`Saturation.lean:201-243`) and calling the landed
        `modalStepBranchS4Keyed` (`LoopChecking.lean:770`) as the per-branch stepper.
  - [x] Define `modalTableauS4Keyed φ` (`Saturation.lean:363` template): entry branch `F(φ)@0`,
        `keys := []`, fuel `modalFuel φ₀` (provisional — repointed to `modalFuelS4 φ₀` in Phase 5).
  - [x] Do NOT redefine the live `modalTableauS4`; leave it in place as the reference artifact.
  - [x] `lean_build` green; no `sorry`.
- **Timing:** landed (~2h)
- **Depends on:** none
- **Completed:** 2026-07-24 (committed "task 535 phase 1-2: keyed S4 driver definitions + hintikka_congr_S4 crux")
- **Files modified:** `Cslib/Logics/Modal/Tableau/LoopChecking.lean` (additive).

### Phase 2: Congruence gate — `hintikka_congr_S4` (crux) [COMPLETED]

**Resolution note**: the crux resolved unconditionally, with no saturation hypothesis needed
and no dependence on `heq1`. `modalHintikkaSetGen`'s conjunct 2 returns literal `True` at exactly
the two shapes (`F(□φ)@w`/`T(◇φ)@w`) where the keyed and live rules can differ; at every other
shape `modalApplyOneS4Keyed φ₀ keys` falls through to `modalApplyOneS4 φ₀` by the definitional
`| _, _ =>` catch-all (`rfl`), so conjunct 2 evaluates identically for both rules regardless of
`keys` or saturation. The proof is the same case-split + `simp_all` technique as `hintikka_congr`
(`S5Simplification.lean:604`). `lean_verify` confirms `propext`/`Classical.choice`/`Quot.sound`
only.

- **Goal:** Prove that on any branch the keyed and live guards agree on Hintikka-set-hood.
- **Tasks:**
  - [x] State and prove `hintikka_congr_S4`: `modalHintikkaSetGen (modalApplyOneS4Keyed φ₀ keys) b a ↔
        modalHintikkaSetGen (modalApplyOneS4 φ₀) b a`, for any `keys`, modeled on `hintikka_congr`.
  - [x] `lean_verify hintikka_congr_S4` axiom-clean.
- **Timing:** landed (~2h)
- **Depends on:** none
- **Completed:** 2026-07-24 (same commit as Phase 1)
- **Files modified:** `Cslib/Logics/Modal/Tableau/LoopChecking.lean` (additive).

### Phase 3 (handoff 3a): Re-derive generic combinatorial measure primitives [COMPLETED]

- **Goal:** Re-derive, as territory-local `private` lemmas in `LoopChecking.lean`, the four generic
  list-counting facts underpinning the per-step measure decrease. `FmpMeasure.lean`'s copies are
  `private` and out of territory, so they are re-derived (not called).
- **Tasks:**
  - [x] `modalCount_notMem_append_drop` analogue (template `FmpMeasure.lean:2788-2859`, ~70 lines):
        generic over any `BEq`/`LawfulBEq`; copy the proof verbatim into a `private` S4-local lemma.
        *(landed as `modalCount_notMem_append_drop_S4`)*
  - [x] `modalCount_notMem_mono` analogue (`FmpMeasure.lean:2865-2878`, ~15 lines).
        *(landed as `modalCount_notMem_mono_S4`)*
  - [x] `modalWork_drop_linear` analogue (`FmpMeasure.lean:2887-2895`, ~10 lines).
        *(landed as `modalWork_drop_linear_S4`)*
  - [x] `modalWork_drop_persistent` analogue (`FmpMeasure.lean:2904-2922`, ~20 lines).
        *(landed as `modalWork_drop_persistent_S4`)*
  - [x] `lean_build` green; no `sorry`; `lean_verify` each axiom-clean.
- **Completed:** 2026-07-24 (all four `lean_verify`-confirmed `propext`/`Classical.choice`/
  `Quot.sound` only; `lake build Cslib.Logics.Modal.Tableau.LoopChecking` green, no new warnings).
- **Timing:** 2 hours (~150-200 lines, mechanical, low risk)
- **Depends on:** none (consumes only landed public `modalWork`/`modalExpMeasure` defs)
- **Files to modify:** `Cslib/Logics/Modal/Tableau/LoopChecking.lean` (additive; `private` lemmas).
- **Verification:** `lean_goal` no remaining goals on all four; `lean_verify` axiom-clean; frozen
  defs unchanged.

### Phase 4 (handoff 3b): Per-call measure obligations for `modalApplyOneS4Keyed φ₀ keys`, ∀ `keys` [COMPLETED]

- **Goal:** Establish the three raw measure-step hypotheses (`hBranchingLength`/`hPersistentFresh`/
  `hOutputsSubsetUniverse`, template `FmpMeasure.lean:3227-3246`) as S4Keyed analogues, each
  universally quantified over `keys`, so a single lemma serves every step.
- **Tasks:**
  - [x] Case-split as `modalStepBranchS4_preserves_bClosure` does (search that name in
        `LoopChecking.lean` for the template): mint-unblocked / mint-blocked / non-mint.
  - [x] **Mint-unblocked** (reduces to `modalApplyOne` via `modalApplyOneS4Keyed_boxNeg_unblocked_eq`/
        `_diaPos_unblocked_eq`, `LoopChecking.lean:727,749`): reuse `modalApplyOne_persistent_props`/
        `modalApplyOne_branching_length` (`FmpMeasure.lean:3062,3125`) directly.
  - [x] **Mint-blocked** (`.linear []`): all three hold vacuously (empty output, not persistent/branching).
  - [x] **Non-mint** (reduces to `modalApplyOneS4Rules`/`modalApplyOneT`): outputs-subset-universe
        from the landed `modalApplyOneS4Keyed_nonMint_universe_S4` (`LoopChecking.lean:2456`,
        same-file-accessible); prove small `persistentFresh`/`branchingLength` lemmas mirroring the
        T/S4Rules dispatch in `modalStepBranchS4_preserves_bClosure`'s non-mint branch.
        *(landed as `modalApplyOneT_persistentFresh`/`_branchingLength` and
        `modalApplyOneS4Rules_persistentFresh`/`_branchingLength`, composing K's own
        `modalApplyOne_persistent_props`/`_branching_length` with four new freshness facts for the
        T-rule/4-rule propagation helpers: `modalTBoxSelf_fresh`, `modalTDiaNegSelf_fresh`,
        `modalFourBoxProp_fresh`, `modalFourDiaNegProp_fresh`.)*
  - [x] `lean_build` green; no `sorry`; `lean_verify` axiom-clean. If a sub-lemma resists,
        `[BLOCKED]` with exact `lean_goal`.
- **Timing:** 3 hours (~150-300 lines)
- **Depends on:** none (consumes landed `modalApplyOne`/S4Keyed facts)
- **Files to modify:** `Cslib/Logics/Modal/Tableau/LoopChecking.lean` (additive).
- **Verification:** `lean_goal` no remaining goals; `lean_verify` axiom-clean.
- **Completed:** 2026-07-24. Landed (all `private`, additive, in `LoopChecking.lean`):
  `modalTBoxSelf_fresh`, `modalTDiaNegSelf_fresh`, `modalFourBoxProp_fresh`,
  `modalFourDiaNegProp_fresh`, `modalApplyOneT_persistentFresh`, `modalApplyOneT_branchingLength`,
  `modalApplyOneS4Rules_persistentFresh`, `modalApplyOneS4Rules_branchingLength`,
  `modalApplyOneS4Keyed_persistentFresh_S4`, `modalApplyOneS4Keyed_branchingLength_S4`,
  `modalApplyOneS4Keyed_outputsSubsetUniverse_S4` (the three target per-call obligations, each
  `∀ keys`). All `lean_verify`-confirmed `propext`/`Classical.choice`/`Quot.sound` only;
  `lake build Cslib.Logics.Modal.Tableau.LoopChecking` green, zero new warnings, zero `sorry`.

### Phase 5 (handoff 3c): `modalFuelS4` + entry-measure sufficiency + fuel repoint [NOT STARTED]

- **Goal:** Define an S4-specific fuel from `modalUniverseS4 φ₀`'s length and prove the entry
  configuration's measure is within it, then repoint `modalTableauS4Keyed`'s fuel argument.
  CONFIRMED not free: at `modalComplexity φ₀ = 0`, `modalWorldBoundS4 φ₀ ≤ 4` exceeds K's
  `modalWorldBound φ₀ = 1`, so `modalFuel φ₀` is not provably sufficient.
- **Tasks:**
  - [ ] Define `modalFuelS4 φ₀ := 3 ^ (2 * (modalUniverseS4 φ₀).length + 1)` (or similar closed form).
  - [ ] Prove entry-measure ≤ `modalFuelS4 φ₀`, mirroring `modalExpMeasure_entry_le_fuel`'s proof
        shape (`FmpMeasure.lean:208-247`) via `modalWork`'s `|U\b|+|U\e|` form — no K-fuel comparison.
  - [ ] Repoint `modalTableauS4Keyed`'s fuel argument (Phase 1 def) from `modalFuel φ₀` to
        `modalFuelS4 φ₀` (small, safe def edit; the only edit to a Phase-1 declaration).
  - [ ] `lean_build` green; no `sorry`; `lean_verify` axiom-clean.
- **Timing:** 2 hours (~100-150 lines)
- **Depends on:** 1 (edits `modalTableauS4Keyed`'s fuel argument)
- **Files to modify:** `Cslib/Logics/Modal/Tableau/LoopChecking.lean` (additive + one-line fuel repoint).
- **Verification:** `lean_goal` no remaining goals on the entry-measure lemma; `modalTableauS4Keyed`
  recompiles green with the new fuel; `lean_verify` axiom-clean.

### Phase 6 (handoff 3d-i): Keys-threaded Hintikka-tracking invariant bundle [NOT STARTED]

- **Goal:** Define the bespoke keys-threaded analogue of the `ModalLoopInvHintikka` bundle
  (`CompletenessLoop.lean:262-337`) and prove its monotone-field lemmas, WITHOUT yet proving
  full single-step preservation (Phase 7).
- **Tasks:**
  - [ ] Define the invariant structure/predicate threading `keys` as an extra argument, with fields
        analogous to `hintikkaInv`/`eBoxOnlyNeg`/`eBoxNegWitness`/`eDiamondOnlyPos`/`eDiamondPosWitness`.
        Exploit `modalHintikkaClauseGen` (`Completeness.lean:652`) carving ALL box/diamond shapes
        (both signs) as vacuous `True` — the real tracking burden is only propositional shapes +
        box-negative/diamond-positive witness existence.
  - [ ] Prove the propositional-shape field is branch/`acc`-independent
        (`modalApplyOne_fst_eq_of_not_box`-style; landed for K), hence trivially monotone as the
        branch grows.
  - [ ] Prove the witness-existence fields are permanent once recorded (`acc`/`b` only grow — same
        monotonicity argument as K/S5/B's landed fields).
  - [ ] `lean_build` green; no `sorry`; `lean_verify` axiom-clean.
- **Timing:** 3 hours (~250-400 lines)
- **Depends on:** none (definitions + monotonicity consume only landed rules)
- **Files to modify:** `Cslib/Logics/Modal/Tableau/LoopChecking.lean` (additive).
- **Verification:** `lean_goal` no remaining goals on each field lemma; `lean_verify` axiom-clean.

### Phase 7 (handoff 3d-ii): Single-step invariant preservation [NOT STARTED]

- **Goal:** Prove that `modalStepBranchS4Keyed` preserves the Phase 6 invariant bundle from parent
  to every child branch (the `AuxStepPreserved` analogue, `CompletenessLoop.lean:262-337`),
  threading `keys → keys'`.
- **Tasks:**
  - [ ] State the single-step preservation lemma: for each child `b'` produced by
        `modalStepBranchS4Keyed`, the Phase-6 invariant holds at `(b', e', newAcc, keys')` given it
        holds at `(b, e, acc, keys)`.
  - [ ] Carry the bundled hypothesis from `modalStepBranchS4_preserves_S4LoopInv`
        (`LoopChecking.lean:4614-4651`): `S4LoopInv φ₀ b' e' newAcc keys' ∧ keysWorldsKnown b' ∧
        worldsContiguousS4 b'`.
  - [ ] Case-split per rule shape reusing Phase 6's monotone-field lemmas; use an S4Keyed-specific
        `_none_saturated` lemma (~25-line analogue of `modalStepBranchGen_none_saturated`,
        `Completeness.lean:809`) for the saturated case.
  - [ ] `lean_build` green; no `sorry`; `lean_verify` axiom-clean. If it resists, `[BLOCKED]` with
        exact `lean_goal`.
- **Timing:** 3 hours (~200-350 lines)
- **Depends on:** 6
- **Files to modify:** `Cslib/Logics/Modal/Tableau/LoopChecking.lean` (additive).
- **Verification:** `lean_goal` no remaining goals; frozen `modalStepBranchS4_preserves_S4LoopInv`
  unchanged; `lean_verify` axiom-clean.

### Phase 8 (handoff 3e): Top-loop induction — `modalExpandBranchesS4Keyed_hintikka` [NOT STARTED]

- **Goal:** Assemble the termination top-loop: an open branch produced by the keyed driver is a
  Hintikka set for the keyed rule, then bridge to the concrete `modalHintikkaSetS4` form.
- **Tasks:**
  - [ ] Assemble the keyed single-step measure-decrease lemma from Phase 3 primitives + Phase 4
        per-call obligations (the `modalExpMeasure_step_lt_gen` analogue for `modalApplyOneS4Keyed`).
  - [ ] Mirror `modalExpandBranchesHintikka`'s ~250-line structure
        (`CompletenessLoop.lean:1430-1650+`), substituting the keys-threaded stepper (landed),
        invariant (Phase 6-7), fuel (Phase 5), and measure decrease.
  - [ ] On the `none` (saturated) case, dispatch each Hintikka conjunct per-shape as in
        `modalExpandBranchesHintikka`'s proof (`CompletenessLoop.lean:1538-1618`).
  - [ ] Close with `hintikka_congr_S4` (Phase 2) + `modalHintikkaSetS4_eq` (`LoopChecking.lean:3874`)
        to reach the concrete `modalHintikkaSetS4 φ₀ b acc` target.
  - [ ] `lean_build` green; no `sorry`; `lean_verify` axiom-clean. If the induction resists,
        `[BLOCKED]` with exact `lean_goal`.
- **Timing:** 3 hours (~250-400 lines)
- **Depends on:** 3, 4, 5, 7 (and consumes Phase 2 + landed `modalHintikkaSetS4_eq`)
- **Files to modify:** `Cslib/Logics/Modal/Tableau/LoopChecking.lean` (additive).
- **Verification:** `lean_goal` no remaining goals; `lean_verify instDecidableS5Valid`/`modalTableauB`
  regression check passes; `lean_verify` axiom-clean.

### Phase 9 (handoff 4-i): S4 blocked-mint-redirect soundness lemma [NOT STARTED]

- **Goal:** Prove the genuinely-new semantic content: redirecting a blocked mint to an existing
  `wBlock` (instead of minting a fresh world) preserves `branchSatisfiableIn s4FC`. No such lemma
  exists anywhere (confirmed via `grep`); the landed `branchSatisfiableIn_s4FC_boxPos_trans_mem`/
  `_diaNeg_trans_mem` (`FrameSoundness.lean:1085,1106`) cover only persistent 4-rule propagation.
- **Tasks:**
  - [ ] State the redirect-preservation lemma: `wBlock`'s existing valuation already witnesses
        whatever the fresh world would have.
  - [ ] Build it from `S4LoopInv.keyLowerBd` (birth key *lower-bounds* the live relevant set — not
        equality, since relevant sets grow after birth) + `S4LoopInv.keysDistinct` + the reflexive-
        transitive frame condition (`s4FC`, `FrameSoundness.lean:1047`).
  - [ ] `lean_build` green; no `sorry`; `lean_verify` axiom-clean. If it resists, `[BLOCKED]` with
        exact `lean_goal`.
- **Timing:** 3 hours (~150-300 lines; highest-variance soundness phase)
- **Depends on:** 2 (standalone semantic lemma; independent of the measure/top-loop machinery)
- **Files to modify:** `Cslib/Logics/Modal/Tableau/FrameSoundness.lean` or
  `Cslib/Logics/Modal/Tableau/FrameCompleteness.lean` (additive; whichever hosts the `s4FC` context).
- **Verification:** `lean_goal` no remaining goals; `lean_verify` axiom-clean.

### Phase 10 (handoff 4-ii): Keys-threaded soundness top-loop — `modalTableauS4Keyed_sound` [NOT STARTED]

- **Goal:** Prove `modalTableauS4Keyed φ = .closed → s4Valid φ` directly about the keyed driver
  (survey Open Q2), via a bespoke keys-threaded analogue of `modalExpandBranchesGen_closed_unsatIn`
  (`FrameSoundness.lean:731`).
- **Tasks:**
  - [ ] State `modalTableauS4Keyed_sound`, modeled on `modalTableauS5_sound`/`modalTableauB_sound`
        (`FrameCompleteness.lean:1877`).
  - [ ] Build the keys-threaded soundness induction reusing Phase 3-5 measure/fuel infrastructure
        (shared with Phase 8) and the Phase 9 redirect lemma for the guarded minting shapes; assemble
        the persistent arms from the landed `branchSatisfiableIn_s4FC_*` family
        (`FrameSoundness.lean:1085,1106,…`).
  - [ ] `lean_build` green; no `sorry`; `lean_verify` axiom-clean. If it resists, `[BLOCKED]` with
        exact `lean_goal`.
- **Timing:** 2.5 hours (~150-250 lines)
- **Depends on:** 3, 4, 5, 9
- **Files to modify:** `Cslib/Logics/Modal/Tableau/FrameCompleteness.lean` (additive).
- **Verification:** `lean_goal` no remaining goals; `lean_verify` axiom-clean.

### Phase 11 (handoff 5): Completeness + decidability — `s4Valid_decides` / `instDecidableS4Valid` [NOT STARTED]

- **Goal:** Prove completeness and land the `Decidable` instance, closing the task and resuming
  parent 511 Phase 7.
- **Tasks:**
  - [ ] State and prove `modalTableauS4Keyed_complete` (open branch refutes `φ`), modeled on
        `modalTableauS5_complete` (`FrameCompleteness.lean:2336`), wiring: `modalTruthLemmaS4`
        (`FrameCompleteness.lean:232`), `extractModelS4` + `_refl`/`_trans`/`_hasEdge_imp_r`
        (`FrameCompleteness.lean:143-185`), `modalOpenBranchS4_countermodel`
        (`FrameCompleteness.lean:401`), `hintikka_congr_S4` (Phase 2),
        `modalExpandBranchesS4Keyed_hintikka` (Phase 8), and the `rfl` bridge `modalHintikkaSetS4_eq`
        (`LoopChecking.lean:3874`).
  - [ ] Assemble `s4Valid_decides` from soundness (Phase 10) and the completeness dichotomy, modeled
        on `s5Valid_decides` (`FrameCompleteness.lean:2407-2421`).
  - [ ] Register `instDecidableS4Valid`, pointed at the keyed driver (NOT the live `modalTableauS4`).
  - [ ] `lean_verify` each of `modalTableauS4Keyed_complete`, `s4Valid_decides`,
        `instDecidableS4Valid` axiom-clean.
  - [ ] Regression check: `lean_verify instDecidableS5Valid` and `modalTableauB` still axiom-clean;
        frozen Phase 1-6 lemmas unchanged.
- **Timing:** 2.5 hours (~150-250 lines)
- **Depends on:** 8, 10, 2
- **Files to modify:** `Cslib/Logics/Modal/Tableau/FrameCompleteness.lean` (additive:
  `modalTableauS4Keyed_complete`, `s4Valid_decides`, `instDecidableS4Valid`).
- **Verification:** `lean_goal` no remaining goals across all three; each `lean_verify` axiom-clean;
  `instDecidableS5Valid`/`modalTableauB` regression check passes.

## Testing & Validation

- [ ] `lean_build` green after each phase; zero `sorry`, zero `admit`, zero new `axiom`.
- [ ] `lean_verify` on every new public declaration reports only `propext`/`Classical.choice`/
      `Quot.sound`.
- [ ] `Decidable (s4Valid φ)` resolves via `instDecidableS4Valid` (keyed driver).
- [ ] Regression: `instDecidableS5Valid` and `modalTableauB` unchanged and axiom-clean.
- [ ] Frozen task-511 Phase 1-6 deliverables (`S4LoopInv`, `modalStepBranchS4Keyed`,
      `modalStepBranchS4_worldBound`, `modalHintikkaSetS4_eq`) byte-unchanged except consuming
      references.
- [ ] Live `modalTableauS4` and S5's `ModalLoopAuxS5w`/`modalExpandBranchesHintikka` call site
      unchanged.
- [ ] Full CI pipeline (cache/build/checkInitImports/lint/lint-style/shake/mk_all/test) green
      after Phase 11.

## Artifacts & Outputs

- plans/02_keyed-s4-driver-restructured.md (this file)
- Landed (Phases 1-2) in `Cslib/Logics/Modal/Tableau/LoopChecking.lean`:
  `modalExpandBranchesS4Keyed`, `modalTableauS4Keyed`, `hintikka_congr_S4`.
- New in `Cslib/Logics/Modal/Tableau/LoopChecking.lean` (Phases 3-8): four `private` combinatorial
  primitives, per-call measure obligations, `modalFuelS4` + entry-measure lemma, the keys-threaded
  Hintikka invariant bundle + preservation, `modalExpandBranchesS4Keyed_hintikka`.
- New in `Cslib/Logics/Modal/Tableau/FrameSoundness.lean`/`FrameCompleteness.lean` (Phases 9-11):
  the blocked-mint-redirect soundness lemma, `modalTableauS4Keyed_sound`,
  `modalTableauS4Keyed_complete`, `s4Valid_decides`, `instDecidableS4Valid`.
- summaries/02_keyed-s4-driver-summary.md (on implementation completion)

## Rollback/Contingency

- All work is additive: new declarations in `LoopChecking.lean`, `FrameSoundness.lean`, and
  `FrameCompleteness.lean`, plus one one-line fuel-argument repoint in Phase 5. No edits to frozen
  or shared-generic files. Reverting = removing the added declarations (and restoring the fuel
  argument); nothing landed in Phases 1-2 is disturbed.
- Each phase is independently committable at its green milestone (commit-per-green-substep). If a
  phase is `[BLOCKED]`, downstream phases that depend on it stop cleanly with the recorded exact
  `lean_goal`; upstream and parallel phases remain committed.
- If a phase build fails, fix forward (correct the proof); never `git reset --hard`/discard
  uncommitted work to reach green, per the recovery ladder.
- Recommended dispatch mode for the remaining phases: `--hard` (H8 phase-sizing, H9 wrap-up
  discipline), given the ~1500-2500-line remaining scope.
