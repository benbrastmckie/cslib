# Implementation Plan: Bespoke Keyed S4 Driver — Close `Decidable (s4Valid φ)`

- **Task**: 535 - Abstract termination-measure interface for S4/B loop lemma (task 511 Phase 7 follow-on)
- **Status**: [PARTIAL]
- **Effort**: 12 hours (range 10-16)
- **Dependencies**: None (parent 511 Phases 1-6 are landed, frozen, and consumed read-only)
- **Research Inputs**: specs/535_abstract_termination_measure_interface_s4b_loop/reports/01_termination-interface-survey.md
- **Artifacts**: plans/01_keyed-s4-driver-plan.md (this file)
- **Standards**: plan-format.md; status-markers.md; artifact-management.md; tasks.md
- **Type**: cslib
- **Lean Intent**: true

## Overview

Close `Decidable (s4Valid φ)` and S4 completeness against `Cube.S4` by building a bespoke,
S4-specific keyed tableau driver — path (b) from the research survey — rather than generalizing
the shared generic driver. The survey establishes three facts that fix this scope: (1) the S4
`keys` list is genuine per-step threaded state that the fixed-`apply` generic driver cannot carry,
(2) B (task 505) and S5 (task 515) already reached decidability via the *state-free* generic
driver, so generalizing it would serve only S4 while risking their landed proofs, and (3) **no**
`modalTableauS4_sound`, `modalTableauS4_complete`, `s4Valid_decides`, or `instDecidableS4Valid`
currently exists — the full soundness + completeness + decidability assembly must be built from
the landed ingredients. All new declarations live in `LoopChecking.lean` (driver defs,
termination top-loop, Hintikka congruence) and `FrameCompleteness.lean` (soundness, completeness,
decidability), mirroring the S5 layout at `FrameCompleteness.lean:2336-2421`. The generic driver
files (`GenericDriver.lean`, `CompletenessLoop.lean`, `Saturation.lean`) and every frozen Phase
1-6 deliverable are consumed read-only, never edited. **Definition of done**: `instDecidableS4Valid`
is a sorry-free, axiom-clean instance; every new public declaration is `lean_verify`-clean; the
existing live `modalTableauS4`, S5's `ModalLoopAuxS5w`/`modalExpandBranchesHintikka`, and B's
`modalExpandBranchesB` are unchanged and unregressed.

### Research Integration

Integrated report `01_termination-interface-survey.md` in full. The plan adopts its recommended
path (b) and its component/precedent map (report "Component map" table) verbatim as the per-phase
target inventory. The plan **reorders** the survey's suggested 5-phase sequence in one respect:
the novel crux `hintikka_congr_S4` (survey Phase 3) is pulled forward to Phase 2 and made
parallel with the driver definitions, because it depends only on the landed rule functions
(`modalApplyOneS4Keyed`, `modalApplyOneS4`, the `heq1` non-minting agreement fact) and **not** on
the new driver loop — gating it early per the task's explicit "gate the crux early" directive
de-risks the whole plan before soundness/completeness effort is spent. The survey's three Open
Questions are assigned to phases: Q1 (crux provability) → Phase 2; Q2 (prove soundness directly
about the keyed driver) → adopted, Phase 4; Q3 (fuel value sufficiency) → Phase 3.

### Prior Plan Reference

No prior plan for task 535. The parent task 511's plan
(`specs/511_s4_loop_checking_termination/plans/01_s4-termination-bound-decidability.md`) is
referenced by the survey for its Planner Decision 2 (shared-beneficiary premise), which the survey
re-evaluated and found no longer holds; this plan therefore does not inherit that decision. Task
511 Phases 1-6 are the landed, frozen assets this plan wires against.

### Roadmap Alignment

No ROADMAP.md consulted for this dispatch (no roadmap flag). This plan advances the S4
decidability line that unblocks parent task 511 Phase 7.

## Goals & Non-Goals

**Goals**:
- Define `modalExpandBranchesS4Keyed` and `modalTableauS4Keyed`, a `keys`-threaded `processNext`-style
  fuel driver around the landed `modalStepBranchS4Keyed`.
- Prove `hintikka_congr_S4`: on a saturated open branch, the keyed and live guards agree on
  Hintikka-set-hood.
- Prove `modalExpandBranchesS4Keyed_hintikka` (termination/open-branch → Hintikka), reusing
  `modalStepBranchS4_preserves_S4LoopInv` and `modalStepBranchS4_worldBound`.
- Prove `modalTableauS4Keyed_sound` and `modalTableauS4Keyed_complete`.
- Land `s4Valid_decides` and `instDecidableS4Valid`, pointed at the keyed driver, closing
  `Decidable (s4Valid φ)`.

**Non-Goals**:
- Path (a): generalizing `GenericDriver.lean`/`CompletenessLoop.lean` to thread opaque state
  (explicitly deprioritized by the survey; out of scope).
- Redefining or replacing the existing live `modalTableauS4` — it stays as the reference artifact
  the `heq1`/`modalHintikkaSetS4_eq` bridges consume.
- Any edit to frozen Phase 1-6 deliverables (`S4LoopInv`, `modalStepBranchS4Keyed`,
  `modalStepBranchS4_worldBound`, `modalHintikkaSetS4_eq`) beyond consuming them.
- Any change to S5's `ModalLoopAuxS5w`/`modalExpandBranchesHintikka` call site or B's
  `modalExpandBranchesB`.

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| `hintikka_congr_S4` fails: keyed-branch saturation does not imply saturation under the live guard at a blocked mint (survey Open Q1) | H | M | Gate it at Phase 2, parallel and early, before soundness/completeness spend. `lean_multi_attempt` the goal before committing. If it resists within budget, mark Phase 2 `[BLOCKED]` with the exact `lean_goal`; downstream Phases 4-5 that depend on it stop cleanly with no wasted work. |
| Fuel value: `modalFuel φ₀` (K's fuel) insufficient for the S4 keyed loop given `modalWorldBoundS4 φ₀ = 2^(2·|Sf|)` (survey Open Q3) | M | M | Confirm fuel sufficiency in Phase 3 against `modalUniverseS4_length_le`/`modalWorldBoundS4`; if K-fuel is short, define an S4-specific fuel local to the keyed driver (does not touch generic defs). |
| Accidental edit/regression of a frozen Phase 1-6 or S5/B deliverable | H | L | Path (b) requires zero edits to them by construction; consume-only. Run `lean_verify` on `instDecidableS5Valid`, `modalTableauB`, and each frozen lemma after Phases 3 and 5 to confirm no regression. |
| A phase cannot close and is tempted toward a `sorry`/placeholder | H | L | Hard constraint: never insert `sorry`/`admit`/vacuous placeholder. Mark the phase `[BLOCKED]` with the exact reached `lean_goal` state and stop. |
| New public declaration pulls a non-standard axiom | M | L | `lean_verify` each new public declaration; require `propext`/`Classical.choice`/`Quot.sound` only. |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1, 2 | -- |
| 2 | 3, 4 | 1 |
| 3 | 5 | 2, 3, 4 |

Phases within the same wave can execute in parallel. Phase 2 (the crux gate) is intentionally
in Wave 1 alongside the driver definitions so the sole novel obligation is resolved or shown
`[BLOCKED]` before any soundness/completeness effort (Waves 2-3) is invested.

### Phase 1: Keyed S4 driver definitions [COMPLETED]

- **Goal:** Define the `keys`-threaded fuel driver and its entry point; compile green with no
  proof obligations discharged yet.
- **Tasks:**
  - [ ] Define `modalExpandBranchesS4Keyed` in `LoopChecking.lean`: a `processNext`-style fuel loop
        threading `keys` (plus the `keysWorldsKnown`/`worldsContiguousS4` aux invariants) as extra
        worklist columns alongside `(branch, expanded, acc)`, structurally mirroring
        `modalExpandBranchesGen`/`processNext` (`Saturation.lean:201-243`) and calling the landed
        `modalStepBranchS4Keyed` (`LoopChecking.lean:770`) as the per-branch stepper.
  - [ ] Define `modalTableauS4Keyed φ` (`Saturation.lean:363` template): entry branch `F(φ)@0`,
        `keys := []`, fuel per Phase 3's confirmed value (start from `modalFuel φ₀`).
  - [ ] Do NOT redefine the live `modalTableauS4`; leave it in place as the reference artifact.
  - [ ] `lean_build` green; no `sorry`.
- **Timing:** 2-3 hours
- **Depends on:** none
- **Files to modify:**
  - `Cslib/Logics/Modal/Tableau/LoopChecking.lean` — add `modalExpandBranchesS4Keyed`,
    `modalTableauS4Keyed` (new declarations only; no edits to frozen defs).
- **Verification:**
  - `lean_build` compiles with the two new definitions present and no `sorry`.
  - `lean_file_outline` shows both new declarations; frozen Phase 1-6 declarations unchanged.

### Phase 2: Congruence gate — `hintikka_congr_S4` (crux) [COMPLETED]

**Resolution note**: the crux resolved unconditionally, with no saturation hypothesis needed
and no dependence on `heq1`. `modalHintikkaSetGen`'s conjunct 2 returns literal `True` at exactly
the two shapes (`F(□φ)@w`/`T(◇φ)@w`) where the keyed and live rules can differ; at every other
shape `modalApplyOneS4Keyed φ₀ keys` falls through to `modalApplyOneS4 φ₀` by the definitional
`| _, _ =>` catch-all (`rfl`), so conjunct 2 evaluates identically for both rules regardless of
`keys` or saturation. The proof is the exact same case-split + `simp_all` technique as
`hintikka_congr` (`S5Simplification.lean:604`). `lean_verify` confirms
`propext`/`Classical.choice`/`Quot.sound` only.

- **Goal:** Prove the sole genuinely-novel obligation: on a saturated open branch, keyed and live
  guards agree on Hintikka-set-hood. This is the gating lemma; `[BLOCKED]`-eligible.
- **Tasks:**
  - [ ] State `hintikka_congr_S4`: `modalHintikkaSetGen (modalApplyOneS4Keyed φ₀ keys) b a ↔
        modalHintikkaSetGen (modalApplyOneS4 φ₀) b a` on a saturated open branch, modeled on
        `hintikka_congr` (`S5Simplification.lean:604`).
  - [ ] Drive the proof from the landed pointwise non-minting agreement `heq1` (call sites
        `LoopChecking.lean:2042, 2470, 2758`): on a saturated branch neither guard mints, so the two
        rules agree at every relevant shape.
  - [ ] Before committing edits, `lean_multi_attempt` the crux goal (and the blocked-mint case in
        particular) to confirm the saturation argument closes.
  - [ ] If the saturated keyed branch does not imply saturation under the live guard at a blocked
        mint (survey Open Q1) and it resists within budget: mark this phase `[BLOCKED]` with the
        exact reached `lean_goal` state; do NOT insert a placeholder.
  - [ ] `lean_verify hintikka_congr_S4` axiom-clean.
- **Timing:** 3-4 hours (crux; highest-variance phase)
- **Depends on:** none (consumes only landed rule functions and `heq1`; independent of Phase 1's
  driver loop)
- **Files to modify:**
  - `Cslib/Logics/Modal/Tableau/LoopChecking.lean` — add `hintikka_congr_S4`.
- **Verification:**
  - `lean_goal` shows no remaining goals for `hintikka_congr_S4`, OR the phase is `[BLOCKED]` with
    the exact goal recorded.
  - `lean_verify` reports only `propext`/`Classical.choice`/`Quot.sound`.

### Phase 3: Termination / Hintikka top-loop — `modalExpandBranchesS4Keyed_hintikka` [BLOCKED]

**BLOCKER** (Phase 3):
- **What failed**: no Lean code was written for this phase (correctly, per the hard constraint
  against partial/placeholder proofs) — the phase was analyzed in depth and found to require
  substantially more original proof engineering than the plan/survey's "nearly free" estimate,
  so implementation was not started until a viable, scoped strategy could be confirmed, and the
  scope confirmed exceeds what remains safely completable in this dispatch.
- **What was tried**: read the full landed precedent this phase is modeled on
  (`modalExpandBranchesHintikka`/`ModalLoopInvHintikka`/`AuxStepPreserved`/`AuxBounds`,
  `CompletenessLoop.lean:229-1650`) and the measure-decrease engine it depends on
  (`modalExpMeasure_step_lt_gen`, `FmpMeasure.lean:3227-3329`, plus its combinatorial core
  `modalCount_notMem_append_drop`/`modalCount_notMem_mono`/`modalWork_drop_linear`/
  `modalWork_drop_persistent`, `FmpMeasure.lean:2788-2922`), and cross-checked the frozen S4Keyed
  ingredients (`modalStepBranchS4Keyed`, `S4LoopInv`, `modalStepBranchS4_worldBound`,
  `modalStepBranchS4_preserves_S4LoopInv`) against them.
- **Why it's stuck** (root cause, confirmed by source reading, not conjecture):
  1. **Every landed top-loop lemma this phase would "instantiate" is hard-wired to a SINGLE
     FIXED `apply : RuleApply Atom` used identically at every step of its fuel induction**
     (`modalExpandBranchesHintikka`'s own `apply` parameter, threaded unchanged through
     `AuxStepPreserved`/`ModalLoopInvHintikka`/the whole induction). The keyed S4 rule
     `modalApplyOneS4Keyed φ₀ keys` is NOT fixed — `keys` grows at every step
     (`modalStepBranchS4Keyed`'s own `keys'` output), so the rule value genuinely differs from
     step to step. `modalExpandBranchesHintikka` cannot be instantiated at this rule at all; a
     bespoke, keys-threaded analogue of the ENTIRE `ModalLoopInvHintikka`/`AuxStepPreserved`
     apparatus (roughly 1400 lines in the K/S5/B precedent) is required, not a substitution port.
  2. **The measure-decrease engine has the same fixed-`apply` shape**
     (`modalExpMeasure_step_lt_gen`'s `apply` parameter), AND its four combinatorial primitives
     (`modalCount_notMem_append_drop`, `modalCount_notMem_mono`, `modalWork_drop_linear`,
     `modalWork_drop_persistent`) are `private` to `FmpMeasure.lean` — outside this task's
     additive-only territory (`LoopChecking.lean`/`FrameCompleteness.lean` only) — so they cannot
     be called and must be re-derived (not merely re-parametrized) inside the territory files.
     These four are, encouragingly, fully generic (no `apply`/`φ0` dependence) and mechanically
     re-derivable (~150-200 lines); the harder remaining part is instantiating the three per-call
     obligations (`hBranchingLength`/`hPersistentFresh`/`hOutputsSubsetUniverse`-style facts) for
     `modalApplyOneS4Keyed φ₀ keys`, universally quantified over `keys` so each step can supply
     its own instantiation — this looks achievable by case-splitting into the mint-unblocked case
     (reduces to `modalApplyOne`, whose analogous facts already exist:
     `modalApplyOne_persistent_props`/`modalApplyOne_branching_length`, `FmpMeasure.lean:3062,
     3125`), the mint-blocked case (`.linear []`, trivially satisfies all three vacuously), and
     the non-mint case (already-landed `modalApplyOneS4Keyed_nonMint_universe_S4`,
     `LoopChecking.lean:2456`, private but same-file-accessible from further code in
     `LoopChecking.lean`).
  3. **Fuel-sufficiency is confirmed NOT free**: comparing growth rates directly (not
     conjecture) — at `modalComplexity φ₀ = 0`, `modalWorldBoundS4 φ₀ = 2^(2·|Sf|) ≤ 2^2 = 4`
     while K's own `modalWorldBound φ₀ = (2·0+1)^(0+1) = 1` — S4's pigeonhole bound EXCEEDS K's at
     small complexity, so `modalFuel φ₀` (K's fuel, independent of `modalWorldBoundS4`) is not
     provably sufficient in general. Confirms survey Open Q3: a fresh `modalFuelS4 φ₀`, defined
     directly from `modalUniverseS4 φ₀`'s length (mirroring `modalExpMeasure_entry_le_fuel`,
     `FmpMeasure.lean:208-247`) rather than reused from `modalFuel`, is the correct fix — this
     requires changing Phase 1's `modalTableauS4Keyed` fuel argument (a small, safe def edit, not
     a redesign).
  4. Given (1)-(3), a **good-faith review of what remains after the measure engine** (item 2)
     shows the Hintikka-tracking invariant itself (`hintikkaInv`/`eBoxOnlyNeg`/`eBoxNegWitness`/
     `eDiamondOnlyPos`/`eDiamondPosWitness`-style fields) is *also* tractable, not merely
     hand-waved: `modalHintikkaClauseGen` carves out **all** box/diamond shapes (both signs) as
     vacuous `True`, so the only real tracking burden is (a) propositional shapes, which are
     branch/`acc`-independent (`modalApplyOne_fst_eq_of_not_box`-style: same argument already
     landed for K) and hence trivially monotone as the branch grows, and (b) the box-negative/
     diamond-positive witness-existence facts, which are permanent once an edge/witness formula
     is recorded (`acc`/`b` only ever grow). None of this is a new mathematical risk; it is
     substantial *transcription volume* (estimated 1000-1500 new lines across the measure engine,
     the keys-threaded invariant bundle, its single-step preservation lemma, and the ~250-line
     top-loop induction itself), which is not safely completable to a fully verified, sorry-free
     state within this dispatch's remaining budget without risking an incomplete or unbuildable
     intermediate state.
- **What is needed**: a dedicated follow-on implementation dispatch (recommend `--hard` with H8
  phase-sizing, decomposed as: 3a — re-derive the four generic combinatorial primitives; 3b —
  establish the three per-call obligations for `modalApplyOneS4Keyed φ₀ keys` (∀ keys); 3c —
  define `modalFuelS4 φ₀` and prove entry-measure sufficiency, adjusting Phase 1's fuel value;
  3d — build the keys-threaded `ModalLoopInvHintikka`-analogue bundle + its single-step
  preservation lemma; 3e — assemble the top-loop induction `modalExpandBranchesS4Keyed_hintikka`
  itself, closing with `hintikka_congr_S4` (Phase 2, already landed) to reach the concrete
  `modalHintikkaSetS4 φ₀ b acc` form). See the continuation handoff
  (`handoffs/01_phase3-5-continuation.md`) for the full technical map.
- **Prohibited workarounds**: no `sorry`/`admit`/vacuous placeholder was inserted; no
  under-scoped theorem statement was committed without proof.

- **Goal:** Prove that an open branch produced by the keyed driver is a Hintikka set for the keyed
  rule — the "nearly free" termination half — by transcribing the generic loop's termination
  reasoning with `keys`/aux-invariants threaded.
- **Tasks:**
  - [ ] State `modalExpandBranchesS4Keyed_hintikka`: open branch ⇒
        `modalHintikkaSetGen (modalApplyOneS4Keyed φ₀ keys) b a`, modeled on the S5 invocation of
        `modalExpandBranchesHintikka` (`FrameCompleteness.lean:2342-2360`) and
        `modalExpandBranchesB_hintikka` (`BDriver.lean:862`).
  - [ ] Carry the bundled induction hypothesis from `modalStepBranchS4_preserves_S4LoopInv`
        (`LoopChecking.lean:4614-4651`): for every child `b'`, `S4LoopInv φ₀ b' e' newAcc keys' ∧
        keysWorldsKnown b' ∧ worldsContiguousS4 b'`.
  - [ ] Discharge fuel-sufficiency using `modalStepBranchS4_worldBound` (`LoopChecking.lean:3806`):
        `modalMaxWorld b < modalWorldBoundS4 φ₀` from `S4LoopInv`; confirm the fuel value chosen in
        Phase 1 suffices (survey Open Q3) against `modalWorldBoundS4 φ₀ = 2^(2·|Sf|)` and
        `modalUniverseS4_length_le`. If K-fuel is short, switch `modalTableauS4Keyed` to an
        S4-local fuel (Phase 1 def edit only).
  - [ ] `lean_verify` axiom-clean; if the loop-induction cannot close within budget, `[BLOCKED]`
        with exact `lean_goal`.
- **Timing:** 2-3 hours
- **Depends on:** 1
- **Files to modify:**
  - `Cslib/Logics/Modal/Tableau/LoopChecking.lean` — add `modalExpandBranchesS4Keyed_hintikka`
    (and, if needed, adjust only the Phase-1 fuel value in `modalTableauS4Keyed`).
- **Verification:**
  - `lean_goal` shows no remaining goals; `lean_verify` axiom-clean.
  - Frozen `modalStepBranchS4_preserves_S4LoopInv`/`modalStepBranchS4_worldBound` unchanged
    (consumed, not edited).

### Phase 4: Soundness — `modalTableauS4Keyed_sound` [BLOCKED]

**BLOCKER** (Phase 4):
- **What failed**: no Lean code was written; analysis found this phase shares Phase 3's
  root-cause family (fixed-`apply` top-loop machinery) plus its own, independent gap.
- **What was tried**: read the soundness top-loop precedent
  (`modalExpandBranchesGen_closed_unsatIn`, `FrameSoundness.lean:731-`), which is (like Phase 3's
  precedent) hard-wired to a single fixed `apply` across its whole fuel induction, so it cannot
  be instantiated at the keys-varying `modalApplyOneS4Keyed φ₀ keys` either. Searched for any
  existing S4 minting-shape soundness lemma (`blockingWorldS4`/`blockingWorldS4Keyed`'s
  redirect-to-existing-world semantics) via `grep` across `FrameSoundness.lean`/`LoopChecking.lean`
  — none exists (confirms the research survey's finding: "No `modalTableauS4_sound` anywhere").
  The landed `branchSatisfiableIn_s4FC_boxPos_trans_mem`/`_diaNeg_trans_mem`
  (`FrameSoundness.lean:1085,1106`) cover only the *persistent* 4-rule propagation arms (T(□φ)@w
  unchanged at a successor), not the guarded minting shapes this phase actually needs.
- **Why it's stuck**: proving that redirecting a blocked mint to an existing `wBlock` (instead of
  minting a genuinely fresh world) preserves `branchSatisfiableIn s4FC` is genuinely new semantic
  content — it must show `wBlock`'s existing valuation already witnesses whatever the fresh
  world would have (using `S4LoopInv.keyLowerBd`: the birth key only *lower-bounds* the live
  relevant set, not equals it, since relevant sets grow after birth) — not an assembly of landed
  pieces. Additionally, the top-loop wrapper needs the same bespoke keys-threaded induction as
  Phase 3 (root cause 1 above applies identically here).
- **What is needed**: (a) a new semantic lemma establishing the blocked-mint redirect preserves
  `branchSatisfiableIn s4FC`, built from `S4LoopInv.keyLowerBd`/`keysDistinct` and the reflexive-
  transitive frame condition; (b) a bespoke keys-threaded soundness top-loop induction mirroring
  `modalExpandBranchesGen_closed_unsatIn`'s structure. Both are appropriately scoped as follow-on
  sub-phases after Phase 3's measure/invariant machinery lands (shared infrastructure). See the
  continuation handoff for the technical map.
- **Prohibited workarounds**: no `sorry`/`admit`/vacuous placeholder was inserted.

- **Goal:** Prove `modalTableauS4Keyed φ = .closed → s4Valid φ` directly about the keyed driver
  (survey Open Q2: direct, avoiding a full driver-equality).
- **Tasks:**
  - [ ] State `modalTableauS4Keyed_sound`, modeled on `modalTableauS5_sound`/`modalTableauB_sound`
        (`FrameCompleteness.lean:1877`).
  - [ ] Assemble from the landed `branchSatisfiableIn_s4FC_*` family (`FrameSoundness.lean:1085,
        1102, …`) and `s4FC`/`s4Valid` (`FrameSoundness.lean:1047, 1051`).
  - [ ] `lean_verify` axiom-clean; `[BLOCKED]` with exact `lean_goal` if it cannot close.
- **Timing:** 2 hours
- **Depends on:** 1
- **Files to modify:**
  - `Cslib/Logics/Modal/Tableau/FrameCompleteness.lean` — add `modalTableauS4Keyed_sound`.
- **Verification:**
  - `lean_goal` no remaining goals; `lean_verify` axiom-clean.

### Phase 5: Completeness + decidability — `s4Valid_decides` / `instDecidableS4Valid` [BLOCKED]

**BLOCKER** (Phase 5)*(deviation: blocked by dependency -- Phase 5 depends on Phases 2 (done), 3
(blocked), and 4 (blocked); it was not independently attempted since its every ingredient
(`modalExpandBranchesS4Keyed_hintikka` from Phase 3, `modalTableauS4Keyed_sound` from Phase 4) is
unavailable)*. No Lean code was written for this phase. See the Phase 3/4 blockers above and the
continuation handoff for the technical map; `modalTableauS4Keyed_complete`/`s4Valid_decides`/
`instDecidableS4Valid` should be attempted only after Phases 3-4 land.

- **Goal:** Prove completeness and land the `Decidable` instance, closing the task and resuming
  parent 511 Phase 7.
- **Tasks:**
  - [ ] State and prove `modalTableauS4Keyed_complete` (open branch refutes `φ`), modeled on
        `modalTableauS5_complete` (`FrameCompleteness.lean:2336`), wiring: `modalTruthLemmaS4`
        (`FrameCompleteness.lean:232`), `extractModelS4` + `_refl`/`_trans`/`_hasEdge_imp_r`
        (`FrameCompleteness.lean:143-185`), `modalOpenBranchS4_countermodel`
        (`FrameCompleteness.lean:401`), `hintikka_congr_S4` (Phase 2),
        `modalExpandBranchesS4Keyed_hintikka` (Phase 3), and the `rfl` bridge `modalHintikkaSetS4_eq`
        (`LoopChecking.lean:3874`).
  - [ ] Assemble `s4Valid_decides` from the soundness (Phase 4) and completeness dichotomy, modeled
        on `s5Valid_decides` (`FrameCompleteness.lean:2407-2421`).
  - [ ] Register `instDecidableS4Valid`, pointed at the keyed driver (NOT the live `modalTableauS4`).
  - [ ] `lean_verify` each of `modalTableauS4Keyed_complete`, `s4Valid_decides`,
        `instDecidableS4Valid` axiom-clean.
  - [ ] Regression check: `lean_verify instDecidableS5Valid` and `modalTableauB` still axiom-clean;
        frozen Phase 1-6 lemmas unchanged.
- **Timing:** 3-4 hours
- **Depends on:** 2, 3, 4
- **Files to modify:**
  - `Cslib/Logics/Modal/Tableau/FrameCompleteness.lean` — add `modalTableauS4Keyed_complete`,
    `s4Valid_decides`, `instDecidableS4Valid`.
- **Verification:**
  - `lean_goal` no remaining goals across all three declarations; each `lean_verify` axiom-clean.
  - `instDecidableS5Valid`/`modalTableauB` regression check passes.

## Testing & Validation

- [ ] `lean_build` green after each phase; zero `sorry`, zero `admit`, zero new `axiom`.
- [ ] `lean_verify` on every new public declaration reports only `propext`/`Classical.choice`/
      `Quot.sound`.
- [ ] `Decidable (s4Valid φ)` resolves via `instDecidableS4Valid` (keyed driver).
- [ ] Regression: `instDecidableS5Valid` and `modalTableauB` unchanged and axiom-clean.
- [ ] Frozen Phase 1-6 deliverables (`S4LoopInv`, `modalStepBranchS4Keyed`,
      `modalStepBranchS4_worldBound`, `modalHintikkaSetS4_eq`) byte-unchanged except for consuming
      references.
- [ ] Live `modalTableauS4` and S5's `ModalLoopAuxS5w`/`modalExpandBranchesHintikka` call site
      unchanged.

## Artifacts & Outputs

- plans/01_keyed-s4-driver-plan.md (this file)
- New declarations in `Cslib/Logics/Modal/Tableau/LoopChecking.lean`:
  `modalExpandBranchesS4Keyed`, `modalTableauS4Keyed`, `hintikka_congr_S4`,
  `modalExpandBranchesS4Keyed_hintikka`.
- New declarations in `Cslib/Logics/Modal/Tableau/FrameCompleteness.lean`:
  `modalTableauS4Keyed_sound`, `modalTableauS4Keyed_complete`, `s4Valid_decides`,
  `instDecidableS4Valid`.
- summaries/01_keyed-s4-driver-summary.md (on implementation completion)

## Rollback/Contingency

- All work is additive: new declarations in `LoopChecking.lean` and `FrameCompleteness.lean`, no
  edits to frozen or shared-generic files. Reverting = removing the added declarations; nothing
  landed is disturbed.
- If Phase 2 (`hintikka_congr_S4`) is `[BLOCKED]`, Phases 4-5 (which depend on it) stop; Phases 1
  and 3 (driver defs + termination top-loop) still land independently and are committable, leaving
  a clean partial state and an exact `lean_goal` for the blocker. Escalate the recorded goal to a
  `--hard` or focused follow-on rather than forcing a placeholder.
- If a phase build fails, fix forward (correct the proof); never `git reset --hard`/discard
  uncommitted work to reach green, per the recovery ladder.
