# Implementation Plan: Corrected-Gate KB5 Tableau Rule, Soundness, and Completeness

- **Task**: 528 - correctedgate_kb5_tableau_rule_soundness_and_completeness
- **Status**: [IMPLEMENTING]
- **Effort**: 14 hours
- **Dependencies**: None (internally). Reuses frozen task-524 deliverables (`modalApplyOneKb5'`, `modalTableauKb5'_sound`, semantic lemma family in `FrameSoundness.lean`) and landed task-525 Phase 1 reachability lemmas (`symmEuclGen_mem_modalKnownWorlds_iff`, `extractModelKb5_root_reach_mem_modalKnownWorlds`) as reference/reuse assets.
- **Research Inputs**:
  - specs/528_correctedgate_kb5_tableau_rule_soundness_and_completeness/reports/01_spawn-analysis.md
  - specs/525_kb5_completeness_and_decidability/reports/02_s5-architecture-investigation.md
- **Artifacts**: plans/01_corrected-gate-kb5-rule.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md, cslib.md, lean4.md, plan-compliance.md, no-task-references-in-deliverables.md
- **Type**: cslib (Lean 4 formal verification)
- **Lean Intent**: false

## Overview

Task 525's Phase 3 truth lemma `modalTruthLemmaKb5` is mathematically FALSE for task 524's frozen
`modalApplyOneKb5'` rule, proven in-repo as `extractModelKb5_nonRoot_boxPos_gap`
(`FrameCompleteness.lean`) with witness `φ₀ = ¬◇◇□p`. The architecture investigation
(`02_s5-architecture-investigation.md`) pins the defect to ONE misplaced boolean gate: the
0-target arm of `modalKb5BoxAllFull` (`FiveSimplification.lean:1535`, dually `modalKb5DiaNegAllFull`
:1552) fires on `w == 0 && clusterNonempty` (trigger-identity) when it must fire on
`clusterNonempty` alone. This plan clones the frozen rule into a corrected-gate sibling
(`modalKb5BoxAllUniv`/`modalKb5DiaNegAllUniv`, dispatcher `modalApplyOneKb5''`, entry point
`modalTableauKb5''` — naming confirmed against repo convention by the implementer), proves its
frame soundness directly against `kb5FC`, proves the now-true truth lemma, and assembles
completeness + decidability. The frozen task-524 rule is left untouched and sits beside the new
rule, exactly as `modalApplyOneKb5'` already sits beside the `modalApplyOneKb5 := modalApplyOneFive`
alias. The extraction `extractModelKb5` (already the total/universal cluster on the connected
edge-touched world set) is reused verbatim; no re-extraction is needed.

Definition of done: `modalTableauKb5''_complete`, `kb5Valid_decides`, `instDecidableKb5Valid`
landed and `lean_verify`-clean (zero sorry, zero new axioms); stale blocker/scope docstrings
reconciled to state completeness as delivered; `ModalFrameSeparation.lean` exercises the new
instance; full CSLib CI pipeline run to completion.

### Research Integration

Both reports are integrated. The S5 architecture investigation is the authoritative root-cause
record and supplies: the exact gate change (Section 2.3), the four-case soundness discharge table
(Section 2.3), the reuse/survival accounting (Section 4.3), and the truth-lemma discharge sketch
(Section 2.3, the `v=0` cluster-nonempty witness argument). The spawn-analysis report confirms this
is a single-task coherent fix (its four sub-parts share files and frozen-524-reuse dependencies)
and enumerates the four semantic soundness obligations with their landed discharges
(`reachable_imp_related_kb5` :1582, `accReachableInv_related_kb5` :1610,
`accReachableInv_kb5_root_refl` :1633, plus the one new `w≠0,v=0` symmetrization one-liner).

### Prior Plan Reference

The prior plan is `specs/525_kb5_completeness_and_decidability/plans/01_kb5-completeness-decidability.md`.
It is a **reference, not a template**: its Phase 3 (`modalTruthLemmaKb5`) and everything downstream
are `[BLOCKED]` precisely because they targeted the frozen rule. Lessons carried forward:
(1) effort calibration — the Five completeness truth lemma is ~190 lines
(`modalTruthLemmaFive`, `FrameCompleteness.lean:2693-2886`), so the KB5 analogue is comparable,
driving per-phase sizing; (2) task 525's landed Phase 1 reachability lemmas survive verbatim and
are reused here; (3) task 525's Phase 2 Hintikka lemmas are pinned to the frozen rule's
trigger-sensitive dichotomy and need mechanical re-derivation (near-copies) against the new rule's
simpler trigger-free dichotomy; (4) unlike task 525, `FiveSimplification.lean` IS in this task's
declared file_scope, so the `_mem_of` insertion lemmas can be placed beside the new dichotomies
without any file-scope escalation.

### Roadmap Alignment

No `roadmap_path` or `roadmap_flag` in the delegation context; no ROADMAP.md consultation was
requested. This task unblocks parent task 525's completeness/decidability deliverable (genuine
pure-KB5 completeness via a rooted symmetric-Euclidean tableau).

## Goals & Non-Goals

**Goals**:
- Land a corrected-gate KB5 rule (`modalKb5BoxAllUniv`/`modalKb5DiaNegAllUniv`, dispatcher
  `modalApplyOneKb5''`, entry `modalTableauKb5''`) whose 0-target box-positive/diamond-negative arm
  fires on `clusterNonempty` alone, with a fresh trigger-free membership dichotomy, `specCore`
  instance, and termination/world bound.
- Land its frame-soundness theorem directly against `kb5FC`, reusing task 524's trigger-agnostic
  semantic lemma family plus one new `w≠0,v=0` symmetrization case.
- Land `modalTruthLemmaKb5` (the truth lemma that was previously false), the re-derived KB5
  Hintikka insertion lemmas it consumes, and the open-branch supply lemmas.
- Land `modalOpenBranchKb5''_countermodel`, `modalTableauKb5''_complete`, `kb5Valid_decides`, and
  `instance instDecidableKb5Valid (φ) : Decidable (kb5Valid φ)`.
- Reconcile stale blocker/scope docstrings (using durable anchors, never task numbers), extend
  `CslibTests/ModalFrameSeparation.lean`, and run the full CSLib CI pipeline.

**Non-Goals**:
- Modifying `modalApplyOneKb5'`, its `RuleApplicationSpecCore` instance, its termination bound
  (`Kb5'WorldInv`), or `modalTableauKb5'_sound` — frozen task-524 deliverables, out of scope.
- Re-extracting the model or building a new cluster-membership bookkeeping device
  (`extractModelKb5` is already the universal cluster; cluster membership IS known-world-ness via
  `accReachableInv`).
- Pursuing handoff fix (ii) (keep trigger-gated rule, change extraction) — a proven dead end per
  the scout-lemma remark (`FrameCompleteness.lean:3507-3511`).
- Touching `extractModelS5` / the S5 completeness route (unaffected by this fix).
- Editing `LoopChecking.lean` (owned by a separate still-partial task).
- Fixing the pre-existing `decide`-reduction kernel stall in `modalExpandBranchesGen`'s fuel
  recursion (`S5Simplification.lean:1959-1963`) — orthogonal; diagnose only, track separately.

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| `specCore` re-derivation for the new rule is heavier than expected (it was the bulk of task 524) | H | M | Phase 2 is isolated to the `specCore`/termination work. `Kb5'WorldInv = FiveWorldInv` by `rfl` (`FiveSimplification.lean:3549`) and the new rule mints NO new worlds (the gate change only adds an existing-world-0 formula, never a fresh child), so the world invariant should carry over. Re-prove only the output-shape arms that differ. Split into 2a/2b if it exceeds ~500 lines/one run. |
| Truth-lemma root box-positive case (`w=0`, cluster `w'=0`) does not close | H | L | Research Section 2.3 gives the exact discharge; the corrected rule's full-cluster + root-reflexive emission is *designed* to cover it. Phase 4 lands the Hintikka insertion lemmas first; Phase 5 consumes them. If it genuinely cannot close, mark Phase 5 `[BLOCKED]` with the exact `lean_goal` state — never a `sorry`. |
| The `v=0` cluster-nonempty witness needs an unstated helper (∃-raw-edge-in-derivation, target known non-root) | M | M | Phase 4 (or the start of Phase 5) explicitly builds/locates this helper: any closure derivation of `.r w 0` contains ≥1 raw edge whose target is known and non-root (`accTargetsKnown`/`accTargetsNeRoot`, cf. `FrameCompleteness.lean:~3497`), supplying the witness. Flag it as a distinct sub-task. |
| Hintikka insertion re-derivation diverges from the near-copy expectation | M | L | Phase 4 mirrors task 525's landed `hintikkaKb5'_box_pos`/`_diamond_neg` (`FrameCompleteness.lean:3409/3449`) with the simpler trigger-free dichotomy; the new dichotomy has strictly fewer cases (trigger dropped), so the port removes rather than adds case work. |
| Pre-existing `decide` kernel stall blocks `lake test` | M | M | Phase 8 explicitly diagnoses whether landing `instDecidableKb5Valid` + `by decide` resolves, sidesteps, or must be reported as still-present; do not silently absorb. Track any residual stall as a separate follow-on concern. |
| Concurrent task leaves `LoopChecking.lean` broken, surfacing in full `lake build` | M | L | Phase 8 reports any `LoopChecking.lean` error not caused by this task as a concurrent-task condition; do NOT edit that file. |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2 | 1 |
| 3 | 3, 4, 6 | 2 |
| 4 | 5 | 4 |
| 5 | 7 | 3, 5, 6 |
| 6 | 8 | 7 |

Phases within the same wave can execute in parallel. **Territory note**: Phases 4 and 6 both add
declarations to `FrameCompleteness.lean` (different sections: 4 in the KB5 Hintikka block, 6 in the
open-branch/entry-point block); if dispatched to separate parallel agents they must be serialized
or given explicit non-overlapping insertion regions to avoid edit conflicts. Phase 3
(`FrameSoundness.lean`) has no file overlap and is freely parallel with 4/6.

All phases obey the following **hard constraints** (per lean4.md, plan-compliance.md, and the task
description): zero `sorry`, zero new axiom declarations, every new public declaration
`lean_verify`-clean (fully-qualified name check). If a phase's proof cannot be completed as
written, mark it `[BLOCKED]` with the reached `lean_goal` state and what is missing — never a
`sorry`, `admit`, or vacuous (`:= True`/`trivial`) placeholder.

---

### Phase 1: Corrected-gate rule definitions + membership dichotomy [COMPLETED]

**Goal**: Land the corrected-gate propagation helpers, the dispatcher, and the trigger-free
membership dichotomy, cloning the frozen `*Full` helpers with the single gate change.

**Tasks**:
- [x] Clone `modalKb5BoxAllFull` (`FiveSimplification.lean:1535`) into `modalKb5BoxAllUniv`,
      changing the 0-target arm gate from `w == 0 && (clusterNonempty)` to `(clusterNonempty)`
      alone. Leave the non-root cluster-dump arm and the mint arms (`T(◇φ)`/`F(□φ)`) UNTOUCHED.
- [x] Clone `modalKb5DiaNegAllFull` (:1552) into `modalKb5DiaNegAllUniv` dually.
- [x] Clone the `modalApplyOneKb5'Prop` dispatcher (:1755) into `modalApplyOneKb5''Prop` /
      `modalApplyOneKb5''`, routing box-positive/diamond-negative shapes through the new `*Univ`
      helpers; keep all other shapes identical to the frozen dispatcher.
- [x] Define the entry point `modalTableauKb5''` (mirror `modalTableauKb5'`, :2133) and its
      `modalTableauKb5''_eq` normalization lemma (mirror :2150) giving
      `modalTableauKb5'' φ = modalTableauGen modalApplyOneKb5'' φ`.
- [x] State the fresh trigger-free membership dichotomy `modalKb5BoxAllUniv_mem` (and dual
      `modalKb5DiaNegAllUniv_mem`): every emitted `x` is fresh and either (target known non-root)
      OR (target `0` with cluster nonempty) — the trigger `w` no longer appears. Add
      `_mem_known`/`_mem_eq` analogues (mirror :1711/:1732) only if downstream phases need them.
      *(deviation: altered -- landed `_mem_eq` (shape-only, no extra hypothesis needed) but
      deliberately did NOT land a `_mem_known` analogue in Phase 1. The frozen `Full` rule's
      `_mem_known` derives `0 ∈ modalKnownWorlds b` for its self-target arm from `w = 0` (baked
      into that arm's gate) plus a caller-supplied `hw : w ∈ modalKnownWorlds b`. The corrected
      `Univ` rule's self-target arm fires for ANY trigger `w`, so `x.label = 0` is no longer tied
      to the trigger being known -- proving `x.label ∈ modalKnownWorlds b` unconditionally for
      this arm requires a genuine "root always known" invariant (`0` is a label of every branch
      reachable from the seed `[F(φ)@0]`, since branches only grow), which is not yet available
      as a local fact at this Prop-level dispatcher lemma. Deferred `_mem_known` (and the
      `modalApplyOneKb5''Prop_boxPos_diaNeg_eq`/`_knownWorlds_step` pair that would consume it --
      themselves Phase-2-territory analogues of `modalApplyOneKb5'Prop_boxPos_diaNeg_eq`/
      `_knownWorlds_step`, not a Phase 1 task) to Phase 2, where the `RuleApplicationSpecCore`
      derivation will surface the correct hypothesis (or `modalUniverse`-level global bound) to
      thread through.*
- [x] `lean_verify` every new declaration (`modalKb5BoxAllUniv_mem`,
      `modalKb5DiaNegAllUniv_mem`, `modalKb5BoxAllUniv_mem_eq`, `modalKb5DiaNegAllUniv_mem_eq`,
      `modalApplyOneKb5''Prop_eq_of_not_boxPos_diaNeg`, `modalApplyOneKb5''`, all mint-shape
      case-split/bridge lemmas, `modalTableauKb5''`, `modalTableauKb5''_eq`) confirmed clean:
      only `propext`/`Quot.sound` axioms, zero `sorry`.

**Timing**: 1.5 hours

**Depends on**: none

**Files to modify**:
- `Cslib/Logics/Modal/Tableau/FiveSimplification.lean` — new `*Univ` helpers, `modalApplyOneKb5''`
  dispatcher, `modalTableauKb5''` entry + `_eq`, dichotomy lemmas (placed beside the frozen KB5
  block, ~1535-1760).

**Verification**:
- `lake build Cslib.Logics.Modal.Tableau.FiveSimplification` succeeds.
- `lean_verify` clean on every new declaration.

---

### Phase 2: specCore instance + termination/world bound [COMPLETED]

**Goal**: Land `modalApplyOneKb5''_specCore` (`RuleApplicationSpecCore`) and the termination/world
bound for the new rule, mirroring `modalApplyOneKb5'_specCore` (`FiveSimplification.lean:2662`) and
`Kb5'WorldInv` (:3539).

**Tasks**:
- [x] Establish `Kb5''WorldInv` (or reuse `Kb5'WorldInv`/`FiveWorldInv` directly): confirm the new
      rule mints no new worlds relative to the frozen rule (the gate change only adds a formula at
      the existing world `0`), so the world invariant coincides — likely `rfl` to `FiveWorldInv`
      exactly as `Kb5'WorldInv_eq` (:3549). Land the `modalMaxWorld_lt_worldBound` analogue
      (mirror :3556) if a fresh name is required.
      *Confirmed rule-independent exactly as predicted: `Kb5''WorldInv := FiveWorldInv` is `rfl`
      (`Kb5''WorldInv_eq`), and `modalMaxWorld_lt_worldBound_of_Kb5''WorldInv` is a free corollary,
      since `modalApplyOneKb5''Prop_boxPos_diaNeg_shape` confirms the propagation shapes never
      mint (same argument `Kb5'WorldInv_eq` already used).*
- [x] Land `modalApplyOneKb5''_specCore : RuleApplicationSpecCore modalApplyOneKb5''` mirroring
      `modalApplyOneKb5'_specCore` (:2662), consuming the Phase 1 dichotomy. Output-shape bounds
      should be unchanged since the emitted set grows by at most the single `@0` formula already
      present in the root-trigger case task 524 handled.
      *(deviation: altered -- the F2 (`outputsSubsetUniverse`) discharge for the self-target arm
      does NOT go through a `modalKnownWorlds b`-membership argument the way the frozen `Full`
      rule's proof does (`modalKb5BoxAllFull_mem_known` + `hlknown : l ∈ modalKnownWorlds b`,
      valid there only because that arm's trigger `w` is forced `= 0`). For the corrected `Univ`
      rule the self-target arm fires for ANY trigger, so `x.label = 0` is no longer tied to the
      trigger's known-ness. Resolved directly and MORE simply than the frozen proof: since
      `WorldIndex := Nat`, `(0 : WorldIndex) ≤ modalWorldBound φ0` holds unconditionally via
      `Nat.zero_le`, so `mem_modalUniverse_of_Five` discharges the self-target case with no
      known-worlds reasoning at all -- confirming the `Full` rule's own docstring aside ("The
      self-target case needs no separate world-bound argument", `FiveSimplification.lean`) that
      the frozen proof itself did not exploit. This also means Phase 1's deferred `_mem_known`
      lemma was never needed at all -- superseded by this direct bound.*
- [x] Land any `_fresh_local`/freshness helper the completeness plumbing consumes (mirror
      `modalApplyOneKb5'_fresh_local`, referenced at `FrameSoundness.lean:~4762`) if it is
      rule-specific. Landed as `modalApplyOneKb5''_fresh_local` (F1 discharge).
- [x] `lean_verify` every new declaration: `modalApplyOneKb5''_specCore`,
      `modalApplyOneKb5''_outputsSubsetUniverse`, `modalMaxWorld_lt_worldBound_of_Kb5''WorldInv`,
      and all F1/F3/F7/F8/F9/F10/F11'/F12' discharge lemmas confirmed clean: only
      `propext`/`Classical.choice`/`Quot.sound` (identical axiom set to the frozen
      `modalApplyOneKb5'_specCore`, i.e. no new axioms), zero `sorry`.

**Timing**: 2 hours

**Depends on**: 1

**Files to modify**:
- `Cslib/Logics/Modal/Tableau/FiveSimplification.lean` — `specCore` instance, world invariant and
  bound, freshness helper (placed beside the frozen analogues, ~2662 and ~3539).

**Verification**:
- `lake build Cslib.Logics.Modal.Tableau.FiveSimplification` succeeds.
- `lean_verify` clean on every new declaration.
- **Split trigger**: if the `specCore` re-derivation exceeds ~500 lines or one agent run, split
  into Phase 2a (world invariant + bound) and Phase 2b (`specCore`); update the wave table.

---

### Phase 3: Frame soundness theorem [COMPLETED]

**Goal**: Land `modalTableauKb5''_sound (φ) (h : modalTableauKb5'' φ = .closed) : kb5Valid φ`,
mirroring `modalTableauKb5'_sound` (`FrameSoundness.lean:~4821`), proved directly against `kb5FC`
(`FrameSoundness.lean:1293`).

**Tasks**:
- [x] Assemble the soundness proof reusing task 524's trigger-agnostic semantic lemma family for
      the four `(trigger w, target v)` cases:
      - `w=0, v≠0`: `reachable_imp_related_kb5` (`FrameSoundness.lean:1582`).
      - `w≠0, v≠0`: `accReachableInv_related_kb5` (:1610).
      - `w=0, v=0`: `accReachableInv_kb5_root_refl` (:1633).
      - `w≠0, v=0` (**new case**): symmetrize `reachable_imp_related_kb5` via `Std.Symm.symm`
        (or the repo's symmetry combinator) — a one-liner. State a small named helper
        (`reachable_imp_related_kb5_symm`) if inline symmetrization is awkward.
      Landed exactly as scoped: `reachable_imp_related_kb5_symm` (one-liner), consumed by
      `modalKb5BoxAllUniv_soundIn`/`modalKb5DiaNegAllUniv_soundIn`'s `lbl ≠ 0` self-target
      sub-case.
- [x] Thread the new `*Univ` emission through the same soundness scaffolding the frozen rule used;
      the corrected 0-target arm now also fires for `w≠0`, which is exactly the case the new
      symmetrization discharges.
      *(deviation: altered/expanded -- assembling `modalTableauKb5''_sound` required re-deriving
      the ENTIRE Kb5' fuel-induction chain (not just the rule-soundness lemmas the task bullets
      above scope), because `modalStepBranchKb5'_preserves_accReachableInv` /
      `modalStepBranchKb5'_preserves_satIn` / `modalExpandBranchesKb5'_closed_unsatIn` are all
      hard-coded to `modalApplyOneKb5'` with no generic/parametric entry point (unlike
      completeness's `RuleApplicationSpecCore` abstraction). Landed the full mirror chain:
      `modalApplyOneKb5''Prop_boxPos_diaNeg_eq`/`_knownWorlds_step` (`FiveSimplification.lean`,
      alongside their Kb5' analogues), `modalStepBranchKb5''_preserves_accReachableInv`,
      `modalStepBranchKb5''_preserves_satIn`, `Kb5''SoundInv` + `modalExpandBranchesKb5''_closed_unsatIn`,
      and the `modalTableauKb5''_sound` capstone (all `FrameSoundness.lean`). Discovered along the
      way: the corrected rule's self-target arm (fires for ANY trigger, not just the root) breaks
      the frozen rule's implicit assumption that the self-target's world `0` is known via the
      trigger's own known-ness -- needed a genuine new "root always known"
      (`(0 : WorldIndex) ∈ modalKnownWorlds b`) invariant, threaded explicitly as a hypothesis
      through the `knownWorlds_step`/`accReachableInv`-preservation/fuel-induction layer (trivial
      to establish and preserve: true at the singleton seed branch, preserved by
      `modalKnownWorlds_mono_append_FS` since branches only grow). This invariant was NOT needed
      by the semantic soundness lemmas (`modalKb5BoxAllUniv_soundIn` et al.) or by
      `modalStepBranchKb5''_preserves_satIn`, since `WorldIndex := Nat` makes the F2-style
      world-bound argument free via `Nat.zero_le` and the semantic root-reflexivity lemma
      (`accReachableInv_kb5_root_refl`) never depended on the trigger being the root in the first
      place -- only the syntactic known-worlds bookkeeping needed it.*
- [x] `lean_verify` the theorem and any helper: `reachable_imp_related_kb5_symm`,
      `modalKb5BoxAllUniv_soundIn`, `modalKb5DiaNegAllUniv_soundIn`,
      `modalApplyOneKb5''Prop_boxPos_diaNeg_eq`, `modalApplyOneKb5''Prop_knownWorlds_step`,
      `modalStepBranchKb5''_preserves_accReachableInv`, `modalStepBranchKb5''_preserves_satIn`,
      `modalExpandBranchesKb5''_closed_unsatIn`, `modalTableauKb5''_sound` all confirmed clean:
      only `propext`/`Classical.choice`/`Quot.sound` (identical to the frozen chain's axiom set,
      `reachable_imp_related_kb5_symm` fully constructive with zero axioms), zero `sorry`.

**Timing**: 1.5 hours

**Depends on**: 2

**Files to modify**:
- `Cslib/Logics/Modal/Tableau/FrameSoundness.lean` — `modalTableauKb5''_sound` and the one new
  symmetrization helper (placed beside the frozen `modalTableauKb5'_sound` and the semantic lemma
  family, ~1582-1640 and ~4821).

**Verification**:
- `lake build Cslib.Logics.Modal.Tableau.FrameSoundness` succeeds.
- `lean_verify` clean; zero sorry, zero new axioms.

---

### Phase 4: Re-derived KB5 Hintikka insertion lemmas [COMPLETED]

**Goal**: Re-derive the full-cluster Hintikka insertion lemmas against the new rule's trigger-free
dichotomy — `modalKb5BoxAllUniv_mem_of`, `modalKb5DiaNegAllUniv_mem_of`, `hintikkaKb5''_box_pos`,
`hintikkaKb5''_diamond_neg` — near-copies of task 525's landed `hintikkaKb5'_box_pos`/`_diamond_neg`
(`FrameCompleteness.lean:3409/:3449`).

**Tasks**:
- [x] Land the `_mem_of` insertion lemmas (`by_contra` direction: if `T(ψ)@w' ∉ b` then it appears
      in `modalKb5BoxAllUniv b ψ w`), mirroring the frozen `modalKb5BoxAllFull_mem_of` pattern.
      Place beside the Phase 1 dichotomies in `FiveSimplification.lean` (in scope — no escalation).
      Landed `modalKb5BoxAllUniv_mem_of`/`modalKb5DiaNegAllUniv_mem_of` exactly as scoped, trigger-
      free (the `w = 0` conjunct dropped from the self-target condition).
- [x] Land `hintikkaKb5''_box_pos`: from a `modalHintikkaSetGen modalApplyOneKb5''` set and
      `T(□ψ)@w ∈ b`, certify `T(ψ)@w' ∈ b` for every cluster world `w'` including the root-reflexive
      `w' = 0` — the case the frozen rule's dichotomy could not cover but the corrected trigger-free
      arm now does.
- [x] Land `hintikkaKb5''_diamond_neg` dually.
- [x] Build/locate the **∃-raw-edge-in-derivation helper** (Risk 3): any closure derivation of
      `(extractModelKb5 b acc).r w 0` contains at least one raw edge whose target is known and
      non-root (via `accTargetsKnown`/`accTargetsNeRoot`, cf. `FrameCompleteness.lean:~3497`),
      supplying the `clusterNonempty` witness the corrected `v=0` arm needs. State it as a named
      lemma so Phase 5 can consume it.
      *(deviation: altered -- landed `extractModelKb5_clusterNonempty_of_reach_root`, simpler than
      the "raw-edge chain" framing anticipated: given `hr : (extractModelKb5 b acc).r w 0` and
      `w ≠ 0`, `w` itself is always a valid `clusterNonempty` witness (known + non-root), derived
      directly from the already-landed `symmEuclGen_mem_modalKnownWorlds_iff`'s `.mpr` direction at
      `(w, 0)` plus the "root always known" invariant `h0` (the same one `FrameSoundness.lean`'s
      fuel induction threads) -- no `accTargetsNeRoot`/raw-edge-chain case analysis needed.*
- [x] Reuse the free generic bridges `hintikka_box_neg_gen`/`hintikka_diamond_pos_gen`
      (`Completeness.lean:~1007-1019`) for box-negative/diamond-positive directions — no new work.
      *(deferred to Phase 5 -- these are consumed at truth-lemma call sites, not declared here.)*
- [x] `lean_verify` every new declaration: `modalKb5BoxAllUniv_mem_of`,
      `modalKb5DiaNegAllUniv_mem_of`, `hintikkaKb5''_box_pos`, `hintikkaKb5''_diamond_neg`,
      `extractModelKb5_clusterNonempty_of_reach_root` all confirmed clean: `propext`/`Quot.sound`
      only (the witness helper fully constructive, zero axioms), zero `sorry`.

**Timing**: 1.5 hours

**Depends on**: 2

**Files to modify**:
- `Cslib/Logics/Modal/Tableau/FrameCompleteness.lean` — `hintikkaKb5''_box_pos`,
  `hintikkaKb5''_diamond_neg`, the ∃-edge helper (KB5 Hintikka block, ~3409-3490).
- `Cslib/Logics/Modal/Tableau/FiveSimplification.lean` — `modalKb5BoxAllUniv_mem_of`,
  `modalKb5DiaNegAllUniv_mem_of` (beside the Phase 1 dichotomies).

**Verification**:
- `lake build Cslib.Logics.Modal.Tableau.FrameCompleteness` succeeds.
- `lean_verify` clean on every new lemma.

---

### Phase 5: Truth lemma `modalTruthLemmaKb5` [COMPLETED]

**Goal**: Land `modalTruthLemmaKb5`, mirroring `modalTruthLemmaFive` (`FrameCompleteness.lean:2693-2886`)
against `extractModelKb5`: for an open Hintikka branch of `modalApplyOneKb5''`, branch membership
and `extractModelKb5`-satisfaction agree at every world and formula, by strong induction on
`modalComplexity`. This is the lemma that was FALSE for the frozen rule and is now TRUE for the
corrected rule.

**Tasks**:
- [x] Port the propositional cases (`imp`/`and`/`or`/`atom`/`bot`) from `modalTruthLemmaFive`,
      substituting the `modalApplyOneKb5''` prop-shape agreement lemma (locate/state the analogue of
      `modalApplyOneKb5'Prop_eq_of_not_boxPos_diaNeg`, `FrameSoundness.lean:~4252`, in a
      `FrameCompleteness`-usable form).
      *Landed `modalApplyOneKb5''_eq_of_prop_shape` (chains the already-landed
      `modalApplyOneKb5''_eq_of_not_mint_shape`/`modalApplyOneKb5''Prop_eq_of_not_boxPos_diaNeg`),
      mirroring `modalApplyOneFive_eq_of_prop_shape` exactly. Propositional cases port verbatim.*
- [x] Box-positive case (`.box ψ`): for `w'` with `(extractModelKb5 b acc).r w w'`, use the landed
      task-525 Phase 1 reachability lemmas `symmEuclGen_mem_modalKnownWorlds_iff` (:3285) and
      `extractModelKb5_root_reach_mem_modalKnownWorlds` (:3310) to place `w'` in the cluster, then
      Phase 4's `hintikkaKb5''_box_pos` to obtain `T(ψ)@w' ∈ b`, then IH. **The crux**: when
      `v = 0`, discharge via Phase 4's ∃-raw-edge helper supplying the `clusterNonempty` witness —
      this is exactly where the frozen rule's gap (`extractModelKb5_nonRoot_boxPos_gap`) dissolves.
      *(deviation: expanded -- the `v = 0` sub-case genuinely splits on the trigger `w`: for
      `w ≠ 0`, Phase 4's `extractModelKb5_clusterNonempty_of_reach_root` supplies the witness
      exactly as scoped; but for `w = 0` (the closure relating the root to ITSELF,
      `(extractModelKb5 b acc).r 0 0`), that Phase 4 lemma does not apply (it requires `w ≠ 0`),
      and no existing lemma covered this residual case. First attempt introduced a NEW abstract
      hypothesis `accEdgeIrrefl` ("raw edges never self-loop, anywhere") -- discovered mid-proof
      to be UNSAFE to assume: witness-reuse (`modalApplyOneKb5''_agree_or_reuse_ne_root`) searches
      `modalKnownWorlds b` for an existing matching formula and does not exclude the trigger's own
      label, so a self-loop via reuse is not structurally ruled out in general. Corrected to reuse
      the ALREADY-ESTABLISHED, provably-true `accTargetsNeRoot` hypothesis instead (raw edges never
      *target* the root specifically -- true because `witnessWorldFive`'s search explicitly
      excludes `0` and mint targets are always fresh, hence non-root; the SAME fact Five's Phase 21
      already fully proved discharges, directly reusable since Kb5'''s mint arms are verbatim
      Five's per Phase 1). Landed `euclGen_symmGen_exists_base` (any `EuclGen (SymmGen r) a b`
      derivation contains a genuine base edge SOMEWHERE, unconditionally -- trivial induction
      through the `eucl` case, no side conditions on `r` needed) and
      `extractModelKb5_clusterNonempty_of_root_selfRelate` (extracts the witness from whichever
      symmetrized direction of that base edge actually fired, using `hTgt`+`hRoot` alone, no
      `hSrc` needed). `modalTruthLemmaKb5`'s signature thus adds `hRoot : accTargetsNeRoot acc`
      alongside `hSrc`/`hTgt`/`h0`/`hH`, discharge deferred to Phase 6/7 via a Kb5''-specific
      top-loop propagation mirroring Five's Phase 21 (`modalApplyOneFive_edge_target_ne_root` /
      `modalStepBranchFive_preserves_accTargetsNeRoot` / `modalExpandBranchesFive_openBranch_
      accTargetsKnown_and_NeRoot`), substituting the Kb5''-specific bridges
      (`modalApplyOneKb5''_agree_or_reuse_ne_root`, `modalApplyOneKb5''Prop_knownWorlds_step`)
      already landed in Phases 1-3.)*
- [x] Box-negative / diamond-positive cases: reuse `hintikka_box_neg_gen`/`hintikka_diamond_pos_gen`
      + `extractModelKb5_hasEdge_imp_r` (:3268), mirroring the Five arms.
      *Landed verbatim as scoped, no KB5-specific work needed.*
- [x] Diamond-negative case: dual to box-positive, via `hintikkaKb5''_diamond_neg`.
      *Landed as the dual of the box-positive case, same `hIrr`-based residual-case handling.*
- [x] `lean_verify` the lemma.
      *`modalTruthLemmaKb5` confirmed clean: `propext`/`Classical.choice`/`Quot.sound` only
      (identical to the frozen chain's axiom set -- no new axioms), zero `sorry`. Also verified
      `modalApplyOneKb5''_eq_of_prop_shape` and `extractModelKb5_clusterNonempty_of_root_selfRelate`
      clean. Scoped build (`lake build Cslib.Logics.Modal.Tableau.FrameCompleteness`) green.*

**Timing**: 2.5 hours

**Depends on**: 4

**Files to modify**:
- `Cslib/Logics/Modal/Tableau/FrameCompleteness.lean` — `modalTruthLemmaKb5` (placed after the KB5
  Hintikka lemmas, mirroring where `modalTruthLemmaFive` sits relative to its Hintikka lemmas).

**Verification**:
- `lake build Cslib.Logics.Modal.Tableau.FrameCompleteness` succeeds.
- `lean_verify` clean; zero sorry.
- If the root box-positive `v=0` case cannot close: mark `[BLOCKED]`, record the exact `lean_goal`
  state and the missing fact, do NOT insert a placeholder.

---

### Phase 6: Open-branch supply lemmas for the new rule [IN PROGRESS]

**Goal**: Land the entry-point plumbing the completeness theorem consumes for `modalApplyOneKb5''`,
mirroring the Five supply lemmas invoked inside `modalTableauFive_complete`
(`FrameCompleteness.lean:~3140-3184`): a `modalHintikkaSetGen modalApplyOneKb5''` producer (Hintikka
lift), `accSourcesKnown`, and a KB5 `accTargetsKnown` open-branch preservation analogue.

**Tasks**:
- [ ] Hintikka lift for `modalApplyOneKb5''`: instantiate the generic `modalExpandBranchesHintikka`
      with `modalApplyOneKb5''_specCore` (Phase 2) and a `ModalLoopAuxKb5''` loop invariant +
      step-preservation + bounds. Leverage the Phase 2 world invariant (coinciding with
      `FiveWorldInv`) to reuse Five's bound machinery; re-prove only the arms where the new rule's
      propagation differs.
      *NOT YET STARTED -- see handoff `handoffs/02_phase5-complete-phase6-continuation.md` for the
      full analysis. This is genuinely the single largest remaining piece of work in the plan
      (estimated 300-500+ lines mirroring `modalApplyOneFive_worldGrowth` (~90 lines) and
      `modalStepBranchFive_preserves_worldInv` (~220 lines), both rule-specific tag-counting
      bookkeeping that does not transfer via the mint-arm agreement lemmas the way Phase 4/6.2's
      work did, because `FiveWorldInv`'s termination measure needs a TIGHT per-step growth
      argument, not just the `outputsSubsetUniverse` catalog-membership bound Phase 2 already
      landed).*
- [x] `accSourcesKnown`: apply the generic `modalExpandBranchesGen_openBranch_accSourcesKnown` with
      `modalApplyOneKb5''` + the Phase 2 freshness helper — this bridge is generic in the rule and
      should apply directly.
      *(deviation: altered -- confirmed this bridge is fully generic and needs NO new declaration
      in this file; it applies directly at the Phase 7 assembly site with
      `modalApplyOneKb5''_fresh_local` (Phase 2). No task-6-specific lemma landed for this bullet;
      documented here as verified-free rather than landed.)*
- [x] `accTargetsKnown`: build a `modalExpandBranchesKb5''_openBranch_accTargetsKnown` analogue via
      a `modalStepBranchKb5''_preserves_accTargetsKnown` step lemma. (NeRoot is not required by the
      truth lemma — KB5's root is in the cluster.)
      *(deviation: altered -- TWO corrections to this bullet's own premises, both discovered during
      Phase 5: (1) `accTargetsKnown` alone is ALSO fully generic (`modalExpandBranchesGen_open
      Branch_accTargetsKnown`, `BDriver.lean`), needing no bespoke lemma either; (2)
      **`accTargetsNeRoot` IS required** by `modalTruthLemmaKb5` after all -- the plan's own
      parenthetical ("NeRoot is not required... KB5's root is in the cluster") is now stale: Phase
      5's residual `w=0` self-relate case (`extractModelKb5_clusterNonempty_of_root_selfRelate`)
      needed `accTargetsNeRoot` as a genuine new hypothesis (see Phase 5's own second deviation
      note for the full "why", including why the FIRST attempt at fixing this, an unsafe
      `accEdgeIrrefl` hypothesis, was corrected). Landed the full bespoke top-loop propagation
      mirroring Five's Phase 21 exactly, EXTENDED with root-known-ness as a third bundled
      invariant (since `modalApplyOneKb5''Prop_knownWorlds_step`, Phase 3, needs `h0` too):
      `modalKnownWorlds_fold_spec_C`/`mem_modalKnownWorlds_C`/`modalKnownWorlds_mono_append_C`
      (local re-derivations), `modalStepBranchGen_knownWorlds_mono_C` (generic new-branches-are-
      prepend helper), `hasEdge_addEdge_cases_C`/`modalNextWorld_ne_zero_C` (local re-derivations),
      `modalApplyOneKb5''_edge_target_ne_root`, `modalStepBranchKb5''_preserves_accTargetsNeRoot`,
      `modalStepBranchKb5''_preserves_accTargetsKnown_and_NeRoot_and_rootKnown`, and the top-loop
      `modalExpandBranchesKb5''_openBranch_accTargetsKnown_and_NeRoot_and_rootKnown`. All
      `lean_verify`-clean, zero sorry, identical axiom profile.*
- [ ] `lean_verify` every new declaration.
      *Done for all Phase 6.2 (accTargetsNeRoot+rootKnown) declarations; the Hintikka-lift
      declarations (Phase 6.1 per the handoff's numbering) remain to be landed and verified.*

**Timing**: 2 hours (revised estimate: 2 hours actual for the accTargetsNeRoot+rootKnown piece
landed so far; the still-outstanding Hintikka lift is now estimated at 3-5 hours given its true
scope, discovered only once `modalApplyOneFive_worldGrowth`/`modalStepBranchFive_preserves_
worldInv`'s actual size and rule-specific-bookkeeping depth were read in full)

**Depends on**: 2

**Files to modify**:
- `Cslib/Logics/Modal/Tableau/FrameCompleteness.lean` — Hintikka-lift instantiation (still
  outstanding), `accTargetsNeRoot`+root-known-ness top-loop propagation (landed, entry-point/
  open-branch block, distinct from the Phase 4 Hintikka block).

**Verification**:
- `lake build Cslib.Logics.Modal.Tableau.FrameCompleteness` succeeds (true for all landed pieces).
- `lean_verify` clean on every new lemma (true for all landed pieces).
- **Split trigger, exercised**: the `ModalLoopAuxKb5''` loop invariant + preservation piece
  (Hintikka lift) is split into its own continuation session per the handoff above -- the
  accTargetsNeRoot+rootKnown piece (originally scoped under the plan's `accTargetsKnown` bullet)
  is fully landed and verified in this session.

---

### Phase 7: Completeness + decidability assembly [NOT STARTED]

**Goal**: Assemble the countermodel wrapper, the completeness theorem wired through the
`modalTableauKb5''` entry point, and the decidability instance.

**Tasks**:
- [ ] `modalOpenBranchKb5''_countermodel`: thin wrapper mirroring `modalOpenBranchFive_countermodel`
      (`FrameCompleteness.lean:~2886`), returning the `extractModelKb5` Kripke countermodel by
      invoking `modalTruthLemmaKb5` (Phase 5) at `F(φ)@0`, with `extractModelKb5_rightEuclidean`
      (:3249) + `extractModelKb5_symm` (:3259) discharging `kb5FC` for free.
- [ ] `modalTableauKb5''_complete (φ₀) (h : kb5Valid φ₀) : modalTableauKb5'' φ₀ = .closed`: mirror
      `modalTableauFive_complete` (:~3131-3198), substituting `modalApplyOneKb5''`, the Phase 6
      supply lemmas, `modalOpenBranchKb5''_countermodel`, and `kb5FC`. Use `modalTableauKb5''_eq`
      (Phase 1) to normalize the entry point to `modalTableauGen modalApplyOneKb5''`.
- [ ] `kb5Valid_decides (φ₀) : modalTableauKb5'' φ₀ = .closed ↔ kb5Valid φ₀ :=
      ⟨modalTableauKb5''_sound φ₀, modalTableauKb5''_complete φ₀⟩`, mirroring `fiveValid_decides`
      (:3203), pairing Phase 3 soundness with Phase 7 completeness.
- [ ] `instance instDecidableKb5Valid (φ₀) : Decidable (kb5Valid φ₀)`, mirroring
      `instDecidableFiveValid` (:3213): match on `modalTableauKb5'' φ₀`.
- [ ] `lean_verify` all four declarations.

**Timing**: 1.5 hours

**Depends on**: 3, 5, 6

**Files to modify**:
- `Cslib/Logics/Modal/Tableau/FrameCompleteness.lean` — the four declarations, placed where the
  stale Phase 3 Blocker note currently sits (to be reconciled in Phase 8).

**Verification**:
- `lake build Cslib.Logics.Modal.Tableau.FrameCompleteness` succeeds.
- `lean_verify` clean; zero sorry, zero new axioms.
- Sanity: `#eval`/`by decide` behavior on a small known-`kb5Valid` / known-non-`kb5Valid` formula
  (subject to the pre-existing kernel stall, diagnosed in Phase 8).

---

### Phase 8: Documentation reconciliation + regression tests + full CI [NOT STARTED]

**Goal**: Reconcile every stale framing that describes KB5 completeness as blocked/open now that it
is delivered, extend the separation test, diagnose the orthogonal `decide` stall, and run the full
CSLib CI pipeline. Keep the scout/gap lemmas as documentation of the design constraint the new rule
satisfies — do NOT delete or reframe them as open blockers.

**Tasks**:
- [ ] Reconcile the `## Phase 3 Blocker` note and the `## 5 / KB5 (Euclidean) Coverage via the S5
      Route` docstring (`FrameCompleteness.lean:~565`) to state KB5 completeness as delivered via
      `modalTableauKb5''_complete`. Keep `extractModelKb5_root_reach_scout` and
      `extractModelKb5_nonRoot_boxPos_gap` as documentation of WHY the corrected gate is required.
- [ ] Update the "completeness is deferred to a follow-on task" note in `FiveSimplification.lean`
      (~1424-1443) to state it as delivered.
- [ ] Update the "KB5's completeness specifically remains open" sentence in the `## Scope Note:
      Pure-K5 / Pure-5` block in `S5Simplification.lean` (~2037+) to state completeness as delivered,
      referencing `modalTableauKb5''_complete`.
- [ ] **MUST NOT** cite ephemeral task numbers in the reconciled `.lean` prose per
      no-task-references-in-deliverables.md — use durable anchors (declaration names, section
      headings). Replace any existing task-number mentions in rewritten docstrings with durable
      anchors where practical.
- [ ] Extend `CslibTests/ModalFrameSeparation.lean` (lines ~14-43): exercise `instDecidableKb5Valid`
      / `by decide` where appropriate, and update the docstring framing that says the instance "is
      not yet landed" / `kb5Valid` "has no `Decidable` instance yet".
- [ ] Diagnose the pre-existing `decide`-reduction kernel stall (`modalExpandBranchesGen` fuel
      recursion, `S5Simplification.lean:1959-1963`): determine whether landing
      `instDecidableKb5Valid` + `by decide` **resolves**, **sidesteps**, or **must be explicitly
      documented** as still-present. If it persists, document precisely; do not silently absorb, and
      do not fold a fix for it into this task.
- [ ] Run the full CI pipeline in order (cslib.md): `lake build`, `lake exe checkInitImports`,
      `lake lint`, `lake exe lint-style`, `lake test`,
      `lake shake --add-public --keep-implied --keep-prefix`.
- [ ] If `lake build` surfaces `LoopChecking.lean` errors NOT caused by this task, report them as a
      concurrent-task condition — do NOT edit `LoopChecking.lean`.
- [ ] Final `lean_verify` sweep on all new public declarations (zero sorry, zero new axioms).

**Timing**: 1.5 hours

**Depends on**: 7

**Files to modify**:
- `Cslib/Logics/Modal/Tableau/FrameCompleteness.lean`
- `Cslib/Logics/Modal/Tableau/FiveSimplification.lean`
- `Cslib/Logics/Modal/Tableau/S5Simplification.lean`
- `CslibTests/ModalFrameSeparation.lean`

**Verification**:
- Full CI pipeline passes (or any failure is attributable and reported as a concurrent-task
  condition, not this task's changes).
- `lake test` covers the new `by decide` `kb5Valid` check (or the residual stall is explicitly
  documented).

## Testing & Validation

- [ ] `modalTableauKb5''_sound`, `modalTruthLemmaKb5`, `modalTableauKb5''_complete`,
      `kb5Valid_decides`, `instDecidableKb5Valid` all build and are `lean_verify`-clean.
- [ ] All supporting Hintikka/reachability/supply lemmas are sorry-free and axiom-free.
- [ ] The corrected-gate rule (`modalApplyOneKb5''`) and its `specCore`/termination bound build
      cleanly beside the frozen `modalApplyOneKb5'` (which remains untouched).
- [ ] `ModalFrameSeparation.lean` `by decide` KB5 check passes under `lake test`, or the residual
      pre-existing kernel stall is explicitly diagnosed and documented.
- [ ] Full CI pipeline (6 steps) completes.
- [ ] Zero new axiom declarations across all new public declarations (`lean_verify` sweep).

## Artifacts & Outputs

- New declarations in `FiveSimplification.lean`: `modalKb5BoxAllUniv`, `modalKb5DiaNegAllUniv`,
  `modalApplyOneKb5''`(`Prop`), `modalTableauKb5''`(`_eq`), trigger-free membership dichotomies,
  `_mem_of` insertion lemmas, `specCore` instance, world invariant/bound (Phases 1, 2, 4).
- New declaration in `FrameSoundness.lean`: `modalTableauKb5''_sound` + one symmetrization helper
  (Phase 3).
- New declarations in `FrameCompleteness.lean`: re-derived KB5 Hintikka lemmas + ∃-edge helper
  (Phase 4), `modalTruthLemmaKb5` (Phase 5), open-branch supply lemmas (Phase 6),
  `modalOpenBranchKb5''_countermodel` / `modalTableauKb5''_complete` / `kb5Valid_decides` /
  `instDecidableKb5Valid` (Phase 7).
- Reconciled docstrings across `FrameCompleteness.lean`, `FiveSimplification.lean`,
  `S5Simplification.lean` (Phase 8).
- Extended `CslibTests/ModalFrameSeparation.lean` (Phase 8).
- Green full CI pipeline (or attributable/documented residual conditions).
- summaries/01_corrected-gate-kb5-rule-summary.md (on implementation completion).

## Rollback/Contingency

Each phase is an additive set of Lean declarations (the new rule sits beside the frozen one) plus
localized docstring edits in Phase 8; `git checkout` of the touched files reverts cleanly. Because
the frozen task-524 rule and its soundness proof are never modified, a failed phase can never
regress landed sound artifacts. Docstring reconciliation (Phase 8) runs only after Phase 7's
declarations land, so a failed Phase 7 leaves the blocker/scope notes intact and honest. If any
proof phase cannot close, it is marked `[BLOCKED]` with the reached `lean_goal` state (no `sorry`),
and downstream phases (per the wave table) do not start — preserving a consistent, sorry-free,
axiom-free tree at every committed milestone.
