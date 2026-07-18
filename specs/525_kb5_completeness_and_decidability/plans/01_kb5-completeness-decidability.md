# Implementation Plan: Task #525

- **Task**: 525 - KB5 completeness and decidability
- **Status**: [IMPLEMENTING]
- **Effort**: 14 hours
- **Dependencies**: Task 524 (COMPLETE — `modalApplyOneKb5'`, `modalTableauKb5'_sound`, `Kb5'WorldInv`, `modalApplyOneKb5'_specCore`, `modalKb5BoxAllFull`/`modalKb5DiaNegAllFull` all landed)
- **Research Inputs**: specs/515_s5_universal_rule_termination_unblock_504/reports/02_spawn-analysis.md
- **Artifacts**: plans/01_kb5-completeness-decidability.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md, cslib.md, lean4.md, plan-compliance.md
- **Type**: cslib (Lean 4 formal verification)
- **Lean Intent**: false

## Overview

Task 524 landed the KB5-specific full-cluster propagation rule (`modalApplyOneKb5'`), its
`RuleApplicationSpecCore` discharge, its termination bound (`Kb5'WorldInv`), and a soundness proof
(`modalTableauKb5'_sound`) proved directly against `kb5FC`. This task closes the completeness
direction and lands decidability, resolving the `[BLOCKED]` Phase 23 note in
`FrameCompleteness.lean`.

The completeness proof mirrors the already-landed Five completeness chain
(`modalTruthLemmaFive` → `modalOpenBranchFive_countermodel` → `modalTableauFive_complete` →
`fiveValid_decides` → `instDecidableFiveValid`, FrameCompleteness.lean:2693-3216) one rule down,
but against `extractModelKb5` (the symmetric right-Euclidean closure, landed sorry-free at
FrameCompleteness.lean:3230-3270) and using `modalApplyOneKb5'`'s full-cluster propagation instead
of `modalApplyOneFive`'s edge-gated root arm. The structural novelty is the **root box-positive
case**: because `extractModelKb5`'s relation puts the root `0` into the same cluster as everything
it reaches (`extractModelKb5_root_reach_scout`, FrameCompleteness.lean:3294) and makes it reflexive
once it has a successor (`Relation.symm_rightEuclidean_root_refl`), the truth lemma must certify
`T(ψ)@w'` for **every** cluster world `w'` (including `w' = 0`), which is exactly what
`modalApplyOneKb5'`'s full-cluster-dump-plus-root-reflexive-propagation was proved sound to emit.

### Research Integration

The spawn-analysis report (02_spawn-analysis.md) is the design record that motivated splitting the
KB5 work into a rule/soundness task (524) and this completeness/decidability task (525). The
Phase 23 Blocker note (FrameCompleteness.lean:3300-3339) is the precise problem statement this
task discharges: it identifies that a genuine KB5 completeness proof needs a rule whose root
trigger dumps to the full known non-root cluster and propagates the root's own box content back
onto world `0` — the rule task 524 built.

### Prior Plan Reference

No prior plan for this task directory. The controlling prior artifact is the delivered task 524
implementation plus the Five completeness chain, which this plan mirrors declaration-for-
declaration. Effort calibration: the Five completeness truth lemma is ~190 lines
(FrameCompleteness.lean:2693-2886); the KB5 analogue is comparable, driving the per-phase sizing
below.

### Roadmap Alignment

No ROADMAP.md consultation was requested (no `roadmap_path` / `roadmap_flag` in the delegation
context). This task completes task 515's re-scoped Phase 23 deliverable (genuine pure-KB5
completeness via a rooted symmetric-Euclidean tableau).

## Goals & Non-Goals

**Goals**:
- Land `modalTableauKb5'_complete (φ) (h : kb5Valid φ) : modalTableauKb5' φ = .closed` in
  `FrameCompleteness.lean`, wired through the `modalTableauKb5'` entry point (the entry point
  task 524's `modalApplyOneKb5'` rule is actually threaded through; `modalTableauKb5'_eq`,
  FiveSimplification.lean:2150, gives `modalTableauKb5' φ = modalTableauGen modalApplyOneKb5' φ`).
- Land `kb5Valid_decides` and `instance instDecidableKb5Valid (φ) : Decidable (kb5Valid φ)`,
  mirroring `fiveValid_decides` / `instDecidableFiveValid` (FrameCompleteness.lean:3203-3216).
- Build the supporting KB5 truth lemma, Hintikka full-cluster insertion lemmas, and open-branch
  supporting facts required by the completeness theorem.
- Reconcile all stale blocker/scope framing across `FrameCompleteness.lean`,
  `FiveSimplification.lean`, and `S5Simplification.lean` to state KB5 completeness as delivered.
- Extend `CslibTests/ModalFrameSeparation.lean` to exercise `instDecidableKb5Valid` / `by decide`.
- Run the full CSLib CI pipeline to completion.

**Non-Goals**:
- Modifying `modalApplyOneKb5'`, its `specCore` instance, its termination bound, or
  `modalTableauKb5'_sound` — all landed and frozen by task 524.
- Retiring the `modalApplyOneKb5 := modalApplyOneFive` alias or the frame-class-monotonicity
  soundness route; both stay (still the cheapest sound-only path).
- Editing `LoopChecking.lean` (owned by the still-`partial` task 511) or any file outside the
  declared file_scope.
- Touching `extractModelS5` / the S5 route.

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| KB5 truth lemma root box-positive case does not close (cluster-reach infra insufficient) | H | M | Phase 1 builds and verifies the reach/known-worlds infra *before* the truth lemma consumes it; if the root case genuinely cannot close, mark Phase 3 `[BLOCKED]` with the exact goal state — never a `sorry` or vacuous placeholder |
| Hintikka lift for `modalApplyOneKb5'` needs a bespoke `ModalLoopAuxKb5'` loop invariant larger than one agent run | M | M | Phase 4 is scoped to the open-branch plumbing only; leverage `Kb5'WorldInv_eq` (rfl to `FiveWorldInv`, FiveSimplification.lean:3547) and `modalApplyOneKb5'_specCore` to reuse Five's bound machinery; split Phase 4 if the loop invariant exceeds ~400 lines |
| Pre-existing `decide`-reduction stall in `ModalFrameSeparation` (from task 515's `Decidable` instances) blocks `lake test` | M | M | Phase 7 explicitly diagnoses whether landing `instDecidableKb5Valid` + `by decide` resolves, sidesteps, or must be reported; do not silently absorb it |
| Concurrent task 511 leaves `LoopChecking.lean` broken, surfacing in full `lake build` | M | L | Phase 7 reports any `LoopChecking.lean` error not caused by this task's changes as a concurrent-task condition — do NOT edit that file |
| `_mem_of` insertion lemmas for `modalKb5BoxAllFull`/`modalKb5DiaNegAllFull` do not exist yet | M | H (confirmed absent) | Phase 2 builds them as its first step, mirroring `modalFiveBoxAll_mem_of_root`/`_of_ne_root` |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1, 2, 4 | -- |
| 2 | 3 | 1, 2 |
| 3 | 5 | 3, 4 |
| 4 | 6 | 5 |
| 5 | 7 | 5, 6 |

Phases within the same wave can execute in parallel. All phases obey: **zero sorry, zero new axiom
declarations, every new public declaration `lean_verify`-clean**. If a phase's proof cannot be
completed as written, mark it `[BLOCKED]` with the reached goal state and what is needed — never a
`sorry`, `admit`, or vacuous (`:= True`/`trivial`) placeholder (per lean4.md and plan-compliance.md).

---

### Phase 1: Symmetric-Euclidean reachability & known-worlds infrastructure [COMPLETED]

**Status update**: landed `symmEuclGen_mem_modalKnownWorlds_iff` and
`extractModelKb5_root_reach_mem_modalKnownWorlds` (FrameCompleteness.lean, after
`extractModelKb5_hasEdge_imp_r`). Both are true and `lean_verify`-clean regardless of the Phase 3
finding recorded further down this file (see the new `## Phase 3 Blocker (task 525)` note replacing
the reconciliation Phase 6 was going to perform).

**Goal**: Land the `extractModelKb5`-relation reachability lemmas the KB5 truth lemma's box/diamond
cases consume — the KB5 analogues of Five's `euclGen_mem_modalKnownWorlds_iff`,
`euclGen_ne_root_of_hasEdge_ne_root`, and `euclGen_root_imp_hasEdge`
(FrameCompleteness.lean:2477-2556), adapted for the *symmetrized* base
`Relation.EuclGen (Relation.SymmGen acc.hasEdge)`.

**Tasks**:
- [ ] Add `symmEuclGen_mem_modalKnownWorlds_iff` (or equivalent): whenever
      `(extractModelKb5 b acc).r w w'` and `w ∈ modalKnownWorlds b`, then `w' ∈ modalKnownWorlds b`,
      consuming `accSourcesKnown`/`accTargetsKnown` (mirror the Five lemma at ~2477-2519, using
      `extractModelKb5_r`, FrameCompleteness.lean:3238, to unfold the relation).
- [ ] Add a root-reach characterization lemma stating what `(extractModelKb5 b acc).r 0 w'`
      certifies about `w'` (full-cluster membership), reusing the already-landed
      `extractModelKb5_root_reach_scout` (3294) and `extractModelKb5_hasEdge_imp_r` (3266) as the
      structural facts — the KB5 truth lemma needs the *positive* direction (root reaches the whole
      cluster), NOT Five's containment (`euclGen_root_imp_hasEdge` restricts root to direct
      successors, which is exactly the fact that does NOT hold for KB5).
- [ ] Verify each new lemma with `lean_verify` (fully-qualified name) for axiom/sorry cleanliness.

**Timing**: 2 hours

**Depends on**: none

**Files to modify**:
- `Cslib/Logics/Modal/Tableau/FrameCompleteness.lean` — add lemmas in the KB5 extraction section
  (after `extractModelKb5_hasEdge_imp_r`, ~3270, before the SCOUT section).

**Verification**:
- `lake build Cslib.Logics.Modal.Tableau.FrameCompleteness` succeeds.
- `lean_verify` clean on every new lemma.

---

### Phase 2: KB5 full-cluster Hintikka insertion lemmas [COMPLETED]

**Status update**: landed `modalKb5BoxAllFull_mem_of`/`modalKb5DiaNegAllFull_mem_of` and
`hintikkaKb5'_box_pos`/`hintikkaKb5'_diamond_neg`, all in `FrameCompleteness.lean` (the
`modalKb5BoxAllFull`/`modalKb5DiaNegAllFull` definitions from `FiveSimplification.lean` are
already transitively imported, so no file-scope escalation was needed). All four
`lean_verify`-clean (`propext`/`Quot.sound` only). **However**: Phase 3's concrete counterexample
(see the new `## Phase 3 Blocker (task 525)` note below, replacing the old Phase 23 blocker)
shows these lemmas, while individually true, are **not sufficient** to prove the general KB5 truth
lemma -- the gap is a case these insertion lemmas do not (and cannot, given `modalApplyOneKb5'`'s
frozen definition) cover: a non-root trigger `w` whose box-positive formula is read by the closure
relation as reaching the root (`(extractModelKb5 b acc).r w 0` via a raw two-hop chain through an
intermediate non-root world), which forces `T(ψ)@0 ∈ b` that no arm of `modalKb5BoxAllFull b ψ w`
(`w ≠ 0`) ever emits.

**Goal**: Land `hintikkaKb5'_box_pos` and `hintikkaKb5'_diamond_neg` — from a
`modalHintikkaSetGen modalApplyOneKb5'` set and `T(□ψ)@w ∈ b`, certify `T(ψ)@w' ∈ b` for every
cluster world `w'` (including the root-reflexive `w' = 0` case), and dually for diamond-negatives.
These are the KB5 analogues of `hintikkaFive_box_pos`/`hintikkaFive_diamond_neg`
(FrameCompleteness.lean:2582-2600), but using `modalApplyOneKb5'`'s **full-cluster** emission
rather than Five's root/non-root dichotomy.

**Tasks**:
- [ ] Build the `_mem_of` insertion lemmas that are confirmed absent:
      `modalKb5BoxAllFull_mem_of` and `modalKb5DiaNegAllFull_mem_of` (the `by_contra` direction:
      if `T(ψ)@w' ∉ b` then it appears in `modalKb5BoxAllFull b ψ w`), mirroring
      `modalFiveBoxAll_mem_of_root`/`_of_ne_root`. Place in `FiveSimplification.lean` beside the
      landed membership dichotomies (`modalKb5BoxAllFull_mem` at 1573, `_mem_known` at 1711,
      `_mem_eq` at 1732).
- [ ] Add `hintikkaKb5'_box_pos` in `FrameCompleteness.lean`: `by_contra` mirroring
      `hintikkaFive_box_pos`, establishing `hall`'s membership via the new `_mem_of` lemma and the
      Hintikka closure. Handle the full-cluster emission (no root exclusion) and the root-reflexive
      arm.
- [ ] Add `hintikkaKb5'_diamond_neg` dually.
- [ ] Reuse the free generic bridges `hintikka_box_neg_gen`/`hintikka_diamond_pos_gen`
      (Completeness.lean:1007-1019) for the box-negative/diamond-positive directions — no KB5-
      specific work needed there.
- [ ] `lean_verify` each new declaration.

**Timing**: 2 hours

**Depends on**: none

**Files to modify**:
- `Cslib/Logics/Modal/Tableau/FrameCompleteness.lean` — `hintikkaKb5'_box_pos`,
  `hintikkaKb5'_diamond_neg`.
- (If needed) `Cslib/Logics/Modal/Tableau/FiveSimplification.lean` — `modalKb5BoxAllFull_mem_of`,
  `modalKb5DiaNegAllFull_mem_of` insertion lemmas. **Note**: FiveSimplification.lean is NOT in the
  declared file_scope — if these insertion lemmas must live there, mark this a `[BLOCKED]`
  file-scope escalation to the user rather than editing out of scope. Prefer stating them in
  `FrameCompleteness.lean` if the `modalKb5BoxAllFull` definition is accessible there.

**Verification**:
- `lake build Cslib.Logics.Modal.Tableau.FrameCompleteness` succeeds.
- `lean_verify` clean on every new lemma.

---

### Phase 3: KB5 truth lemma `modalTruthLemmaKb5` [BLOCKED]

**BLOCKER**:
- **What failed**: `modalTruthLemmaKb5` as specified (branch membership agreeing with
  `extractModelKb5`-satisfaction at every world `w`, including non-root triggers) cannot be
  proved — it is **false** for `modalApplyOneKb5'`, not merely difficult.
- **What was tried**: Phases 1-2 landed cleanly (reachability infra + Hintikka insertion
  lemmas, all `lean_verify`-clean). Attempting Phase 3's box-positive case for a general trigger
  `w` (not just `w = 0`) surfaced that `w' = 0` is reachable via `(extractModelKb5 b acc).r w w'`
  for `w ≠ 0` (a non-root trigger connected to root by a two-hop raw chain), and
  `hintikkaKb5'_box_pos`'s hypothesis for this case (`w = 0 ∧ cluster nonempty`) cannot be
  discharged since the actual trigger `w ≠ 0`.
- **Why it's stuck**: this is a genuine, Lean-verified mathematical gap, not a proof-search
  failure. See `extractModelKb5_nonRoot_boxPos_gap` and the `## Phase 3 Blocker (task 525)`
  module note (`FrameCompleteness.lean`, replacing the old Phase 23 blocker note) for the full
  proof and a reproducible witness: `φ₀ := ¬(◇◇□p)` makes `modalTableauKb5' φ₀` produce an open
  branch with raw edges `[(1,2),(0,1)]`, `T(□p)@2 ∈ b`, `T(p)@0 ∉ b`, and
  `(extractModelKb5 b acc).r 2 0` holds (proved, not just observed) — a genuine countermodel-side
  failure: the extracted model does not actually satisfy what the branch asserts. Root cause:
  `modalKb5BoxAllFull`'s non-root cluster-dump arm unconditionally excludes target `0` regardless
  of the trigger, while the closure's symmetry lets *any* two-hop-connected non-root trigger reach
  root in the model.
  - Kernel `decide` does **not** reduce the real `modalTableauKb5'` computation (a pre-existing
    stall from task 515, also affecting `ModalFrameSeparation.lean`); the witness above was
    confirmed via `lean_run_code` (`#eval`/`native_decide`, not committed), but the *general*
    structural fact (`extractModelKb5_nonRoot_boxPos_gap`) is landed as a fully kernel-checked,
    `native_decide`-free lemma in `FrameCompleteness.lean`.
- **What is needed**: `modalApplyOneKb5'` is frozen (task 524's landed deliverable; out of this
  task's file_scope). A genuine fix needs either (i) a rule whose box-positive/diamond-negative
  propagation dumps to the full known cluster unconditionally including target `0` whenever the
  cluster is connected to root by *any* length chain (not just literal `w = 0` triggers) — likely
  requiring a cluster-membership bookkeeping device rather than trigger-identity gating — or (ii) a
  different model extraction that does not let non-root-triggered chains reach the root
  semantically while the rule stays root-trigger-gated. Both are new rule/extraction design
  comparable in scope to the original Phases 15-21 Five construction; this is a follow-on task,
  not a completion of this plan.
- **Prohibited workarounds**: no `sorry`, no `def X := True`/vacuous placeholder, no modification
  of `modalApplyOneKb5'`/`modalTableauKb5'_sound` (frozen, out of scope).

**Downstream impact**: Phases 4, 5, 6, 7 all depend (directly or transitively) on
`modalTruthLemmaKb5` and are marked `[BLOCKED]` below per the escalation protocol — none of
`modalOpenBranchKb5'_countermodel`/`modalTableauKb5'_complete`/`kb5Valid_decides`/
`instDecidableKb5Valid` can be built without it.

**Goal**: Land `modalTruthLemmaKb5`, mirroring `modalTruthLemmaFive`
(FrameCompleteness.lean:2693-2886) against `extractModelKb5`: for an open Hintikka branch of
`modalApplyOneKb5'`, branch membership and `extractModelKb5`-satisfaction agree at every world and
formula, by strong induction on `modalComplexity`.

**Tasks**:
- [ ] Port the propositional cases (`imp`/`and`/`or`/`atom`/`bot`) verbatim from
      `modalTruthLemmaFive`, substituting the `modalApplyOneKb5'` prop-shape agreement lemma for
      `modalApplyOneFive_eq_of_prop_shape` (locate/confirm the analogue —
      `modalApplyOneKb5'Prop_eq_of_not_boxPos_diaNeg`, FrameSoundness.lean:4252, establishes shape
      agreement; find or state the `FrameCompleteness`-usable form).
- [ ] Box-positive case (`.box ψ`): for `w' with (extractModelKb5 b acc).r w w'`, use Phase 1's
      known-worlds closure + root-reach characterization to place `w'` in the cluster, then
      `hintikkaKb5'_box_pos` (Phase 2) to obtain `T(ψ)@w' ∈ b`, then IH. **The root case
      `w = 0` must handle every cluster `w'` including `w' = 0`** — this is the crux the Phase 23
      Blocker flagged; the full-cluster + root-reflexive emission of `modalApplyOneKb5'` is what
      makes it discharge.
- [ ] Box-negative / diamond-positive cases: reuse `hintikka_box_neg_gen`/
      `hintikka_diamond_pos_gen` + `extractModelKb5_hasEdge_imp_r` (3266), mirroring the Five arms.
- [ ] Diamond-negative case: dual to box-positive, via `hintikkaKb5'_diamond_neg`.
- [ ] `lean_verify` the lemma.

**Timing**: 2.5 hours

**Depends on**: 1, 2

**Files to modify**:
- `Cslib/Logics/Modal/Tableau/FrameCompleteness.lean` — `modalTruthLemmaKb5` (place after the
  KB5 Hintikka lemmas, mirroring where `modalTruthLemmaFive` sits relative to
  `hintikkaFive_box_pos`).

**Verification**:
- `lake build Cslib.Logics.Modal.Tableau.FrameCompleteness` succeeds.
- `lean_verify` clean; zero sorry.
- If the root box-positive case cannot close: mark `[BLOCKED]`, record the exact `lean_goal` state
  and the missing fact, do NOT insert a placeholder.

---

### Phase 4: KB5 open-branch supporting facts (Hintikka lift, accSourcesKnown, accTargetsKnown) [BLOCKED]

**BLOCKER**: depends on Phase 3, which is blocked (`modalTruthLemmaKb5` is false for `modalApplyOneKb5'`, see Phase 3's blocker note above). Not attempted -- building this phase's supply lemmas would only feed a completeness theorem that cannot close.

**Goal**: Land the entry-point plumbing the completeness theorem consumes for `modalApplyOneKb5'`,
mirroring the Five supply lemmas invoked inside `modalTableauFive_complete`
(FrameCompleteness.lean:3140-3184): a `modalHintikkaSetGen modalApplyOneKb5'` producer via the
generic Hintikka lift, `accSourcesKnown` via the generic open-branch lemma, and a KB5
`accTargetsKnown` open-branch preservation analogue.

**Tasks**:
- [ ] Establish the Hintikka lift for `modalApplyOneKb5'`: instantiate the generic
      `modalExpandBranchesHintikka` with `modalApplyOneKb5'_specCore` (FiveSimplification.lean:2662)
      and a `ModalLoopAuxKb5'` loop invariant + step-preservation + bounds. Leverage
      `Kb5'WorldInv_eq` (rfl to `FiveWorldInv`, FiveSimplification.lean:3547) and
      `modalMaxWorld_lt_worldBound_of_Kb5'WorldInv` (3556) to reuse Five's bound machinery where
      the invariant coincides; only re-prove the arms where `modalApplyOneKb5'`'s propagation
      differs from `modalApplyOneFive`'s.
- [ ] `accSourcesKnown`: apply the generic `modalExpandBranchesGen_openBranch_accSourcesKnown`
      with `modalApplyOneKb5'` + `modalApplyOneKb5'_fresh_local` (referenced at
      FrameSoundness.lean:4762) — this bridge is generic in the rule, so it should apply directly.
- [ ] `accTargetsKnown`: build a `modalExpandBranchesKb5'_openBranch_accTargetsKnown` analogue of
      `modalExpandBranchesFive_openBranch_accTargetsKnown_and_NeRoot`
      (FrameCompleteness.lean:3015) via a `modalStepBranchKb5'_preserves_accTargetsKnown` step
      lemma. **NeRoot is intentionally dropped** — KB5's root is in the cluster (reflexive), so the
      truth lemma does not consume `accTargetsNeRoot`; only `accTargetsKnown` is needed.
- [ ] `lean_verify` each new declaration.

**Timing**: 2.5 hours

**Depends on**: none

**Files to modify**:
- `Cslib/Logics/Modal/Tableau/FrameCompleteness.lean` — Hintikka-lift instantiation,
  `accTargetsKnown` open-branch lemma and its step-preservation helper.
  (`accSourcesKnown` uses the existing generic lemma; no new declaration unless a wrapper helps.)

**Verification**:
- `lake build Cslib.Logics.Modal.Tableau.FrameCompleteness` succeeds.
- `lean_verify` clean on every new lemma.
- **Split trigger**: if the `ModalLoopAuxKb5'` loop invariant + preservation exceeds ~400 lines or
  one agent run, split into Phase 4a (Hintikka lift) and Phase 4b (accTargetsKnown); update the
  wave table accordingly.

---

### Phase 5: `modalOpenBranchKb5'_countermodel`, `modalTableauKb5'_complete`, decidability [BLOCKED]

**BLOCKER**: depends on Phases 3 and 4, both blocked. `modalTableauKb5'_complete` cannot be stated as a theorem (its proof obligation, `modalTruthLemmaKb5`, is false) without either modifying the frozen `modalApplyOneKb5'` rule (out of scope) or a new rule/extraction design (out of scope for this plan). Not attempted.

**Goal**: Assemble the countermodel wrapper, the completeness theorem wired through the
`modalTableauKb5'` entry point, and the decidability instance.

**Tasks**:
- [ ] `modalOpenBranchKb5'_countermodel`: thin wrapper mirroring `modalOpenBranchFive_countermodel`
      (FrameCompleteness.lean:2886), returning the `extractModelKb5` Kripke countermodel by
      invoking `modalTruthLemmaKb5` (Phase 3) at `F(φ)@0`, with `extractModelKb5_rightEuclidean`
      (3247) + `extractModelKb5_symm` (3257) discharging `kb5FC` for free.
- [ ] `modalTableauKb5'_complete (φ₀) (h : kb5Valid φ₀) : modalTableauKb5' φ₀ = .closed`: mirror
      `modalTableauFive_complete` (3131-3198) exactly, substituting `modalApplyOneKb5'`, the
      Phase 4 Hintikka/accSourcesKnown/accTargetsKnown supply lemmas, `modalOpenBranchKb5'_
      countermodel`, and `kb5FC` (via `extractModelKb5_rightEuclidean` + `extractModelKb5_symm`).
      Use `modalTableauKb5'_eq` (FiveSimplification.lean:2150) to normalize the entry point to
      `modalTableauGen modalApplyOneKb5'`.
- [ ] `kb5Valid_decides (φ₀) : modalTableauKb5' φ₀ = .closed ↔ kb5Valid φ₀ :=
      ⟨modalTableauKb5'_sound φ₀, modalTableauKb5'_complete φ₀⟩`, mirroring `fiveValid_decides`
      (3203). Confirm `modalTableauKb5'_sound` (FrameSoundness.lean:4821) has signature
      `(φ) (h : modalTableauKb5' φ = .closed) : kb5Valid φ`.
- [ ] `instance instDecidableKb5Valid (φ₀) : Decidable (kb5Valid φ₀)`, mirroring
      `instDecidableFiveValid` (3213): match on `modalTableauKb5' φ₀`.
- [ ] `lean_verify` all four declarations.

**Timing**: 2 hours

**Depends on**: 3, 4

**Files to modify**:
- `Cslib/Logics/Modal/Tableau/FrameCompleteness.lean` — the four declarations, placed where the
  Phase 23 Blocker note currently sits (~3300, to be replaced/relocated in Phase 6).

**Verification**:
- `lake build Cslib.Logics.Modal.Tableau.FrameCompleteness` succeeds.
- `lean_verify` clean; zero sorry, zero new axioms.
- Sanity: `#eval` or `by decide` on a small known-`kb5Valid` / known-non-`kb5Valid` formula behaves.

---

### Phase 6: Documentation reconciliation [BLOCKED]

**BLOCKER**: depends on Phase 5 (blocked). The plan's Phase 6 goal was to retire the Phase 23 blocker note as delivered; instead, `FrameCompleteness.lean`'s blocker note has been REPLACED with a new, more precise `## Phase 3 Blocker (task 525)` note (see Phase 3 above) documenting the deeper gap found in this task. The `FiveSimplification.lean`/`S5Simplification.lean` "completeness is deferred"/"remains open" framing has intentionally been LEFT AS-IS (not reconciled to "delivered"), since completeness is genuinely still not delivered -- reconciling those notes to claim delivery would be false. No edits made to either file (both outside this task's actual file_scope for a completed deliverable in any case).

**Goal**: Update every stale framing that describes KB5 completeness as blocked/open, now that it
is delivered. Keep the scout lemma as documentation of the design constraint the new rule
satisfies — do NOT delete it or reframe it as an open blocker.

**Tasks**:
- [ ] Replace the `## Phase 23 Blocker: modalTableauKb5_complete` note
      (FrameCompleteness.lean:3300-3339) with a delivered-state note explaining how
      `modalApplyOneKb5'`'s full-cluster + root-reflexive propagation discharges the root box-
      positive case that the alias rule could not.
- [ ] Reconcile the `### SCOUT` section (FrameCompleteness.lean:3272-3299): keep
      `extractModelKb5_root_reach_scout` as documentation of *why* the full-cluster rule is
      required (the design constraint), reframing surrounding prose from "before spending effort"
      to the delivered rationale.
- [ ] Reconcile the `## 5 / KB5 (Euclidean) Coverage via the S5 Route` docstring
      (FrameCompleteness.lean:565) to state KB5 completeness as delivered via `modalTableauKb5'`.
- [ ] Update the `modalApplyOneKb5'-based completeness is deferred to a follow-on task` note in
      `FiveSimplification.lean` (1424-1443) to state it as delivered.
- [ ] Update the `## Scope Note: Pure-K5 / Pure-5` block in `S5Simplification.lean` (2037+,
      located by content) — the "KB5's **completeness** specifically remains open" sentence — to
      state completeness as delivered, referencing `modalTableauKb5'_complete`.
- [ ] **MUST NOT** cite ephemeral task numbers in the reconciled prose per
      no-task-references-in-deliverables.md — these are `.lean` deliverables. Use durable anchors
      (declaration names, section headings). Existing task-number mentions in these docstrings that
      are being rewritten should be replaced with durable anchors where practical.

**Timing**: 1 hour

**Depends on**: 5

**Files to modify**:
- `Cslib/Logics/Modal/Tableau/FrameCompleteness.lean`
- `Cslib/Logics/Modal/Tableau/FiveSimplification.lean` — **NOT in declared file_scope**; if edits
  here are required, escalate as a file-scope expansion to the user before editing.
- `Cslib/Logics/Modal/Tableau/S5Simplification.lean`

**Verification**:
- `lake build Cslib.Logics.Modal.Tableau.FrameCompleteness` and `.S5Simplification` succeed
  (docstring edits must not break compilation).

---

### Phase 7: Regression tests + full CI pipeline [BLOCKED]

**BLOCKER**: depends on Phase 5 (blocked) for `instDecidableKb5Valid` -- there is no new decidability instance to exercise in `ModalFrameSeparation.lean`. The full CSLib CI pipeline is still run (see task-level verification below) to confirm the landed Phase 1/2 additions do not regress the build; `ModalFrameSeparation.lean` is not edited since its `instDecidableKb5Valid`-is-not-yet-landed framing remains accurate.

**Goal**: Extend `ModalFrameSeparation.lean` to exercise the new decidability instance, then run
the full CSLib CI pipeline to completion.

**Tasks**:
- [ ] Update `CslibTests/ModalFrameSeparation.lean` (lines 14-43): replace the term-proof-only
      `boxImp_not_kb5Valid` check (line 42-43) with an `instDecidableKb5Valid` / `by decide`
      check where appropriate, and update the module docstring framing (14-21, 39-41) that says
      `instDecidableKb5Valid` "is not yet landed" / `kb5Valid` "has no `Decidable` instance yet".
- [ ] Diagnose the pre-existing `decide`-reduction stall reported by task 524's implementer in
      `ModalFrameSeparation` (a `decide`-reduction stall in `FrameCompleteness.lean`'s `Decidable`
      instances originating from task 515): determine whether landing `instDecidableKb5Valid` +
      `by decide` coverage **resolves**, **sidesteps**, or **must be explicitly diagnosed**. If the
      stall persists, document it precisely; do not silently absorb it.
- [ ] Run the full CI pipeline in order (cslib.md CI verification order):
      `lake build`, `lake exe checkInitImports`, `lake lint`, `lake exe lint-style`, `lake test`,
      `lake shake --add-public --keep-implied --keep-prefix`.
- [ ] If `lake build` surfaces `LoopChecking.lean` errors NOT caused by this task's changes,
      report them as a concurrent task-511 condition (task 511 owns `LoopChecking.lean` and is
      still `partial`) — **do NOT edit `LoopChecking.lean`**.
- [ ] Final `lean_verify` sweep on all new public declarations (zero sorry, zero new axioms).

**Timing**: 1.5 hours

**Depends on**: 5, 6

**Files to modify**:
- `CslibTests/ModalFrameSeparation.lean`

**Verification**:
- Full CI pipeline passes (or any failure is attributable and reported as a concurrent-task
  condition, not this task's changes).
- `lake test` covers the new `by decide` `kb5Valid` check.

## Testing & Validation

- [ ] `modalTableauKb5'_complete`, `kb5Valid_decides`, `instDecidableKb5Valid` build and are
      `lean_verify`-clean.
- [ ] `modalTruthLemmaKb5` and all supporting Hintikka/reachability lemmas are sorry-free.
- [ ] `ModalFrameSeparation.lean` `by decide` KB5 check passes under `lake test`.
- [ ] Full CI pipeline (6 steps) completes.
- [ ] Zero new axiom declarations across all new public declarations (`lean_verify` sweep).

## Artifacts & Outputs

- New declarations in `FrameCompleteness.lean`: reachability/known-worlds infra (Phase 1), KB5
  Hintikka insertion lemmas (Phase 2), `modalTruthLemmaKb5` (Phase 3), open-branch supply lemmas
  (Phase 4), `modalOpenBranchKb5'_countermodel` / `modalTableauKb5'_complete` / `kb5Valid_decides`
  / `instDecidableKb5Valid` (Phase 5).
- Reconciled docstrings across `FrameCompleteness.lean`, `FiveSimplification.lean`,
  `S5Simplification.lean` (Phase 6).
- Extended `CslibTests/ModalFrameSeparation.lean` (Phase 7).
- Green full CI pipeline.

## Rollback/Contingency

Each phase is an additive set of Lean declarations plus localized docstring edits; `git checkout`
of the touched files reverts cleanly. The Phase 23 Blocker note (Phase 6) is only rewritten after
Phase 5's declarations land, so a failed Phase 5 leaves the blocker note intact and honest. If any
proof phase cannot close, the phase is marked `[BLOCKED]` with the reached goal state (no `sorry`),
and downstream phases (which depend on it via the wave table) do not start — preserving a
consistent, sorry-free, axiom-free tree at every committed milestone.
