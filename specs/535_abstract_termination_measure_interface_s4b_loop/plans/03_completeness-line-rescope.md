# Implementation Plan: Keyed S4 Driver — Completeness-Line Rescope (v3)

- **Task**: 535 - Abstract termination-measure interface for S4/B loop lemma (task 511 Phase 7 follow-on)
- **Status**: [IMPLEMENTING]
- **Effort**: 9.5 hours remaining (range 7-14); Phases 1-7 (~18h) landed and committed. Total ~27.5h.
- **Dependencies**: None for the in-scope completeness line (parent 511 Phases 1-6 are landed, frozen,
  and consumed read-only). The deferred soundness line depends on a separately-spawned task (see
  "Deferred / Spawned Scope").
- **Research Inputs**:
  - specs/535_abstract_termination_measure_interface_s4b_loop/reports/02_remaining-work-and-phase9-obstruction.md (drives this revision)
  - specs/535_abstract_termination_measure_interface_s4b_loop/reports/01_termination-interface-survey.md
  - specs/535_abstract_termination_measure_interface_s4b_loop/handoffs/04_phase8-11-assessment-and-continuation.md (Phase 8 technical map)
  - specs/535_abstract_termination_measure_interface_s4b_loop/handoffs/01_phase3-5-continuation.md (v2 technical map, carried forward)
- **Artifacts**: plans/03_completeness-line-rescope.md (this file)
- **Standards**: plan-format.md; status-markers.md; artifact-management.md; tasks.md
- **Type**: cslib
- **Lean Intent**: true

## Overview

This is a revision (v3) of `plans/02_keyed-s4-driver-restructured.md`, made after research confirmed
that the plan's remaining work splits into **two independent lines**, only one of which is reachable:

- **Completeness/termination line** — fully unblocked, all dependencies landed. This is now the
  task's entire deliverable.
- **Soundness line** — blocked at its root on a genuine mathematical gap (not proof engineering).
  Moved out of this plan entirely; see "Deferred / Spawned Scope".

**Rescope decision (owner-directed)**: *Phase 8 now, spawn Phase 9 separately.* This plan carries
only the completeness line. The v2 Phase 8 (`modalExpandBranchesS4Keyed_hintikka`, estimated
250-400 lines) is decomposed into three bounded phases, and the completeness half of v2 Phase 11 is
retained as a fourth. The v2 Phases 9 and 10, and the decidability half of v2 Phase 11, are removed
from this plan.

**Definition of done (CHANGED from v1/v2)**: `modalTableauS4Keyed_complete` is a sorry-free,
axiom-clean theorem, established via a sorry-free `modalExpandBranchesS4Keyed_hintikka`; every new
public declaration is `lean_verify`-clean; the live `modalTableauS4`, S5's
`ModalLoopAuxS5w`/`modalExpandBranchesHintikka`, and B's `modalExpandBranchesB` are unchanged and
unregressed; frozen task-511 Phase 1-6 deliverables are byte-unchanged except for consuming
references.

**`instDecidableS4Valid` is NOT achievable within this task and is no longer a goal of this plan.**
The `Decidable (s4Valid φ)` instance requires the soundness/completeness dichotomy — both halves. The
completeness half is what this plan delivers; the soundness half is blocked on the deferred work
described below. Stating this plainly: **this task will terminate with `Decidable (s4Valid φ)` still
open.** Any status transition to `[COMPLETED]` for this task means "the completeness line landed",
not "S4 decidability landed".

### Research Integration

This revision integrates `reports/02_remaining-work-and-phase9-obstruction.md` (new since v2) and
`handoffs/04_phase8-11-assessment-and-continuation.md`, and carries forward v2's integration of
`reports/01_termination-interface-survey.md` and `handoffs/01_phase3-5-continuation.md`.

What the new report establishes and this plan acts on:

1. **Source is green and all landed work is verified present.** `lake build
   Cslib.Logics.Modal.Tableau.LoopChecking` succeeds (847 jobs, exit 0); **zero** `sorry`/`admit` in
   code across all four `file_scope` files (three hits are docstring prose only:
   `LoopChecking.lean:4619`, `FrameCompleteness.lean:576`, `GenericDriver.lean:62`). Working tree
   clean on `Cslib/Logics/Modal/Tableau/*`, matching commit `1ce152b6`. Phases 1-7 are landed and
   verified at their line numbers. **Nothing in Phases 1-7 is re-opened by this revision.**
2. **The two lines are independent**, and the completeness line's dependencies (Phases 3, 4, 5, 7)
   are all landed. It can proceed immediately with no reference to the soundness line.
3. **The soundness line's root (v2 Phase 9) is a genuine mathematical gap**, and
   `modalTableauS4Keyed_sound` is likely FALSE as stated under the current guard. Recorded in full
   in "Deferred / Spawned Scope" below.
4. **The `modalExpMeasure_step_lt_gen` reuse lead** — recorded concretely, with a material
   correction found while verifying it, in "Measure-Decrease Lead" below.

### Prior Plan Reference and Phase Renumbering

Supersedes `plans/02_keyed-s4-driver-restructured.md`, which supersedes `plans/01_keyed-s4-driver-plan.md`.

Phases 1-7 are carried over verbatim as `[COMPLETED]`, with their original content and completion
records intact. The remaining numbering maps as follows:

| v2 | v3 | Disposition |
|----|----|-------------|
| Phases 1-7 | Phases 1-7 | Unchanged, `[COMPLETED]`, preserved verbatim |
| Phase 8 (`modalExpandBranchesS4Keyed_hintikka`, 250-400 lines) | Phases 8, 9, 10 | Decomposed into three one-agent-run phases |
| Phase 9 (blocked-mint-redirect soundness) | -- | **Deferred / spawned** |
| Phase 10 (`modalTableauS4Keyed_sound`) | -- | **Deferred / spawned** |
| Phase 11, completeness half (`modalTableauS4Keyed_complete`) | Phase 11 | Retained, in scope |
| Phase 11, decidability half (`s4Valid_decides`, `instDecidableS4Valid`) | -- | **Deferred / spawned** |

Numbering continuity 1-11 is preserved. Note that "Phase 9" and "Phase 10" mean different things in
v2 and v3; prior handoffs referring to "Phase 8" mean the whole of v3 Phases 8-10, and prior
handoffs referring to "Phase 9" mean the deferred soundness root.

## Measure-Decrease Lead (v2 Phase 8's main unknown, now resolved)

The research flagged the generic `modalExpMeasure_step_lt_gen` as a possible way to obtain the
fuel-decrease without bespoke re-derivation, and asked that its visibility and applicability be
confirmed. Both were checked against source during this revision. The result is **partially
positive with one material blocker**, and it is what drives the Phase 8/9 split:

**Confirmed positive:**
- `modalExpMeasure_step_lt_gen` is a **public** `lemma` at `FmpMeasure.lean:3227` — not `private`,
  so it is callable from `LoopChecking.lean`. (Public call sites already exist at
  `GenericDriver.lean:548` and `CompletenessLoop.lean:1344,1641`.)
- Its three raw hypotheses are exactly the shapes Phase 4 landed:

  | `modalExpMeasure_step_lt_gen` hypothesis | Landed Phase 4 lemma (all `private`, all `∀ keys`) |
  |------------------------------------------|-----------------------------------------------------|
  | `hBranchingLength` | `modalApplyOneS4Keyed_branchingLength_S4` (`LoopChecking.lean:5318`) |
  | `hPersistentFresh` | `modalApplyOneS4Keyed_persistentFresh_S4` (`LoopChecking.lean:5270`) |
  | `hOutputsSubsetUniverse` | `modalApplyOneS4Keyed_outputsSubsetUniverse_S4` (`LoopChecking.lean:5371`) |

  The first two match the generic hypothesis shapes verbatim.

**Material blocker found (correction to the research's lead):** the third does **not** match, and
neither does the lemma's conclusion. `modalExpMeasure_step_lt_gen` is hardwired to **K's** universe
and world bound throughout — its `hb : ∀ x ∈ bh, x ∈ modalUniverse φ0`, its
`hW : modalMaxWorld bh < modalWorldBound φ0`, its `hOutputsSubsetUniverse` (stated over
`modalUniverse φ0`), and its conclusion `modalExpMeasure (modalUniverse φ0) … ≤ …` all name
`modalUniverse`/`modalWorldBound`. The keyed S4 line runs over **`modalUniverseS4 φ₀`** and
**`modalWorldBoundS4 φ₀`**: `modalApplyOneS4Keyed_outputsSubsetUniverse_S4` concludes over
`modalUniverseS4 φ₀` (and additionally takes `hknown`/`hWC`/`hKT`/`hKD`/`hKI`), and
`modalExpMeasure_entry_le_fuelS4` (`LoopChecking.lean:5432`) bounds
`modalExpMeasure (modalUniverseS4 φ₀) …`. **Direct instantiation at
`apply := modalApplyOneS4Keyed φ₀ keys` therefore does not typecheck.** The lemma is a *proof
template to transcribe*, not a lemma to call.

**Consequence, and why it is cheap anyway:** transcribing it over `modalUniverseS4` is tractable
because the load-bearing pieces are already available:
- Phase 3's four re-derived primitives are stated over an **arbitrary** universe `U`
  (`modalCount_notMem_append_drop_S4` / `_mono_S4` / `modalWork_drop_linear_S4` /
  `modalWork_drop_persistent_S4`, `LoopChecking.lean:4793`/`4869`/`4889`/`4904` — all take
  `(U … : List α)` or `(U … : List (SignedFormula …))`). They apply at `U := modalUniverseS4 φ₀`
  with no change.
- `pow3_add_one_le` and `pow3_two_add_one_le` are **public** at
  `Cslib/Foundations/Logic/Tableau/Measure.lean:128`/`117`.
- The only two helpers that are `private` and thus need local re-derivation are
  `modalExpMeasure_split` (`FmpMeasure.lean:3174`) and `modalExpMeasure_append`
  (`FmpMeasure.lean:3191`) — both small, and re-derived by exactly the same territory-local pattern
  Phase 3 already used.

**4-tuple to 3-tuple bridging (the research's other named item):** `modalExpMeasure_step_lt_gen`'s
`hstep` is phrased over `modalStepBranchGen apply bh e acc` (3-tuple:
`Option (branches × expandedSets × Accessibility)`, `Saturation.lean:122-129`), whereas
`modalStepBranchS4Keyed` returns a **4-tuple** with `keys'` bolted on
(`Option (branches × expandedSets × Accessibility × keys)`, `LoopChecking.lean:780-786`). The bridge
is to prove once that the keyed stepper's first three components agree with
`modalStepBranchGen (modalApplyOneS4Keyed φ₀ keys)` — both are a `b.findSome?` over the same
`expanded.any` guard and the same four `RuleResult` arms, so this should be a structural
`findSome?`-congruence argument, not a semantic one. That projection lemma is v3 Phase 8; the
transcribed measure lemma consuming it is v3 Phase 9.

## Goals & Non-Goals

**Goals**:
- Bridge the keyed 4-tuple stepper to the generic 3-tuple `modalStepBranchGen` projection, and
  re-derive the two `private` measure-split helpers locally.
- Transcribe the per-step measure decrease over `modalUniverseS4 φ₀`, consuming Phase 3's
  universe-generic primitives and Phase 4's three landed `_S4` obligations.
- Assemble the termination top-loop `modalExpandBranchesS4Keyed_hintikka`, bridged to the concrete
  `modalHintikkaSetS4` form.
- Land `modalTableauS4Keyed_complete` (an open branch from the keyed driver refutes `φ`).
- Preserve every landed asset from Phases 1-7 byte-unchanged except for consuming references.

**Non-Goals**:
- **`s4Valid_decides` / `instDecidableS4Valid`.** Explicitly removed as a goal — unreachable without
  the deferred soundness line (see below). Do not attempt, do not stub, do not state under-scoped.
- **Any soundness result for the keyed driver**, including the blocked-mint-redirect lemma and
  `modalTableauS4Keyed_sound`.
- Editing the frozen task-511 guard `blockingWorldS4Keyed` (`LoopChecking.lean:469`). This plan
  consumes it read-only. Guard revision belongs to the spawned task, which carries its own
  authorization.
- Path (a): generalizing `GenericDriver.lean`/`CompletenessLoop.lean`/`Saturation.lean` to thread
  opaque state (deprioritized by the survey; out of scope).
- Editing `FmpMeasure.lean` — its helpers are re-derived territory-locally, not modified.
- Redefining or replacing the live `modalTableauS4`; any change to S5's
  `ModalLoopAuxS5w`/`modalExpandBranchesHintikka` call site or B's `modalExpandBranchesB`.

## Deferred / Spawned Scope

The following work is **removed from this plan** and is to be carried by a **separately spawned
task** with its own scope and its own explicit authorization to edit the frozen task-511 guard code.
It must not be attempted under this plan.

**Deferred items** (v2 Phases 9, 10, and the decidability half of v2 Phase 11):

| Deferred item | v2 label | Why deferred |
|---------------|----------|--------------|
| Blocked-mint-redirect soundness lemma | Phase 9 | Genuine mathematical gap (below) |
| `modalTableauS4Keyed_sound` | Phase 10 | Depends on the above |
| `s4Valid_decides`, `instDecidableS4Valid` | Phase 11 (decidability half) | Needs BOTH lines |

**The obstruction, stated precisely.** `modalApplyOneS4Keyed` at the two minting shapes
(`F(□φ)@w` / `T(◇φ)@w`, `LoopChecking.lean:710-722`) emits `(.linear [], acc.addEdge sf.label wBlock)`
— a bare accessibility edge with no new branch formula. Soundness of that edge requires
`m.r (f lbl) (f wBlock)` in an arbitrary model witnessing `branchSatisfiableIn s4FC`. But
`blockingWorldS4Keyed` (`LoopChecking.lean:469`) picks `wBlock` by matching **birth content across
all recorded worlds, with no reachability restriction to `lbl`** — and `s4FC`
(`FrameSoundness.lean:1047`) is reflexive + transitive but **non-symmetric**, so common-ancestor
reachability does not yield relatedness (a tree with two unrelated siblings is the standard
countermodel). No field of the frozen `S4LoopInv` supplies the missing reachability fact:
`keyLowerBd` only lower-bounds a world's own key against its own relevant set; `keysDistinct` only
separates distinct worlds' keys. The one in-codebase precedent for a cheap redirect edge — S5's
`modalApplyOneS5w` via `accReachableInv`/`reachable_imp_related_s5`
(`FrameSoundness.lean:1432-1482`) — **relies on symmetry and does not transfer**; B's driver never
mints a world at all (`BDriver.lean:53`), so it is not a precedent either. **As stated,
`modalTableauS4Keyed_sound` is likely FALSE**, not merely hard.

**What the spawned task must decide and carry** (do not pre-commit here):
- Route (i), recommended and matching standard S4 loop-checking theory: narrow
  `blockingWorldS4Keyed`'s candidate domain to worlds already `acc`-reachable from `lbl`
  (`Relation.ReflTransGen acc.hasEdge lbl wBlock`, or the ancestor-on-current-path variant), so
  transitivity supplies the edge at the point of selection. **This edits frozen task-511 code and
  requires the spawned task's own authorization** — it is a Non-Goal here.
- Route (ii), higher risk: re-architect the soundness statement to build the witnessing model from
  the tableau's own construction (canonical-model style) rather than closing over an arbitrary
  `branchSatisfiableIn` witness. Not supported by any existing `branchSatisfiableIn_s4FC_*` lemma
  (`FrameSoundness.lean:1085,1106` cover only persistent 4-rule propagation).
- The decidability instance is assembled only after a soundness result exists; its templates are
  `s5Valid_decides`/`instDecidableS5Valid` and `modalTableauB_sound`+`instDecidableBValid`
  (`FrameCompleteness.lean:1877`/`1925`), both verified present.

**Carry-forward warning for the spawned task** — see Risk R1 below: Route (i) is not a local guard
edit. Narrowing the candidate set is predicted to break `S4LoopInv.keysDistinct`, and through it the
pigeonhole world bound the *termination* line depends on. The spawned task must verify this before
committing to Route (i).

## Risks & Mitigations

| ID | Risk | Impact | Likelihood | Mitigation |
|----|------|--------|------------|------------|
| R1 | **Guard-narrowing re-work risk.** If the spawned task later narrows `blockingWorldS4Keyed` to acc-reachable candidates, saturation changes and parts of this plan's work need re-verification. | H | M | Bounded and enumerated below — see "R1 blast radius". Land the completeness line first regardless: it is the only reachable deliverable, and most of it is guard-independent. |
| R2 | The 4-tuple to 3-tuple projection (Phase 8) does not hold definitionally — e.g. `keys'` computation forces a different `findSome?` matcher, as bit Phase 7. | M | M | Phase 8 is deliberately sized small and dispatched first precisely to retire this risk early. If the projection fails, fall back to transcribing the measure lemma directly against the 4-tuple stepper (Phase 9 absorbs the extra case work); record the exact `lean_goal`. Phase 7's matcher-compilation gotchas (below) apply directly. |
| R3 | Transcribing `modalExpMeasure_step_lt_gen` over `modalUniverseS4` (Phase 9) hits a step where K's universe was load-bearing beyond `hb`/`hW`. | M | L | Phase 3's primitives are already universe-generic (verified: they take an arbitrary `U`), and `modalExpMeasure_entry_le_fuelS4`'s own docstring records that the `modalWork ≤ 2*U.length` step is universe-agnostic. Re-derive `modalExpMeasure_split`/`_append` locally first (they are the only `private` dependencies). |
| R4 | The top-loop induction (Phase 10) is the largest genuinely-new phase; Phase 7 showed even a near-complete skeleton needed non-trivial defeq debugging. | H | M | Dispatch `--hard` (H8 phase sizing, H9 wrap-up). Phases 8-9 remove the measure component from it entirely, cutting its size to ~200-350 lines. Commit at every green sub-step. |
| R5 | A phase cannot close and is tempted toward a `sorry`/placeholder or an under-scoped statement. | H | L | Hard constraint: never insert `sorry`/`admit`/vacuous placeholder or weaken a theorem statement to make it close. Mark the phase `[BLOCKED]` with the exact reached `lean_goal` and stop. |
| R6 | Accidental edit/regression of a frozen Phase 1-7 or S5/B deliverable. | H | L | Additive-only by construction. Run `lean_verify` on `instDecidableS5Valid`, `modalTableauB`, and `modalStepBranchS4Keyed_preserves_S4KeyedHintikkaInv` after Phases 10 and 11. |
| R7 | A new public declaration pulls a non-standard axiom. | M | L | `lean_verify` each new public declaration; require `propext`/`Classical.choice`/`Quot.sound` only. |
| R8 | Task terminates with `Decidable (s4Valid φ)` open and this is mistaken for failure or for a missing deliverable. | M | M | Stated plainly in the Overview, Goals, and completion summary: the decidability instance is out of scope by design, deferred to the spawned task. Do not record it as an unmet goal of this plan. |

### R1 blast radius (what guard-narrowing would and would not affect)

Recorded now so that, if Route (i) is later taken, the re-work is bounded and predictable rather
than an open-ended re-audit. Narrowing `blockingWorldS4Keyed` changes **when the guard returns
`some wBlock` versus `none`** — i.e. fewer redirects, more fresh mints. Consequences, in decreasing
order of severity:

1. **Highest impact — the pigeonhole world bound, which the *termination* line depends on.**
   `modalApplyOneS4Keyed_outputsSubsetUniverse_S4` (Phase 4, `LoopChecking.lean:5371`) consumes
   `modalStepBranchS4_worldBound φ₀ b keys hWC hKT hKD hKI` (frozen task-511), whose `hKD` is
   `keysDistinct` (`∀ w1 w2 k1 k2, (w1,k1) ∈ keys → (w2,k2) ∈ keys → w1 ≠ w2 → k1 ≠ k2`) and whose
   `hKI` is `k ⊆ signedSubfmls φ₀` — together exactly the pigeonhole giving
   `modalMaxWorld b < modalWorldBoundS4 φ₀`. **`keysDistinct` is precisely what the *unrestricted*
   guard buys**: a world is born only when no existing world has the same birth content. Under an
   acc-reachability-restricted guard, two same-birth-content worlds that are mutually unreachable
   could both be born, and `keysDistinct` would fail. That would invalidate the world bound, hence
   Phase 4's `_outputsSubsetUniverse_S4`, hence v3 Phase 9's measure decrease and Phase 5's fuel
   sufficiency. **This is a prediction from the verified hypothesis shapes, not a verified fact —
   the spawned task must check it before committing to Route (i)**, and if it holds, Route (i)
   needs a replacement world bound (e.g. path-length-bounded ancestor blocking) rather than a
   drop-in guard swap.
2. **Medium impact — `modalStepBranchS4Keyed_blocked_witness_mem`** (Phase 7,
   `LoopChecking.lean:5750`). Its statement is conditional on `blockingWorldS4Keyed … = some wBlock`,
   so it remains *true* under a narrower guard, but its proof must be re-checked to confirm the
   narrowed guard still guarantees the birth-content match it relies on. Single-lemma re-check.
3. **Medium impact — v3 Phase 10's `none`-case dispatch for the box-negative and diamond-positive
   shapes.** This is where the Hintikka clauses are verified, and it currently must handle the
   "matched, but redirected to a blocked world, so no NEW witness formula was emitted" sub-case via
   item 2 plus `S4KeyedHintikkaInv.eBoxNegWitness`/`eDiamondPosWitness`. Under a narrower guard the
   sub-case **narrows but does not vanish** (some redirects survive), so the argument *structure*
   is preserved; only the guard's `some`-characterization changes. **This is the specific part of
   the Hintikka argument that would need re-work — not the whole of Phase 10.**
4. **No impact expected — Phase 6's witness-permanence fields**
   (`S4KeyedHintikkaInv_weaken`'s `eBoxNegWitness`/`eDiamondPosWitness` cases,
   `LoopChecking.lean:5721`). These are monotonicity arguments in `b`/`acc` only, with no reference
   to the guard.
5. **No impact — Phases 1, 2, 3, and the propositional-shape half of Phase 6.**
   `hintikka_congr_S4` is unconditional in `keys` and holds for any guard; Phase 3's primitives are
   pure list combinatorics over an arbitrary `U`.

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1, 2 | -- |
| 2 | 3, 4, 5, 6 | 1, 2 |
| 3 | 7 | 6 |
| 4 | 8 | 1 |
| 5 | 9 | 3, 4, 5, 8 |
| 6 | 10 | 7, 9 |
| 7 | 11 | 2, 10 |

Phases within the same wave can execute in parallel. Waves 1-3 are already `[COMPLETED]`. The
remaining path (Waves 4-7) is strictly sequential — each remaining phase consumes the previous
phase's output — and each is sized to one agent run.

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

### Phase 3 (v2 handoff 3a): Re-derive generic combinatorial measure primitives [COMPLETED]

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
- **Files modified:** `Cslib/Logics/Modal/Tableau/LoopChecking.lean` (additive; `private` lemmas).
- **Verification:** `lean_goal` no remaining goals on all four; `lean_verify` axiom-clean; frozen
  defs unchanged.

**v3 note (no re-work):** all four are stated over an **arbitrary** universe `U`
(`LoopChecking.lean:4793`/`4869`/`4889`/`4904`), so they instantiate at `U := modalUniverseS4 φ₀`
unchanged. This is what makes v3 Phase 9's transcription tractable.

### Phase 4 (v2 handoff 3b): Per-call measure obligations for `modalApplyOneS4Keyed φ₀ keys`, ∀ `keys` [COMPLETED]

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
- **Files modified:** `Cslib/Logics/Modal/Tableau/LoopChecking.lean` (additive).
- **Verification:** `lean_goal` no remaining goals; `lean_verify` axiom-clean.
- **Completed:** 2026-07-24. Landed (all `private`, additive, in `LoopChecking.lean`):
  `modalTBoxSelf_fresh`, `modalTDiaNegSelf_fresh`, `modalFourBoxProp_fresh`,
  `modalFourDiaNegProp_fresh`, `modalApplyOneT_persistentFresh`, `modalApplyOneT_branchingLength`,
  `modalApplyOneS4Rules_persistentFresh`, `modalApplyOneS4Rules_branchingLength`,
  `modalApplyOneS4Keyed_persistentFresh_S4`, `modalApplyOneS4Keyed_branchingLength_S4`,
  `modalApplyOneS4Keyed_outputsSubsetUniverse_S4` (the three target per-call obligations, each
  `∀ keys`). All `lean_verify`-confirmed `propext`/`Classical.choice`/`Quot.sound` only;
  `lake build Cslib.Logics.Modal.Tableau.LoopChecking` green, zero new warnings, zero `sorry`.

**v3 note (no re-work):** these three are the exact inputs v3 Phase 9 consumes. Their current
locations are `LoopChecking.lean:5270` (`_persistentFresh_S4`), `:5318` (`_branchingLength_S4`),
`:5371` (`_outputsSubsetUniverse_S4`). Re-grep before use — Phase 8's insertions will shift them.

### Phase 5 (v2 handoff 3c): `modalFuelS4` + entry-measure sufficiency + fuel repoint [COMPLETED]

- **Goal:** Define an S4-specific fuel from `modalUniverseS4 φ₀`'s length and prove the entry
  configuration's measure is within it, then repoint `modalTableauS4Keyed`'s fuel argument.
  CONFIRMED not free: at `modalComplexity φ₀ = 0`, `modalWorldBoundS4 φ₀ ≤ 4` exceeds K's
  `modalWorldBound φ₀ = 1`, so `modalFuel φ₀` is not provably sufficient.
- **Tasks:**
  - [x] Define `modalFuelS4 φ₀ := 3 ^ (2 * (modalUniverseS4 φ₀).length + 1)` (or similar closed form).
        *(landed as `modalFuelS4 φ₀ := 3 ^ (4 * (2 * modalComplexity φ₀ + 1) * (modalWorldBoundS4 φ₀ + 1))`
        -- the exact closed form `modalFuel` itself uses, with `modalWorldBoundS4` swapped in;
        placed early in the file, right after `modalUniverseS4_length_le`, so it is in scope for
        `modalTableauS4Keyed`'s def which comes later.)*
  - [x] Prove entry-measure ≤ `modalFuelS4 φ₀`, mirroring `modalExpMeasure_entry_le_fuel`'s proof
        shape (`FmpMeasure.lean:208-247`) via `modalWork`'s `|U\b|+|U\e|` form — no K-fuel comparison.
        *(landed as `modalExpMeasure_entry_le_fuelS4`; the `modalWork ≤ 2*U.length` step transfers
        verbatim since it is universe-agnostic.)*
  - [x] Repoint `modalTableauS4Keyed`'s fuel argument (Phase 1 def) from `modalFuel φ₀` to
        `modalFuelS4 φ₀` (small, safe def edit; the only edit to a Phase-1 declaration).
  - [x] `lean_build` green; no `sorry`; `lean_verify` axiom-clean.
- **Timing:** 2 hours (~100-150 lines)
- **Depends on:** 1 (edits `modalTableauS4Keyed`'s fuel argument)
- **Files modified:** `Cslib/Logics/Modal/Tableau/LoopChecking.lean` (additive + one-line fuel repoint).
- **Verification:** `lean_goal` no remaining goals on the entry-measure lemma; `modalTableauS4Keyed`
  recompiles green with the new fuel; `lean_verify` axiom-clean.
- **Completed:** 2026-07-24. `lean_verify modalExpMeasure_entry_le_fuelS4`: `propext`/`Quot.sound`
  only. Regression check `lean_verify hintikka_congr_S4` (consumes `modalExpandBranchesS4Keyed`,
  `modalTableauS4Keyed`'s sibling def): unchanged, `propext`/`Classical.choice`/`Quot.sound` only.
  `lake build` green, zero new warnings, zero `sorry`.

**v3 note (no re-work):** `modalExpMeasure_entry_le_fuelS4` (`LoopChecking.lean:5432`) is stated over
`modalExpMeasure (modalUniverseS4 φ₀) …`. This fixes the universe v3 Phase 9's measure lemma must be
transcribed over, and is the reason `modalExpMeasure_step_lt_gen` cannot be called directly.

### Phase 6 (v2 handoff 3d-i): Keys-threaded Hintikka-tracking invariant bundle [COMPLETED]

- **Goal:** Define the bespoke keys-threaded analogue of the `ModalLoopInvHintikka` bundle
  (`CompletenessLoop.lean:262-337`) and prove its monotone-field lemmas, WITHOUT yet proving
  full single-step preservation (Phase 7).
- **Tasks:**
  - [x] Define the invariant structure/predicate threading `keys` as an extra argument, with fields
        analogous to `hintikkaInv`/`eBoxOnlyNeg`/`eBoxNegWitness`/`eDiamondOnlyPos`/`eDiamondPosWitness`.
        Exploit `modalHintikkaClauseGen` (`Completeness.lean:652`) carving ALL box/diamond shapes
        (both signs) as vacuous `True` — the real tracking burden is only propositional shapes +
        box-negative/diamond-positive witness existence.
        *(landed as `S4KeyedHintikkaInv`, carrying ONLY the five Hintikka-specific conjuncts —
        the universe-closure/keys-bookkeeping conjuncts already live in the frozen `S4LoopInv`
        and are threaded as a separate ambient hypothesis rather than duplicated.)*
  - [x] Prove the propositional-shape field is branch/`acc`-independent
        (`modalApplyOne_fst_eq_of_not_box`-style; landed for K), hence trivially monotone as the
        branch grows.
        *(landed as `modalApplyOneS4Keyed_fst_eq_of_not_box` (F8 discharge, two dispatch layers
        deeper than T's own `modalApplyOneT_localShapeInvariance`) + a territory-local
        re-derivation `modalHintikkaClauseGen_lift_S4` of `Completeness.lean`'s `private`
        `modalHintikkaClauseGen_lift`, composed in `S4KeyedHintikkaInv_weaken`'s `hintikkaInv`
        case.)*
  - [x] Prove the witness-existence fields are permanent once recorded (`acc`/`b` only grow — same
        monotonicity argument as K/S5/B's landed fields).
        *(landed as the `eBoxNegWitness`/`eDiamondPosWitness` cases of `S4KeyedHintikkaInv_weaken`,
        consuming raw `hbsub`/`haccsub` hypotheses; the supporting `modalApplyOneS4Keyed_hasEdge_mono`
        per-call fact — built from the unconditional accessibility-snd equalities
        `modalApplyOneT_snd_eq`/`modalApplyOneS4Rules_snd_eq` against raw K plus
        `modalApplyOne_fresh_local` — is the per-step instantiation Phase 7 will feed into
        `haccsub`.)*
  - [x] `lean_build` green; no `sorry`; `lean_verify` axiom-clean.
- **Timing:** 3 hours (~250-400 lines)
- **Depends on:** none (definitions + monotonicity consume only landed rules)
- **Files modified:** `Cslib/Logics/Modal/Tableau/LoopChecking.lean` (additive).
- **Verification:** `lean_goal` no remaining goals on each field lemma; `lean_verify` axiom-clean.
- **Completed:** 2026-07-24 (commit `828aefd4`). `lean_verify` confirmed
  `modalApplyOneS4Keyed_fst_eq_of_not_box`/`modalApplyOneS4Keyed_hasEdge_mono`/
  `S4KeyedHintikkaInv_weaken` each `propext`/`Classical.choice`/`Quot.sound` only;
  `lake build Cslib.Logics.Modal.Tableau.LoopChecking` green, zero new warnings, zero `sorry`.

### Phase 7 (v2 handoff 3d-ii): Single-step invariant preservation [COMPLETED]

- **Goal:** Prove that `modalStepBranchS4Keyed` preserves the Phase 6 invariant bundle from parent
  to every child branch (the `AuxStepPreserved` analogue, `CompletenessLoop.lean:262-337`),
  threading `keys → keys'`.
- **Tasks:**
  - [x] State the single-step preservation lemma: for each child `b'` produced by
        `modalStepBranchS4Keyed`, the Phase-6 invariant holds at `(b', e', newAcc, keys')` given it
        holds at `(b, e, acc, keys)`.
        *(landed as `modalStepBranchS4Keyed_preserves_S4KeyedHintikkaInv`.)*
  - [x] Carry the bundled hypothesis from `modalStepBranchS4_preserves_S4LoopInv`
        (`LoopChecking.lean:4614-4651`): `S4LoopInv φ₀ b' e' newAcc keys' ∧ keysWorldsKnown b' ∧
        worldsContiguousS4 b'`.
        *(altered: the theorem takes the ambient `S4LoopInv φ₀ b e acc keys` hypothesis directly
        (for `keyLowerBd`'s blocked-witness argument), rather than re-deriving the full
        `keysWorldsKnown`/`worldsContiguousS4` triple inline — those are consumed unchanged from
        the frozen `S4LoopInv` structure, not duplicated.)*
  - [x] Case-split per rule shape reusing Phase 6's monotone-field lemmas; use an S4Keyed-specific
        `_none_saturated` lemma (~25-line analogue of `modalStepBranchGen_none_saturated`,
        `Completeness.lean:809`) for the saturated case.
        *(altered: no separate `_none_saturated` lemma was needed — `findSome?_eq_some`'s own
        `some`-witness plus `split_ifs at hsf with hexp` already rules out the saturated
        (`e.any (· == sf) = true`) sub-case at the point `sf` is selected, so the three-way
        mint-unblocked/mint-blocked/non-mint split covers every reachable branch directly.)*
  - [x] `lean_build` green; no `sorry`; `lean_verify` axiom-clean.
- **Timing:** 3 hours (~200-350 lines)
- **Depends on:** 6
- **Files modified:** `Cslib/Logics/Modal/Tableau/LoopChecking.lean` (additive).
- **Verification:** `lean_goal` no remaining goals; frozen `modalStepBranchS4_preserves_S4LoopInv`
  unchanged; `lean_verify` axiom-clean.
- **Completed:** 2026-07-24. This dispatch recovered ~376 uncommitted lines left by a
  session-limit-killed prior agent (the theorem's full case-split skeleton, already essentially
  correct), then fixed three real bugs blocking the build: (1) a redundant `clear hnbd` after an
  `obtain` that had already consumed it; (2) a broken helper lemma
  `keysMatch_eq_keys_of_not_mint` whose `hnbd` hypothesis (depending on the same `s`/`φ` being
  matched) was auto-reverted into its compiled matcher's motive by Lean's equation compiler,
  making it permanently non-defeq to the call sites' own (hnbd-free) inline match term — deleted
  as dead code and replaced at all 4 call sites with an inline `rcases hs : sf.sign with _ | _ <;>
  rcases hf : sf.formula with _ | _ | _ | _ | _ | ψ | ψ <;> dsimp only [hs, hf]` case split (the
  same idiom already used successfully at `modalStepBranchS4_preserves_keyLowerBd`,
  `LoopChecking.lean:1491`) followed by two `absurd ⟨hs, ψ, hf⟩ hnbd.{1,2}` closers for the two
  surviving (impossible) box/diamond branches — note `Sign`'s constructor order is `pos, neg`
  (`Sign.lean:47-50`), so the surviving-goal order is (pos,diamond) then (neg,box), NOT the
  reverse; (3) two `hinveq` `have`s stated with bare `sf` instead of the exposed
  `⟨sf.sign, sf.formula, sf.label⟩` structure literal, which made the later `rw [hff] at hinveq`
  steps unable to find `sf.formula` as a rewritable subterm (structure-eta makes the two forms
  defeq, so restating the type change nothing semantically). `lean_verify` on
  `modalStepBranchS4Keyed_preserves_S4KeyedHintikkaInv` confirms
  `propext`/`Classical.choice`/`Quot.sound` only. Full CSLib CI pipeline (build, checkInitImports,
  lint, lint-style, shake, mk_all) green with zero new warnings versus the pre-Phase-7 baseline
  (`lake build Cslib.Logics.Modal.Tableau.LoopChecking`: 847 jobs, success). Zero `sorry` in the
  file (one pre-existing docstring-prose mention only).

**v3 note (no re-work):** the three bug-fix idioms recorded above are the load-bearing per-step API
v3 Phases 8-10 assemble against — treat them as stable/frozen inputs, not subject to re-derivation.
The `Sign` constructor-order gotcha (`pos` first) applies to every new case split in Phases 8-11.

### Phase 8: 4-tuple stepper projection bridge + local measure-split helpers [IN PROGRESS]

- **Goal:** Retire the two structural unknowns standing between the landed Phase 3-4 assets and a
  keyed measure-decrease lemma: (a) bridge the keyed 4-tuple stepper to the generic 3-tuple
  `modalStepBranchGen` projection, and (b) make the two `private` `modalExpMeasure` split/append
  helpers available territory-locally. Nothing semantic; this phase is deliberately small and
  dispatched first because it is where a structural mismatch, if any, will surface cheaply.
- **Tasks:**
  - [ ] State and prove the projection lemma (suggested name
        `modalStepBranchS4Keyed_proj_stepBranchGen`): for all `φ₀ b e acc keys`,
        `modalStepBranchS4Keyed φ₀ b e acc keys = some (newBs, newExps, newAcc, keys')` implies
        `modalStepBranchGen (modalApplyOneS4Keyed φ₀ keys) b e acc = some (newBs, newExps, newAcc)`.
        Both sides are a `b.findSome?` over the same `expanded.any (· == sf)` guard and the same four
        `RuleResult` arms (`Saturation.lean:122-142` vs `LoopChecking.lean:780`), so this is a
        `findSome?`-congruence argument, not a semantic one. **Also record the converse/`none`
        direction** if it falls out — Phase 10's saturated case will want it.
  - [ ] Re-derive `modalExpMeasure_split` (`FmpMeasure.lean:3174`) and `modalExpMeasure_append`
        (`FmpMeasure.lean:3191`) as territory-local `private` lemmas in `LoopChecking.lean` — both
        are `private` upstream and cannot be called, exactly as with Phase 3's four primitives.
        These are small (~17 lines each) and universe-generic; copy the proofs.
  - [ ] Confirm `pow3_add_one_le` / `pow3_two_add_one_le`
        (`Cslib/Foundations/Logic/Tableau/Measure.lean:128`/`117`) are public and importable from
        `LoopChecking.lean` — they are the only other external dependency Phase 9 needs.
  - [ ] `lake build Cslib.Logics.Modal.Tableau.LoopChecking` green; no `sorry`; `lean_verify`
        axiom-clean.
- **Timing:** 1.5 hours (~100-170 lines; small, structural, low semantic risk)
- **Depends on:** 1
- **Files to modify:** `Cslib/Logics/Modal/Tableau/LoopChecking.lean` (additive; `private` lemmas).
- **Verification:**
  - `lean_goal` reports no remaining goals on the projection lemma and both re-derived helpers.
  - `lean_verify` on each new declaration: `propext`/`Classical.choice`/`Quot.sound` only.
  - `lake build` green with zero new warnings versus the Phase 7 baseline (8 pre-existing
    `unusedSimpArgs` warnings at `LoopChecking.lean` ~2533/3054/3058/3120/3124/3145/3152).
  - Frozen `modalStepBranchS4Keyed` and `modalStepBranchGen` byte-unchanged.
- **Contingency:** if the projection does not hold definitionally (R2 — most likely cause is the
  `keys'` computation forcing a different compiled matcher, the exact failure mode that bit Phase 7),
  do NOT force it. Record the exact `lean_goal`, drop the projection, and note in the handoff that
  Phase 9 must transcribe the measure lemma directly against the 4-tuple stepper. Phase 8's second
  and third tasks are independent of the first and land regardless.

### Phase 9: Keyed per-step measure decrease over `modalUniverseS4` [COMPLETED]

- **Goal:** Establish the fuel-decrease fact the top-loop induction needs: one step of the keyed
  stepper strictly decreases `modalExpMeasure (modalUniverseS4 φ₀) …`. This is a **transcription** of
  `modalExpMeasure_step_lt_gen` (`FmpMeasure.lean:3227`, public) over the S4 universe — it cannot be
  called directly, because that lemma is hardwired to `modalUniverse φ0`/`modalWorldBound φ0` while
  this line runs over `modalUniverseS4 φ₀`/`modalWorldBoundS4 φ₀` (see "Measure-Decrease Lead").
- **Tasks:**
  - [x] State `modalExpMeasure_step_lt_S4Keyed`, mirroring `modalExpMeasure_step_lt_gen`'s
        conclusion shape with `modalUniverse φ0` replaced by `modalUniverseS4 φ₀`, `hW` replaced by
        `modalMaxWorld bh < modalWorldBoundS4 φ₀`, and `hstep` phrased against the keyed stepper via
        Phase 8's projection.
        *(landed with `hstep : modalStepBranchS4Keyed φ₀ bh e acc keys = some (…, keys')`; the
        proof's first step calls `modalStepBranchS4Keyed_proj_stepBranchGen` to obtain the
        generic-driver form, which is what the rest of the transcription consumes. The raw
        `modalMaxWorld bh < modalWorldBoundS4 φ₀` fact is NOT a separate parameter — it is derived
        internally by `modalApplyOneS4Keyed_outputsSubsetUniverse_S4` from `hWC`/`hKT`/`hKD`/`hKI`,
        so those five hypotheses replace the generic template's `accFreshInv`/`hW` pair, matching
        the "not free" note in the next task.)*
  - [x] Feed the three landed Phase 4 obligations at the three hypothesis positions (re-grep exact
        line numbers first — Phase 8's insertions shift them):
        `modalApplyOneS4Keyed_branchingLength_S4` → `hBranchingLength`;
        `modalApplyOneS4Keyed_persistentFresh_S4` → `hPersistentFresh`;
        `modalApplyOneS4Keyed_outputsSubsetUniverse_S4` → `hOutputsSubsetUniverse`. **Note the third
        carries extra hypotheses** the generic form does not (`hknown`/`hWC`/`hKT`/`hKD`/`hKI`);
        these must be threaded into the lemma's own signature and supplied from the ambient
        `S4LoopInv` at the Phase 10 call site — they are not free.
        *(landed: all three fed exactly as named, at their post-Phase-8 locations `:5270`/`:5318`/
        `:5371`; the five extra hypotheses threaded as raw parameters of
        `modalExpMeasure_step_lt_S4Keyed` itself.)*
  - [x] Transcribe the four `RuleResult` arms of the generic proof
        (`FmpMeasure.lean:3275-3335`): `.linear` and `.persistent` close via `pow3_add_one_le`,
        `.branching` via `pow3_two_add_one_le` after `hBranchingLength` gives `brs.length = 2`,
        `.notApplicable` is vacuous. The `modalWork`-drop steps consume Phase 3's four primitives at
        `U := modalUniverseS4 φ₀` (they are universe-generic; verified). The split/append steps
        consume Phase 8's local re-derivations.
        *(landed verbatim per the generic template's case split. One deviation found: the generic
        proof also needs the **private** `modalExpMeasure_const_exp` (`FmpMeasure.lean:3204`),
        which Phase 8's task list did not enumerate (only `_split`/`_append` were named) — a third
        local re-derivation `modalExpMeasure_const_exp_S4` was added alongside the Phase 9 lemma,
        by the identical re-derivation pattern.)*
  - [x] `lake build Cslib.Logics.Modal.Tableau.LoopChecking` green; no `sorry`; `lean_verify`
        axiom-clean. If a step resists, `[BLOCKED]` with the exact `lean_goal`.
- **Timing:** 2.5 hours (~150-250 lines; mostly mechanical transcription, one genuinely new
  hypothesis-threading decision)
- **Depends on:** 3, 4, 5, 8
- **Files to modify:** `Cslib/Logics/Modal/Tableau/LoopChecking.lean` (additive).
- **Verification:**
  - `lean_goal` reports no remaining goals on `modalExpMeasure_step_lt_S4Keyed`.
  - `lean_verify modalExpMeasure_step_lt_S4Keyed`: `propext`/`Classical.choice`/`Quot.sound` only.
  - The statement's universe is `modalUniverseS4 φ₀` and its world bound is `modalWorldBoundS4 φ₀` —
    i.e. it composes with `modalExpMeasure_entry_le_fuelS4` (`LoopChecking.lean:5432`). Check this
    explicitly; a lemma accidentally stated over K's universe is useless here and would not be
    caught by the build.
  - `lake build` green, zero new warnings; `FmpMeasure.lean` byte-unchanged.
- **Contingency:** if the transcription reveals that K's universe was load-bearing somewhere beyond
  `hb`/`hW` (R3), stop and record the exact step. Do not weaken the statement to make it close.
- **Completed:** 2026-07-24 (commit `31557bf1`). `lean_verify` confirms both new declarations
  (`modalExpMeasure_step_lt_S4Keyed`, `modalExpMeasure_const_exp_S4`) `propext`/
  `Classical.choice`/`Quot.sound` only. `lake build Cslib.Logics.Modal.Tableau.LoopChecking`:
  847 jobs, exit 0, zero new warnings versus the Phase 8 baseline (the same 8 pre-existing
  `unusedSimpArgs` + 1 `unusedDecidableInType` warnings). Zero `sorry` in the file (the one
  pre-existing docstring-prose mention at `:4619` only). `lake lint`/`lake exe lint-style`: the
  2 errors surfaced by `lake lint` are in unrelated files (`CS5Completeness.lean`,
  `Saturation.lean`, from concurrent out-of-scope work) — zero hits in `LoopChecking.lean` from
  either check. `FmpMeasure.lean` byte-unchanged (read-only). `lake exe checkInitImports`: clean.

### Phase 10: Top-loop induction — `modalExpandBranchesS4Keyed_hintikka` [COMPLETED]

- **Goal:** Assemble the termination top-loop: an open branch produced by the keyed driver is a
  Hintikka set for the keyed rule, then bridge to the concrete `modalHintikkaSetS4` form. This is the
  single largest genuinely-new phase remaining and the core of the completeness line.
- **Template:** `modalExpandBranchesHintikka` (`CompletenessLoop.lean:1430-1660+`). Structure:
  (1) outer induction on `fuel`; (2) a `suffices key : …` restating the goal in terms of the
  `pending`/`done` worklist split; (3) inner induction on `pending` (`nil`/`cons`); (4) within
  `cons`, `by_cases hcl : isModalClosed bh`, else `cases hstep : modalStepBranchS4Keyed …`;
  (5) the `none` (saturated/open) case is where Hintikka clauses are verified per-shape; (6) the
  `some step` case recurses via the outer fuel induction.
- **Tasks:**
  - [x] Thread the per-index invariant as the **conjunction** `S4LoopInv φ₀ bi ei ai keysi ∧
        S4KeyedHintikkaInv φ₀ bi ei ai keysi`. There is no single bundled structure playing
        `ModalLoopInvHintikka`'s role for the keyed driver — Phase 6 deliberately did not bundle
        `S4LoopInv`'s fields. Use Phase 7's own call-site convention (ambient `S4LoopInv` plus the
        two proof-internal `keysWorldsKnown`/`worldsContiguousS4` auxiliaries) verbatim.
        *(landed as a literal 4-way conjunction `S4LoopInv ∧ S4KeyedHintikkaInv ∧
        keysWorldsKnown ∧ worldsContiguousS4` in the per-index hypothesis, rather than nesting
        the two auxiliaries inside a separate pair — simpler to destructure at each call site.)*
  - [x] Note the **extra `keys`/`keys'` worklist column**: `modalExpandBranchesS4Keyed`
        (`LoopChecking.lean:4689`) carries `keyss` alongside `branches`/`expandedSets`/`accs`, and its
        `processNext` threads `pendingKeys`/`doneKeys`. Every recursive call and worklist tuple in the
        induction needs the extra component — absent from anything in the generic file.
        *(threaded throughout: `keyss` in the outer statement, `pendingKeys`/`doneKeys` in the
        `key`-suffices restatement and the inner `pending` induction, `List.replicate
        newBs.length keys'` alongside the `newAcc` replicate in the `some step` recursion.)*
  - [x] `some step` case: consume Phase 7's `modalStepBranchS4Keyed_preserves_S4KeyedHintikkaInv`
        (`LoopChecking.lean:5949`) for invariant preservation and Phase 9's
        `modalExpMeasure_step_lt_S4Keyed` for the fuel decrease, supplying the latter's
        `hknown`/`hWC`/`hKT`/`hKD`/`hKI` from the ambient `S4LoopInv`.
        *(landed verbatim, plus `modalStepBranchS4_preserves_S4LoopInv` (Phase 7,
        `LoopChecking.lean:4624`) consumed for the combined `S4LoopInv`/`keysWorldsKnown`/
        `worldsContiguousS4` preservation in one call, and a new territory-local
        `modalStepBranchS4Keyed_newExps_const` (re-deriving `CompletenessLoop.lean`'s `private
        modalStepBranchGen_newExps_const` for the 4-tuple stepper) to get the constant-`newExp`
        form the measure lemma's hypothesis requires.)*
  - [x] `none` (saturated) case: dispatch each Hintikka conjunct per-shape
        (`atom`/`bot`/`imp`/`and`/`or`/`box`/`diamond`, each split on `sign`), as
        `modalExpandBranchesHintikka` does at `CompletenessLoop.lean:1538-1618`. **Do NOT use**
        `modalStepBranchGen_none_saturated` (`Completeness.lean:809`) — mirror Phase 7's own
        `findSome?_eq_some` + `split_ifs at hsf with hexp` case-split idiom instead, which already
        rules out the saturated sub-case at the point `sf` is selected.
        *(landed as a new territory-local `modalStepBranchS4Keyed_none_saturated`, mirroring the
        `findSome?_eq_none_iff` + case-split idiom directly against the keyed 4-tuple stepper,
        since no converse/`none`-direction projection to the generic 3-tuple driver was landed in
        Phase 8.)*
  - [x] Box-negative / diamond-positive shapes: the keyed driver has **no `RuleApplicationSpecCore`
        instance**, so `hs.boxNegWitness'`/`hs.diaPosWitness'` are unavailable. Use Phase 7's
        `modalStepBranchS4Keyed_blocked_witness_mem` (`LoopChecking.lean:5750`, re-grep) plus
        `S4KeyedHintikkaInv.eBoxNegWitness`/`eDiamondPosWitness` to handle the "matched but redirected
        to a blocked world, so no NEW witness formula emitted" sub-case. **This is the sub-argument
        R1 identifies as guard-sensitive** — keep it localized and clearly delimited in the proof so
        a later guard narrowing has a bounded re-work target.
        *(finding: `modalStepBranchS4Keyed_blocked_witness_mem` is NOT called directly from this
        phase's own code — it is already fully consumed, internally, by Phase 7's landed
        `modalStepBranchS4Keyed_preserves_S4KeyedHintikkaInv`. By the point this phase's `none`
        case is reached, every box-neg/dia-pos formula on the branch is provably `∈ e` (two new
        territory-local lemmas, `modalApplyOneS4Keyed_{boxNeg,diaPos}_ne_notApplicable`, show the
        keyed rule's result is `.linear _` — never `.notApplicable` — at these two shapes in BOTH
        the blocked and unblocked sub-cases, guard-independently), so `hHinv.eBoxNegWitness`/
        `eDiamondPosWitness` (established along the induction path via Phase 7) applies directly
        with no redirect-specific case split needed HERE. The R1-sensitive sub-case is therefore
        already isolated inside Phase 7's landed, unmodified code — this phase's own contribution
        is guard-independent, narrowing R1's future blast radius further than anticipated.)*
  - [x] Close with `hintikka_congr_S4` (Phase 2, `LoopChecking.lean:4767`) +
        `modalHintikkaSetS4_eq` (`LoopChecking.lean:3884`, re-grep) to reach the concrete
        `modalHintikkaSetS4 φ₀ b acc` target.
        *(landed as `rw [modalHintikkaSetS4_eq, ← hintikka_congr_S4 φ₀ k]` immediately after
        obtaining the saturated-leaf invariant, rewriting the goal to the keyed-rule
        `modalHintikkaSetGen` form before dispatching the four conjuncts.)*
  - [x] `lake build Cslib.Logics.Modal.Tableau.LoopChecking` green; no `sorry`; `lean_verify`
        axiom-clean. If the induction resists, `[BLOCKED]` with the exact `lean_goal`.
- **Timing:** 3 hours (~200-350 lines). Dispatch `--hard` with real runway (fresh session), per the
  Phase 7 experience that even a near-complete skeleton needed three non-trivial defeq/matcher fixes.
- **Depends on:** 7, 9 (and consumes Phase 2 + landed `modalHintikkaSetS4_eq`)
- **Files to modify:** `Cslib/Logics/Modal/Tableau/LoopChecking.lean` (additive).
- **Verification:**
  - `lean_goal` reports no remaining goals on `modalExpandBranchesS4Keyed_hintikka`.
  - `lean_verify modalExpandBranchesS4Keyed_hintikka`: `propext`/`Classical.choice`/`Quot.sound` only.
  - The conclusion is the concrete `modalHintikkaSetS4 φ₀ b acc` form (not the `…Gen` form) — confirm
    the `hintikka_congr_S4` + `modalHintikkaSetS4_eq` bridge actually fired.
  - Regression: `lean_verify instDecidableS5Valid` and `modalTableauB` still axiom-clean;
    `lean_verify modalStepBranchS4Keyed_preserves_S4KeyedHintikkaInv` unchanged.
  - `lake build` green, zero new warnings versus the Phase 7 baseline.
- **Contingency:** commit at every green sub-step (`task 535 phase 10.{O}: …`). If context runs out
  mid-phase, mark `[PARTIAL]` and write a continuation handoff recording exactly which Hintikka
  conjuncts are discharged and which remain.
- **Completed:** 2026-07-24. Landed `modalExpandBranchesS4Keyed_hintikka` plus four
  territory-local helper lemmas: `modalStepBranchS4Keyed_newExps_const`,
  `modalStepBranchS4Keyed_none_saturated`, `modalApplyOneS4Keyed_boxNeg_ne_notApplicable`,
  `modalApplyOneS4Keyed_diaPos_ne_notApplicable`. `lean_verify` on the top-loop theorem and on
  the single-step preservation regression target both confirm `propext`/`Classical.choice`/
  `Quot.sound` only. `lake build Cslib.Logics.Modal.Tableau.LoopChecking`: 847 jobs, exit 0, zero
  new warnings versus the Phase 9 baseline (the same 10 pre-existing warnings: 8
  `unusedSimpArgs` + 1 `unusedSectionVars`-style hypothesis-unused note + 1 `longLine`, none in
  this task's additions). Zero `sorry` in the file (the one pre-existing docstring-prose mention
  at `:4619` only). `lake exe checkInitImports`, `lake lint`, `lake exe lint-style`: zero hits in
  `LoopChecking.lean` (a `lake shake` run surfaces unrelated pre-existing `sorry`s in
  `Propositional/Tableau/{Intuitionistic,Minimal}` files, out of this task's territory).
  `lean_verify instDecidableS5Valid` (`FrameCompleteness.lean`) confirms empty extra-axiom set,
  unaffected. Two deviations from the plan's anticipated shape, both recorded inline above: (1)
  the R1-sensitive blocked-redirect witness sub-case turned out to be fully absorbed by Phase 7's
  landed code rather than needing any new call to `modalStepBranchS4Keyed_blocked_witness_mem`
  from this phase; (2) the `none`-direction projection to the generic 3-tuple driver (flagged as
  a maybe-needed Phase 8 follow-up) was not available, so a direct territory-local
  `_none_saturated` re-derivation against the keyed 4-tuple stepper was added instead.

### Phase 11: Completeness — `modalTableauS4Keyed_complete` [IN PROGRESS]

- **Goal:** Land the task's closing deliverable: an open branch from the keyed driver yields a
  countermodel refuting `φ`. **Scope note**: this is the completeness half of v2 Phase 11 only. The
  decidability half (`s4Valid_decides`, `instDecidableS4Valid`) is deferred — do not attempt it here.
- **Tasks:**
  - [ ] State and prove `modalTableauS4Keyed_complete`, modeled on `modalTableauS5_complete`
        (`FrameCompleteness.lean:2336`), wiring: `modalTruthLemmaS4` (`FrameCompleteness.lean:232`),
        `extractModelS4` + `_refl`/`_trans`/`_hasEdge_imp_r` (`FrameCompleteness.lean:143-188`),
        `modalOpenBranchS4_countermodel` (`FrameCompleteness.lean:401`), `hintikka_congr_S4`
        (Phase 2), and `modalExpandBranchesS4Keyed_hintikka` (Phase 10). All wiring targets are
        verified present; re-grep line numbers before use.
  - [ ] **Do NOT** state `s4Valid_decides` or register `instDecidableS4Valid`, and do not state a
        weakened or one-directional stand-in for either. They require the deferred soundness line.
  - [ ] Regression check: `lean_verify instDecidableS5Valid` and `modalTableauB` still axiom-clean;
        frozen task-511 Phase 1-6 lemmas unchanged.
  - [ ] `lean_verify modalTableauS4Keyed_complete` axiom-clean.
- **Timing:** 2.5 hours (~150-250 lines)
- **Depends on:** 2, 10
- **Files to modify:** `Cslib/Logics/Modal/Tableau/FrameCompleteness.lean` (additive:
  `modalTableauS4Keyed_complete` only).
- **Verification:**
  - `lean_goal` reports no remaining goals on `modalTableauS4Keyed_complete`.
  - `lean_verify modalTableauS4Keyed_complete`: `propext`/`Classical.choice`/`Quot.sound` only.
  - `grep -n "instDecidableS4Valid\|s4Valid_decides" Cslib/` returns nothing — confirming the
    deferred half was not accidentally attempted or stubbed.
  - Full CSLib CI pipeline green: `lake build`, `lake exe checkInitImports`, `lake lint`,
    `lake exe lint-style`, `lake shake`, `lake exe mk_all --module`.

## Testing & Validation

- [ ] `lake build Cslib.Logics.Modal.Tableau.LoopChecking` green after each phase; zero `sorry`,
      zero `admit`, zero new `axiom`.
- [ ] `grep -n "\bsorry\b" Cslib/Logics/Modal/Tableau/LoopChecking.lean` returns only the
      docstring-prose mention (currently line 4619; re-grep after each phase's insertions).
- [ ] `lean_verify` on every new public declaration reports only `propext`/`Classical.choice`/
      `Quot.sound`.
- [ ] Zero new warnings versus the Phase 7 baseline (8 pre-existing `unusedSimpArgs` warnings in
      `LoopChecking.lean` at ~2533/3054/3058/3120/3124/3145/3152, none in this task's additions).
      Prefer `dsimp only [...]` over `simp only [...]` in multi-branch case splits where only one
      rewrite is load-bearing, to avoid triggering new `unusedSimpArgs`.
- [ ] Regression: `instDecidableS5Valid` and `modalTableauB` unchanged and axiom-clean.
- [ ] Regression: `lean_verify modalStepBranchS4Keyed_preserves_S4KeyedHintikkaInv` unchanged.
- [ ] Frozen task-511 Phase 1-6 deliverables (`S4LoopInv`, `blockingWorldS4Keyed`,
      `modalStepBranchS4Keyed`, `modalStepBranchS4_worldBound`, `modalHintikkaSetS4_eq`)
      byte-unchanged except for consuming references.
- [ ] Live `modalTableauS4` and S5's `ModalLoopAuxS5w`/`modalExpandBranchesHintikka` call site
      unchanged; `FmpMeasure.lean` byte-unchanged.
- [ ] `s4Valid_decides` and `instDecidableS4Valid` do NOT exist anywhere in the tree — the deferred
      half must not be partially landed.
- [ ] Full CI pipeline (cache/build/checkInitImports/lint/lint-style/shake/mk_all/test) green after
      Phase 11.

## Artifacts & Outputs

- plans/03_completeness-line-rescope.md (this file)
- Landed (Phases 1-7) in `Cslib/Logics/Modal/Tableau/LoopChecking.lean` — preserved, not re-derived:
  `modalExpandBranchesS4Keyed`, `modalTableauS4Keyed`, `hintikka_congr_S4`, the four `private`
  combinatorial primitives, `modalApplyOneT`/`S4Rules` freshness+branching lemmas, the three
  per-call obligations `modalApplyOneS4Keyed_{persistentFresh,branchingLength,outputsSubsetUniverse}_S4`,
  `modalFuelS4` + `modalExpMeasure_entry_le_fuelS4`, `S4KeyedHintikkaInv` +
  `S4KeyedHintikkaInv_weaken` + `modalApplyOneS4Keyed_{fst_eq_of_not_box,hasEdge_mono}`,
  `modalStepBranchS4Keyed_blocked_witness_mem`, and
  `modalStepBranchS4Keyed_preserves_S4KeyedHintikkaInv`.
- New in `Cslib/Logics/Modal/Tableau/LoopChecking.lean` (Phases 8-10): the 4-tuple→3-tuple
  projection lemma, territory-local `modalExpMeasure_split`/`_append` re-derivations,
  `modalExpMeasure_step_lt_S4Keyed`, and `modalExpandBranchesS4Keyed_hintikka`.
- New in `Cslib/Logics/Modal/Tableau/FrameCompleteness.lean` (Phase 11):
  `modalTableauS4Keyed_complete`.
- Not produced by this task (deferred/spawned): the blocked-mint-redirect soundness lemma,
  `modalTableauS4Keyed_sound`, `s4Valid_decides`, `instDecidableS4Valid`.
- summaries/03_completeness-line-summary.md (on implementation completion)

## Rollback/Contingency

- All work is additive: new declarations in `LoopChecking.lean` and `FrameCompleteness.lean`. No
  edits to frozen or shared-generic files (`FmpMeasure.lean`, `Saturation.lean`,
  `CompletenessLoop.lean`, `blockingWorldS4Keyed`) in this plan. Reverting = removing the added
  declarations; nothing landed in Phases 1-7 is disturbed.
- Each phase is independently committable at its green milestone; commit at every green sub-step
  (`task 535 phase {P}.{O}: {objective}`), not only at phase end.
- If a phase is `[BLOCKED]`, downstream phases stop cleanly with the recorded exact `lean_goal`;
  upstream phases remain committed. Never insert `sorry`/`admit` or weaken a statement to reach
  green.
- If a phase build fails, fix forward (correct the proof); never `git reset --hard` or discard
  uncommitted work to reach green, per the recovery ladder.
- Recommended dispatch mode for the remaining phases: `--hard` (H8 phase sizing, H9 wrap-up
  discipline). Phases 8 and 9 are small enough for standard mode if runway is short; Phase 10 should
  always get `--hard` and a fresh session.
- **If the spawned soundness task later narrows `blockingWorldS4Keyed`**: re-work is bounded to the
  five items enumerated in "R1 blast radius" above, in that order of severity. Re-verify item 1 (the
  pigeonhole world bound via `S4LoopInv.keysDistinct`) **first** — it affects the termination line,
  not just the Hintikka argument, and if it breaks, Route (i) needs a replacement world bound rather
  than a drop-in guard swap.
