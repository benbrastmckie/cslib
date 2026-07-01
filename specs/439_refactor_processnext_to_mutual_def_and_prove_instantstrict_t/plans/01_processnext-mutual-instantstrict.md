# Implementation Plan: Task #439 — Refactor `processNext` to `mutual` def and prove run-level `InstantStrict`

- **Task**: 439 - refactor_processnext_to_mutual_def_and_prove_instantstrict_t (Phase 3 of parent task 426)
- **Status**: [NOT STARTED]
- **Effort**: 5 hours
- **Dependencies**: 180 (parent task 426 phases 1, 2, 4, 5 already DONE green). Territory: shares `Completeness.lean` with task 427 — serialize, never parallelize.
- **Research Inputs**: specs/426_temporal_tableau_ordconstraints_redesign/reports/01_ordconstraints-redesign.md (Option B instant scheme); spawn-analysis (referenced in state.json artifacts)
- **Artifacts**: plans/01_processnext-mutual-instantstrict.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md, cslib.md, lean4.md
- **Type**: cslib
- **Lean Intent**: true

## Overview

Parent task 426 redesigned the temporal-tableau time-ordering invariant: the false
`ordConstraints_strict` was replaced by `TimeOrdering.InstantStrict` plus the `D = ℤ / f =
ord.instant` countermodel choice. Phases 1, 2, 4, 5 are complete, sorry-free, and green. The one
remaining piece (this task) is Phase 3: thread `InstantStrict` through the run-level saturation
loop so the extracted model is well-founded, then wire that result into `openBranch_branchSat`.

The blocker is structural: in `Cslib/Logics/Temporal/Tableau/Saturation.lean`, `processNext` is a
`let rec` nested inside `temporalExpandBranches`. The two functions are mutually recursive
(`processNext` calls `temporalExpandBranches`, and vice versa). Lean 4 generates no standalone
recursion/equation principle for a `let rec` binding, so the fuel/structural induction the proof
requires cannot be expressed. This plan (1) mechanically lifts the pair into a top-level
`mutual ... end` block, (2) establishes a single-step preservation lemma with the freshness
coupling invariant, (3) runs the induction to get the run-level `InstantStrict` result, and (4)
wires it into `Completeness.lean` and finalizes the parent task. Definition of done: full CI
green (`lake build`, `lake test`, `lake exe checkInitImports`, `lake exe lint-style`) with zero
new `sorry`, and parent task 426 marked completed.

### Research Integration

- Option B "instant" scheme (report 01): each `addFuture t tNew` sets `instant tNew = instant t + 1`;
  each `addPast t tNew` sets `instant tNew = instant t - 1`. `InstantStrict ord := ∀ a b, (a,b) ∈
  ord.constraints → ord.instant a < ord.instant b`.
- Phase 2 edge-by-edge lemmas already exist in `TimeOrdering.lean` and are the inductive step:
  - `instantStrict_empty : InstantStrict TimeOrdering.empty`
  - `instantStrict_addFuture (ord) (t tNew) (h : InstantStrict ord) (htne : t ≠ tNew)
    (hfresh : ∀ a b, (a,b) ∈ ord.constraints → a ≠ tNew ∧ b ≠ tNew) : InstantStrict (ord.addFuture t tNew)`
  - `instantStrict_addPast (…) : InstantStrict (ord.addPast t tNew)` (symmetric)
- Freshness discharge: `tNew = branchNextTime b` with `branchNextTime_gt` (Rules.lean) giving
  `sf.label < branchNextTime b` for every `sf ∈ b`, so the fresh time differs from all existing
  constraint endpoints — provided every endpoint is a label on the branch (the coupling invariant).

### Prior Plan Reference

Reference plan `specs/426_.../plans/02_phase3-streamlined.md` (v2, streamlined) supplies the step
breakdown (3.1 lift, 3.2 threading, 3.3 wire). This plan aligns with it but is sized so each phase
is a single implementation-agent run, and it splits the threading proof (3.2) into a single-step
preservation lemma (Phase 2 here) plus the run-level induction (Phase 3 here), because the freshness
coupling invariant is the crux and warrants its own bounded dispatch. The reference plan's hard
constraints (build green after the lift before any proof; zero-debt fallback = keep green refactor +
mark BLOCKED + document, never `sorry`; never call `lean_diagnostic_messages`) are carried forward.

### Roadmap Alignment

No ROADMAP.md consulted for this task (no `roadmap_path` provided; `roadmap_flag` not set). Parent
task 426 tracks the temporal-tableau ordering redesign; completing this task closes 426.

## Goals & Non-Goals

**Goals**:
- Convert the nested `let rec processNext` + `temporalExpandBranches` into a top-level `mutual …
  end` block that builds green, behaviour-preserving (Step 3.1).
- Prove a single-step lemma: `temporalStepBranch` (equivalently the `newOrd` it returns via
  `temporalApplyOne`) preserves `InstantStrict`, discharging the `addFuture`/`addPast` freshness
  side-conditions from the branch/ordering coupling invariant (Step 3.2a).
- Prove the run-level result: the `TimeOrdering` produced by `temporalExpandBranches` (and the
  mutually-recursive `processNext`) satisfies `InstantStrict`, by induction on `fuel` and structural
  induction on the worklist (Step 3.2b).
- Wire the run-level `InstantStrict` into the order-preservation component of
  `openBranch_branchSat` for the `D = ℤ / f = ord.instant` model, as far as the FMP boundary allows
  (Step 3.3), and finalize CI + parent task 426.

**Non-Goals**:
- Resolving the FMP-blocked components (`temporalTruthLemma`, Until/Since fulfilment,
  `temporalTableau_complete`, `instDecidableValid`) — these remain documented as blocked, no `sorry`.
- Any change to the tableau's runtime behaviour or termination measure semantics (the lift must be
  definitionally faithful).
- Touching task 427's territory in `Completeness.lean` beyond the `openBranch_branchSat`
  order-preservation wiring (serialize; do not parallelize).

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| `mutual` block termination proof (lexicographic: `fuel` for `temporalExpandBranches`, `List.length pending` for `processNext`, `fuel'` strictly smaller on the cross-call) does not go through automatically | H | M | Supply explicit `termination_by` / `decreasing_by`; test measure with `lean_multi_attempt` before committing; keep the exact accumulator/parameter shapes from the current nesting to minimise ripple |
| Refactor ripples into lemmas that `unfold`/`simp [temporalExpandBranches]` elsewhere | M | M | After the lift (Phase 1) run scoped `lake build Cslib.Logics.Temporal.Tableau.Saturation` AND build dependents (`Completeness`) BEFORE any proof work; fix references before proceeding |
| Freshness coupling invariant hard to state/discharge (must show every constraint endpoint is a branch label so `branchNextTime` is fresh) | H | M | Isolate as its own predicate + lemma in Phase 2; use `branchNextTime_gt` + `mem_futureOf_iff`/`mem_pastOf_iff`; numeric goals via `omega`; `lean_multi_attempt` each tricky step |
| Run-level induction (Phase 3) cannot close after the lift | M | L | Zero-debt fallback: keep Phases 1-2 green committed, mark Phase 3 [BLOCKED], document the exact remaining goal state — NEVER introduce `sorry` or a vacuous def |
| Completeness.lean edit conflicts with task 427 | M | L | Territory rule: confirm no concurrent 427 dispatch; serialize; edit only the `openBranch_branchSat` order-preservation region |
| Accidental `sorry`/vacuous def to force green | H | L | Zero-Debt gate: `lean_verify` fully-qualified names + `grep -n "sorry" ` on touched files before each commit |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2 | 1 |
| 3 | 3 | 2 |
| 4 | 4 | 3 |

Phases within the same wave can execute in parallel. This plan is fully sequential (each phase
depends on the prior); the lift must be green before any proof, and each proof layer builds on the
one below.

### Phase 1: Lift `processNext`/`temporalExpandBranches` into a top-level `mutual` block [COMPLETED]

- **Goal:** Replace the nested `let rec processNext` (Saturation.lean ~194-230) with a top-level
  `mutual def temporalExpandBranches … / def processNext … end`, giving `processNext` a standalone
  recursion principle while preserving behaviour. Build green before any proof.
- **Tasks:**
  - [ ] In `Cslib/Logics/Temporal/Tableau/Saturation.lean`, open a `mutual … end` block containing
    both `temporalExpandBranches` and `processNext` as top-level `def`s. `processNext` takes the
    worklist quadruple (`pending`, `pendingExp`, `pendingOrd`, `pendingTrack`), the accumulators
    (`done`, `doneExp`, `doneOrd`, `doneTrack`), and the current `fuel'` as explicit parameters;
    its cross-call uses `temporalExpandBranches … fuel'`.
  - [ ] Rewrite `temporalExpandBranches`'s `fuel' + 1` arm to call the top-level
    `processNext branches expandedSets orderings trackers [] [] [] [] fuel'` (thread `fuel'` in).
  - [ ] Provide the termination measure: `termination_by` lexicographic on `(fuel, List.length
    pending)` — `temporalExpandBranches` decreases `fuel`; `processNext` decreases `List.length
    pending` structurally and its call to `temporalExpandBranches` uses the strictly smaller `fuel'`.
    Add `decreasing_by` if the default measure inference fails; test with `lean_multi_attempt`.
  - [ ] Confirm definitional faithfulness: `temporalTableau` entry point still calls
    `temporalExpandBranches` unchanged; any lemma that `unfold`s/`simp`s `temporalExpandBranches`
    still elaborates.
  - [ ] `lake build Cslib.Logics.Temporal.Tableau.Saturation 2>&1 | grep -E 'error|warning|Built'`
    green, then `lake build Cslib.Logics.Temporal.Tableau.Completeness` to catch ripple.
  - [ ] `grep -n "sorry" Cslib/Logics/Temporal/Tableau/Saturation.lean` shows no new sorry.
  - [ ] Commit: `task 439 phase 1: lift processNext into mutual block (green refactor)`.
- **Timing:** ~1.5 hours
- **Depends on:** none
- **Files to modify:** `Cslib/Logics/Temporal/Tableau/Saturation.lean` — restructure lines ~179-230.
- **Verification:** scoped build of `Saturation` + `Completeness` green; entry-point behaviour
  unchanged (same signatures, same match arms); zero new sorry.

### Phase 2: Single-step preservation lemma with freshness coupling invariant [COMPLETED]

- **Goal:** State the branch/ordering coupling invariant and prove that one expansion step
  (`temporalStepBranch`, whose `newOrd` comes from `temporalApplyOne` via `addFuture`/`addPast` at
  `tNew = branchNextTime b`) preserves both `InstantStrict` and the coupling. This packages the
  Phase 2 (426) edge-by-edge lemmas as a reusable inductive step.
- **Tasks:**
  - [x] Define a coupling predicate pairing a branch `b` with an ordering `ord`: every endpoint of
    every edge in `ord.constraints` is a time label occurring on `b` (so `branchNextTime b` is fresh
    w.r.t. `ord` by `branchNextTime_gt`). Keep it minimal — only what the freshness hypothesis of
    `instantStrict_addFuture`/`instantStrict_addPast` needs. *(deviation: altered -- the coupling
    predicate already existed as `OrdFreshWRT` in `Rules.lean` (landed under task 180 phase 8,
    ahead of this task), with `ordFreshWRT_empty`, `ordFreshWRT_append_left`,
    `ordFreshWRT_addFuture_of_witness`/`ordFreshWRT_addPast_of_witness` already proved. Reused
    directly instead of redefining.)*
  - [x] Prove: if `InstantStrict ord` and the coupling holds for `(b, ord)`, and
    `temporalStepBranch b e ord tracker = some (newBs, newExps, newOrd, newTracker)`, then
    `InstantStrict newOrd` and the coupling holds for each produced branch with `newOrd`.
    Discharge `t ≠ tNew` and the `hfresh` side-conditions via `branchNextTime_gt`
    (`sf.label < branchNextTime b`) and the coupling; numeric goals via `omega`.
    *(deviation: altered -- `Rules.lean` already provides `temporalApplyOne_preserves`
    (edge-case work over `temporalApplyPos`/`temporalApplyNeg`, also task 180 phase 8), so the
    new lemma `temporalStepBranch_preserves` is a thin wrapper: unfold
    `temporalStepBranch`'s `List.findSome?`, extract the witnessing `sf ∈ b` via
    `List.exists_of_findSome?_eq_some`, then dispatch to `temporalApplyOne_preserves` and
    case on the `RuleResult`. No `omega`/freshness re-derivation needed at this layer.)*
  - [x] Handle the `temporalApplyOne` result cases (`linear`, `branching`, `persistent`,
    `notApplicable`) — only the `addFuture`/`addPast`-producing cases change `ord`; others leave
    `ord` unchanged and preserve the invariants trivially.
  - [x] `lean_multi_attempt` before editing each tricky step; `lean_goal` to confirm after each.
    *(deviation: altered -- proof converged on the first `lake build` attempt after one
    `if_pos`/`absurd` fix for the `notApplicable`-via-`expanded.any` short-circuit case; no
    `lean_multi_attempt` exploration was needed given the direct reuse of
    `temporalApplyOne_preserves`.)*
  - [x] `lake build Cslib.Logics.Temporal.Tableau.Saturation` green; `lean_verify` the new lemma
    (fully-qualified) to confirm no `sorry`/new axiom.
  - [x] Commit: `task 439 phase 2: single-step InstantStrict preservation + coupling (green, sorry-free)`.
- **Timing:** ~1.5 hours
- **Depends on:** 1
- **Files to modify:** `Cslib/Logics/Temporal/Tableau/Saturation.lean` (new lemma near the loop, or
  a supporting lemma; may reference `Rules.lean`/`TimeOrdering.lean` lemmas — read-only there).
- **Verification:** new lemma builds green and is `sorry`-free by `lean_verify`; coupling predicate
  is discharged for `TimeOrdering.empty` + initial branch (base case sanity check).

### Phase 3: Run-level `InstantStrict` threading by induction [COMPLETED]

- **Goal:** Prove that the `TimeOrdering` returned by `temporalExpandBranches` (and its mutually
  recursive `processNext`) satisfies `InstantStrict`, given the initial `InstantStrict` + coupling,
  using the now-available recursion principle and the Phase 2 single-step lemma as the step.
- **Tasks:**
  - [x] State the run-level lemma over the `mutual` pair: assuming every `(branch, ord)` pair in the
    worklist satisfies `InstantStrict ord` + the coupling, the ordering carried in the
    `.openBranch b ord` result satisfies `InstantStrict ord` (mirror for `processNext`'s
    accumulators/pending lists). *(deviation: altered -- introduced `WorklistInv` (list-level
    pairing of `InstantStrict`+`OrdFreshWRT` per branch/ordering position) and `ResultInv`
    (`.closed ↦ True`, `.openBranch _ ord ↦ InstantStrict ord`) as the two motives `P1`/`P2`,
    rather than an ad hoc index-based statement.)*
  - [x] Prove by the `mutual`-generated induction: `temporalExpandBranches` by induction on `fuel`
    (fuel-0 base case returns an existing worklist ordering; `fuel'+1` delegates to `processNext`);
    `processNext` by structural induction on `pending`, using the Phase 2 single-step lemma to carry
    the invariant across each `addFuture`/`addPast` and across the cross-call to
    `temporalExpandBranches … fuel'`. *(deviation: altered -- confirmed Lean auto-generates
    `temporalExpandBranches.induct`/`processNext.induct` for the `mutual` well-founded pair
    (verified via `#check`), but its raw case shapes (dependent-if encodings of the `fuel=0`
    `findSome?` search) were awkward to discharge directly. Used a hand-rolled equivalent instead:
    `Nat.strong_induction_on` on `fuel` (giving `P1 fuel` for all smaller `fuel` as `ih`), with a
    nested `induction pending` to establish `P2 fuel'` inside the `fuel'+1` case, citing the outer
    `ih` at the *same* `fuel'` for the processNext→temporalExpandBranches cross-call. Also added
    `processNext_mismatch_closed`: the three length-mismatch fallback arms of `processNext`
    (defensive/unreachable in practice) always drain to `.closed` regardless of any invariant,
    which sidesteps needing extra length-matching hypotheses on `pendingExp`/`pendingTrack`.)*
  - [x] Instantiate at the `temporalTableau` entry point (initial ordering `TimeOrdering.empty` via
    `instantStrict_empty`, initial branch coupling trivial) to obtain: whenever `temporalTableau φ =
    .openBranch b ord`, `InstantStrict ord` holds. *(landed as `temporalTableau_instantStrict`.)*
  - [x] `lean_multi_attempt`/`lean_goal` throughout; `lake build Cslib.Logics.Temporal.Tableau.Saturation`
    green; `lean_verify` the run-level lemma for `sorry`/axiom cleanliness. *(deviation: altered --
    given the proof shape (heavy `simp only`/structural case-splitting rather than exploratory
    tactic search), iterated primarily via `lake build` error messages instead of
    `lean_multi_attempt`; `lean_verify` confirmed `propext`/`Quot.sound` only, no `sorry`/new axiom.)*
  - [x] Commit: `task 439 phase 3: run-level InstantStrict threaded through saturation (green, sorry-free)`.
  - [ ] **Zero-debt fallback (only if it cannot close):** keep Phases 1-2 committed green, mark this
    phase [BLOCKED], document the exact remaining goal state and what is needed — do NOT introduce
    `sorry` or a vacuous def; return `partial`.
- **Timing:** ~1.5 hours
- **Depends on:** 2
- **Files to modify:** `Cslib/Logics/Temporal/Tableau/Saturation.lean`.
- **Verification:** run-level lemma + entry-point corollary build green and `sorry`-free by
  `lean_verify`; the corollary is stated in the `openBranch`-yields-`InstantStrict` form Phase 4 needs.

### Phase 4: Wire into `openBranch_branchSat` and finalize [NOT STARTED]

- **Goal:** Use the run-level `InstantStrict` corollary to discharge the order-preservation
  component (`hInst`) of `openBranch_branchSat` for the `D = ℤ / f = ord.instant` model, as far as
  the FMP boundary allows; run full CI; finalize parent task 426.
- **Tasks:**
  - [ ] Territory check: confirm no concurrent task-427 work on `Completeness.lean` before editing.
  - [ ] In `Cslib/Logics/Temporal/Tableau/Completeness.lean`, supply `hInst : TimeOrdering.InstantStrict
    ord` in the `openBranch_branchSat` order-preservation region (currently a documented sketch,
    lines ~980-1005) from the Phase 3 entry-point corollary, for the `D = ℤ`, `f = ord.instant`
    choice. Advance only the order-preservation component; leave the FMP-blocked
    `temporalTruthLemma`/Until/Since parts documented as blocked (no `sorry`).
  - [ ] Update the surrounding blocker documentation so it reflects that the run-level
    `InstantStrict` (task 426 Phase 3) is now RESOLVED and only FMP remains.
  - [ ] Full CI, in order: `lake build`; `lake exe checkInitImports`; `lake exe lint-style`;
    `lake test 2>&1 | tail -5` (expect the 9152/9152 suite green). Confirm no active `sorry`
    introduced by 439 (`grep -n "sorry"` on both touched files; the pre-existing 427 imp-case sorry,
    if present, is the only allowed one and must be unchanged).
  - [ ] Update `specs/state.json`: mark parent task 426 status `completed` with `completion_summary`
    (Phase 3 threaded: run-level `InstantStrict` proved and wired into `openBranch_branchSat`); mark
    task 439 `implemented`. Regenerate TODO.md via `bash .claude/scripts/generate-todo.sh`.
  - [ ] Write/update the task summary and commit:
    `task 439: complete (426 phase 3 — run-level InstantStrict threaded and wired)`.
- **Timing:** ~0.5-1 hour
- **Depends on:** 3
- **Files to modify:** `Cslib/Logics/Temporal/Tableau/Completeness.lean`; `specs/state.json`;
  `specs/439_.../summaries/01_*.md`.
- **Verification:** full CI green (`lake build`, `lake test`, `lake exe checkInitImports`,
  `lake exe lint-style`); no new `sorry`; parent 426 marked completed with summary.

## Testing & Validation

- [ ] `lake build Cslib.Logics.Temporal.Tableau.Saturation` green after Phase 1 (refactor) and after
  each proof phase.
- [ ] `lake build Cslib.Logics.Temporal.Tableau.Completeness` green after Phase 1 (ripple check) and
  after Phase 4 (wiring).
- [ ] `lake build` (full project) green at Phase 4.
- [ ] `lake test 2>&1 | tail -5` — full suite green (no regressions; expect 9152/9152).
- [ ] `lake exe checkInitImports` — pass.
- [ ] `lake exe lint-style` — pass.
- [ ] `lean_verify` (fully-qualified) on each new lemma: no `sorry`, no new axioms.
- [ ] `grep -n "sorry" Saturation.lean Completeness.lean` — no new sorry introduced by task 439.

## Artifacts & Outputs

- `specs/439_refactor_processnext_to_mutual_def_and_prove_instantstrict_t/plans/01_processnext-mutual-instantstrict.md` (this file)
- `specs/439_refactor_processnext_to_mutual_def_and_prove_instantstrict_t/summaries/01_processnext-mutual-instantstrict-summary.md` (on completion)
- Modified: `Cslib/Logics/Temporal/Tableau/Saturation.lean` (mutual refactor + threading lemmas)
- Modified: `Cslib/Logics/Temporal/Tableau/Completeness.lean` (order-preservation wiring)
- Modified: `specs/state.json` (parent task 426 -> completed; task 439 -> implemented) + regenerated `specs/TODO.md`

## Rollback/Contingency

- Each phase ends with a green, scoped-built commit. If a later phase fails, revert only that
  phase's commit; earlier green commits (especially the Phase 1 refactor and Phase 2 lemma) stand.
- **Zero-debt hard rule:** if the run-level threading (Phase 3) or wiring (Phase 4) cannot close,
  keep the green refactor/lemmas, mark the failing phase [BLOCKED], document the exact remaining
  goal state, and return `partial` with `requires_user_review: true`. NEVER introduce `sorry` or a
  vacuous definition (`def X := True`, `theorem X := trivial`) to force green.
- The mutual-block refactor is the highest-value deliverable even in isolation: it unblocks the
  recursion principle permanently, so a Phase-1-only outcome is a real, committable improvement.
- Territory: if a task-427 dispatch is active on `Completeness.lean`, pause Phase 4 and serialize;
  do not parallelize edits to that file.
