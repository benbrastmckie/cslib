# Implementation Plan: Task #573

- **Task**: 573 - tableau_quotient_soundness_spike
- **Status**: [NOT STARTED]
- **Effort**: 4 hours
- **Dependencies**: 572
- **Research Inputs**: specs/317_propositional_tableau_completeness/reports/14_blocker-analysis.md
- **Artifacts**: plans/01_quotient-soundness-spike.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: cslib
- **Lean Intent**: false

## Overview

This is a time-boxed GO/NO-GO spike, not a proof effort. It must determine — against live Lean
goal state — whether `intExpandBranches_closed_unsat`
(`Cslib/Logics/Propositional/Tableau/Intuitionistic/Soundness.lean:1108`) survives two proposed
calculus changes: (a) restating `IBranchSaturation.sat_fimp` (`Scheme.lean:97-101`) over the
blocking quotient frame, and (b) replacing `intFImpReuseWitness?` (`Expansion.lean:291-319`)
with an ancestor-directed `Sfor`-containment check that drops the `F(ψ)@x` conjunct
(`Expansion.lean:316`).

The plan is structured around a specific, cheap, falsifiable hypothesis discovered while
scoping (stated as H1/H2 in Phase 1, and **required to be tested against goal state, not
accepted on inspection**): the soundness proof may be *content-agnostic* about the reuse
predicate, depending only on the *shape* of the `go` match in `Expansion.lean:420-443` — the
`some _x` arm recurses on `bPers`, `edges`, `nw` completely unchanged, and discards the witness
label with an underscore. If that holds under `lean_goal`, swapping the predicate's body is
soundness-neutral and the verdict is GO. If any reuse-arm goal turns out to mention the
predicate's content, the verdict is NO-GO or UNCERTAIN. Either verdict is a successful outcome.

No file under `Cslib/` is edited or committed. Prototyping happens via `lean_run_code` and one
uncommitted scratch file that is deleted before the final commit.

### Research Integration

`reports/14_blocker-analysis.md` supplies the framing this plan encodes: (1) the existing
loop-check searches **descendants** (`isAccessible edges w x`) whereas Fitting-style blocking
requires an **ancestor**, so the direction reversal is the change under test; (2) an earlier
"Option B" fix (appending `F(ψ)@x` unconditionally) died at exactly `intExpandBranches_closed_unsat`,
and `Expansion.lean:256-264` records why — Option B **modified the branch**, invalidating the
already-established `intBranchSatisfied` witness for `bPers`. That failure mode isolates the
real soundness-relevant variable (branch modification on the reuse path), which is what Phase 4
must confirm or refute under goal state.

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

No `roadmap_path` supplied in the delegation context; no ROADMAP.md consulted.

## Goals & Non-Goals

**Goals**:
- Produce a GO / NO-GO / UNCERTAIN verdict on the quotient-restated `sat_fimp` plus
  ancestor-directed containment check versus `intExpandBranches_closed_unsat`.
- Back the verdict with **quoted live goal state** from `lean_goal` / `lean_run_code` /
  `lean_multi_attempt` at named source positions.
- Write the decision record to
  `specs/573_tableau_quotient_soundness_spike/handoffs/01_quotient-soundness-spike-decision.md`,
  including an explicit re-scope instruction (if NEGATIVE/UNCERTAIN) or an explicit green light
  (if POSITIVE) for the downstream calculus-repair task.
- Leave the library bit-for-bit unchanged.

**Non-Goals**:
- Completing the `intExpandBranches_closed_unsat` proof against the new definitions.
- Closing, or even touching, any existing `sorry` (`Scheme.lean:607`, `Scheme.lean:2623`,
  `Completeness.lean:133`).
- Implementing the ancestor-directed check or quotient `sat_fimp` in the library.
- Fixing the `intExpandBranches` divergence itself.
- Rewriting `truthLemma`'s F-imp case (`Scheme.lean:608+`).

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Spike slides into a full proof attempt and blows the time-box | H | H | Phase 5 is a hard ABORT gate with numeric stop conditions; Phase 4 carries its own per-step budget |
| Scratch file gets committed / library accidentally modified | H | L | Phase 6 verifies `git status --porcelain Cslib/` is empty and deletes the scratch dir; staging is by explicit file path only, never `git add <taskdir>` |
| `lean_goal` cannot elaborate a scratch file outside the module tree | M | M | Primary vehicle is `lean_run_code` (project env, imports resolve); scratch file is the fallback, and Phase 2 verifies elaboration before Phase 4 depends on it |
| Rebuild of the Intuitionistic module tree is slow, eating the time-box | M | M | Phase 1 runs `lake exe cache get` + a single scoped `lake build` once and reuses the LSP session; no further full builds |
| Verdict is stated as hand-argument rather than goal state | H | M | Every phase names the specific tool call producing its evidence; Phase 5's classification criteria require a quoted goal state or an explicit "no goal state obtained" |
| The two reuse arms (`Soundness.lean:1470`, mirror under `:1573`) behave differently | M | M | Phase 4 inspects **both** arms; a divergence between them is itself a reportable NO-GO signal |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2 | 1 |
| 3 | 3 | 2 |
| 4 | 4 | 3 |
| 5 | 5 | 4 |
| 6 | 6 | 5 |

Phases within the same wave can execute in parallel. This spike is a strict chain: every phase
consumes the previous phase's goal-state evidence, and Phases 2-4 share a single scratch file,
so no parallelism is available.

---

### Phase 1: Baseline Capture and Hypothesis Formulation [NOT STARTED]

**Goal**: Establish a green LSP baseline and record the two falsifiable hypotheses the spike
tests, so Phase 4's evidence has something to confirm or refute.

**Tasks**:
- [ ] Run `lake exe cache get`, then `lake build Cslib.Logics.Propositional.Tableau.Intuitionistic.Soundness`; confirm green. Record the build time (it bounds all later re-elaboration).
- [ ] `lean_goal` at `Soundness.lean:1470` (the `-- Reuse:` arm of the first `rcases hwit`) — capture and record the full goal state verbatim.
- [ ] `lean_goal` at `Soundness.lean:1573` region's reuse arm (the mirror `rcases hwit` in the `bp ∈ bt` case) — capture and record verbatim.
- [ ] `lean_hover_info` on `intFImpReuseWitness?` at `Expansion.lean:291` and on `intFImpReuseWitness?_spec` at `Expansion.lean:328` — record exact signatures.
- [ ] Record the dependency-surface facts: `grep -c "IBranchSaturation" Soundness.lean` and `grep -n "intFImpReuseWitness?_spec" Soundness.lean`.
- [ ] Write the two hypotheses into a scratch notes buffer, verbatim, as falsifiable claims:
      **H1 (predicate-content-agnosticism)**: the reuse arm's goal state at `Soundness.lean:1470` and its `:1573` mirror contains no occurrence of `intFImpReuseWitness?`'s *body* and no use of `intFImpReuseWitness?_spec`; it depends only on the fact that the `go` recursion receives `bPers`/`edgesP`/`nwH` unchanged.
      **H2 (soundness/saturation disjointness)**: `IBranchSaturation` (hence `sat_fimp`) does not occur anywhere in the `intExpandBranches_closed_unsat` dependency cone, so the quotient restatement cannot break it.
- [ ] Note explicitly in the notes buffer that H1 and H2 are **hypotheses**, and that grep/inspection evidence alone does NOT satisfy this task's deliverable — Phase 4 must confirm or refute them against live goal state.

**Timing**: 0.5 hours

**Depends on**: none

**Files to modify**:
- None. Read-only phase. (Notes may be kept in the agent's scratchpad directory, outside the repo.)

**Verification**:
- Scoped `lake build` exits 0.
- Two verbatim reuse-arm goal states are recorded.
- H1 and H2 are written down as falsifiable statements with the source positions that would refute them.

---

### Phase 2: Prototype the Ancestor-Directed Containment Check [NOT STARTED]

**Goal**: Get an ancestor-directed replacement for `intFImpReuseWitness?` to elaborate at the
same type, so Phase 4 can substitute it.

**Tasks**:
- [ ] Create the uncommitted scratch file `specs/573_tableau_quotient_soundness_spike/scratch/QuotientSpike.lean` with `import Cslib.Logics.Propositional.Tableau.Intuitionistic.Soundness` and the same `namespace`/`variable` preamble as `Expansion.lean`.
- [ ] Verify the scratch file elaborates and that `lean_goal` returns a position-addressable state in it (this is the fallback-vehicle viability check). If it does not, fall back to `lean_run_code` for all remaining Lean work and record that in the notes.
- [ ] Define `intFImpReuseWitnessAnc? (bPers : IBranch Atom) (edges : IEdges) (newForms : List (ISF Atom)) (newEdge : Nat × Nat) : Option Nat` — same signature as `intFImpReuseWitness?` — differing from `Expansion.lean:303-319` in exactly two ways: the accessibility test is reversed to search **ancestors** (`isAccessible edges x w` with `x.ble w`, rather than `isAccessible edges w x` with `w.ble x`), and the `bPers.any (... F(ψ)@x ...)` conjunct at `Expansion.lean:316` is **dropped**.
- [ ] Confirm it elaborates with no errors and that `lean_hover_info` reports the identical `Option Nat` return type.
- [ ] Optional, only if it costs under 10 minutes: `#eval` the new check against the F1 divergence witness `phi0 = (((a→b)→c) ∧ ((d→e)→f)) → ((u1→v1) ∨ (u2→v2))` to see whether it fires where the current check does not. This is a nice-to-have signal, **not** required evidence for the verdict — skip it if the eval is slow.

**Timing**: 1 hour

**Depends on**: 1

**Files to modify**:
- `specs/573_tableau_quotient_soundness_spike/scratch/QuotientSpike.lean` - NEW, uncommitted, deleted in Phase 6.
- No file under `Cslib/`.

**Verification**:
- `intFImpReuseWitnessAnc?` elaborates with zero errors.
- Its type matches `intFImpReuseWitness?`'s exactly (hover output compared).
- The vehicle decision (scratch file vs. `lean_run_code`) is recorded.

---

### Phase 3: Prototype the Quotient-Restated `sat_fimp` [NOT STARTED]

**Goal**: Get a quotient-frame restatement of `sat_fimp` to elaborate, and determine whether it
appears anywhere in `intExpandBranches_closed_unsat`'s dependency cone.

**Tasks**:
- [ ] In the scratch file, define `IBranchSaturationQ` — a copy of `IBranchSaturation` (`Scheme.lean:74-108`) with all fields unchanged except `sat_fimp`, restated so the witness `w'` is read off the blocking quotient: a blocked world is identified with its blocking ancestor, so the required `w ≤ w'` is discharged in the quotient rather than by the raw numeric label order.
- [ ] Confirm `IBranchSaturationQ` elaborates.
- [ ] Test H2 directly: run `lean_verify` (or `#print axioms` / the transitive-dependency listing) on `Cslib.Logic.PL.intExpandBranches_closed_unsat` and check whether `IBranchSaturation`, `sat_fimp`, or `IBranchSaturationQ` appear in its dependency cone. Record the output verbatim.
- [ ] Record the verdict on H2: CONFIRMED (saturation absent from the cone → the restatement is soundness-neutral by construction) or REFUTED (it appears → the restatement is a live soundness risk, and Phase 4 must trace where).

**Timing**: 0.5 hours

**Depends on**: 2

**Files to modify**:
- `specs/573_tableau_quotient_soundness_spike/scratch/QuotientSpike.lean` - append only.
- No file under `Cslib/`.

**Verification**:
- `IBranchSaturationQ` elaborates with zero errors.
- H2's verdict is recorded with the verbatim tool output that decided it.

---

### Phase 4: Decisive Soundness Experiment Against Live Goal State [NOT STARTED]

**Goal**: Confirm or refute H1 by re-running the two reuse arms of
`intExpandBranches_closed_unsat` against the ancestor-directed check, inspecting goal state at
each step. **This phase produces the evidence the verdict rests on.**

**Tasks**:
- [ ] In the scratch file, define `intExpandBranchesAnc` — a copy of `intExpandBranches`'s `go` (`Expansion.lean:400-443`) with `intFImpReuseWitness?` replaced by `intFImpReuseWitnessAnc?` at the call site (`Expansion.lean:423`), everything else byte-identical. Confirm it elaborates.
- [ ] Confirm the structural precondition H1 rests on: in `intExpandBranchesAnc`, the `some _x` arm still recurses with `bPers`, `edges`, `nw` **unchanged** (no `Branch.extendMany`, no `edges ++ [e]`, no `nw'`), exactly as `Expansion.lean:424-433`. Quote the elaborated definition.
- [ ] State a scratch copy of `intExpandBranches_closed_unsat` over `intExpandBranchesAnc` (statement only; body starts as `sorry`).
- [ ] Walk the proof to the **first** reuse arm (the `Soundness.lean:1470` analogue) by replaying `Soundness.lean:1390-1470`'s tactic prefix, calling `lean_goal` after each step. Capture the goal state at the point corresponding to `rw [hwit] at hgo; simp only [] at hgo`. **Compare it to the Phase 1 baseline goal state, term by term.**
- [ ] Try to discharge that arm with the *unchanged* tactic block from `Soundness.lean:1471-1519` (which uses `hsat_pers` + `ih` on `bPers` directly). Use `lean_multi_attempt` rather than editing, where practical. Record whether it closes, and if not, the exact error and residual goal.
- [ ] Repeat for the **second** reuse arm (the `Soundness.lean:1573` mirror, `bp ∈ bt` case). Record the same evidence.
- [ ] If either arm produces a goal mentioning `intFImpReuseWitnessAnc?`'s body, or requires an analogue of `intFImpReuseWitness?_spec`, record that goal verbatim — that is the obstruction, and H1 is REFUTED.
- [ ] Record H1's verdict: CONFIRMED (both arms close with unchanged tactics), REFUTED (a named obstruction), or UNRESOLVED (time-box hit before either arm was decided).

**Timing**: 1.25 hours

**Depends on**: 3

**Files to modify**:
- `specs/573_tableau_quotient_soundness_spike/scratch/QuotientSpike.lean` - append only.
- No file under `Cslib/`.

**Verification**:
- At least one reuse arm has a captured, quotable goal state at the `rw [hwit]` point.
- H1's verdict is recorded with the goal state or error that decided it.
- The library is still unmodified: `git status --porcelain Cslib/` is empty.

---

### Phase 5: ABORT Gate and Verdict Classification [NOT STARTED]

**Goal**: Stop the Lean work — unconditionally — and classify the verdict. This phase exists to
prevent the spike from becoming a proof effort.

**Tasks**:
- [ ] **HARD STOP.** On entering this phase, do no further Lean proof work. Any incomplete proof attempt is abandoned as-is; whatever goal state has been captured is the evidence base.
- [ ] Apply the stop conditions retroactively and record which (if any) fired: elapsed work exceeded ~3.25 hours; the scratch proof attempt exceeded ~150 lines; three or more consecutive `lean_multi_attempt` batches failed on the same goal; or a rebuild loop exceeded 15 minutes. Any one firing means the spike ends here with whatever evidence exists — this is a normal, successful termination, not a failure.
- [ ] Classify the verdict against these criteria:
      **GO** — H1 CONFIRMED and H2 CONFIRMED: at least one reuse arm closed with the unchanged `Soundness.lean` tactic block against `intFImpReuseWitnessAnc?`, and saturation is absent from the soundness cone.
      **NO-GO** — a concrete obstruction was found: a reuse-arm goal that mentions the predicate's content, requires a `_spec` analogue, or otherwise cannot be discharged without branch modification (the Option B failure mode recorded at `Expansion.lean:256-264`).
      **UNCERTAIN** — anything else, including: the time-box fired before either arm was decided; only one of the two arms was inspected; H1 confirmed but H2 refuted (or vice versa); or the evidence is inspection-based rather than goal-state-based.
- [ ] Confirm the classification cites a specific captured goal state (or explicitly states that no goal state was obtained, which forces UNCERTAIN).

**Timing**: 0.25 hours

**Depends on**: 4

**Files to modify**:
- None.

**Verification**:
- Exactly one of GO / NO-GO / UNCERTAIN is selected.
- The selection names the goal state or the absence of one.
- No Lean tool call is made after this phase begins.

---

### Phase 6: Write Decision Record and Restore Clean Tree [NOT STARTED]

**Goal**: Deliver the decision record and prove the library is untouched.

**Tasks**:
- [ ] Write `specs/573_tableau_quotient_soundness_spike/handoffs/01_quotient-soundness-spike-decision.md` containing, in order:
      **(1) Verdict** — GO / NO-GO / UNCERTAIN, with the specific goal state or obstruction quoted verbatim, and the source positions it was taken at.
      **(2) Downstream instruction** — if NO-GO **or** UNCERTAIN, an explicit, unambiguous statement that the downstream calculus-repair task's quotient/rewrite step rests on a premise this spike did not establish, and that the repair task MUST be re-scoped via `/revise` or `/spawn` **before** it is dispatched. If GO, an explicit green light for the repair task's quotient/rewrite step, naming exactly what was and was not established.
      **(3) Evidence appendix** — the Phase 1 baseline goal states, the Phase 4 experimental goal states, H1/H2 verdicts, and which stop condition (if any) fired.
      **(4) Scope note** — what was NOT tested, so a future dispatch does not over-read the verdict.
- [ ] Do not cite task numbers anywhere outside `specs/**`.
- [ ] Delete `specs/573_tableau_quotient_soundness_spike/scratch/` entirely.
- [ ] Run `git status --porcelain Cslib/` and confirm empty output. If it is non-empty, restore the affected files from HEAD and re-verify before proceeding.
- [ ] Run `git status --short` and confirm the only new/modified paths are the decision record, this plan, the task metadata files, and `specs/state.json` / `specs/TODO.md`.
- [ ] Stage by explicit file path only (never `git add <taskdir>`, never `git add -A`).

**Timing**: 0.5 hours

**Depends on**: 5

**Files to modify**:
- `specs/573_tableau_quotient_soundness_spike/handoffs/01_quotient-soundness-spike-decision.md` - NEW, the deliverable.
- `specs/573_tableau_quotient_soundness_spike/scratch/` - DELETED.
- No file under `Cslib/`.

**Verification**:
- The decision record exists, is non-empty, and contains all four required sections.
- Sections (1) and (2) are both present and mutually consistent.
- `git status --porcelain Cslib/` is empty.
- The scratch directory no longer exists.

## Testing & Validation

- [ ] `lake build Cslib.Logics.Propositional.Tableau.Intuitionistic.Soundness` is green at Phase 1 and remains green at Phase 6 (the library was never touched).
- [ ] `git status --porcelain Cslib/` is empty at Phase 6.
- [ ] `git diff HEAD -- Cslib/` is empty at Phase 6.
- [ ] The decision record contains at least one verbatim Lean goal state, with the file and line it was captured at.
- [ ] The decision record's verdict section states GO, NO-GO, or UNCERTAIN explicitly — never leaves it implied.
- [ ] If the verdict is NO-GO or UNCERTAIN, the record contains the literal re-scope instruction for the downstream repair task.
- [ ] `specs/573_tableau_quotient_soundness_spike/scratch/` does not exist.
- [ ] No sorry count changed anywhere in the repository.

## Artifacts & Outputs

- `specs/573_tableau_quotient_soundness_spike/handoffs/01_quotient-soundness-spike-decision.md` — the deliverable.
- `specs/573_tableau_quotient_soundness_spike/.orchestrator-handoff.json` — orchestrator handoff.
- `specs/573_tableau_quotient_soundness_spike/.return-meta.json` — return metadata.
- No library artifacts. No new committed Lean code.

## Rollback/Contingency

Rollback is trivial by construction: the only committed changes are markdown under
`specs/573_tableau_quotient_soundness_spike/` plus task-state files. If anything under `Cslib/`
is modified at any point, restore it from HEAD immediately and continue — the spike does not
depend on any library edit.

**Contingency — verdict is UNCERTAIN.** This is an acceptable, successful outcome. Write the
decision record with the partial evidence and the explicit re-scope instruction. Do not extend
the time-box to reach a cleaner answer; an honest UNCERTAIN protects the downstream repair task
exactly as well as a NO-GO does, and a manufactured GO does not.

**Contingency — the scratch file cannot be elaborated by the LSP.** Fall back to `lean_run_code`
for all Lean work (Phase 2 makes this determination). `lean_run_code` cannot do positional
`lean_goal` inspection, so in that case Phase 4's evidence comes from `#print axioms`,
elaboration errors, and `lean_multi_attempt` results instead; note this limitation explicitly in
the decision record's scope section, since it weakens the evidence and may force UNCERTAIN.

**Contingency — Phase 1's baseline build is not green.** Stop and report; do not attempt to
repair the library (that is out of scope and would violate the no-library-changes constraint).
Write the decision record stating the spike could not run and why.
