# Implementation Plan: Discharge DP-5 and land the honest conjunct-2 negative result

- **Task**: 604 - Prove the countermodel forcing conjunct over the constructed frame
- **Status**: [IMPLEMENTING]
- **Effort**: 4.5 hours
- **Dependencies**: 603 (landed)
- **Research Inputs**: specs/604_prove_countermodel_forcing_conjunct_over_constructed_frame/reports/01_conjunct2-frame-adequacy.md
- **Artifacts**: plans/01_dp5-discharge-honest-restructure.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: cslib
- **Lean Intent**: false

## Overview

The task's literal target — conjunct 2 of `openBranch_countermodel` over the `rawEdges` frame
task 603 constructed — is **machine-refuted**, not merely hard, and the delegation explicitly
authorised a documented negative result. This plan therefore lands the two things that ARE
available: the verified DP-5 discharge (`truthLemma`'s T(φ'→ψ') case becomes sorry-free), and a
restructuring of `openBranch_countermodel` so that its one surviving `sorry` sits on a genuinely
open goal rather than a refuted one. Net effect on `Scheme.lean`: 2 live sorries -> 1, zero new
sorries, zero new axioms, zero new definitions or imports. The residual obligation and the
excluded search space are recorded in the file's existing honesty register, and the root-cause
calculus defect gets its own follow-on task rather than being attempted here.

### Research Integration

The plan implements section 6 of `reports/01_conjunct2-frame-adequacy.md` verbatim in intent.
Findings carried directly into phases:

- **Section 5 (verified positive)**: the DP-5 proof compiled green in a spike
  (`lake build` -> "Build completed successfully (932 jobs)", `truthLemma` sorry warning gone),
  then was reverted. The 28-line diff is preserved at `scratch/dp5-spike.diff` and the pre-spike
  snapshot at `scratch/Scheme.lean.bak`. Phase 1 re-applies it.
- **Section 5 ordering trap**: `intro hforce_φ'` MUST come **after** the persistence `have`, or
  `induction hle` sweeps `hforce_φ'` into the motive and the tail case fails with an application
  type mismatch. This is a hard-won ordering fact, not a style preference.
- **Section 5 rationale for an inline hypothesis**: `hpers` is stated inline rather than as
  `IPosPersistRaw` because `IPosPersistRaw` (`Scheme.lean:6782`), `IWorldsPlanted`
  (`:3568`), and `isAccessible_target_mem_edges` (`:3446`) are all defined AFTER `truthLemma`
  in the file and are `private`.
- **Section 3 (frame-adequacy table)**: `IFimpAccess` and positive persistence sit on opposite
  frames; each candidate frame's missing half is machine-refuted, not merely unproved. This is
  the content Phase 2 records at both annotation sites.
- **Section 4 (four excluded constructions)**: `rawEdges`, prune-at-blocked,
  prune-at-strictly-blocked, and the `IFimpAccess` greatest fixpoint are all positively excluded.
  Do not re-attempt any of them.
- **Section 3, honesty consequence**: the current `sorry` at `Scheme.lean:8051` sits *after*
  `refine ⟨edges, ?_, …⟩` has committed the witness to `augSets`, so its goal — upward closure
  over the augmented frame — is itself a REFUTED statement. Phase 1 fixes exactly this.
- **Section 6, final paragraph**: the root cause is `intFImpReuseWitnessAnc?`
  (`Expansion.lean:316`) recording a loop-back edge on a containment check it never re-validates
  as the branch grows. Calculus-level work, out of scope here, gets its own task (Phase 4).

### Discovered during planning: two external `truthLemma` call sites

The research report scopes the `hpers` signature change to `openBranch_countermodel`'s internal
call. **This is incomplete.** `truthLemma` has two further call sites outside `Scheme.lean`:

| Site | Wrapper | Downstream consumers |
|---|---|---|
| `Cslib/Logics/Propositional/Tableau/Intuitionistic/Completeness.lean:97` | `intTruthLemma` | none (docstring mentions only) |
| `Cslib/Logics/Propositional/Tableau/Minimal/Completeness.lean:102` | `minTruthLemma` | none (docstring mentions only) |

Both pass arguments positionally (`truthLemma S b edges hopen hsat hfimp φ w`), so adding
`hpers` breaks both. Both wrappers were verified to have no downstream consumers, so the fix is
contained: each wrapper takes the same `hpers` hypothesis and threads it through — roughly four
lines per file. **The delegation's "file in scope is `Scheme.lean`" constraint therefore cannot
hold literally for the recommended landing.** This plan proceeds under the stated assumption
that the two wrapper edits are in scope as the mechanical closure of a signature change, not as
scope creep. If the implementer is forbidden from touching those two files, the fallback in
"Rollback/Contingency" applies instead.

### Prior Plan Reference

No prior plan for this task.

### Roadmap Alignment

No `roadmap_path` was supplied in the delegation context and no roadmap consultation was
performed; no roadmap phases are included.

## Goals & Non-Goals

**Goals**:

- Discharge DP-5: `truthLemma`'s T(φ'→ψ') `sorry` (`Scheme.lean:768`) is replaced by the
  verified 15-line proof, and `truthLemma` becomes sorry-free.
- Thread the new `hpers` hypothesis through the two external wrapper lemmas so the repo-wide
  `lake build` stays green.
- Restructure `openBranch_countermodel` so its single remaining `sorry` carries the whole
  existential `∃ edges, upward-closed ∧ ¬IForces` — a genuinely open goal — instead of a
  frame-committed goal that is machine-refuted.
- Reduce `Scheme.lean` from 2 live sorries to 1, with zero new sorries and zero new axioms.
- Record the frame-adequacy table, the two CI citations, and the four excluded constructions in
  the file's existing honesty register at both annotation sites.
- Sweep the now-stale cross-file claims that `truthLemma` still carries a sorry.
- Create a follow-on task for the `intFImpReuseWitnessAnc?` re-validation defect.

**Non-Goals**:

- Proving conjunct 2 over `rawEdges`, over the maximal atom-inclusion frame `⊑`, over either
  pruning rule, or over the `IFimpAccess` greatest fixpoint. All five are excluded with machine
  evidence; re-attempting any of them is forbidden by this plan.
- Any edit to `Cslib/Logics/Propositional/Tableau/Intuitionistic/Expansion.lean`. The
  `intFImpReuseWitnessAnc?` repair is calculus-level work and belongs to the follow-on task.
- Discharging `intuitionisticTableau_complete`'s own `sorry` (`Intuitionistic/Completeness.lean`)
  or any `Completeness.lean` sorry. Those remain untouched and still open.
- Introducing any new definition, typeclass, notation, or Mathlib import. `hpers` is a composite
  of two existing exports stated inline, not a new abstraction.
- Weakening any statement, or landing an Option-B / placeholder sorry to reach a green build.

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| `induction hle` sweeps `hforce_φ'` into the motive; tail case fails with an application type mismatch | H | H if ordering ignored | Place `intro hforce_φ'` AFTER the persistence `have hmem'`, exactly as in `scratch/dp5-spike.diff`. This is the single most likely failure and it is already diagnosed. |
| The preserved spike diff no longer applies cleanly (file drift since the spike) | M | L | The research confirmed `Cslib/` was restored byte-identical; verify with `git status --porcelain Cslib/` and confirm `sed -n '767,768p'` still shows `intro _` / `sorry` before editing. Apply the hunks by hand via `Edit`, never `git apply` — the diff's third hunk contains a `(by sorry)` that MUST NOT be landed (see next row). |
| Landing the spike's third hunk verbatim would sorry a REFUTED statement | H | M | The spike kept its build green by passing `(by sorry)` for `hpers` at the `openBranch_countermodel` call site. `hpers` is refuted at the augmented frame, so that sorry is exactly what the file's honesty discipline forbids. Phase 1 drops the whole `refine` line instead. |
| Adding `hpers` breaks the two external wrapper call sites, leaving the repo build red | H | H if unhandled | Phase 1 is a declared `atomic-batch` spanning all three files; intermediate per-file states are expected red and are not committed. |
| Deleting `openBranch_countermodel`'s now-dead extraction block loses documented machinery | M | L | The identical ~40-line `intExpandBranches_openBranch_sat` invocation is preserved verbatim in `openBranch_rawEdges_upward_closed` immediately below in the same file, so nothing is actually lost. Record this in the annotation. Fallback: keep the block with all binders `_`-prefixed. |
| An annotation cites the follow-on task number, violating the no-task-references-in-deliverables rule | M | M | `Cslib/**` is a deliverable tree. Annotations name the durable anchor (`intFImpReuseWitnessAnc?` in `Expansion.lean`) and NEVER a task number. The write-time hook blocks such writes; do not work around it. |
| `next_project_number` drifts before Phase 4 runs (other tasks are in flight in this session) | L | M | Re-read `next_project_number` from `specs/state.json` at the moment of the Phase 4 write. Do not hardcode a number from plan time. |
| The word "refuted" leaks onto a claim that is not machine-refuted | H | M | Apply the vocabulary discipline in Phase 2's task list literally: "refuted" only for the four cells with CI or probe evidence; "open" for `openBranch_countermodel` itself; "excluded" for the probe-eliminated candidate constructions. |

## Implementation Phases

**Dependency Analysis**:

| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1, 4 | -- |
| 2 | 2, 3 | 1 |
| 3 | 5 | 1, 2, 3, 4 |

Phases within the same wave can execute in parallel.

### Phase 1: Discharge DP-5 and restructure `openBranch_countermodel` [COMPLETED]
<!-- confirmed by implementation agent: exactly 3 call sites of `truthLemma` (internal + intTruthLemma + minTruthLemma), both wrappers have no downstream consumers beyond docstrings. Full repo `lake build` green (3325 jobs); only pre-existing sorries remain (Scheme.lean:7994 openBranch_countermodel, Completeness.lean:156 intTruthLemma-adjacent, Minimal/Completeness.lean:152). truthLemma sorry warning confirmed gone. -->


- **Goal:** `truthLemma` becomes sorry-free via the verified DP-5 proof; the two external
  wrappers thread the new `hpers` hypothesis; `openBranch_countermodel`'s single `sorry` moves
  from a refuted goal to the open existential. Repo-wide `lake build` green at phase end.

- **Tasks:**
  - [ ] Confirm the working tree is clean for `Cslib/` (`git status --porcelain Cslib/`) and that
        `Cslib/Logics/Propositional/Tableau/Intuitionistic/Scheme.lean:767-768` still reads
        `intro _` / `sorry`. If either check fails, stop and report rather than guessing.
  - [ ] Re-confirm the call-site inventory before editing (see Scope Hypothesis below).
  - [ ] Add the `hpers` hypothesis to `truthLemma`, positioned immediately after `hfimp` and
        before `(φ : Proposition Atom) (w : Nat)`:
        `(hpers : ∀ (χ : Proposition Atom) (x y : Nat), isAccessible edges x y = true →`
        `(⟨.pos, χ, x⟩ : ISF Atom) ∈ b → (⟨.pos, χ, y⟩ : ISF Atom) ∈ b)`.
        State it inline; do NOT reference `IPosPersistRaw` by name — that definition and its two
        side-condition helpers are declared later in the file and are `private`.
  - [ ] Replace `intro _` / `sorry` in the T(φ'→ψ') case with the 15-line proof from
        `scratch/dp5-spike.diff` (hunk 2). Order is load-bearing: lift `hT` to membership, chain
        `hpers` along `ReflTransGen` by `induction hle`, rebuild `hany'`, and only THEN
        `intro hforce_φ'`, then `rcases hsat.sat_timp φ' ψ' w' hany'` closing the `F(φ')@w'` arm
        by `ih_φ'.2` and the `T(ψ')@w'` arm by `ih_ψ'.1`.
  - [ ] Add the same `hpers` hypothesis to `intTruthLemma`
        (`Intuitionistic/Completeness.lean`) and pass it through in the delegating
        `exact truthLemma intScheme b edges hopen hsat hfimp hpers φ w`.
  - [ ] Add the same `hpers` hypothesis to `minTruthLemma` (`Minimal/Completeness.lean`) and
        pass it through identically.
  - [ ] In `openBranch_countermodel`, delete the frame-committing
        `refine ⟨edges, ?_, (truthLemma S b edges hopen hsat hfimp φ 0).2 hFmem⟩` line and reduce
        the proof body to a single `sorry` carrying the whole `∃ edges, …` goal. Do NOT pass
        `(by sorry)` for `hpers` — `hpers` is refuted at the augmented frame.
  - [ ] Remove the extraction block that is now dead (the `hopen` / `hFmem` `have`s and the
        `obtain ⟨edges, …⟩ := intExpandBranches_openBranch_sat …` invocation). The identical
        invocation survives verbatim in `openBranch_rawEdges_upward_closed` directly below, so
        no machinery is lost. If deletion produces any unexpected error, fall back to keeping the
        block with every binder `_`-prefixed.
  - [ ] Leave a minimal placeholder note at the surviving `sorry` site; the full annotation is
        Phase 2's job. Do not let this phase drift into prose work.
  - [ ] Run `lake build` (full) and confirm it completes successfully with sorry warnings at
        `openBranch_countermodel` and the pre-existing `Completeness.lean` sites only — the
        `truthLemma` warning must be GONE.
  - [ ] Commit the whole batch once green.

- **Timing:** 1.5 hours

- **Depends on:** none

- **Verification Tier:** interface

- **Commit Mode:** atomic-batch

- **Scope Hypothesis:** This phase asserts that `truthLemma` has exactly three call sites — one
  internal (`openBranch_countermodel`, being removed) and two external (`intTruthLemma` at
  `Intuitionistic/Completeness.lean:97`, `minTruthLemma` at `Minimal/Completeness.lean:102`) —
  and that the two wrappers have no downstream consumers beyond docstrings. Confirm at
  implementation time with
  `grep -rn "truthLemma" --include=*.lean Cslib CslibTests` and
  `grep -rn "intTruthLemma\|minTruthLemma" --include=*.lean Cslib CslibTests`. If a fourth call
  site or a live wrapper consumer appears, widen the batch to cover it before building; do not
  land a partial signature change.

- **Files to modify:**
  - `Cslib/Logics/Propositional/Tableau/Intuitionistic/Scheme.lean` — `truthLemma` gains `hpers`
    and loses its `sorry`; `openBranch_countermodel` loses its `refine` and dead extraction block
    and keeps one `sorry` on the full existential.
  - `Cslib/Logics/Propositional/Tableau/Intuitionistic/Completeness.lean` — `intTruthLemma` gains
    and threads `hpers`.
  - `Cslib/Logics/Propositional/Tableau/Minimal/Completeness.lean` — `minTruthLemma` gains and
    threads `hpers`.

- **Verification:**
  - Full `lake build` completes successfully.
  - The `truthLemma` sorry warning is absent from build output.
  - `grep -c "^\s*sorry$" Cslib/Logics/Propositional/Tableau/Intuitionistic/Scheme.lean` reports
    one fewer live `sorry` than the baseline of 2.
  - No new `axiom` declaration anywhere in the diff.

---

### Phase 2: Record the frame-adequacy verdict at both `Scheme.lean` annotation sites [COMPLETED]
<!-- confirmed by implementation agent: annotations rewritten at the sat_timp STOP-gate note, the T-imp in-body comment, IPosPersistRaw's docstring, openBranch_countermodel's docstring/sorry-site, and openBranch_rawEdges_upward_closed's docstring. Vocabulary audit: no bare "task N" citation introduced (grep confirmed). Full repo lake build green (3325 jobs). -->


- **Goal:** The file's existing honesty register carries the machine-checked frame-adequacy
  table, the exact residual obligation, and the excluded search space — with "refuted" used only
  where something is genuinely machine-refuted.

- **Tasks:**
  - [ ] At the `truthLemma` STOP-gate note (`Scheme.lean:658-670` region) and the surviving
        in-body comments of the former T-imp case: record that DP-5 is now DISCHARGED, that the
        obstruction the note described was an artefact of the frame parameter and disappears
        when the frame is raw or sub-raw, and that `truthLemma` is now an unconditionally true,
        reusable theorem over any persistence-carrying frame. Delete or rewrite the parts of the
        note that assert DP-5 is open — a stale "open" claim on a discharged obligation is itself
        an honesty defect.
  - [ ] At `openBranch_countermodel`'s docstring and its surviving `sorry`: record the section-3
        frame-adequacy table (augmented frame: `IFimpAccess` holds, positive persistence
        REFUTED; raw frame: positive persistence holds, `IFimpAccess` REFUTED at world 2 for
        `phiRef1`/`phiRef2` and worlds 3,4 for `phiRef3`).
  - [ ] State that `rawEdges` is REFUTED as a conjunct-2 witness, citing both CI assertions
        precisely: `CslibTests/WitnessProbe.lean:174-176` (`check [(1,0),(2,1)] = some (true,
        true)` — upward-closed but FORCES `phiRef1` at world 0) and
        `CslibTests/BetaSplitRefutation.lean:304`/`:387` (that `[(1,0),(2,1)]` is the real
        algorithm's raw edge list at the real fuel, with `branchesAgree = true`).
  - [ ] State that three natural pruning rules (prune-at-blocked, prune-at-strictly-blocked, and
        the rules' mutual contradiction on the same syntactic signal) plus the `IFimpAccess`
        greatest fixpoint (collapses to `K = ∅` for `phiRef1`/`phiRef2`/`phiRef3`) are EXCLUDED,
        and that the maximal atom-inclusion frame `⊑` was already excluded.
  - [ ] State the residual obligation in exactly this shape: *a frame carrying `IFimpAccess` and
        positive persistence simultaneously, which the current calculus does not produce.* Note
        that this is the surviving `sorry`'s goal and that it is OPEN, not refuted.
  - [ ] Record that the sub-frame search is not merely untried: conjunct 2 can hold without a
        truth lemma (the `phiRef2` case, where the fixpoint collapses although `rawEdges` itself
        is a witness), so truth-lemma routes are strictly stronger than the goal.
  - [ ] Name the root-cause defect by its durable anchor — `intFImpReuseWitnessAnc?` in
        `Expansion.lean` records a loop-back edge on a containment check it never re-validates as
        the branch grows — and state that repairing it is calculus-level work outside this file.
        **Do NOT cite any task number**: `Cslib/**` is a deliverable tree and the
        no-task-references-in-deliverables rule applies.
  - [ ] Update `openBranch_rawEdges_upward_closed`'s docstring where it says reconciling the two
        conjuncts "is the successor task's job" — that reconciliation is now known impossible on
        the current calculus output. Again, name no task number.
  - [ ] Vocabulary audit before building: every occurrence of "refuted" in the new text maps to
        a cell with CI or probe evidence; `openBranch_countermodel` itself is described as
        "open"; the four eliminated constructions are "excluded".
  - [ ] Run `lake build` and confirm green.

- **Timing:** 1 hour

- **Depends on:** 1

- **Verification Tier:** local

- **Files to modify:**
  - `Cslib/Logics/Propositional/Tableau/Intuitionistic/Scheme.lean` — annotations only.

- **Verification:**
  - Full `lake build` green (Lean doc-comments elaborate; a malformed docstring is a build error).
  - Live sorry count unchanged from Phase 1 (1 in `Scheme.lean`).
  - `grep -n "task [0-9]" Cslib/Logics/Propositional/Tableau/Intuitionistic/Scheme.lean` returns
    no new matches introduced by this phase.

---

### Phase 3: Sweep stale cross-file "truthLemma carries a sorry" claims [NOT STARTED]

- **Goal:** No file in the repository still asserts that the parametric `truthLemma` carries the
  single deferred completeness obligation, since it no longer carries any sorry.

- **Tasks:**
  - [ ] Enumerate every site asserting `truthLemma` has a live sorry (see Scope Hypothesis).
  - [ ] Rewrite each to state the corrected disposition: `truthLemma` is sorry-free; the
        surviving deferred obligations are `openBranch_countermodel`'s existential
        (`Scheme.lean`) and the `Completeness.lean` sorries that rest on it.
  - [ ] Where a file lists a sorry inventory (the `DecisionProcedure.lean` pair), remove the
        `truthLemma` entry rather than reword it, and check the surrounding count/prose still
        reads correctly after removal.
  - [ ] Leave every OTHER sorry disposition in these files untouched — they remain open and
        their annotations remain accurate.
  - [ ] Cite no task numbers in any of these files.
  - [ ] Run `lake build` and confirm green.

- **Timing:** 45 minutes

- **Depends on:** 1

- **Verification Tier:** full

- **Scope Hypothesis:** The stale-claim set is hypothesised to be six files:
  `Tableau/Intuitionistic/Completeness.lean`, `Tableau/Minimal/Completeness.lean`,
  `Tableau/Intuitionistic/DecisionProcedure.lean`, `Tableau/Minimal/DecisionProcedure.lean`,
  `Metalogic/IntDecidability.lean`, and `Metalogic/MinDecidability.lean`. Confirm and correct
  this list at implementation time with
  `grep -rn "truthLemma" --include=*.lean Cslib | grep -i "sorry\|deferred\|open"`. The
  hypothesised count is a starting point, not a budget: sweep whatever the grep actually returns.

- **Files to modify:** the confirmed subset of the six files above — annotations only.

- **Verification:**
  - Full `lake build` green.
  - The confirming grep returns no remaining assertion that `truthLemma` carries a sorry.
  - Repo-wide live sorry count is exactly one lower than the pre-task baseline.

---

### Phase 4: Create the follow-on task for the `intFImpReuseWitnessAnc?` defect [NOT STARTED]

- **Goal:** The root-cause calculus defect is tracked as its own task, so it is neither
  attempted inside this task nor lost.

- **Tasks:**
  - [ ] Re-read `next_project_number` from `specs/state.json` at write time (other tasks are in
        flight this session; do not reuse a plan-time number).
  - [ ] Append an `active_projects` entry with `task_type: "cslib"`, `status: "not_started"`,
        `topic: "Propositional Logic"`, `dependencies: [604]`, and
        `file_scope: ["Cslib/Logics/Propositional/Tableau/Intuitionistic/Expansion.lean"]`.
  - [ ] Title it along the lines of "Re-validate `intFImpReuseWitnessAnc?` loop-back containment
        as the branch grows".
  - [ ] Write a description that carries forward, at minimum: the defect statement
        (`intFImpReuseWitnessAnc?` records a loop-back edge on a `Sfor`-containment check it
        never re-validates as the branch grows); why it matters (re-validating it is what would
        let the augmented frame carry positive persistence, yielding one frame with BOTH
        `IFimpAccess` and persistence and collapsing the whole `openBranch_countermodel`
        problem); the four excluded constructions so they are not re-attempted; and that this is
        calculus-level work in `Expansion.lean`, explicitly outside `Scheme.lean`'s scope.
  - [ ] Reference `specs/604_prove_countermodel_forcing_conjunct_over_constructed_frame/reports/01_conjunct2-frame-adequacy.md`
        as the source. Task-number references ARE permitted here — `specs/**` is exempt from the
        no-task-references rule.
  - [ ] Increment `next_project_number` and run `bash .claude/scripts/generate-todo.sh`.
  - [ ] Verify the new entry appears in `specs/TODO.md` and that `specs/state.json` still parses
        (`jq . specs/state.json > /dev/null`).

- **Timing:** 30 minutes

- **Depends on:** none

- **Verification Tier:** prose

- **Scope Hypothesis:** `next_project_number` was 607 at plan time. This is a hypothesis with a
  known drift risk — confirm by re-reading `specs/state.json` immediately before the write, and
  use whatever value is current.

- **Files to modify:**
  - `specs/state.json` — one new `active_projects` entry, `next_project_number` incremented.
  - `specs/TODO.md` — regenerated, never hand-edited.

- **Verification:**
  - `jq '.active_projects[] | select(.project_number == <new>)' specs/state.json` returns the
    entry.
  - The task appears in `specs/TODO.md` after regeneration.
  - No file under `Cslib/` was touched by this phase.

---

### Phase 5: Final verification and summary [NOT STARTED]

- **Goal:** The full gate set passes, the zero-debt claims are confirmed by measurement rather
  than assertion, and the outcome — including the negative result — is written up.

- **Tasks:**
  - [ ] Run the full `lake build` from a clean state and confirm success.
  - [ ] Confirm `Scheme.lean` live sorry count is exactly 1 (baseline was 2), and that the
        survivor is `openBranch_countermodel`'s existential.
  - [ ] Confirm zero new axioms: check the diff for any `axiom` declaration and run
        `#print axioms` (or `lean_verify`) on `truthLemma`, `intTruthLemma`, and `minTruthLemma`
        to confirm no unexpected axiom dependency was introduced.
  - [ ] Confirm zero new definitions, typeclasses, notations, or imports in the diff.
  - [ ] Run the CSLib CI gate per contribution standards and confirm it passes.
  - [ ] Confirm no task-number citation entered any file outside `specs/**`
        (`bash .claude/scripts/check-task-references.sh` if available; otherwise grep the diff).
  - [ ] Write the implementation summary at
        `specs/604_prove_countermodel_forcing_conjunct_over_constructed_frame/summaries/01_dp5-discharge-honest-restructure-summary.md`,
        leading with the negative result (conjunct 2 over `rawEdges` is machine-refuted; the
        task's literal target is unattainable and this is the authorised documented negative)
        and the positive result (DP-5 discharged, 2 sorries -> 1), and naming the follow-on task.
  - [ ] Commit.

- **Timing:** 45 minutes

- **Depends on:** 1, 2, 3, 4

- **Verification Tier:** full

- **Scope Hypothesis:** The plan asserts a 2 -> 1 live-sorry transition in `Scheme.lean` and a
  repo-wide net change of exactly -1. Confirm both by counting before and after rather than by
  restating this line.

- **Files to modify:**
  - `specs/604_prove_countermodel_forcing_conjunct_over_constructed_frame/summaries/01_dp5-discharge-honest-restructure-summary.md`

- **Verification:**
  - `lake build` green.
  - CSLib CI gate green.
  - Sorry and axiom counts confirmed by command output quoted in the summary.

---

## Testing & Validation

- [ ] Full `lake build` completes successfully at the end of every phase that touches `Cslib/`.
- [ ] The `truthLemma` sorry warning is absent from build output after Phase 1.
- [ ] `Scheme.lean` live sorry count: 2 before, 1 after.
- [ ] Repo-wide live sorry count decreases by exactly 1; no sorry is added anywhere.
- [ ] No new `axiom` declaration; `#print axioms` on the three touched truth-lemma declarations
      shows no unexpected dependency.
- [ ] No new definition, typeclass, notation, or Mathlib import appears in the diff.
- [ ] The CSLib CI gate passes.
- [ ] No task-number citation appears in any file outside `specs/**`.
- [ ] Every use of "refuted" in new annotation text corresponds to a machine-checked cell;
      `openBranch_countermodel` is described as "open".
- [ ] The follow-on task exists in both `specs/state.json` and `specs/TODO.md`.

## Artifacts & Outputs

- `specs/604_prove_countermodel_forcing_conjunct_over_constructed_frame/plans/01_dp5-discharge-honest-restructure.md` (this file)
- `specs/604_prove_countermodel_forcing_conjunct_over_constructed_frame/summaries/01_dp5-discharge-honest-restructure-summary.md`
- Modified: `Cslib/Logics/Propositional/Tableau/Intuitionistic/Scheme.lean`
- Modified: `Cslib/Logics/Propositional/Tableau/Intuitionistic/Completeness.lean`
- Modified: `Cslib/Logics/Propositional/Tableau/Minimal/Completeness.lean`
- Modified (Phase 3, confirmed subset): the `DecisionProcedure.lean` pair and the
  `IntDecidability.lean`/`MinDecidability.lean` pair
- Modified: `specs/state.json`, `specs/TODO.md` (follow-on task)

## Rollback/Contingency

**Per-phase rollback.** Every phase ends at a green `lake build` and its own commit, so reverting
any single phase is `git revert` of that commit. Phase 1 is a declared `atomic-batch`: its three
files revert together or not at all. Never use a destructive git operation on a dirty tree —
snapshot first via `bash .claude/scripts/git-snapshot.sh 604` if a rollback is genuinely needed.

**Contingency A — the two wrapper edits are ruled out of scope.** If the `Completeness.lean`
pair may not be touched, the `hpers` signature change to `truthLemma` cannot land. Fall back to
the route in report section 6: land the DP-5 proof as a **standalone sorry-free variant beside
`truthLemma`** (taking `hpers` as its own hypothesis), leaving `truthLemma`,
`openBranch_countermodel`, and both wrappers untouched except for annotations. This costs roughly
90 lines of duplicated induction and does NOT reduce the sorry count — `truthLemma` keeps its
`sorry`. It is strictly worse and is a fallback, not an alternative. Phases 2, 3, 4, and 5 still
apply, with Phase 3's sweep reduced to whatever remains accurate.

**Contingency B — the DP-5 proof does not reproduce green.** The proof was verified by a real
build, so a failure most likely means the ordering trap (`intro hforce_φ'` placed before the
persistence `have`). Re-check that first. If it still fails, diff the current `truthLemma` region
against `scratch/Scheme.lean.bak` to find the drift. Do not weaken the statement, do not add a
placeholder sorry, and do not proceed to Phase 2 on a red build.

**Contingency C — removing `openBranch_countermodel`'s extraction block breaks the build.** Keep
the block with every binder `_`-prefixed instead of deleting it. The goal is that the surviving
`sorry` carries the whole existential; how much dead scaffolding remains above it is secondary.

**What must never be the recovery.** Passing `(by sorry)` for `hpers` at any call site over the
augmented frame. That statement is machine-refuted, and sorrying a refuted statement is exactly
what this file's honesty discipline forbids — it would be a regression, not a rollback.
