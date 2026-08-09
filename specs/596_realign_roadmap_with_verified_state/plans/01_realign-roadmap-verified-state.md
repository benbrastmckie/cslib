# Implementation Plan: Realign ROADMAP.md with verified repository state

- **Task**: 596 - Correct ROADMAP.md's stale cleanup agenda and fold in the unrepresented open tasks
- **Status**: [NOT STARTED]
- **Effort**: 7 hours
- **Dependencies**: None
- **Research Inputs**: `specs/596_realign_roadmap_with_verified_state/reports/01_roadmap-realignment-verification.md`
- **Artifacts**: plans/01_realign-roadmap-verified-state.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: meta
- **Lean Intent**: false

## Overview

`specs/ROADMAP.md` has drifted from the tree in three distinct ways: figures that were correct
once and have since moved (decidability matrix, task tracking chains), figures that were **never**
correct (the sorry census, which was already wrong at the exact commit it cites), and whole work
streams that have no roadmap presence at all (CS5, temporal tableau, propositional upstream, modal
tableau decidability). This plan corrects all three classes in a single documentation-only pass
over `specs/ROADMAP.md`, and converts the one self-declared "open decision (no task yet)" into a
tracked task. No `.lean` file is touched.

The governing discipline for the whole plan: **every number written into ROADMAP.md is measured
fresh at execution time by the implementer**, from the commands embedded in each phase below.
Nothing is copied from the research report, from the task description, or from this plan — all
three are dated and the tree has already been observed to move between them (open-task count went
30 -> 46 between the review and the research pass).

### Research Integration

The research report re-verified every claim in the task description against the current tree, and
against commit `26644732` via `git worktree` where the claim is commit-scoped. Two findings
restructure the work relative to the task description:

1. The description declared the sorry census ("27: Bimodal 23 / Propositional 4 / Modal 0") as
   already correct and off-limits. Research overturned this: the repo's own comment-aware counter
   (`.claude/scripts/lean-sorry-census.sh`) gives **Bimodal 41 / Propositional 4 / Modal 0 = 45**,
   and gives the identical figure at commit `26644732` itself. The old number was a methodology
   artifact — `set_option warn.sorry false in` suppression *sites* were counted 1-for-1 while
   several annotated declarations carry 4-6 raw sorries each. This plan therefore corrects the
   census **and records why the old figure was wrong**, so the same undercount is not reintroduced
   by the next person who counts suppression annotations.
2. Several description figures are stale in the *other* direction — genuine forward progress
   (S4 and TB decidability landed after the review) — and several are stale in both directions at
   once (`LoopChecking.lean` is neither the roadmap's 10,723 lines nor the description's 1,626).

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

This task's deliverable *is* `specs/ROADMAP.md`. No `roadmap_flag` phases apply: the roadmap is
the edit target here, not a side artifact to be annotated, so the usual review-snapshot /
update-roadmap wrapper phases would be circular. Phase 1's measurement record serves the same
before-state-snapshot purpose.

## Goals & Non-Goals

**Goals**:
- Correct the sorry census in ROADMAP.md to a freshly measured figure, with a short provenance
  note explaining the counting methodology and why the prior figure undercounted.
- Correct every falsified claim identified in the task description's items (1) and (2), each
  re-verified at execution time.
- Move terminal (completed/expanded/abandoned) work out of "Remaining" and into "Completed".
- Give the four unrepresented streams — modal tableau decidability, CS5, temporal tableau,
  propositional upstream — their own roadmap sections, and fold in the open tasks that currently
  have zero roadmap presence.
- Resolve item (5) by creating a tracked task for the BXCanonical/dense-vs-algebraic decision and
  repointing the roadmap at it.

**Non-Goals**:
- No `.lean` file is created, edited, or deleted. Not one.
- No proof, build, or CI work. `lake build` is not required by any phase and must not be run as
  a gate (the tree is knowingly red on the 4 bare Propositional sorries).
- No edits to `README.md`, even though it is suspected to carry the same stale census — it is
  outside this task's `file_scope`. Phase 6 flags it for a follow-up instead.
- No autonomous mathematical decision on BXCanonical. The decision is *tracked*, not *made*.
- No edits to `specs/reviews/review-2026-08-07.md` or `specs/ROADMAP-alignment-audit.md`; those
  are historical records and stay as written.

## Cross-Cutting Constraints (apply to every phase)

1. **Anchor edits by content, never by line number.** Every line number in the research report and
   in this plan (`:114`, `:146-149`, `:157`, `:173-176`, `:183`) refers to ROADMAP.md *as of
   planning time*. Each phase shifts subsequent lines. Locate each edit target by its section
   heading plus its distinctive row text (e.g. the row whose Tracking cell reads `511 → 506 →
   umbrella 300`), and re-`grep` for it at the start of the phase that edits it.
2. **Measure, then write.** No figure enters ROADMAP.md that was not produced by a command run in
   this execution. If a command's output disagrees with this plan, the command wins — record the
   discrepancy in the measurement record and proceed with the measured value.
3. **Date-stamp volatile figures.** Any figure known to move (sorry counts, file sizes, task
   counts) is written with an explicit `(as of YYYY-MM-DD)` qualifier so the next reader knows its
   vintage rather than inheriting an undated assertion.
4. **One file.** The only deliverable file modified is `specs/ROADMAP.md`, plus `specs/state.json`
   / `specs/TODO.md` via the standard task-creation path in Phase 4, plus this task's own
   artifacts under `specs/596_realign_roadmap_with_verified_state/`.

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Implementer copies figures from this plan or the research report instead of measuring | H | M | Each phase embeds its exact commands; Phase 1 produces a measurement record that Phase 6 cross-checks every written figure against. A figure present in ROADMAP.md but absent from the measurement record is a Phase 6 failure. |
| Line-number anchors drift as earlier phases edit the file | M | H | Cross-cutting constraint 1: content-anchored edits, re-grep at phase start. |
| The corrected census (45) is written in one place and the old figure (27/23) survives elsewhere | H | M | Phase 6 greps the whole file for every superseded numeral (`27`, `23`, `14`, `10,723`, `230`, `6 `) and requires each surviving hit to be explained. |
| Re-introducing the same undercount later by counting suppression annotations | M | M | Phase 2 writes the methodology note naming `.claude/scripts/lean-sorry-census.sh` as the counter of record, not just the corrected number. |
| Scope creep into `.lean` files or into README.md | H | L | Non-Goals are explicit; Phase 6 verifies `git status` shows no `.lean` file modified. |
| Autonomous context cannot prompt for the BXCanonical decision | M | H | Phase 4 deliberately creates a *decision task* rather than deciding; no user prompt needed. |
| Newly created task number collides with a concurrent session | M | L | Phase 4 reads `next_project_number` from `specs/state.json` at write time and regenerates TODO.md via the standard script rather than hand-editing. |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2 | 1 |
| 3 | 3 | 1, 2 |
| 4 | 4 | 1, 3 |
| 5 | 5 | 1, 4 |
| 6 | 6 | 2, 3, 4, 5 |

Phases within the same wave can execute in parallel. This plan is fully sequential: every phase
after the first edits the same file, so no two edit phases may run concurrently.

---

### Phase 1: Re-measure the full numeric baseline [NOT STARTED]

**Goal**: Produce a dated, command-cited measurement record that every later phase writes from and
that Phase 6 audits against. No ROADMAP.md edit occurs in this phase.

**Tasks**:
- [ ] Run the sorry census per subtree and record each figure:
  - `bash .claude/scripts/lean-sorry-census.sh Cslib/Logics/Bimodal`
  - `bash .claude/scripts/lean-sorry-census.sh Cslib/Logics/Propositional`
  - `bash .claude/scripts/lean-sorry-census.sh Cslib/Logics/Modal`
  - `bash .claude/scripts/lean-sorry-census.sh Cslib/` (repo-wide total, plus confirmation that
    Temporal / LTL / HML / LinearLogic / Foundations are sorry-free)
- [ ] From the repo-wide `sorry_inventory` output, derive the per-file Bimodal breakdown and the
  BXCanonical subtotal (`BXCanonical/Chronicle/ChronicleToCountermodel.lean` +
  `BXCanonical/Frame.lean`) and the Bundle subtotal (`Bundle/SuccRelation.lean` +
  `Bundle/UntilSinceCoherence.lean`).
- [ ] Record how many Propositional sorries are bare vs `warn.sorry`-suppressed (this is what the
  existing prose claims drives the red `lake build --wfail --iofail`); confirm by inspecting the
  inventory's cited lines, not by running a build.
- [ ] Enumerate decidability instances and their true locations:
  `grep -rn "^instance instDecidable.*Valid" --include=*.lean Cslib/` — record count and the
  file:line of each, especially which file holds the K instance.
- [ ] Measure the modal system grid: `ls Cslib/Logics/Modal/ProofSystem/Instances/ | wc -l` and
  the subsumption theorem count
  `grep -c "^theorem \|^lemma " Cslib/Logics/Modal/Metalogic/InterSystem/AxiomSubsumption.lean`.
- [ ] Measure `wc -l Cslib/Logics/Modal/Tableau/LoopChecking.lean` and its declaration count; also
  `ls Cslib/Logics/Modal/Tableau/S4/` and the combined line total of that directory.
- [ ] Confirm the structural claims: `Boneyard/` exists and its contents;
  `Cslib/Foundations/Logic/Tableau/Blocking.lean` exists, its line count, and its declaration
  list; `Cslib/Logics/Temporal/Tableau/` file list and line total.
- [ ] Enumerate open tasks and their roadmap presence:
  - open task list from `specs/state.json` (`project_number`, `status`, `title`)
  - task numbers literally appearing in ROADMAP.md prose
  - the set difference: open tasks with zero roadmap presence, with counts for both sides
- [ ] Read the status of every task number ROADMAP.md currently cites (from `specs/state.json` and
  `specs/archive/state.json`) so later phases know which rows are terminal.
- [ ] Confirm `grep -n "Modal Tableau Decidability" specs/ROADMAP.md` still returns nothing.
- [ ] Confirm no task in either state file targets BXCanonical or the algebraic-pipeline decision
  by name.
- [ ] Write all of the above, with the exact command and its raw output for each figure, to
  `specs/596_realign_roadmap_with_verified_state/reports/02_execution-time-measurements.md`,
  headed with the execution date and `git rev-parse HEAD`.

**Timing**: 1.5 hours

**Depends on**: none

**Verification Tier**: prose

**Scope Hypothesis**: The research report predicts Bimodal 41 / Propositional 4 / Modal 0 = 45,
8 decidability instances, `LoopChecking.lean` at 2,216 lines / 15 declarations, BXCanonical 21
sorries, and 36 of 46 open tasks absent from the roadmap. **These are hypotheses, not inputs.**
Confirm each by the command listed above and record the measured value. Where measurement and
hypothesis disagree, the measurement is authoritative and the divergence is noted explicitly in
the measurement record.

**Files to modify**:
- `specs/596_realign_roadmap_with_verified_state/reports/02_execution-time-measurements.md` -
  created

**Verification**:
- The measurement record exists, is non-empty, and every figure in it is accompanied by the
  command that produced it and that command's raw output.
- `git status --short` shows no modification to any `.lean` file and no modification to
  `specs/ROADMAP.md`.

---

### Phase 2: Correct the sorry census and Section A rows [NOT STARTED]

**Goal**: Bring the "Remaining -> A. Completeness / decidability gaps" section — its census prose
and all six of its rows — into agreement with the Phase 1 measurements, and record why the
previous census was wrong.

**Tasks**:
- [ ] Replace the "Verified sorry counts (2026-08-07)" prose block with the Phase 1 figures,
  date-stamped to the execution date, keeping the existing sentence structure (repo-wide total,
  per-module split, the sorry-free module list, the bare-vs-suppressed distinction and its
  connection to the red `lake build --wfail --iofail`).
- [ ] Add a short methodology note immediately after the census: the count is produced by
  `.claude/scripts/lean-sorry-census.sh` (comment/string-aware, depth-counting nested block
  comments); a prior census undercounted because it counted `set_option warn.sorry false in`
  suppression *sites* rather than raw `sorry` occurrences, and a single suppressed declaration can
  carry several. State this as the reason the figure changed, so the correction is not mistaken
  for new proof debt appearing.
- [ ] S4 decidability row (Tracking `511 → 506 → umbrella 300`): if Phase 1 confirms the S4
  instance landed and the tracking task is terminal, remove the row from Remaining; it is
  re-homed in the Completed section by Phase 3.
- [ ] Pure-K5 / pure-5 row (Tracking `534`): re-check the tracked task's status and the presence
  of a `Five`/`K5` decidability instance; keep, amend, or retire the row accordingly.
- [ ] Propositional tableau completeness row: replace the dead tracking chain with the live owner
  chain identified in Phase 1; state the measured Propositional sorry count and that the tracked
  sorries are still live even though the old chain is fully terminal.
- [ ] S4 keyed loop-check guard row (DISCHARGED BY REFUTATION): re-confirm its cited artifacts
  still exist; leave the row's substance intact if so.
- [ ] Bimodal discrete completeness row: replace the sorry figure with the measured Bimodal total,
  and replace the "23 sorries across three tasks" ownership claim with the measured subtotals
  (BXCanonical group / Bundle group / conservativity group). Where a group has no open task naming
  its files, say so explicitly rather than implying coverage.
- [ ] Bimodal -> temporal conservativity row: re-verify the sorry count against the measurement
  record and correct if needed.

**Timing**: 1.5 hours

**Depends on**: 1

**Verification Tier**: prose

**Scope Hypothesis**: This phase assumes Section A contains exactly six rows plus the census prose
block, and that the S4 row is removable. Confirm the row inventory by re-reading the section
before editing; if the row count differs, adjust and note it — the row list here is a hypothesis
about the file's current shape, not a specification of it.

**Files to modify**:
- `specs/ROADMAP.md` - "Remaining -> A. Completeness / decidability gaps" section only

**Verification**:
- Every numeral in the edited section appears in the Phase 1 measurement record.
- The methodology note names `.claude/scripts/lean-sorry-census.sh` explicitly.
- The census carries an execution-date stamp.
- No other section of ROADMAP.md is modified by this phase (`git diff` is confined to Section A).

---

### Phase 3: Correct falsified claims in the Completed section [NOT STARTED]

**Goal**: Fix the three Completed-section claims contradicted by the tree, and re-home the work
that genuinely completed since the review.

**Tasks**:
- [ ] Decidability-instances row: correct the instance count to the Phase 1 measurement, list the
  systems actually covered, and correct the module attribution — the row currently attributes all
  instances to `FrameCompleteness.lean`, but Phase 1 measured the K instance in a different file.
  Cite both files.
- [ ] Add an explicit statement of how much of the 15-system grid is decidable (measured
  instances out of the measured grid size), so the row can no longer read as "decidability is
  essentially delivered" when it is not.
- [ ] CS5 row ("Constructive CS5 = IS5 completeness ... the constructive capstone"): reconcile
  against `Cslib/Logics/Modal/Metalogic/Constructive/Labelled/Soundness.lean`'s module docstring,
  re-read at execution time. If the docstring still states the general soundness direction has not
  landed, qualify the row to name precisely what did land and what did not, rather than deleting
  the row or leaving it unqualified.
- [ ] Temporal "tableau" claim in the Bimodal & Temporal table: re-check the Temporal tableau
  directory contents and the status of the tasks that own it. If those tasks are non-terminal,
  qualify the claim to state which components are delivered and which remain open, rather than
  listing "tableau" as unqualified-delivered.
- [ ] Add the S4 (and any other newly landed) decidability corner to the "Consolidation &
  completeness landed since the mid-2026 review" table, so the work removed from Remaining in
  Phase 2 lands somewhere.

**Timing**: 1 hour

**Depends on**: 1, 2

**Verification Tier**: prose

**Scope Hypothesis**: Assumes the CS5 and Temporal-tableau overstatements are still present as
described and that the Soundness.lean docstring still carries the "not yet landed" language.
Confirm by re-reading the docstring and the two roadmap rows at phase start; if either has changed,
record the divergence and adjust the edit rather than forcing the planned wording.

**Files to modify**:
- `specs/ROADMAP.md` - "Completed" section tables only

**Verification**:
- The decidability row's count and file attributions match the measurement record.
- The CS5 and Temporal rows quote or paraphrase a source re-read in this phase, and the source is
  cited by path in the row or an adjacent note.
- `git diff` for this phase is confined to the Completed section.

---

### Phase 4: Rewrite Section B and track the BXCanonical decision [NOT STARTED]

**Goal**: Reduce "B. Abstraction & Redundancy Cleanup" to the work that is actually outstanding,
correct its figures, and convert the self-declared "open decision (no task yet)" into a tracked
task.

**Tasks**:
- [ ] For each of the five Section B rows, check every tracked task's status against the Phase 1
  status table. Move rows whose tracked tasks are all terminal into the Completed section (the
  "landed since the mid-2026 review" table), preserving what was delivered rather than deleting
  the row outright.
- [ ] Correct the `LoopChecking.lean` figure to the Phase 1 measurement, with an explicit
  as-of date and a note that the file is under active change (an open task targets it), so the
  figure is not read as stable. Also correct or drop the claim about how many `Modal/Tableau/S4/*`
  modules the split produced, per the measured directory listing.
- [ ] Drop the "(new)" tag from the `Foundations/Logic/Tableau/Blocking.lean` target and state its
  measured size and declaration inventory; the file exists and is no longer new.
- [ ] Keep any row whose tracked tasks are genuinely open, with its status re-stated accurately.
- [ ] Correct the BXCanonical sorry count in the "Open decision" paragraph to the Phase 1
  BXCanonical subtotal.
- [ ] Create a task for the BXCanonical decision, using the standard path: read
  `next_project_number` from `specs/state.json`, append the task entry (title naming the decision
  between completing `BXCanonical/dense` and consolidating onto the algebraic pipeline; body
  carrying the measured sorry count, the fact that nothing downstream imports the leaf, and both
  options), increment `next_project_number`, then run `bash .claude/scripts/generate-todo.sh`.
  Do **not** decide the question — the task's purpose is to hold the decision, not pre-empt it.
- [ ] Replace "Open decision (no task yet)" with a pointer to the newly created task number.
- [ ] Re-title Section B if the "current priority" framing is no longer accurate after the stale
  rows are removed.

**Timing**: 1.5 hours

**Depends on**: 1, 3

**Verification Tier**: local

**Scope Hypothesis**: Assumes Section B has five rows of which four are fully terminal, and that
no existing task already covers the BXCanonical decision. Both were checked at research time and
must be re-checked here: re-read the section for the row count, and re-grep both state files for
BXCanonical/algebraic-pipeline coverage before creating a duplicate task.

**Files to modify**:
- `specs/ROADMAP.md` - Section B and the Completed "landed since" table
- `specs/state.json` - one new task entry, `next_project_number` incremented
- `specs/TODO.md` - regenerated via `generate-todo.sh` (never hand-edited)

**Verification**:
- `python3 -c "import json; json.load(open('specs/state.json'))"` parses cleanly and the new task
  appears exactly once with a unique `project_number`.
- `specs/TODO.md` was regenerated by the script (its diff shows the new task) and was not edited
  by hand.
- The Section B "Open decision" paragraph now names a real task number present in `state.json`.
- No `.lean` file appears in `git status --short`.

---

### Phase 5: Correct Section C and add the four missing stream sections [NOT STARTED]

**Goal**: Fix the false "folded into" claim in Section C, and give the four unrepresented work
streams roadmap sections that fold in the open tasks currently absent from the document.

**Tasks**:
- [ ] Section C: the "Abstract shared completeness infrastructure across Temporal + Bimodal" row
  claims the obligation was folded into the Chronicle-consolidation task. Re-read that task's
  summary; if it closed as a descoped partial with the relevant phases explicitly out of scope,
  correct the row to say the obligation was **not** absorbed, name the task that still holds it and
  the task created because the consolidation did not deliver it, and state their current statuses.
- [ ] Add a **Modal Tableau Decidability** section under Remaining, implementing the
  recommendation from `specs/ROADMAP-alignment-audit.md` that was never applied. It should state
  the measured matrix coverage (instances landed out of grid size), name the corners still without
  a `Decidable` instance, name the blocker class that gates them, and list the open tasks that own
  the successor work.
- [ ] Add a **Constructive CS5** section naming the open tasks in that stream, their statuses, and
  the specific soundness direction still outstanding per the module docstring re-read in Phase 3.
- [ ] Add a **Temporal tableau** section naming the open tasks in that stream, their statuses, and
  which components of `Cslib/Logics/Temporal/Tableau/` are complete versus partial.
- [ ] Add a **Propositional upstream** section covering the connective-typeclass, naming, and
  bot-rule-free ND stream, plus the open tasks in it.
- [ ] Fold the remaining roadmap-absent open tasks from the Phase 1 set difference into the most
  appropriate existing or new section. Where a task genuinely does not belong on the roadmap
  (housekeeping, meta, or reconciliation tasks including this one), do not force it in — instead
  record the deliberate exclusions and their reason in a short note so the next audit does not
  re-flag them as omissions.
- [ ] State the open-task coverage figure (tasks with roadmap presence out of total open) with an
  as-of date, so the next audit has a baseline to compare against.

**Timing**: 1.5 hours

**Depends on**: 1, 4

**Verification Tier**: prose

**Scope Hypothesis**: Assumes 36 of 46 open tasks currently lack roadmap presence and that the
four named streams are entirely absent. Both figures come from Phase 1's measurement, not from
this plan; the section-writing must consume Phase 1's set difference directly. If the measured
count differs, write the measured count.

**Files to modify**:
- `specs/ROADMAP.md` - Section C plus four new Remaining subsections

**Verification**:
- `grep -n "Modal Tableau Decidability" specs/ROADMAP.md` now returns a hit.
- Every task number newly written into ROADMAP.md exists in `specs/state.json` or
  `specs/archive/state.json` with the status claimed for it.
- The set of open tasks with zero roadmap presence, recomputed after this phase, is smaller than
  Phase 1's measurement, and every task still absent is covered by the deliberate-exclusion note.

---

### Phase 6: Whole-document consistency audit and residue sweep [NOT STARTED]

**Goal**: Verify the document is internally consistent, that no superseded figure survives
anywhere, and that scope was respected.

**Tasks**:
- [ ] Sweep for superseded numerals across the whole file: the old census figures, the old
  BXCanonical count, the old `LoopChecking.lean` line and declaration counts, and the old
  decidability-instance count. For each surviving hit, either correct it or record why it is a
  legitimate different use of the same numeral.
- [ ] Cross-check every numeral now present in ROADMAP.md against the Phase 1 measurement record.
  A figure in the document with no counterpart in the record is a failure of this phase — either
  measure it now and add it to the record, or remove the assertion.
- [ ] Re-verify every task number cited anywhere in ROADMAP.md against `specs/state.json` and
  `specs/archive/state.json`: no citation may claim a status the state files contradict, and no
  Remaining row may be tracked solely by terminal tasks.
- [ ] Confirm internal consistency between sections: the Completed decidability row, the new
  Modal Tableau Decidability section, and Section A must state the same matrix coverage; the
  Section A census, the Bimodal row subtotals, and the Section B BXCanonical figure must sum
  consistently.
- [ ] Check `README.md` for the same superseded census figures. **Do not edit it** — it is outside
  this task's `file_scope`. If stale figures are present, record the finding in the implementation
  summary and flag it for a follow-up task.
- [ ] Confirm scope: `git status --short` shows no `.lean` file modified and no file outside
  `specs/` modified.
- [ ] Write the implementation summary to
  `specs/596_realign_roadmap_with_verified_state/summaries/01_realign-roadmap-verified-state-summary.md`,
  including a before/after table of every corrected figure and the README.md finding.

**Timing**: 1 hour

**Depends on**: 2, 3, 4, 5

**Verification Tier**: prose

**Scope Hypothesis**: None asserted by this phase; it consumes and audits the counts asserted by
Phases 1-5 rather than introducing new ones.

**Files to modify**:
- `specs/ROADMAP.md` - residual corrections found by the sweep
- `specs/596_realign_roadmap_with_verified_state/summaries/01_realign-roadmap-verified-state-summary.md` - created

**Verification**:
- Zero unexplained hits for superseded figures.
- Every numeral in ROADMAP.md traces to the measurement record.
- Every task citation matches the state files.
- `git status --short` confirms scope: `specs/ROADMAP.md`, `specs/state.json`, `specs/TODO.md`,
  and this task's artifacts only.

---

## Testing & Validation

- [ ] `specs/ROADMAP.md` renders as valid markdown; all tables have consistent column counts and
  the mermaid block is untouched.
- [ ] Every numeric claim in ROADMAP.md appears in
  `reports/02_execution-time-measurements.md` with its producing command.
- [ ] Every task number cited in ROADMAP.md exists in `specs/state.json` or
  `specs/archive/state.json`, with a status matching the claim made about it.
- [ ] No Remaining row is tracked exclusively by terminal (completed/abandoned/expanded) tasks.
- [ ] `grep -n "Modal Tableau Decidability" specs/ROADMAP.md` returns a hit.
- [ ] The BXCanonical open decision names a real task number.
- [ ] `python3 -c "import json; json.load(open('specs/state.json'))"` parses cleanly.
- [ ] `git status --short` lists no `.lean` file and nothing outside `specs/`.
- [ ] `git diff --stat` on `specs/ROADMAP.md` shows changes confined to the Completed, Remaining
  A/B/C, and new stream sections — the Approach, Module Dependency Structure, and Project
  Structure sections are unchanged.

## Artifacts & Outputs

- `specs/ROADMAP.md` (modified — the deliverable)
- `specs/596_realign_roadmap_with_verified_state/reports/02_execution-time-measurements.md` (new)
- `specs/596_realign_roadmap_with_verified_state/summaries/01_realign-roadmap-verified-state-summary.md` (new)
- `specs/state.json`, `specs/TODO.md` (one new task for the BXCanonical decision)

## Rollback/Contingency

Every change is documentation-only and confined to tracked files, so rollback is a targeted
`git checkout` of `specs/ROADMAP.md` at the pre-task commit. Phases are committed individually
(`task 596 phase {P}: {name}`), so a bad phase can be reverted without losing the measurement
record from Phase 1 — which is the expensive artifact and is worth preserving even if the
ROADMAP edits are redone. If Phase 4's task creation lands but later phases fail, leave the task
in place: a tracked decision is correct regardless of the rest of the realignment. If the tree
moves mid-execution such that Phase 1's measurements go stale, re-run Phase 1 and note both
measurement rounds in the record rather than silently overwriting the first.
