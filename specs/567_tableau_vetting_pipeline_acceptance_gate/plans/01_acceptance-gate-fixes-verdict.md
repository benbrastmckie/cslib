# Implementation Plan: Tableau Vetting-Pipeline Acceptance Gate

- **Task**: 567 - Run the CSLib vetting pipeline against the refactored Tableau subsystem as acceptance gate
- **Status**: [NOT STARTED]
- **Effort**: 5 hours
- **Dependencies**: 553, 558, 562, 563, 564, 565, 566, 586 (all landed; the programme is complete and this task is its terminal gate)
- **Research Inputs**: `specs/567_tableau_vetting_pipeline_acceptance_gate/reports/01_acceptance-gate-ci-verification.md`
- **Artifacts**: plans/01_acceptance-gate-fixes-verdict.md (this file)
- **Standards**:
  - .claude/context/formats/plan-format.md
  - .claude/context/standards/status-markers.md
  - .claude/rules/artifact-formats.md
  - .claude/rules/state-management.md
  - .claude/rules/no-task-references-in-deliverables.md
- **Type**: cslib

## Overview

The acceptance verification has already been run end-to-end (see the research report): all eleven
blocking correctness criteria are green, the `checkInitImports` prerequisite is cleared, and the
two CI failures (`lake lint`'s 145 `unusedArguments`, `lake build --wfail --iofail`'s six modules)
are both pre-existing and outside the programme's territory. What remains is not verification but
**remediation and record-keeping**: correct the cheap, user-facing documentation defects the
verification surfaced, re-record one stale out-of-tree probe verdict with its attribution, emit
the formal acceptance-gate verdict document, and hand the out-of-scope findings forward as
proposed roadmap items.

Definition of done: the nine documentation figures reproduce under their own documented commands;
`s4witness.lean`'s recorded verdict is honest again; a verdict document exists stating
`PASS WITH FIX TASKS` with the full blocking-criteria table and the out-of-scope ledger; and the
full CI gate set is still green after every edit.

### Research Integration

The research report is the evidence base for every figure this plan corrects, and its §7 verdict
grammar is the structure the Phase 6 verdict document instantiates. Three of its dispositions are
load-bearing constraints on this plan:

- **D1-D6 are the in-scope documentation fixes.** All nine findings are documentation-accuracy
  defects; not one touches a proof term.
- **D8 (the `s4witness.lean` divergence) is a stale recorded verdict, not a regression.** Its
  cause is identified and dated to the box-plus birth-key enrichment (`80feb736`, `7960c12e`,
  `5733dcd1`, all 2026-08-05), which `git merge-base --is-ancestor` proves predates the first
  commit of this programme. The correct disposition is re-recording with attribution, never
  deletion and never treating it as a behaviour-preservation failure.
- **D7, D9, and the `unusedArguments` debt are deliberately out of scope** and become proposed
  roadmap items in Phase 6, not work in this task.

**Every figure in the research report was re-confirmed live at plan time** against tree state
`a3a98e56` (working tree clean under `Cslib/`, `CslibTests/`, `ORGANISATION.md`): S4 module count
10, `LoopChecking.lean` 1,626 lines, `S4LoopGuardRegression.lean` 214 lines, `hintikkaS4_*` 10,
`FrameSoundness.lean` 5,396 lines, `FrameCompleteness.lean` 8,264 lines, `ModalTableauResult`
subsystem span 9. The corrections below are therefore twice-measured, not carried over.

**Correction to the research report, discovered at plan time**: the report's `README.md` line
citations are accurate through roughly line 65 but drift by 6-8 lines beyond it. The report cites
`README.md:105, 107, 143, 145`; the live file has those content sites at `:99, :101, :135, :137`.
This is exactly the drift the task description warns about ("ANCHOR ON DECLARATION NAMES, NEVER
LINE NUMBERS"). **Every edit in this plan must be anchored on a quoted string, never on a line
number from the research report.**

### Prior Plan Reference

No prior plan. This is the first plan for this task.

### Roadmap Alignment

No `specs/ROADMAP.md` found in this repository; no roadmap alignment section applies. The
`roadmap_items` written to `completion_data` in Phase 6 are the forward-handoff channel instead.

## Goals & Non-Goals

**Goals**:
- Correct the systematic "eleven S4 modules" off-by-one (there are ten) in all three deliverable
  files it reached, including the root-level `ORGANISATION.md`.
- Correct the six drifted numeric figures in `Cslib/Logics/Modal/Tableau/README.md` and refresh
  the two figures that README self-flags as stale.
- Rescope the `ModalTableauResult` repo-wide command so it stops scanning `specs/` and drifting on
  every task artifact added.
- Re-record `s4witness.lean`'s verdict in the S4 loop-guard task's report 02 with the box-plus
  attribution, preserving the original trace as the historical refutation it documents.
- Emit a formal acceptance-gate verdict document stating `PASS WITH FIX TASKS`, with the eleven
  blocking criteria, the four non-blocking criteria, and the out-of-scope ledger.
- Keep the full CI gate set green after every edit.
- Hand the three out-of-scope remediation bundles forward as `roadmap_items` in
  `completion_data`.

**Non-Goals**:
- **Do not** "fix" the KNOWN-UNSOUND row 1 of `CslibTests/S4LoopGuardRegression.lean` to `"OPEN"`.
  It is a deliberate regression lock (that file's docstring is explicit); changing it destroys the
  regression.
- **Do not** add direct `import Cslib.Init` to any of the ten `S4/` modules. Transitive
  satisfaction is exactly what `checkInitImports` tests; direct imports would create shake residue.
- **Do not** touch any of the 145 pre-existing `lake lint` `unusedArguments` findings, including
  the ten in `Modal/Tableau/`. They trace to work predating this programme, `lake lint` is not in
  PR CI, and they are recorded as a Reasoned Exclusion.
- **Do not** attempt to make `lake build --wfail --iofail` green. It reproduces the documented
  Reasoned Exclusion exactly and would require touching the recorded `[BLOCKED]` sorry or five
  untouched files.
- **Do not** re-run the six expensive probe harnesses (`s4probe`, `s4boxed`, `s4ancestor`,
  `s4subtractive`, `s4subtractive2`, `s4subtractive3`). That is a multi-hour job needing its own
  budget.
- **Do not** create fix tasks directly. Record them as `roadmap_items`; the orchestrator/user
  decides.
- **Do not** touch any figure listed in the research report's §6.2 "Figures that DO reproduce"
  table (declarations 20, pre-split 11,393 lines, `S4/*.lean` 10,294 lines, sorry census 1, axiom
  counts 0/26, 12 re-derivation comment sites, `S4LoopInv` location, boneyard count 1, 3323 jobs).
- **Do not** modify any `.lean` proof term. Every `.lean` edit in this plan is confined to a
  docstring.

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Research-report line numbers are stale (confirmed 6-8 line drift in `README.md` past line ~65) | M | H (already observed) | Anchor every edit on a quoted string. Phase 1 re-derives every site by `grep -n` and records the live anchors; no phase may cite a research-report line number as an edit target. |
| A `.lean` docstring edit accidentally unbalances the `/-! ... -/` delimiters and breaks elaboration | H | L | Phase 2 carries `Verification Tier: local` — build `Cslib.Logics.Modal.Tableau.LoopChecking` immediately after the edit, before proceeding. |
| The `validate-no-task-references.sh` PreToolUse gate blocks a `README.md`/`ORGANISATION.md` edit because new prose cites a task number | M | M | Deliverables outside `specs/**` must use durable anchors only — declaration names, commit SHAs, dates, filenames. Never write "task N" into `README.md`, `LoopChecking.lean`, or `ORGANISATION.md`. If the gate fires, rewrite the prose with a durable anchor rather than working around the gate. |
| Over-correction: touching a figure that already reproduces | M | M | Phase 1's ledger explicitly partitions figures into CORRECT (do not touch) and DRIFTED (correct). Phase 3 works only from the DRIFTED partition. |
| The tree advances mid-implementation and a re-measured figure changes again | M | L | Phase 1 records the tree SHA with the ledger; Phase 5 re-measures the corrected figures a final time and fails the phase if any disagrees with what was written. |
| Editing the README "Provenance of this section" paragraph, which mixes a correct pre-split line count (11,393) with a drifted declaration count (241) in the same sentence | M | M | Phase 3 treats that sentence as a targeted two-token edit (241 -> 243, 1,723 -> 1,626); 11,393 stays. |
| Re-recording `s4witness.lean` deletes the historical refutation the original trace documents | H | L | Phase 4 is strictly additive: annotate the original as superseded and append the live trace. The original block is never removed — it is still the reason `blockedRedirect_boxctx_mem` was retired. |
| The final gate takes far longer than budgeted because the Mathlib cache or build is cold | M | L | Phase 5 runs `lake build Cslib` first; if it is not near-instant, the cache state is reported and the phase budget is extended rather than the gate being skipped. |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2, 4 | 1 |
| 3 | 3 | 2 |
| 4 | 5 | 3, 4 |
| 5 | 6 | 5 |

Phases within the same wave can execute in parallel.

**Territory note**: Phases 2 and 3 both edit `Cslib/Logics/Modal/Tableau/README.md`, so Phase 3 is
serialized behind Phase 2 despite having no logical dependency on it. Phase 4's territory
(`specs/553_.../reports/02_...md`) is disjoint from both, so it runs in parallel with Phase 2.

---

### Phase 1: Live re-measurement and evidence ledger [NOT STARTED]

**Goal**: Re-derive every disputed figure and every edit anchor against the current tree, so no
later phase writes a number or targets a site on the research report's authority alone.

**Tasks**:
- [ ] Record the current tree SHA (`git rev-parse --short HEAD`) and confirm `git status --porcelain Cslib CslibTests ORGANISATION.md` is empty.
- [ ] Re-run each README-documented measurement command and record the live value: S4 module count (`ls -1 Cslib/Logics/Modal/Tableau/S4/*.lean | wc -l`), `wc -l` on `LoopChecking.lean` / `FrameSoundness.lean` / `FrameCompleteness.lean` / `CslibTests/S4LoopGuardRegression.lean`, the attribute-aware declaration-count pattern against `LoopChecking.lean` and against `cat Cslib/Logics/Modal/Tableau/S4/*.lean`, the two-grep repo-wide sorry census (with and without the `Modal/Tableau/` filter), `grep -rnE '^axiom '` at both scopes, the `hintikkaS4_` count against `S4/Hintikka.lean`, and both `ModalTableauResult` span commands.
- [ ] Partition every figure into **CORRECT (do not touch)** and **DRIFTED (correct in Phase 3)**, quoting the live command and its output for each.
- [ ] Enumerate every literal `eleven` occurrence with `grep -rn 'eleven' Cslib/Logics/Modal/Tableau/ ORGANISATION.md` and record each as a quoted-string anchor (not a line number).
- [ ] Re-run `lake env lean specs/553_s4_loop_guard_soundness_reachability_restriction/artifacts/s4witness.lean` and capture the full live trace verbatim for Phase 4.
- [ ] Re-run the box-plus attribution chain (`git log -1 --format='%h %ad' --date=short` on `5733dcd1`, `7960c12e`, `80feb736`; `git merge-base --is-ancestor 5733dcd1 <first programme commit> && echo YES`) and record the outputs.
- [ ] Write `specs/567_tableau_vetting_pipeline_acceptance_gate/artifacts/measurement-ledger.md` holding the tree SHA, the CORRECT/DRIFTED partition with commands and outputs, the quoted-string anchor list, the live `s4witness` trace, and the attribution chain.

**Timing**: 0.75 hours

**Depends on**: none

**Verification Tier**: prose

**Scope Hypothesis**: The research report asserts nine documentation findings (D1-D9), six of them
(D1-D6) in-scope figures, plus two self-flagged stale figures from §6.1 — so roughly eleven
correctable numeric/textual sites, spread over three deliverable files. Plan-time spot-checks
confirmed seven of these live (module count 10, `LoopChecking.lean` 1,626, regression corpus 214,
`hintikkaS4_*` 10, `FrameSoundness.lean` 5,396, `FrameCompleteness.lean` 8,264,
`ModalTableauResult` subsystem span 9). **Confirm at implementation time** by completing the full
partition above; if the DRIFTED partition's cardinality differs from eleven, record the actual
count in the ledger and let Phase 3's checklist follow the ledger, not this hypothesis.

**Files to modify**:
- `specs/567_tableau_vetting_pipeline_acceptance_gate/artifacts/measurement-ledger.md` - created; the evidence base for Phases 3-6

**Verification**:
- The ledger exists, is non-empty, and every DRIFTED row carries both its command and its live output.
- Every anchor in the ledger is a quoted string; no research-report line number appears as an edit target.
- The live `s4witness` trace is captured verbatim, including the `SATURATED OPEN` terminator.

---

### Phase 2: Correct the S4 module count (eleven -> ten) [NOT STARTED]

**Goal**: Eliminate the systematic off-by-one module count from all three deliverable files,
including the root-level governance document.

**Tasks**:
- [ ] Edit `Cslib/Logics/Modal/Tableau/LoopChecking.lean`'s module docstring: `was extracted into eleven \`S4/*.lean\` modules (below)` -> `ten`. This is the self-contradiction the research report names — the same docstring's own bullet list and ASCII dependency diagram already enumerate exactly ten modules.
- [ ] Edit `ORGANISATION.md`'s `Tableau/` subtree annotation: `re-exporting all eleven modules.` -> `re-exporting all ten modules.`
- [ ] Edit each `eleven` occurrence in `Cslib/Logics/Modal/Tableau/README.md` identified by the Phase 1 anchor list (plan-time survey found four: `distributed across the eleven \`S4/*.lean\` modules`, `the eleven-module map`, `live in the eleven \`S4/*.lean\` modules`, and `across eleven new files`) — correcting the word and, where the surrounding prose says "eleven-module map", keeping the phrasing natural ("ten-module map").
- [ ] Re-run `grep -rn 'eleven\|Eleven' Cslib/Logics/Modal/Tableau/ ORGANISATION.md` and confirm zero remaining hits.
- [ ] Build the single edited Lean module: `lake build Cslib.Logics.Modal.Tableau.LoopChecking`.

**Timing**: 0.5 hours

**Depends on**: 1

**Verification Tier**: local

**Scope Hypothesis**: Six `eleven` sites are asserted — one in `LoopChecking.lean`, four in
`README.md`, one in `ORGANISATION.md`. This was measured live at plan time by
`grep -n 'eleven\|Eleven'` against each file. **Confirm at implementation time** against Phase 1's
anchor list; the post-edit `grep` returning zero hits is the closing evidence. If the live count
exceeds six, correct all of them and record the actual count — the hypothesis is the floor, not a
cap.

**Files to modify**:
- `Cslib/Logics/Modal/Tableau/LoopChecking.lean` - module docstring only; one word
- `Cslib/Logics/Modal/Tableau/README.md` - four prose sites
- `ORGANISATION.md` - one subtree-annotation site

**Verification**:
- `grep -rn 'eleven\|Eleven' Cslib/Logics/Modal/Tableau/ ORGANISATION.md` returns nothing.
- `ls -1 Cslib/Logics/Modal/Tableau/S4/*.lean | wc -l` returns 10, matching the new prose.
- `lake build Cslib.Logics.Modal.Tableau.LoopChecking` exits 0 — the docstring edit did not break elaboration.
- `git diff` on `LoopChecking.lean` shows only lines inside the `/-! ... -/` docstring region.

---

### Phase 3: Correct the drifted README numeric figures [NOT STARTED]

**Goal**: Bring every drifted measurement row in the subsystem README back into agreement with the
command printed beside it, and stop the one command that is structurally guaranteed to keep
drifting.

**Tasks**:
- [ ] `LoopChecking.lean` size: `1,723 lines` -> `1,626 lines`, at both the "Provenance of this section" sentence (`and again after the split completed (1,723 lines / 20 declarations`) and the "Corrected `LoopChecking.lean` figures" paragraph (`is **1,723 lines / 20 top-level declarations**`). The `20 declarations` figure is CORRECT and must not change.
- [ ] Pre-split declaration count: `241` -> `243` at both the provenance sentence (`11,393 lines / 241 declarations`) and the corrected-figures paragraph (`241 top-level declarations / 58 \`private\``). The `11,393 lines` figure is CORRECT and must not change.
- [ ] Derived residue count: `The other 221 declarations` -> `223`. This makes the split's arithmetic close exactly (20 + 223 = 243) against the live `S4/*.lean` total; note in the prose that the arithmetic was always right and only the input was off by two.
- [ ] Repo-wide code-position sorry count: `gives **29** code-position sorries repo-wide` -> `**28**`, and the follow-on sentence `The 29 above counts sorries in *code position*` -> `28`.
- [ ] Regression-corpus size: the `wc -l CslibTests/S4LoopGuardRegression.lean   # 197` comment -> `# 214`.
- [ ] `hintikkaS4_*` bridge set: the command comment `# 8` -> `# 10`, and the prose bullet `**\`hintikkaS4_*\` bridge set: 8 declarations.**` -> `10 declarations`. Re-check the adjacent "counting distinct identifiers instead returns 11" claim against the live tree and correct or drop it if it no longer holds.
- [ ] `ModalTableauResult` span: subsystem `# 8` -> `# 9`, and the prose bullet `spans 8 modules here, 9 repo-wide` updated to the live subsystem figure. **Rescope the repo-wide command**: replace `grep -rl 'ModalTableauResult' --include='*.lean' . --exclude-dir=.lake` with a form scoped to `Cslib CslibTests` so it no longer scans `specs/` and drift-bumps on every task artifact added; record the rescoped command's live value as the new stored figure and state in the prose that the command was rescoped and why.
- [ ] Refresh the two self-flagged stale figures: `FrameSoundness.lean 5,317 lines` -> `5,396 lines`, `FrameCompleteness.lean 4,307 lines` -> `8,264 lines`. Update the accompanying caveat sentence — these are now measured at the current tree, not carried over from the `7eb51f69` capture, so the "neither re-measured by the `S4/` split" clause must be replaced with the new provenance rather than left contradicting the refreshed numbers.
- [ ] Re-run every command in the README's `## Measured Baseline` region and confirm each stored number now matches its command's output. This is the README's stated contract with itself.

**Timing**: 1 hour

**Depends on**: 2

**Verification Tier**: prose

**Scope Hypothesis**: Roughly ten distinct figure corrections are asserted across eight anchor
regions of `README.md`, drawn from findings D2-D6 plus the two §6.1 self-flagged stale figures.
Plan-time measurement confirmed the target values (1,626 / 243 / 223 / 28 / 214 / 10 / 9 / 5,396 /
8,264). **Confirm at implementation time** against Phase 1's DRIFTED partition, and close the
hypothesis with the final task above: every command in the `## Measured Baseline` region re-run,
every stored number matching. If a figure in the DRIFTED partition has no corresponding task
above, correct it too and record the addition.

**Files to modify**:
- `Cslib/Logics/Modal/Tableau/README.md` - measurement rows and their surrounding prose; no other section

**Verification**:
- Every command in the README's `## Measured Baseline` region re-run, each stored figure matching its live output.
- The rescoped `ModalTableauResult` repo-wide command does not traverse `specs/`, verified by running it and confirming no `specs/` path appears in its file list.
- No figure from the research report's §6.2 CORRECT table was altered — verified by `git diff` review against the Phase 1 ledger's CORRECT partition.
- No task-number citation was introduced into `README.md` (durable anchors only).

---

### Phase 4: Re-record the s4witness verdict with attribution [NOT STARTED]

**Goal**: Make the out-of-tree regression corpus honest again by annotating the superseded
`s4witness.lean` trace and appending the live one with its cause, without destroying the
historical refutation the original documents.

**Tasks**:
- [ ] In `specs/553_s4_loop_guard_soundness_reachability_restriction/reports/02_redirect-inertness-divergence-audit.md`, add a clearly-marked **SUPERSEDED** annotation immediately above the §2.2 "machine-checked trace" code block, stating that the trace was captured on 2026-07-26 code and no longer reproduces.
- [ ] Append the live trace captured in Phase 1 verbatim, labelled with its capture date and the tree SHA, showing the three concrete divergences: `guard(pos,p0,@2)` reading `none` rather than `some 1` at step [6]; step [7] minting a fresh world 3 (`acc = [2→3 0→2 0→1]`) instead of firing the redirect edge `2→1`; and termination at [7] with `SATURATED OPEN` rather than continuing to [8], with a boxed member now present in the keys.
- [ ] Attribute the change to the box-plus birth-key enrichment, citing the three commits by SHA (`80feb736` additive box-plus mint definitions, `7960c12e` mint-payload switch, `5733dcd1` birth-key enrichment, all 2026-08-05) and the declarations they introduced (`boxPlusPair`, `BoxPlusClosed`, `boxPlusExtraS4`, now in `Cslib/Logics/Modal/Tableau/S4/BirthKey.lean`). Anchor on declaration names, not line numbers.
- [ ] State plainly that this is a **stale recorded verdict, not a behaviour-preservation failure**, and include the `git merge-base --is-ancestor` evidence from Phase 1 showing the enrichment predates the programme's first commit.
- [ ] Confirm by re-reading the edited section that the original trace block, its hypothesis-instantiation table, and the surrounding refutation argument for `blockedRedirect_boxctx_mem` all survive intact — the annotation is additive only.
- [ ] Confirm the in-tree corpus is untouched: `git status --porcelain CslibTests/` empty, and specifically that row 1 (KNOWN-UNSOUND, `"CLOSED"`) of `CslibTests/S4LoopGuardRegression.lean` was not modified.

**Timing**: 0.75 hours

**Depends on**: 1

**Verification Tier**: prose

**Scope Hypothesis**: Three concrete divergences are asserted between the recorded and live
`s4witness.lean` traces, attributed to three named commits. **Confirm at implementation time**
against the Phase 1 captured trace — if the live trace shows a different number of divergences
than three, record the actual set rather than forcing it into three, and re-check whether the
box-plus attribution still fully explains it. An unexplained residual divergence would change the
verdict from `PASS WITH FIX TASKS` to `FAIL` under the research report's §7.4 decision rule
(an unexplained behavioural change is a FAIL even when every build is green), so this confirmation
is gate-critical, not cosmetic.

**Files to modify**:
- `specs/553_s4_loop_guard_soundness_reachability_restriction/reports/02_redirect-inertness-divergence-audit.md` - additive annotation plus appended live trace

**Verification**:
- `git diff` on the report shows additions only in the §2.2 region; zero deletions from the original trace block or its table.
- The appended trace matches the Phase 1 capture byte-for-byte.
- `git status --porcelain CslibTests/` is empty.
- The three attribution SHAs resolve (`git cat-file -e`) and their dates are as recorded.

---

### Phase 5: Post-fix full CI gate re-run [NOT STARTED]

**Goal**: Establish that every blocking criterion is still green after the documentation edits,
producing the evidence table the verdict document instantiates.

**Tasks**:
- [ ] Run the seven-step CI order from the repository root and capture each exit code immediately (never through a compound command ending in `echo` — the research report records mis-reading a result for exactly that reason): `lake build`, `lake exe checkInitImports`, `lake lint`, `lake exe lint-style`, `lake test`, `lake exe mk_all --module`, and `bash scripts/check-shake-residue.sh` (the ratchet wrapper, not bare `lake shake`).
- [ ] Confirm `lake build` job count is unchanged and `lake exe mk_all --module` reports no update necessary with `Cslib.lean` byte-identical after the run.
- [ ] Run the ratchet scripts: `bash scripts/check-sorry-suppressions.sh`, `bash scripts/check-lint-suppressions.sh`, `bash scripts/check-axiom-census.sh`, `bash scripts/check-boneyard-quarantine.sh`.
- [ ] Re-verify behaviour preservation at the axiom level: a standalone snippet importing `Cslib.Logics.Modal.Tableau.FrameCompleteness` and `...CompletenessLoop`, running `#print axioms` on `Cslib.Logic.Modal.Tableau.modalTableauS4Keyed_complete` and on the six `instDecidable{K,T,B,S5,Five,Kb5}Valid` instances; all seven must report only `[propext, Classical.choice, Quot.sound]`.
- [ ] Re-run the two-grep sorry census filtered to `Modal/Tableau/` and confirm exactly one hit, in `FrameSoundness.lean`'s `branchSatisfiableIn_s4FC_ancestor_redirect`.
- [ ] Re-run `lake env lean .../s4driver.lean` and confirm it still reproduces its four-line recorded block exactly.
- [ ] Re-measure every figure Phase 3 wrote and confirm each still agrees; any disagreement fails this phase and sends the figure back to Phase 3.
- [ ] Confirm the two known failures are unchanged in character: `lake lint` still fails with its pre-existing `unusedArguments` findings and **zero** in `S4/` or `LoopChecking.lean` (verified by grepping the lint log for those paths); `lake build --wfail --iofail` still fails on the same six modules with no new warning site.
- [ ] Append the full evidence table (criterion, command, exit code, observed value) to `specs/567_tableau_vetting_pipeline_acceptance_gate/artifacts/measurement-ledger.md`.

**Timing**: 1.25 hours

**Depends on**: 3, 4

**Verification Tier**: full

**Scope Hypothesis**: The gate asserts specific ratchet values — build 3323 jobs, subsystem sorry
census exactly 1, subsystem axiom declarations 0, axiom census 43/43 exact-set, shake residue
12/12 exact-set, lint suppressions 19/19, sorry suppressions 18/18 markers and 28/28 sorries,
boneyard five invariants — and that `lake lint`'s failure count stays at its pre-existing level
with zero findings in programme territory. **Confirm at implementation time** by running every
command above and recording the observed value beside the expected one. A ratchet script's own
exit code is the authority; the numbers here are the research report's observations and may have
moved with unrelated repository work. A ratchet that has moved for reasons outside this
subsystem is a finding to record, not a number to force.

**Files to modify**:
- `specs/567_tableau_vetting_pipeline_acceptance_gate/artifacts/measurement-ledger.md` - evidence table appended

**Verification**:
- All eleven blocking criteria green, each with its command and exit code recorded.
- All seven axiom-checked declarations report the three standard axioms and nothing else.
- Both known non-blocking failures unchanged in character, with zero programme-territory findings.
- Every figure written in Phase 3 re-measured and matching.

---

### Phase 6: Acceptance-gate verdict document and fix-task handoff [NOT STARTED]

**Goal**: Emit the formal verdict and hand the out-of-scope findings forward without creating
tasks directly.

**Tasks**:
- [ ] Write `specs/567_tableau_vetting_pipeline_acceptance_gate/artifacts/acceptance-gate-verdict.md` with: the verdict `PASS WITH FIX TASKS`, the tree SHA and toolchain it was taken against, and the four-level verdict grammar (`PASS` / `PASS WITH FIX TASKS` / `CONDITIONAL` / `FAIL`) with the condition under which each is emitted.
- [ ] Include the **blocking criteria table** (all eleven, each with criterion, verification command, and the Phase 5 observed result) and the **non-blocking criteria table** (the four: `lake lint`, `lake build --wfail --iofail`, documentation-figure reproduction, out-of-tree probe reproduction) each with its rationale for being non-blocking.
- [ ] Record the **decision rule** that separates fix-task-needed from blocking: no proof is weaker, the defect is pre-existing or documentational, and the fix is independently schedulable — all three must hold. State explicitly that an unexplained regression-corpus divergence would have been a FAIL, and that D8 avoided that only because its cause is identified and dated.
- [ ] Record the **remediation ledger**: which findings this task fixed (the module count, the six drifted README figures, the two refreshed stale figures, the rescoped volatile command, the re-recorded `s4witness` verdict) and which it deliberately did not.
- [ ] Record the **Reasoned Exclusions**: the 145 pre-existing `unusedArguments` findings (zero in programme territory, `lake lint` not in PR CI), the six unrun expensive probes, the `--wfail` six-module set, and the `s4ancestor.lean` harness having no logged actual result to reproduce at all.
- [ ] Record the **standing do-nots** so a future reader does not undo them: the KNOWN-UNSOUND regression row must stay `"CLOSED"`; no direct `Cslib.Init` imports in the `S4/` modules.
- [ ] Write `roadmap_items` into `completion_data` in `.return-meta.json` for the three proposed fix bundles: (a) retarget the stale out-of-tree probe artifact records — annotate the S4 loop-guard report 01's `s4probe.lean` harness description as a superseded revision and replace `s4subtractive3.lean`'s pre-split `LoopChecking.lean` line citations with declaration names; (b) repo-wide `unusedArguments` lint hygiene, 145 sites across 27 modules, uniform `omit [Hashable Atom] in` idiom; (c) re-establish the six expensive out-of-tree probe verdicts under a dedicated multi-hour budget.
- [ ] Write `completion_summary` into `completion_data` and set `.return-meta.json` status to `implemented`.
- [ ] Do **not** create tasks, edit `specs/state.json`'s `active_projects`, or invoke `/task`. The roadmap items are a proposal for the orchestrator/user.

**Timing**: 0.75 hours

**Depends on**: 5

**Verification Tier**: prose

**Scope Hypothesis**: Three fix-task bundles and a fifteen-row criteria set (eleven blocking, four
non-blocking) are asserted. **Confirm at implementation time** against the Phase 5 evidence table —
the verdict document's blocking table must have exactly one row per criterion actually run in
Phase 5, with no criterion asserted that was not measured. If Phase 5 surfaced a finding not in the
research report's ledger, it gets its own row and, if out of scope, its own roadmap item; the
count of three is not a cap.

**Files to modify**:
- `specs/567_tableau_vetting_pipeline_acceptance_gate/artifacts/acceptance-gate-verdict.md` - created
- `specs/567_tableau_vetting_pipeline_acceptance_gate/.return-meta.json` - `completion_data` with `completion_summary` and `roadmap_items`

**Verification**:
- The verdict document exists and states exactly one of the four grammar verdicts.
- Every blocking-criteria row traces to a command and observed result recorded in Phase 5's evidence table; no unmeasured criterion is asserted.
- `.return-meta.json` parses as JSON, carries `completion_data.roadmap_items` as a non-empty array of strings, and carries a non-empty `completion_summary`.
- `git diff specs/state.json` is empty for `active_projects` — no task was created.

---

## Testing & Validation

- [ ] `lake build` exits 0; job count recorded and unchanged from baseline.
- [ ] `lake exe checkInitImports` exits 0.
- [ ] `lake exe lint-style` exits 0.
- [ ] `lake test` exits 0 — all eight `S4LoopGuardRegression` rows reproduce, including the deliberately-unsound row 1 at `"CLOSED"`.
- [ ] `lake exe mk_all --module` reports no update necessary; `Cslib.lean` byte-identical.
- [ ] `bash scripts/check-shake-residue.sh` exact-set match against baseline.
- [ ] `bash scripts/check-sorry-suppressions.sh`, `check-lint-suppressions.sh`, `check-axiom-census.sh`, `check-boneyard-quarantine.sh` all pass.
- [ ] `#print axioms` on `modalTableauS4Keyed_complete` and the six `Decidable` instances: all seven report only `[propext, Classical.choice, Quot.sound]`.
- [ ] Subsystem sorry census exactly 1; subsystem `^axiom ` count exactly 0.
- [ ] `lake env lean .../s4driver.lean` reproduces its recorded four-line block exactly.
- [ ] `grep -rn 'eleven\|Eleven' Cslib/Logics/Modal/Tableau/ ORGANISATION.md` returns nothing.
- [ ] Every command in the README's `## Measured Baseline` region re-run with its stored figure matching.
- [ ] No `.lean` diff outside a docstring region; no proof term modified.
- [ ] No task-number citation introduced into any file outside `specs/**`.

## Artifacts & Outputs

- `specs/567_tableau_vetting_pipeline_acceptance_gate/plans/01_acceptance-gate-fixes-verdict.md` (this plan)
- `specs/567_tableau_vetting_pipeline_acceptance_gate/artifacts/measurement-ledger.md` (Phase 1, extended in Phase 5)
- `specs/567_tableau_vetting_pipeline_acceptance_gate/artifacts/acceptance-gate-verdict.md` (Phase 6)
- `specs/567_tableau_vetting_pipeline_acceptance_gate/summaries/01_acceptance-gate-summary.md` (implementation summary)
- Modified: `Cslib/Logics/Modal/Tableau/LoopChecking.lean` (docstring only)
- Modified: `Cslib/Logics/Modal/Tableau/README.md`
- Modified: `ORGANISATION.md`
- Modified: `specs/553_s4_loop_guard_soundness_reachability_restriction/reports/02_redirect-inertness-divergence-audit.md`

## Rollback/Contingency

Every edit in this plan is confined to prose — docstrings, markdown, and a specs-tree report. No
proof term, no definition, no import, and no test assertion is touched, so rollback is
mechanically trivial and carries zero risk to the subsystem's verified state.

- **Per-phase**: each phase commits independently at its own green point, so reverting a single
  phase's commit restores the prior state without disturbing the others.
- **If Phase 2's `LoopChecking.lean` edit breaks elaboration**: revert that one file's hunk and
  re-apply the edit strictly inside the `/-! ... -/` delimiters. The `local` tier catches this
  before any later phase depends on it.
- **If Phase 5 finds a ratchet has moved**: do not force the number. Determine whether the movement
  originates inside this subsystem (which would be a real regression and escalates the verdict to
  `CONDITIONAL` or `FAIL`) or outside it (which is a finding to record in the verdict document and
  hand forward as a roadmap item).
- **If Phase 4's live `s4witness` trace shows a divergence the box-plus attribution does not
  explain**: stop. Under the research report's §7.4 decision rule an unexplained behavioural change
  is a FAIL regardless of build state. Mark the phase `[BLOCKED]`, record the residual divergence,
  and escalate rather than re-recording a verdict that has not actually been explained.
- **Full rollback**: `git revert` the phase commits in reverse order. The tree returns to
  `a3a98e56` state with all eleven blocking criteria still green — they were green before any of
  this work and none of it can change them.
