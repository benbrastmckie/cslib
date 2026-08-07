# Implementation Plan: Delete the Refuted Ancestor-Redirect Lemma

- **Task**: 582 - s4_ancestor_redirect_soundness_obstruction
- **Status**: [IMPLEMENTING]
- **Effort**: 5 hours
- **Dependencies**: None (tasks 553, 566, 567, 586 all [COMPLETED])
- **Research Inputs**: specs/582_s4_ancestor_redirect_soundness_obstruction/reports/01_ancestor-redirect-refutation-and-route-choice.md
- **Artifacts**: plans/01_delete-refuted-ancestor-redirect-lemma.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: cslib
- **Lean Intent**: false

## Overview

**ROUTE (c) — DELETE.** `branchSatisfiableIn_s4FC_ancestor_redirect`
(`Cslib/Logics/Modal/Tableau/FrameSoundness.lean:1227`, `sorry` at `:1251`) is the repository's
only `sorry` with no owning task. Research produced a machine-checked refutation: the lemma's
statement is **false**, not merely unprovable — an explicit 3-world countermodel compiles clean
with axioms `[propext, Quot.sound]` and no `sorryAx`. This eliminates route (a) on logical
grounds (there is no proof of a false statement to import) and makes route (b) a fourth
restatement of a fact the tree already proves three times. The task description pre-authorizes
route (c), including reversing the retain-by-user-decision and coordinating with the Boneyard
carve-out.

The deletion is not an erasure. The countermodel is promoted into `CslibTests/` as an executable
regression witness (so a fifth rediscovery of this obstruction fails the test suite instead), and
the upgraded obstruction record — now "refuted", not "blocked" — is relocated into the
`accPinnedBy` module comment, which already names this lemma as one of three dead routes.

Definition of done: route recorded in plan and in file/commit; `FrameSoundness.lean` contains no
`sorry`; `lake build --wfail --iofail` emits strictly fewer sorry warnings than before and no new
warnings; `lake test` exit 0; no other proof/definition/theorem statement altered; Boneyard
carve-out record updated.

### Research Integration

Findings from `reports/01_ancestor-redirect-refutation-and-route-choice.md` driving this plan:

- **The refutation** (report §0): countermodel `acc = {0→1, 2→1}`, `b = [T(□p)@0, F(p)@2]`,
  redirect `1→2`; `hboxback`/`hdianeg` hold vacuously. The defect is structural — transitive
  closure transmits box-positive payload from every `acc`-ancestor of `src`, and a hypothesis set
  naming only `src` cannot see them. Probe preserved at
  `specs/582_s4_ancestor_redirect_soundness_obstruction/scratch_refute_ancestor_redirect.lean`.
- **Zero code consumers** (report §1), re-verified live: 3 `.lean` hits, all in
  `FrameSoundness.lean`, none a use site.
- **Route (b) is a duplicate** (report §4): all three ways to supply the missing hypothesis are
  already landed — `branchSatisfiablePinnedIn_redirect_mechanical`,
  `branchSatisfiableIn_s4FC_addEdge_of_blocked`, and the `S4RedirectSoundInv_*` family.
- **Six-touch-point deletion surface** (report §5), with the census regenerated via
  `--update`, never hand-edited.
- **Relocation over erasure** (report §6): `CslibTests/` promotion preferred over specs-tree
  retention, because a compiled countermodel cannot go stale.

**One correction to the research report's §5 table, found during planning**: the report lists
`specs/ROADMAP.md:146` as the only ROADMAP touch point. A live sweep found a **second**:
`specs/ROADMAP.md:156`, a Remaining-work table row naming the lemma by name
(`| **S4 keyed loop-check guard soundness** (1 sorry, the only Modal one) | 553 → 582 | ... |`).
The report's own §5 caveat about re-running the sweep applies; Phase 6 re-runs it rather than
trusting either enumeration.

### Prior Plan Reference

No prior plan for this task. Two adjacent completed tasks calibrate effort and risk:

- **586** (duplicate adjudication) is direct precedent for the work *shape*: it deleted a
  zero-consumer declaration, rerouted call sites, and "reconciled three prose records the
  deletions falsified", with all CI gates at baseline. Prose reconciliation was the bulk of that
  task, not the deletion.
- **567** (vetting acceptance gate) is the source of the current measured CI baseline and
  established the house standard that documentation figures are live-re-measured, and drifted
  numeric prose is a defect. Every count in this plan is therefore a hypothesis to confirm at
  implementation time, never a fact to copy forward.

### Roadmap Alignment

`specs/ROADMAP.md` exists and was read for context only (no `roadmap_flag`; ROADMAP.md is not
modified by this plan except as one of the falsified-prose touch points in Phase 6). Items this
task advances:

- **Section A, "Completeness / decidability gaps"** — the repo-wide code-position sorry count
  drops by one (Modal goes to 0), and the `**S4 keyed loop-check guard soundness**` Remaining row
  is discharged by refutation rather than by proof.
- **CI honesty gates** — the `axiom-census` ratchet's `sorryAx`-tainted set shrinks by one.

## Goals & Non-Goals

**Goals**:
- Record route (c) in this plan, in the tree (relocated module comment), and in the commit.
- Bring `FrameSoundness.lean`, and therefore the Modal/Tableau subsystem, to **0** sorries.
- Preserve the refutation as an executable `CslibTests/` regression witness.
- Relocate the upgraded (refuted, not blocked) obstruction record into the `accPinnedBy` module
  comment, including the Massacci category-error note.
- Reconcile every prose/baseline record the deletion falsifies, with the axiom census regenerated
  by `--update`.
- Reverse the retain-by-user-decision and record that task 566's carve-out 1 rationale has lapsed.

**Non-Goals**:
- Proving the lemma, or any restatement of it (route (a) is impossible; route (b) is a duplicate).
- Altering any other proof, definition, or theorem statement. `accPinnedBy`,
  `branchSatisfiablePinnedIn`, `branchSatisfiablePinnedIn_redirect_mechanical`,
  `branchSatisfiableIn_s4FC_addEdge_of_blocked`, and the `S4RedirectSoundInv_*` family are
  untouched.
- Moving anything to `Boneyard/`. The lemma is deleted, not quarantined — a false statement's
  provenance value is fully captured by the relocated countermodel.
- Touching `specs/TODO.md` measured-state prose inside other tasks' descriptions (historical
  measurement records, generated from `state.json`, not live ratchets).
- Re-deriving Massacci's Theorem 8.1 gap. It is accepted as recorded, per the task's explicit
  instruction.

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| The scratch probe no longer compiles against a drifted tree | H | L | Phase 1 re-runs it before anything is edited; a red probe halts the plan and re-opens the route decision rather than proceeding to delete |
| Deletion line range drifts between planning and execution | M | M | Phase 4 re-locates all three boundaries by `grep -n` on declaration/section markers, never by the line numbers written here |
| Census baseline hand-edited instead of regenerated | H | L | Phase 5 runs `scripts/check-axiom-census.sh --update` exclusively; the file header says "do not hand-edit" and the ratchet compares column 1 as an exact set |
| A falsified prose record is missed | M | M | Phase 6 re-runs the repo-wide sweep rather than working from either the report's or this plan's enumeration; Phase 8 re-sweeps as a gate |
| `CslibTests/` promotion fails on the module-system idiom | M | M | The scratch file uses a bare `import`; `CslibTests/*.lean` use `module` + paired `import` / `public meta import`. Phase 2 adapts to the neighbour file's idiom (`S4LoopGuardRegression.lean`) rather than pasting the probe verbatim |
| Reversing an explicit user decision without confirmation | M | L | The task description pre-authorizes route (c) explicitly, including the reversal; the refutation is new evidence unavailable when the retention decision was made, and it is recorded in the relocated comment and the commit message |
| `--wfail` warning-count comparison is confounded by build caching | M | M | Phase 1 and Phase 8 both take the count from a build that actually re-elaborates the touched modules; the README already warns that an incremental count is an undercount and must never be used as a census |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2 | 1 |
| 3 | 3 | 2 |
| 4 | 4 | 3 |
| 5 | 5, 6, 7 | 4 |
| 6 | 8 | 5, 6, 7 |

Phases within the same wave can execute in parallel. Wave 5's three phases touch disjoint files
(`scripts/axiom-census-baseline.txt`; `Cslib/Logics/Modal/Tableau/README.md` + `specs/ROADMAP.md`;
`specs/566_boneyard_creation_eligible_moves/`) and are genuinely parallel-safe.

---

### Phase 1: Re-verify the Refutation and Capture Pre-Change Baselines [COMPLETED]

**Goal**: Confirm the refutation still holds against the live tree, and record every "before"
figure the definition of done compares against. Nothing is edited in this phase.

**Phase Record (live-measured 2026-08-07)**:
- Probe `lake env lean specs/582_.../scratch_refute_ancestor_redirect.lean`: exit 0, zero
  diagnostics.
- `#print axioms` on `sat_before`/`not_sat_after`/`statement_is_false`: `[propext, Quot.sound]`
  (`not_sat_after` alone shows `[propext]`), no `sorryAx` on any of the three.
- `lake build --wfail --iofail` on the touched modules
  (`Cslib.Logics.Modal.Tableau.S4.Driver`, `Cslib.Logics.Modal.Tableau.FrameSoundness`, full
  re-elaboration via `touch`): exactly **one** `declaration uses 'sorry'` warning —
  `FrameSoundness.lean:1227:6`.
- `lake test`: exit 0.
- Two-grep code-position sorry census (`^\s*sorry(...)?$` + `(:=|\bby)\s+sorry(...)?$`):
  repo-wide **28**; `Modal/Tableau/` **1** (`FrameSoundness.lean:1251`).
- `wc -l scripts/axiom-census-baseline.txt`: **58** total lines, **15** header/comment lines,
  **43** data rows (the file is an exact-set list, so every data row is sorryAx-tainted); row 40
  is `Cslib.Logic.Modal.Tableau.branchSatisfiableIn_s4FC_ancestor_redirect`.
  `bash scripts/check-axiom-census.sh` (no flag): exit 0, "43 (baseline: 43)".
- Consumer audit `grep -rn 'branchSatisfiableIn_s4FC_ancestor_redirect' --include='*.lean' Cslib/
  CslibTests/`: 3 hits, all in `FrameSoundness.lean` — the docstring-quoted grep command itself
  (1206), the declaration line (1227), and one docstring mention (5294, "...
  `branchSatisfiableIn_s4FC_ancestor_redirect` above; ..."). **0 use sites.**
- All figures match the plan's Scope Hypothesis exactly: 28 / 1 / 58 total-rows / 43
  sorryAx-tainted / 3-hit-0-use-site.

**Tasks**:
- [ ] Re-run the probe: `lake env lean specs/582_s4_ancestor_redirect_soundness_obstruction/scratch_refute_ancestor_redirect.lean` — expect exit 0, zero diagnostics.
- [ ] Confirm the axiom profile via `#print axioms` on `RefuteAncestorRedirect.statement_is_false` — expect `[propext, Quot.sound]`, and specifically **no `sorryAx`**.
- [ ] Capture the pre-change `lake build --wfail --iofail` `declaration uses 'sorry'` warning set (names and count), from a build that re-elaborates the touched modules — not an incremental cached count.
- [ ] Capture `lake test` exit status.
- [ ] Capture the two-grep code-position sorry census, repo-wide and filtered to `Modal/Tableau/`.
- [ ] Capture `wc -l scripts/axiom-census-baseline.txt` and the count of `sorryAx`-tainted rows.
- [ ] Re-run the consumer audit: `grep -rn 'branchSatisfiableIn_s4FC_ancestor_redirect' --include='*.lean' Cslib/ CslibTests/` — confirm zero *use* sites.
- [ ] Write all captured figures into the phase record; every later phase compares against these, not against the numbers written in this plan.

**Timing**: 45 minutes (dominated by the build).

**Depends on**: none

**Verification Tier**: full

**Scope Hypothesis**: The report's measured baselines are hypotheses: repo-wide code-position
sorries **28**; `Modal/Tableau/` **1** (at `FrameSoundness.lean:1251`); census file **58** rows
with **43** `sorryAx`-tainted, exactly **1** of them in Modal/Tableau; consumer audit **3** `.lean`
hits, **0** of them use sites. Confirm each by running the command in the corresponding task
bullet above. **If the probe does not compile, or if any consumer audit finds a use site, STOP** —
the route decision is invalidated and the task returns to research rather than proceeding.

**Files to modify**: none (measurement only).

**Verification**:
- Probe exits 0 with the expected axiom profile and no `sorryAx`.
- Every baseline figure is recorded with the exact command that produced it.

---

### Phase 2: Promote the Countermodel into CslibTests/ [COMPLETED]

**Phase Record**: Created `CslibTests/AncestorRedirectRefutation.lean` (namespace
`RefuteAncestorRedirect`, per plan) adapted to the `module` + paired `import`/`public meta
import` idiom from `S4LoopGuardRegression.lean`, with a full module docstring covering the
refuted statement, the countermodel data, and the refutation mechanism. Registered
`public import CslibTests.AncestorRedirectRefutation` in `CslibTests.lean` before
`CslibTests.Bisimulation` (alphabetical). `lake build CslibTests` succeeds; `lake test` exit 0;
`lean_verify` on `RefuteAncestorRedirect.statement_is_false` reports `["propext","Quot.sound"]`,
no warnings, no `sorryAx`. Two-grep sorry census over `CslibTests/` unchanged at 0.
`git status --short` confirms exactly the two expected paths touched
(`CslibTests.lean`, `CslibTests/AncestorRedirectRefutation.lean`).

**Goal**: Turn the scratch probe into a durable, executable regression witness so any future
attempt to re-add the lemma fails the test suite.

**Tasks**:
- [ ] Create `CslibTests/AncestorRedirectRefutation.lean` from the scratch probe's content.
- [ ] Adapt to the `CslibTests/` module-system idiom, using `CslibTests/S4LoopGuardRegression.lean` as the template: Apache-2.0 copyright header, `module` declaration, and paired `import X` / `public meta import X` for `Cslib.Logics.Modal.Tableau.FrameSoundness` (the scratch file's bare `import` will not do).
- [ ] Write a module docstring stating: the refuted statement, the countermodel data (`acc = {0→1, 2→1}`, `b = [T(□p)@0, F(p)@2]`, redirect `1→2`), why it refutes (transitivity forces `m.r (f 0) (f 2)`, `T(□p)@0` then forces `p` at `f 2`, contradicting `F(p)@2`), and that the corresponding lemma was deleted for this reason.
- [ ] Keep the `RefuteAncestorRedirect` namespace and the three theorems `sat_before`, `not_sat_after`, `statement_is_false`.
- [ ] Register the module: add `public import CslibTests.AncestorRedirectRefutation` to `CslibTests.lean`, in the existing alphabetical position (before `CslibTests.Bisimulation`).
- [ ] Confirm the new module is `sorry`-free and adds no axioms beyond `[propext, Quot.sound]`.

**Timing**: 1 hour.

**Depends on**: 1

**Verification Tier**: interface

**Commit Mode**: per-substep

**Scope Hypothesis**: Two files touched — one new (`CslibTests/AncestorRedirectRefutation.lean`)
and one edited (`CslibTests.lean`). Confirm by `git status --short` showing exactly those two
paths before committing. The claim that `S4LoopGuardRegression.lean` is the right idiom template
is confirmed by reading its first 15 lines, not assumed.

**Files to modify**:
- `CslibTests/AncestorRedirectRefutation.lean` - new; adapted refutation with full docstring
- `CslibTests.lean` - add one `public import` line

**Verification**:
- `lake build CslibTests` succeeds.
- `lake test` exit 0.
- `#print axioms RefuteAncestorRedirect.statement_is_false` shows `[propext, Quot.sound]`, no `sorryAx`.
- The two-grep sorry census over `CslibTests/` is unchanged (the new file adds none).

---

### Phase 3: Relocate the Upgraded Obstruction Record [COMPLETED]

**Phase Record**: Rewrote the "three prior soundness routes ... died" sentence in the
`accPinnedBy` module comment (`FrameSoundness.lean:~5292`) to no longer name
`branchSatisfiableIn_s4FC_ancestor_redirect` or say "above". Added a new `### The standalone
redirect lemma was refuted, not merely left unproven` subsection carrying the three surviving
facts from report §6 (statement is false + 3-line countermodel; why it is false — ancestor
transitive-closure payload; Massacci citation dead end + category error re π-completeness),
citing the Phase 2 regression witness by path
(`CslibTests/AncestorRedirectRefutation.lean`), and recording the route decision inline
(deleted because false; discharged sorry-free by `branchSatisfiableIn_s4FC_addEdge_of_blocked`
and the `S4RedirectSoundInv` family). `git diff --stat` shows a single hunk in
`FrameSoundness.lean`, comment-only; delimiters balanced (`/-! ... -/` intact). Fixed one
line-length linter warning surfaced by the edit (5299 → wrapped). `lake build
Cslib.Logics.Modal.Tableau.FrameSoundness` succeeds with only the pre-existing expected
warnings (the `:1227` sorry, an unrelated pre-existing `S4/Driver.lean` warning) — no new
warnings.

**Goal**: Move the obstruction record — upgraded from "blocked" to "refuted" — into the
`accPinnedBy` module comment, which already names this lemma as one of three dead routes. This
turns a scattered record into one coherent narrative: why the naive statement fails, and what
invariant repairs it.

**Tasks**:
- [ ] Locate the `accPinnedBy` module comment by `grep -n 'Pinned-Witness Truth Lemma'` (do not trust the line number `5280`).
- [ ] Rewrite the sentence that currently reads `three prior soundness routes ... died precisely because ... (\`branchSatisfiableIn_s4FC_ancestor_redirect\` above; ancestor-only blocking; the origin-edge revision)` so it no longer refers to a declaration that Phase 4 removes, and no longer says "above".
- [ ] Add the three surviving facts from the research report §6: (1) the statement is false, with the three-line countermodel; (2) why it is false — transitive closure transmits box-positive payload from every `acc`-ancestor of `src`, and a hypothesis set naming only `src` cannot see them; (3) the Massacci citation is a dead end *and* a category error here, since Thm 8.1 concerns π-completed (saturated) branches, which is exactly the hypothesis the deleted lemma dropped.
- [ ] Cite the Phase 2 regression witness by path so a reader can run the refutation.
- [ ] Record the route decision inline: deleted because the statement is false; the soundness obligation it served is discharged sorry-free by `branchSatisfiableIn_s4FC_addEdge_of_blocked` and the `S4RedirectSoundInv` family.
- [ ] Confirm every changed hunk lies inside the `/-! ... -/` doc-comment region and no code line is touched.

**Timing**: 45 minutes.

**Depends on**: 2

**Verification Tier**: prose

**Scope Hypothesis**: Exactly one file, one contiguous comment region. Confirm by
`git diff --stat` showing only `Cslib/Logics/Modal/Tableau/FrameSoundness.lean`, and by reading
the full diff to check every hunk is inside the doc comment. **Blind-spot note for the `prose`
tier**: the risk here is an edit that crosses out of the comment boundary or unbalances the
`/-!` … `-/` delimiters — read the diff for both, and close the phase with a build of
`Cslib.Logics.Modal.Tableau.FrameSoundness` to catch a broken delimiter.

**Files to modify**:
- `Cslib/Logics/Modal/Tableau/FrameSoundness.lean` - `accPinnedBy` module comment only

**Verification**:
- Diff read-through confirms comment-only changes with balanced delimiters.
- `lake build Cslib.Logics.Modal.Tableau.FrameSoundness` succeeds.
- No declaration count change in the file.

---

### Phase 4: Delete the Section Comment, Docstring, and Lemma [COMPLETED]

**Phase Record**: Re-derived boundaries by content (unchanged from Phase 1's hypothesis:
section comment at `:1159`, `sorry` at `:1251`, next section at `:1253`). Deleted lines
1159-1252 inclusive, leaving exactly one blank line between the preceding declaration and
`/-! ### Propagation-Adequacy Invariant (S4-Keyed)`. `lake build
Cslib.Logics.Modal.Tableau.FrameSoundness` succeeds with zero sorry warnings for this file.
Modal/Tableau two-grep sorry census = **0**; repo-wide two-grep census = **27** (one fewer than
Phase 1's 28). `lake test` exit 0.

**Deviation/tension found and resolved**: the plan's Phase 4 verification requires
`grep -rn 'branchSatisfiableIn_s4FC_ancestor_redirect' --include='*.lean' Cslib/ CslibTests/` to
return **0 hits**, but Phase 2's and Phase 3's own prose (already committed) named the deleted
identifier literally for documentation clarity, producing 2 hits (both comment prose, not code).
Resolved by rewording both mentions (`CslibTests/AncestorRedirectRefutation.lean`'s module
docstring; `FrameSoundness.lean`'s `accPinnedBy` comment) to describe the deleted lemma
descriptively ("the deleted standalone, driver-independent ancestor-redirect decision-gate
lemma") without reproducing the exact identifier substring, preserving full semantic content.
Re-verified: grep now returns 0 hits; both files rebuild clean; `lake test` exit 0.
`git status --short` confirms exactly the two expected Lean files touched by this phase's
deletion + rewording (`Cslib/Logics/Modal/Tableau/FrameSoundness.lean`,
`CslibTests/AncestorRedirectRefutation.lean`).

**Goal**: Remove the false declaration and its `sorry`, bringing `FrameSoundness.lean` to zero
sorries.

**Tasks**:
- [ ] Re-locate all three boundaries by content, not by the line numbers recorded here: section-comment open (`grep -n '### Ancestor-Redirect Decision Gate'`), the `sorry` (`grep -n '^\s*sorry\s*$'`), and the start of the next section (`grep -n '### Propagation-Adequacy Invariant'`).
- [ ] Delete the contiguous block: the `/-! ### Ancestor-Redirect Decision Gate ... -/` section comment, the lemma docstring, the `lemma branchSatisfiableIn_s4FC_ancestor_redirect` declaration, its proof body, and the trailing `sorry`.
- [ ] Leave the preceding declaration and the following `/-! ### Propagation-Adequacy Invariant (S4-Keyed)` section comment intact, separated by exactly one blank line.
- [ ] Confirm no other declaration was touched: the diff must contain deletions in this one region and nothing else.
- [ ] Confirm the two-grep code-position sorry census over `Cslib/Logics/Modal/Tableau/` now returns **0**, and over `Cslib/` returns one fewer than the Phase 1 baseline.

**Timing**: 45 minutes.

**Depends on**: 3

**Verification Tier**: full

**Scope Hypothesis**: The deletion block is `FrameSoundness.lean:1159-1252` inclusive (section
comment at `:1159`, declaration at `:1227`, `sorry` at `:1251`) — a hypothesis measured before
Phase 3's comment edit and therefore **already stale by the time this phase runs**. Re-derive all
three boundaries with the greps above and delete by content. Confirm the block is contiguous and
contains exactly one declaration before deleting.

**Files to modify**:
- `Cslib/Logics/Modal/Tableau/FrameSoundness.lean` - delete the section comment, docstring, and lemma

**Verification**:
- `lake build` succeeds (full, not incremental for this module).
- Modal/Tableau code-position sorry census = **0**.
- `grep -rn 'branchSatisfiableIn_s4FC_ancestor_redirect' --include='*.lean' Cslib/ CslibTests/` returns 0 hits.
- `lake test` exit 0.
- `git diff` for this phase touches exactly one file, deletions only.

---

### Phase 5: Regenerate the Axiom Census Baseline [COMPLETED]

**Phase Record**: `bash scripts/check-axiom-census.sh --update` → "Baseline updated: 42 tainted
declaration(s)." Confirmed `Cslib.Logic.Modal.Tableau.branchSatisfiableIn_s4FC_ancestor_redirect`
row is gone. File total: 58 → 57 lines; sorryAx-tainted data rows: 43 → 42 — exactly one row
removed, matching the Phase 1 baseline and the Scope Hypothesis exactly. `bash
scripts/check-axiom-census.sh` (no flag): exit 0, "42 (baseline: 42)".

**Incidental non-compared metadata change, noted for the record**: `git diff` also shows the
`reason` (column 3) for the already-tainted, unrelated row
`Cslib.Logic.PL.openBranch_countermodel` changed from `Cslib.Logic.PL.truthLemma` to `direct`.
The baseline file's own header states columns 2/3 are "D1 debt-ledger metadata ... NOT compared:
a changed reason for an already-tainted declaration never fails this check, only a name entering
or leaving the tainted set does." This is expected, benign regeneration drift, not scope creep
from this task's deletion — the tainted *name set* changed by exactly one row (the target), as
required.

**Goal**: Bring the `sorryAx`-tainted exact-set ratchet in line with the deletion, by
regeneration rather than hand-editing.

**Tasks**:
- [ ] Run `bash scripts/check-axiom-census.sh --update`.
- [ ] Confirm the row `Cslib.Logic.Modal.Tableau.branchSatisfiableIn_s4FC_ancestor_redirect` is gone.
- [ ] Confirm the file's total row count and `sorryAx`-tainted count each dropped by exactly 1 from the Phase 1 baseline, and that no other row changed.
- [ ] Run `bash scripts/check-axiom-census.sh` (no flag) and confirm it exits 0 against the new baseline.

**Timing**: 30 minutes.

**Depends on**: 4

**Verification Tier**: full

**Scope Hypothesis**: The census file goes **58 → 57** rows and the `sorryAx`-tainted subset goes
**43 → 42**, with exactly one row removed and none added or otherwise modified. Confirm by
`git diff scripts/axiom-census-baseline.txt` showing a single deleted line, and by `wc -l`
against the Phase 1 figure. **Do not hand-edit this file under any circumstances** — the header
states this and the ratchet compares column 1 as an exact set.

**Files to modify**:
- `scripts/axiom-census-baseline.txt` - regenerated (one row removed)

**Verification**:
- `git diff` shows exactly one deleted line in the baseline file and no other change.
- `bash scripts/check-axiom-census.sh` exits 0.

---

### Phase 6: Reconcile the Falsified Prose Records [COMPLETED]

**Phase Record**: Repo-wide sweep for `ancestor_redirect` (excluding `.git/` and all of
`specs/**`, per the same not-a-live-ratchet principle the plan applies to `TODO.md`, since
other tasks' own historical reports/plans/summaries are frozen records of decisions made at the
time) found exactly the plan's predicted **two** live-tree files:
`Cslib/Logics/Modal/Tableau/README.md` and `specs/ROADMAP.md` — confirming the plan's
Scope Hypothesis (no fourth site found).

- **README.md** "Sorry census": `**1**` → `**0**`; dropped the retained/immovable clause and
  the lemma's name entirely (per the task's explicit "drop ... the naming" instruction — an
  earlier draft of this edit still named it and was corrected before commit); re-measured
  (not hand-decremented) the repo-wide figure `**28**` → `**27**`. Also re-measured the
  adjacent, same-site "CI-pipeline grep" raw count (`grep -rn "\bsorry\b" Cslib/`), which had
  independently drifted `158` → `187` since this section's last capture — corrected per the
  task 567 house standard (live-re-measure, don't copy stale numbers forward), since it sits in
  the same paragraph already being edited.
- **ROADMAP.md** section-A prose: re-measured per-subsystem breakdown (Bimodal 23,
  Propositional 4, Modal **0**, confirmed by direct census over each subsystem directory), date
  stamp updated to the live measurement date, and the "Propositional 4 and Modal 1 are bare"
  sentence revised to name only Propositional 4 as the `--wfail --iofail` red-cause.
- **ROADMAP.md** Remaining table: the S4 keyed loop-check guard soundness row revised to
  "DISCHARGED BY REFUTATION", Notes cell repointed from the deleted in-file docstring to the
  relocated `accPinnedBy` record and the `CslibTests/` regression witness.
- `specs/TODO.md` left untouched (explicit non-goal; historical measured-state prose generated
  from `state.json`).
- Final re-sweep confirms zero remaining live-tree prose asserting a Modal/Tableau sorry or
  naming the deleted lemma as extant; `git status --short` confirms exactly the two expected
  files touched.

**Goal**: Correct every prose/numeric record the deletion falsifies, with all figures
live-re-measured per the house standard established by task 567.

**Tasks**:
- [ ] Re-run the repo-wide sweep `grep -rn 'ancestor_redirect' --include='*.md' --include='*.sh' --include='*.txt' --include='*.lean' .` (excluding `.git/` and this task's own directory) and enumerate the live touch points — do not work from this plan's or the report's enumeration.
- [ ] `Cslib/Logics/Modal/Tableau/README.md`, "Sorry census" section: change "**1** in this subsystem" to **0**, drop the "the retained, user-decided, immovable obstruction" clause and the naming of the deleted lemma, and re-measure the repo-wide figure (currently stated as **28**) rather than decrementing it by hand.
- [ ] `specs/ROADMAP.md` Remaining/section-A prose: re-measure and update the repo-wide code-position sorry count and the per-subsystem breakdown (Modal goes to 0), and revise the sentence asserting that "the Propositional 4 and Modal 1 are **bare**, and are the stated reason `lake build --wfail --iofail` is red" so it no longer counts a Modal sorry.
- [ ] `specs/ROADMAP.md` Remaining table: revise the `**S4 keyed loop-check guard soundness** (1 sorry, the only Modal one)` row — the item is discharged by refutation, and its Notes cell's appeal to the now-deleted in-file docstring must point at the relocated record instead.
- [ ] Leave `specs/TODO.md` alone: its `sorries 28/28` and `sorryAx-tainted 43/43` figures sit inside other tasks' historical measured-state descriptions, generated from `state.json`, and are not live ratchets.
- [ ] Confirm no remaining live-tree prose asserts a Modal/Tableau sorry or names the deleted lemma as extant.

**Timing**: 1 hour.

**Depends on**: 4

**Verification Tier**: prose

**Scope Hypothesis**: Two files (`Cslib/Logics/Modal/Tableau/README.md`, `specs/ROADMAP.md`) and
**three** distinct edit sites — the README sorry census, the ROADMAP section-A prose (reported at
`:146`), and the ROADMAP Remaining-table row (`:156`). The report's §5 table lists only the first
two; the third was found during planning and is the reason this phase re-runs the sweep instead
of trusting any enumeration. If the sweep finds a fourth live site, handle it here and record the
addition.

**Files to modify**:
- `Cslib/Logics/Modal/Tableau/README.md` - sorry census section
- `specs/ROADMAP.md` - section-A prose and the Remaining-table row

**Verification**:
- Every number written is accompanied by the command that measured it.
- The repo-wide sweep returns no live-tree prose treating the lemma as extant.
- Diff read-through confirms markdown-only changes.

---

### Phase 7: Update the Boneyard Carve-Out Record [NOT STARTED]

**Goal**: Record that task 566's mandatory carve-out 1 no longer applies, as required by the
task's definition of done.

**Tasks**:
- [ ] Append a dated note to task 566's artifacts recording that carve-out 1 (`branchSatisfiableIn_s4FC_ancestor_redirect` is IMMOVABLE) has **lapsed**: the declaration was deleted, not moved.
- [ ] State the reason explicitly: the carve-out's rationale was entirely parasitic on the retained `sorry` — both of its mechanical confirmations (the census row, the docstring retention note) were consequences of the retention, and both vanished with it.
- [ ] Record that the Boneyard convention itself is **unaffected**: the Boneyard is for zero-consumer code with retained provenance value, and a false statement's provenance value is fully captured by the relocated countermodel and the `CslibTests/` regression witness.
- [ ] Confirm carve-out 2 (`keysOriginS4`, 22 code consumers) is untouched and still stands.

**Timing**: 30 minutes.

**Depends on**: 4

**Verification Tier**: prose

**Scope Hypothesis**: Edits confined to `specs/566_boneyard_creation_eligible_moves/`. The
specific artifact to annotate (report §3.1, the plan's carve-out bullets, or the summary's
carve-out table row) is chosen at implementation time after reading them; the requirement is that
a reader of task 566's record learns the carve-out lapsed, not that a particular file is edited.
Task-number citations are permitted here — this is the `specs/**` tree.

**Files to modify**:
- `specs/566_boneyard_creation_eligible_moves/` - carve-out record annotation (specific file chosen at implementation time)

**Verification**:
- The note is dated and states both the lapse and the reason.
- Carve-out 2 is explicitly confirmed intact.
- Diff read-through confirms markdown-only changes inside `specs/566_.../`.

---

### Phase 8: Full Gate and Route Record [NOT STARTED]

**Goal**: Demonstrate every clause of the definition of done against the Phase 1 baselines, and
record the route in the commit.

**Tasks**:
- [ ] Run `lake build --wfail --iofail` from a state that re-elaborates the touched modules; compare the `declaration uses 'sorry'` warning set against the Phase 1 capture — require **strictly fewer** warnings and **no new** warnings of any kind.
- [ ] Run `lake test` — require exit 0.
- [ ] Run `bash scripts/check-axiom-census.sh` — require exit 0.
- [ ] Run the remaining honesty-gate scripts that were green at baseline (`check-sorry-suppressions.sh`, `check-shake-residue.sh`, `check-lint-suppressions.sh`, `check-boneyard-quarantine.sh`) and require no regression against Phase 1.
- [ ] Confirm `FrameSoundness.lean` contains no `sorry` in code position.
- [ ] Review the cumulative `git diff` and confirm **no other proof, definition, or theorem statement was altered** — the only Lean-code change outside `CslibTests/` is a deletion.
- [ ] Re-run the repo-wide `ancestor_redirect` sweep as a final gate.
- [ ] Compose the commit message recording route (c) and its one-line justification: the lemma was deleted because its statement is false — a machine-checked countermodel ships as a regression test — and the soundness obligation it served is discharged sorry-free by `branchSatisfiableIn_s4FC_addEdge_of_blocked` and the `S4RedirectSoundInv` family.

**Timing**: 45 minutes.

**Depends on**: 5, 6, 7

**Verification Tier**: full

**Scope Hypothesis**: The cumulative change set is expected to be: 1 new file
(`CslibTests/AncestorRedirectRefutation.lean`), and edits to `CslibTests.lean`,
`Cslib/Logics/Modal/Tableau/FrameSoundness.lean`,
`Cslib/Logics/Modal/Tableau/README.md`, `scripts/axiom-census-baseline.txt`, `specs/ROADMAP.md`,
plus this task's and task 566's `specs/` artifacts. Confirm by `git status --short` and reject any
path outside that set.

**Files to modify**: none (verification and commit only).

**Verification**:
- `lake build --wfail --iofail`: strictly fewer sorry warnings, no new warnings.
- `lake test`: exit 0.
- All honesty-gate scripts at or better than the Phase 1 baseline.
- Diff review confirms no unrelated statement changed.

---

## Testing & Validation

- [ ] Refutation probe compiles clean with axioms `[propext, Quot.sound]` and no `sorryAx` (Phase 1).
- [ ] `CslibTests/AncestorRedirectRefutation.lean` builds and its theorems carry no `sorryAx` (Phase 2).
- [ ] `lake test` exit 0 after the test-suite addition (Phase 2) and after the deletion (Phase 4).
- [ ] Modal/Tableau code-position sorry census = **0** (Phase 4).
- [ ] `grep -rn 'branchSatisfiableIn_s4FC_ancestor_redirect' --include='*.lean' Cslib/ CslibTests/` = 0 hits (Phase 4).
- [ ] `bash scripts/check-axiom-census.sh` exit 0 against the regenerated baseline (Phase 5).
- [ ] `lake build --wfail --iofail` emits strictly fewer sorry warnings than the Phase 1 baseline, with no new warnings (Phase 8).
- [ ] Cumulative diff alters no other proof, definition, or theorem statement (Phase 8).

## Artifacts & Outputs

- `specs/582_s4_ancestor_redirect_soundness_obstruction/plans/01_delete-refuted-ancestor-redirect-lemma.md` (this file)
- `CslibTests/AncestorRedirectRefutation.lean` (new — executable regression witness)
- `CslibTests.lean` (one import registration)
- `Cslib/Logics/Modal/Tableau/FrameSoundness.lean` (relocated obstruction record; lemma deleted)
- `Cslib/Logics/Modal/Tableau/README.md` (sorry census corrected)
- `scripts/axiom-census-baseline.txt` (regenerated, one row fewer)
- `specs/ROADMAP.md` (sorry counts and the S4 guard row reconciled)
- `specs/566_boneyard_creation_eligible_moves/` (carve-out lapse recorded)
- `specs/582_s4_ancestor_redirect_soundness_obstruction/summaries/01_*-summary.md` (produced at implementation completion)

## Rollback/Contingency

Every phase is a separate commit, so rollback is per-phase `git revert` in reverse dependency
order. No phase depends on a schema migration or an irreversible operation.

- **If Phase 1's probe fails to compile**: STOP. The refutation is the sole basis for route (c);
  a red probe invalidates the route decision. Mark the task `[BLOCKED]` and return to research
  rather than deleting on the strength of a stale finding.
- **If Phase 4's deletion breaks the build**: the consumer audit was wrong. Revert the deletion,
  re-run the audit to find the real use site, and re-open the route decision — a lemma with a
  consumer is not a route (c) candidate.
- **If Phase 5's census regeneration removes more than one row**: revert the baseline file and
  investigate. More than one row means the deletion had reach beyond the target declaration,
  which contradicts the zero-consumer finding.
- **Full revert**: reverting Phases 2 through 7 restores the lemma, its `sorry`, the census row,
  and all prose to the pre-task state. Nothing outside this task's touch set is affected, so a
  full revert is clean.
