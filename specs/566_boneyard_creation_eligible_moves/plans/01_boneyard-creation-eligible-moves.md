# Implementation Plan: Create `Boneyard/` and Move Re-Verified Zero-Consumer Declarations

- **Task**: 566 - Create Boneyard/ with its convention and move only re-verified zero-consumer declarations
- **Status**: [IMPLEMENTING]
- **Effort**: 6 hours
- **Dependencies**: 553, 563, 564, 586 (all landed)
- **Research Inputs**: `specs/566_boneyard_creation_eligible_moves/reports/01_boneyard-convention-and-consumer-reaudit.md`
- **Artifacts**: plans/01_boneyard-creation-eligible-moves.md (this file)
- **Standards**: plan-format.md; status-markers.md; artifact-management.md; tasks.md
- **Type**: cslib
- **Lean Intent**: false

## Overview

Create a root-level `Boneyard/` quarantine directory with a documented convention, then move
exactly three zero-consumer declaration units (~157 lines) out of
`Cslib/Logics/Modal/Tableau/LoopChecking.lean` into it. The move is deliberately conservative:
nothing is deleted, both mandatory carve-outs are honoured, and every declaration whose
zero-consumer status could not be re-verified by name in this tree stays put. The work is not a
cut-and-paste — creating `Boneyard/` falsifies an in-file assertion in `LoopChecking.lean`, three
surviving prose references to the moved lemmas would otherwise dangle, and the `keysRootEmpty`
section comment carries an unrelated `keysOriginS4` retraction that must remain in live code.
Definition of done: `Boneyard/` exists, is documented, is provably outside the build, the three
units live in it under the upstream file convention, all live prose is true again, and the full
CI gate set is unchanged from baseline.

### Research Integration

The plan is built directly on `reports/01_boneyard-convention-and-consumer-reaudit.md`. Findings
carried into phases:

- **Eligible set is three units, not four** (§2.1): `blockedRedirect_diaNeg_mem_of_diaOrigin`,
  `blockedRedirect_boxctx_mem_of_boxOrigin`, and the `keysRootEmpty` / `keysRootEmpty_entry`
  pair. Total ~157 lines.
- **The `outDegEq` candidate is MOOT** (§2.2): both S4 preservation lemmas were deleted by an
  earlier task in this programme and return zero grep hits by full name. A bare `grep outDegEq`
  still returns 8 hits, but every one of them is the *unrelated, heavily consumed*
  `ModalPotentialInv.outDegEq` field (declared in `FmpMeasure.lean`, destructured as
  `hpot.outDegEq` in `CompletenessLoop.lean`) plus the generic
  `modalStepBranch*_preserves_outDegEq*` family. This plan contains **no phase that touches
  `outDegEq`**, by design.
- **Both carve-outs hold** (§3): `branchSatisfiableIn_s4FC_ancestor_redirect` is IMMOVABLE (it
  carries the one retained Modal/Tableau `sorry`, an explicit user decision, and is the sole
  Modal/Tableau row of `scripts/axiom-census-baseline.txt`); `keysOriginS4` is pervasively
  consumed and not eligible.
- **No build/lint/census config needs touching** (§4.3): all twelve CI-relevant mechanisms are
  `lean_lib`-scoped, import-reachability-scoped, or hardcoded to a `Cslib` scan root. **Root-level
  placement is what makes this free and is therefore load-bearing** — placing the Boneyard under
  `Cslib/` would immediately break `mk_all --check`.
- **Two repo-wide `.lean` scanners are exceptions** (§4.2b): `.github/workflows/todo-issue.yml`
  and `scripts/bench/size/run`. Neither blocks this task (the eligible regions carry zero
  `TODO:`/`FIXME:` markers, verified), but both are recorded as standing constraints.
- **Implementation hazards** (§5): the falsified no-`Boneyard/` assertion in `LoopChecking.lean`'s
  measured-figures block, three dangling prose references, and the `keysOriginS4` retraction
  embedded in the `keysRootEmpty` section comment.

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

No ROADMAP.md consultation was requested for this dispatch.

## Goals & Non-Goals

**Goals**:

- Create `Boneyard/` at the **repository root** with a documented convention ported from the
  upstream `BimodalLogic/FormalSystem/Boneyard/README.md` model.
- Move (never delete) exactly three re-verified zero-consumer declaration units out of
  `LoopChecking.lean` into `Boneyard/ModalTableauS4Keyed/`.
- Keep `Boneyard/` fully outside the build, the linters, and every census — and prove it
  empirically rather than assuming it.
- Leave every surviving prose reference in live code true: repair the falsified no-`Boneyard/`
  assertion and redirect the three dangling lemma references.
- Keep the `keysOriginS4` retraction in live code, where it belongs.
- Add a cheap defensive self-test so a future regression of the quarantine is caught rather than
  silent.

**Non-Goals**:

- Moving `branchSatisfiableIn_s4FC_ancestor_redirect` (carve-out 1, IMMOVABLE).
- Moving `keysOriginS4` or any of its `_entry` / `_mono_branch` / `_mono_acc` relatives
  (carve-out 2).
- Moving `modalS4Saturated`, the `hintikkaS4_*` bridge set, `hasEdge_accWithReds_iff`,
  `reflTransGen_accWithReds_first_red`, `blockedRedirect_unwrapped_{boxPos,diaNeg}_mem`, or the
  `Reds` / `accWithReds` packaging — these are route-independent preserved assets to be *placed*
  by the abstraction decision, not quarantined.
- Touching anything named `outDegEq` (the candidate is moot; the surviving hits are a different
  declaration).
- Editing `lakefile.toml`, `.gitignore`, any file under `.github/workflows/`, or any baseline file.
- Deleting any declaration, anywhere.
- Correcting the `hintikkaS4_*` "8 vs 10" figure — the 8 is a semantic set, the 10 is a prefix
  grep; both are already reconciled in-file and neither is in scope.

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Implementer greps bare `outDegEq`, concludes the candidate is live, and moves consumed code | H | M | Non-Goals names the trap explicitly; no phase mentions `outDegEq`; Phase 6 gate would catch the resulting build break |
| A consumer was missed and the build breaks or job count shifts | H | L | Phase 2 and Phase 3 each re-run the by-name consumer grep *before* excising, and gate on `lake build Cslib` green; a job-count change from 3313 is treated as a signal to investigate, not as noise |
| Moving the `keysRootEmpty` section comment wholesale carries the `keysOriginS4` retraction out of live code | H | M | Phase 3 splits the comment explicitly; the retraction paragraph is named as must-stay and is re-grepped in live code after the edit |
| `Boneyard/` accidentally enters the build (a `lean_lib` entry, a `Cslib/`-relative placement, or an `import Boneyard.*`) | H | L | Root-level placement is mandated; three standing invariants are recorded in the README; Phase 5 adds a mechanical self-test; Phase 6 gates on unchanged job count |
| Archived `TODO:` markers get filed as GitHub issues by the repo-wide `todo-issue.yml` | M | L | Zero markers exist in the eligible regions (verified); README records the no-live-marker rule; Phase 5's self-test asserts it mechanically |
| A future second Boneyard escapes an exclusion filter silently | M | M | Phase 5 mirrors upstream's `B0` self-test: assert the *expected number* of Boneyard directories, not merely that filtering ran |
| Stale line numbers in the research report drift before implementation | L | H | Every phase anchors on declaration names and section headings; line numbers appear only as navigational hints |

## Implementation Phases

**Dependency Analysis**:

| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2, 5 | 1 |
| 3 | 3 | 2 |
| 4 | 4 | 1, 2, 3 |
| 5 | 6 | 1, 2, 3, 4, 5 |

Phases within the same wave can execute in parallel. Phases 2 and 3 are serialized against each
other because both edit `LoopChecking.lean`; Phase 5 touches only `scripts/` and is disjoint from
Phase 2's territory.

---

### Phase 1: Create the quarantine skeleton and prove the exclusion empirically [COMPLETED]

**Goal**: `Boneyard/` exists at the repository root with its convention documented, and the
"no build/lint/census config needs changing" claim is confirmed by running the full gate set
*before* any Lean code is at stake.

**Tasks**:

- [x] Record the pre-change baseline by running the gate set (see Testing & Validation) and
      capturing each figure. This is the reference every later phase compares against.
- [x] Create `Boneyard/README.md` at the **repository root** (not under `Cslib/`), covering:
  - [x] The archival criterion: a file belongs here when it is unreachable from every Lake target
        root and is not intended to become reachable. Unreachability alone is not sufficient —
        merely not-yet-wired code belongs elsewhere.
  - [x] The build policy, stated as *liveness equals reachability*: there is no Lake target
        covering `Boneyard/`; import lines inside archived files are historical text, not build
        edges; stale imports in never-built code are cosmetic and need not be repaired.
  - [x] The `#exit` guard convention and the `ARCHIVED (Boneyard)` header-docstring convention
        (header names the moved declarations and ends `Do not import from live code.`).
  - [x] A Directory Inventory table with columns: subdirectory / files / lines / archived-from /
        why-archived.
  - [x] "Sorry counts here are not bugs" — archived sorries are dead ends, not open obligations.
  - [x] "Do not grep this directory when auditing live identifier usage."
  - [x] The **three standing invariants**, each of which would individually undo the quarantine:
        (1) never add `[[lean_lib]] name = "Boneyard"` to `lakefile.toml`; (2) never
        `import Boneyard.*` from anything reachable from `Cslib.lean` — because `srcDir` defaults
        to the repo root the module name *does* resolve, and this is the one live vector; (3)
        never pass `--scope Boneyard` to `check-sorry-suppressions.sh`.
  - [x] The **two repo-wide scanner constraints**: `.github/workflows/todo-issue.yml` is
        diff-driven with no `paths-ignore` filter and would file GitHub issues for `TODO:`/`FIXME:`
        markers in archived code — therefore archived code MUST NOT carry live markers (neutralize
        to `ARCHIVED-TODO:` if a note is genuinely needed); and `scripts/bench/size/run` globs every
        non-dotted top-level directory and would count archived lines as live (manual tool, not
        CI-wired). Record that editing `todo-issue.yml` was considered and rejected because every
        file under `.github/workflows/` is shared with the upstream remote and each edit adds a
        recurring sync-conflict hunk.
  - [x] A note that **root-level placement is load-bearing, not cosmetic**: under `Cslib/` the
        directory would be globbed by `mk_all --check`, which would demand the files be imported
        from `Cslib.lean` and thereby pull them into the build, the censuses, and lint-style.
- [x] Create `Boneyard/ModalTableauS4Keyed/README.md` explaining why these particular declarations
      were archived: all three are sorry-free, proven, and true; eligibility rests purely on
      re-verified zero-consumer status, not on being broken; and moving-never-deleting is the
      right disposition because the provenance is the point.
- [x] Confirm `lakefile.toml`, `.gitignore`, `.github/workflows/**`, `scripts/nolints-style.txt`,
      and all baseline files are untouched.
- [x] Re-run the full gate set and confirm every figure is identical to the baseline captured at
      the start of this phase.

**Timing**: 0.75 hours

**Depends on**: none

**Verification Tier**: full

**Commit Mode**: per-substep

**Scope Hypothesis**: This phase asserts that creating a root-level `Boneyard/` perturbs **zero**
CI mechanisms and requires **zero** config edits. Confirm at implementation time by running the
complete gate set both before and after directory creation and diffing the figures; any change to
build job count, any ratchet exit code, any census total, or any newly-flagged file falsifies the
hypothesis and must be investigated before proceeding to Phase 2.

**Files to modify**:

- `Boneyard/README.md` - new: convention, inventory table, three standing invariants, two
  scanner constraints, root-placement rationale
- `Boneyard/ModalTableauS4Keyed/README.md` - new: why these three units were archived

**Verification**:

- `Boneyard/` exists at the repository root; `find . -type d -name 'Boneyard' -not -path './.lake/*'`
  returns exactly one path, `./Boneyard`.
- `lake build Cslib` green at 3313 jobs (unchanged).
- All five ratchet scripts exit 0 with unchanged counts; `checkInitImports` exit 0.
- `git status` shows no modification to `lakefile.toml`, `.gitignore`, any workflow file, or any
  baseline file.

---

### Phase 2: Move the two `blockedRedirect_*_of_*Origin` lemmas [IN PROGRESS]

**Goal**: `blockedRedirect_boxctx_mem_of_boxOrigin` and `blockedRedirect_diaNeg_mem_of_diaOrigin`
live in `Boneyard/ModalTableauS4Keyed/RedirectOriginTransfer.lean` and no longer appear in
`LoopChecking.lean`; the one prose reference that stays behind is repaired.

**Tasks**:

- [x] **Re-verify zero-consumer status immediately before excising.** Word-boundary grep both full
      declaration names over `Cslib/`, `CslibTests/`, `scripts/`, and `Cslib.lean`; classify every
      hit as declaration site / code consumer / comment-only. Proceed only if code consumers is 0
      for both. Anchor on the full names — never on a substring.
- [x] Locate the contiguous block containing both lemmas by declaration name (navigational hint:
      `blockedRedirect_boxctx_mem_of_boxOrigin` near `LoopChecking.lean:1785`,
      `blockedRedirect_diaNeg_mem_of_diaOrigin` near `:1825`; treat both as stale).
- [x] Create `Boneyard/ModalTableauS4Keyed/RedirectOriginTransfer.lean` with, in order:
  - [x] the import block needed to state the lemmas (`import Cslib.Logics.Modal.Tableau.LoopChecking`
        or the source file's own imports) — recorded as historical text, not a build edge;
  - [x] an `ARCHIVED (Boneyard)` header docstring naming both moved declarations, noting they are
        sorry-free and were archived as zero-consumer, and ending `Do not import from live code.`;
  - [x] `#exit`;
  - [x] the excised code **verbatim**, including each lemma's own docstring. The docstring of
        `blockedRedirect_diaNeg_mem_of_diaOrigin` cites
        `blockedRedirect_boxctx_mem_of_boxOrigin` — that reference travels with the block and is
        self-resolving; do not rewrite it.
- [x] Confirm the moved region carries **no** live `TODO:`/`FIXME:`/`BUG:`/`HACK:`/`NOTE:`/
      `QUESTION:` markers (expected: none). Neutralize any that appear to `ARCHIVED-TODO:`.
- [x] Delete the block from `LoopChecking.lean`.
- [x] Repair the reference that **stays behind**: in the "The Witness Disjunct (Gate)" section
      (navigational hint: near `:1865`), the phrase *"case (b) (closed above, via
      `blockedRedirect_boxctx_mem_of_boxOrigin`)"* sits inside a narrative explaining a refutation.
      Do **not** delete the name — that would damage the explanation. Redirect it, e.g. "…now
      archived at `Boneyard/ModalTableauS4Keyed/RedirectOriginTransfer.lean`".
- [x] Update the Directory Inventory table in `Boneyard/README.md` with the new file's line count.
- [x] Note that this is an **excise-and-create**, not a whole-file rename: `git mv` does not apply
      here, because no existing file moves. Stage the deletion and the new file together.

**Timing**: 1.25 hours

**Depends on**: 1

**Verification Tier**: full

**Commit Mode**: atomic-batch

**Scope Hypothesis**: This phase asserts a contiguous ~101-line block containing exactly two
declarations, with exactly **one** surviving in-file reference that needs repair (the "Witness
Disjunct (Gate)" mention) and one that is self-resolving (the sibling docstring). Confirm at
implementation time by re-running the by-name grep before excising and re-running it after, and by
checking that post-move grep hits for both names inside `Cslib/` are zero. A third surviving
reference, or a non-contiguous block, falsifies the hypothesis and must be recorded before
proceeding.

**Files to modify**:

- `Boneyard/ModalTableauS4Keyed/RedirectOriginTransfer.lean` - new: header, `#exit`, both lemmas
  verbatim
- `Cslib/Logics/Modal/Tableau/LoopChecking.lean` - delete the two-lemma block; redirect the
  "Witness Disjunct (Gate)" reference
- `Boneyard/README.md` - inventory row

**Verification**:

- Word-boundary grep for both full names over `Cslib/` + `CslibTests/` + `scripts/` +
  `Cslib.lean` returns zero hits.
- `lake build Cslib` green at 3313 jobs. A job-count change is a signal worth investigating, not
  noise — the moved declarations were leaves, so no change is expected.
- Modal/Tableau sorry census still exactly 1.
- All five ratchets exit 0 with unchanged counts; `checkInitImports` exit 0.

---

### Phase 3: Move the `keysRootEmpty` pair, splitting the section comment [IN PROGRESS]

**Goal**: `keysRootEmpty` and `keysRootEmpty_entry` live in
`Boneyard/ModalTableauS4Keyed/KeysRootEmpty.lean`; the `keysOriginS4` retraction stays in
`LoopChecking.lean`; the two prose references that stay behind are repaired.

**Tasks**:

- [x] **Re-verify zero-consumer status immediately before excising.** Grep both names by word
      boundary; confirm the only code consumer of `keysRootEmpty` is `keysRootEmpty_entry` itself,
      which travels with it — hence the pair is eligible as a unit and only as a unit.
- [x] Locate the `### keysRootEmpty` section by heading (navigational hints: section comment
      `:2523`–`:2563`, `keysRootEmpty` `:2566`, `keysRootEmpty_entry` `:2572`; treat all as stale).
- [x] **Split the ~40-line section comment.** It is an audit record, not ordinary documentation,
      and it contains two separable things:
  - [x] The `keysRootEmpty`-specific paragraphs (the measured consumer audit for `keysRootEmpty`,
        its reproduction commands, and the "audited, no longer hedged" conclusion) **travel** to
        `Boneyard/ModalTableauS4Keyed/README.md`.
  - [x] The **`keysOriginS4` retraction MUST STAY in `LoopChecking.lean`** — the "Consumer audit
        (measured; supersedes an earlier hedge)" block stating that `keysOriginS4` was *not*
        removed and is *not* orphaned, and that any future claim it was deleted is false and should
        not be reintroduced. This is about a live, heavily consumed declaration. Carrying it out of
        the live tree would re-open exactly the defect carve-out 2 exists to close.
  - [x] Re-home the retained retraction under a heading that still makes sense once `keysRootEmpty`
        is gone (it can no longer live under a `### keysRootEmpty` heading).
- [x] Create `Boneyard/ModalTableauS4Keyed/KeysRootEmpty.lean` with the same structure as Phase 2:
      import block, `ARCHIVED (Boneyard)` header docstring naming both declarations and ending
      `Do not import from live code.`, `#exit`, then the excised code verbatim.
- [x] Confirm no live `TODO:`/`FIXME:`-family markers travel into the Boneyard.
- [x] Delete `keysRootEmpty`, `keysRootEmpty_entry`, and the `keysRootEmpty`-specific comment
      paragraphs from `LoopChecking.lean`.
- [x] Repair the two references that **stay behind**, redirecting rather than deleting:
  - [x] The `BoxPlusClosed` docstring (hint: near `:910`) — *"the same treatment
        `keysOriginS4`/`keysRootEmpty` already receive"*.
  - [x] The "### Redirect-Inertness Assembly -- REMOVED" section (hint: near `:2586`), which lists
        `keysRootEmpty` among the hypotheses that held in a refutation. This sits inside a
        narrative explaining that refutation; deleting the name would damage the explanation.
- [x] Update the Directory Inventory table in `Boneyard/README.md`.

**Timing**: 1.5 hours

**Depends on**: 2

**Verification Tier**: full

**Commit Mode**: atomic-batch

**Scope Hypothesis**: This phase asserts a ~56-line section (including its comment), exactly two
declarations, exactly **two** surviving references needing repair, and that the section comment
splits cleanly into a travelling part and a must-stay `keysOriginS4` retraction. Confirm at
implementation time by re-running the by-name greps, and — critically — by grepping live `Cslib/`
after the edit for the retraction's distinguishing sentence (that any claim `keysOriginS4` was
deleted is false) and confirming it is **still present** in `LoopChecking.lean`. Its absence
falsifies the hypothesis and must be fixed before the phase closes.

**Files to modify**:

- `Boneyard/ModalTableauS4Keyed/KeysRootEmpty.lean` - new: header, `#exit`, both declarations
- `Cslib/Logics/Modal/Tableau/LoopChecking.lean` - delete the pair and its specific comment
  paragraphs; re-home the retained `keysOriginS4` retraction; redirect the `BoxPlusClosed` and
  "Redirect-Inertness Assembly" references
- `Boneyard/ModalTableauS4Keyed/README.md` - absorb the travelling audit paragraphs
- `Boneyard/README.md` - inventory row

**Verification**:

- Word-boundary grep for `keysRootEmpty` and `keysRootEmpty_entry` over `Cslib/` returns zero
  *declaration* hits; any remaining hits are the redirected prose pointers only.
- Grep confirms the `keysOriginS4` retraction text is still present in `LoopChecking.lean`.
- Word-boundary grep for `keysOriginS4` over `Cslib/` still returns a pervasive count (order 40+);
  it must not have shrunk to near zero.
- `lake build Cslib` green at 3313 jobs; Modal/Tableau sorry census exactly 1; all ratchets
  unchanged.

---

### Phase 4: Reconcile falsified and incomplete prose [COMPLETED]

**Goal**: Every surviving statement about `Boneyard/` in the repository is true.

**Tasks**:

- [x] Correct the now-falsified assertion in `LoopChecking.lean`'s measured-figures block. It
      currently states: *"There is no `Boneyard/` directory (`find . -type d -name 'Boneyard'
      -not -path './.lake/*'` returns nothing)."* Creating `Boneyard/` falsifies this in the same
      change set. Replace it with the true statement — one root-level `Boneyard/` exists, holding
      the archived declarations, excluded from the build by reachability — and keep the
      reproduction command so the claim stays checkable. This block is the file's authoritative
      census of measured figures; a stale claim here is the exact defect class this programme has
      already been burned by twice.
- [x] Add `Boneyard/` to `ORGANISATION.md`'s `## Top-Level Structure` section, which currently
      lists only `Cslib/` and its subdirectories. Describe it as: quarantined archive, never
      imported by `Cslib/`, excluded from `lake build`, `mk_all`, `lint-style`, `shake`, and all
      sorry/axiom censuses; retained for provenance rather than use. Point at
      `Boneyard/README.md` for the convention.
- [x] Re-read the redirected references introduced in Phases 2 and 3 and confirm each names a path
      that actually exists.

**Timing**: 0.75 hours

**Depends on**: 1, 2, 3

**Verification Tier**: prose

**Commit Mode**: per-substep

**Scope Hypothesis**: This phase asserts exactly **two** prose sites need reconciliation beyond
the per-phase redirects already handled (the `LoopChecking.lean` no-Boneyard assertion and the
`ORGANISATION.md` top-level structure list). Confirm at implementation time by grepping the whole
repository (excluding `specs/` and `.lake/`) for `Boneyard` and reviewing every hit for truth; any
additional false or incomplete claim found is an in-scope addition to this phase.

**Files to modify**:

- `Cslib/Logics/Modal/Tableau/LoopChecking.lean` - comment only: replace the falsified
  no-`Boneyard/` assertion
- `ORGANISATION.md` - document `Boneyard/` under Top-Level Structure

**Verification**:

- Diff read-through confirms every changed hunk in `LoopChecking.lean` lies inside a comment
  region (no code or declaration boundary is crossed).
- Repo-wide grep for `Boneyard` outside `specs/` and `.lake/` yields only true statements.
- Every redirected path in a comment resolves to a file that exists.

---

### Phase 5: Add the defensive quarantine self-test [NOT STARTED]

**Goal**: The exclusion stops being implicit and unasserted. A regression that sweeps archived
lines into live counts is caught mechanically.

**Tasks**:

- [ ] Add a check (either a new `scripts/check-boneyard-quarantine.sh` or a step inside
      `scripts/pre-pr-check.sh`) asserting:
  - [ ] (a) `Boneyard/` exists at the repository root;
  - [ ] (b) no `Boneyard` reference appears in `Cslib.lean` (`grep -c 'Boneyard' Cslib.lean` is 0),
        so nothing under `Boneyard/` is reachable from the aggregator;
  - [ ] (c) no `Boneyard` path appears in `lakefile.toml`;
  - [ ] (d) no `.lean` file under `Boneyard/` carries a live `TODO:`/`FIXME:` marker — this guards
        the `todo-issue.yml` exposure at the cheap end without editing a synced workflow file;
  - [ ] (e) **the `B0` mirror**: the exclusion pattern matches the *expected number* of Boneyard
        directories (currently 1), so adding a second Boneyard later cannot silently escape a
        filter. This is the single most valuable element to port from upstream, which documents
        having suffered exactly this failure.
- [ ] Wire it into `scripts/pre-pr-check.sh` — a **local, non-synced** file — rather than into
      `.github/workflows/lean_action_ci.yml`. This matches the established divergence-cost
      convention the repo already follows for `check-lint-suppressions.sh` and
      `check-shake-residue.sh`, and avoids adding a recurring upstream sync-conflict hunk.
- [ ] If a new script is added under `scripts/`, add a corresponding entry to `scripts/README.md`
      (`linter.allScriptsDocumented` is currently disabled, but documenting is the low-cost
      choice).
- [ ] Run the check and confirm it passes on the current tree; then confirm it *fails* when
      deliberately fed a violating condition (e.g. a temporary expected-count mismatch), so the
      assertion is known to be live rather than vacuously green.

**Timing**: 1 hour

**Depends on**: 1

**Verification Tier**: local

**Commit Mode**: per-substep

**Scope Hypothesis**: This phase asserts the expected Boneyard directory count is **1**. Confirm
at implementation time with `find . -type d -name 'Boneyard' -not -path './.lake/*' | wc -l`, and
hard-code the confirmed number into the self-test rather than deriving it at runtime — a self-test
that computes its own expectation asserts nothing.

**Files to modify**:

- `scripts/pre-pr-check.sh` - add the quarantine step (or invoke the new script)
- `scripts/check-boneyard-quarantine.sh` - new, if implemented as a standalone script
- `scripts/README.md` - document the new script, if one is added

**Verification**:

- `bash scripts/pre-pr-check.sh` runs the new step and exits 0.
- The negative test (deliberate violation) makes the check exit non-zero, then is reverted.
- `shellcheck` clean, consistent with the repo's existing shellcheck workflow.

---

### Phase 6: Full CI gate and closeout [NOT STARTED]

**Goal**: Every gate is green and every figure matches the baseline; the task's claims are
evidenced rather than asserted.

**Tasks**:

- [ ] `lake build Cslib` — expect green at **3313 jobs**. `Boneyard/` must NOT appear in the build
      output. A job-count deviation is a signal that a consumer was missed; investigate rather than
      accept.
- [ ] Modal/Tableau sorry census via the canonical two-grep recipe recorded in `LoopChecking.lean`
      — expect exactly **1**, `branchSatisfiableIn_s4FC_ancestor_redirect` in `FrameSoundness.lean`.
- [ ] `bash scripts/check-shake-residue.sh` — gate on **9 findings, none in Modal/Tableau**, exit 0
      against the unmodified baseline. Do not gate on a raw "zero findings" reading.
- [ ] `bash scripts/check-axiom-census.sh` — 43 sorryAx-tainted, exit 0; exactly one Modal/Tableau
      row, and it is the carve-out declaration.
- [ ] `lake exe checkInitImports` — exit 0.
- [ ] `bash scripts/check-lint-suppressions.sh` (19, ceiling 19) and
      `bash scripts/check-sorry-suppressions.sh` (markers 18, sorries 28) — both exit 0.
- [ ] `lake test` — green.
- [ ] `lake exe mk_all --check` — green; confirm it does not demand a `Boneyard.lean` aggregator.
- [ ] Confirm no baseline file was modified: grep each of `axiom-census-baseline.txt`,
      `shake-residue-baseline.txt`, `sorry-suppression-baseline.txt`,
      `lint-suppression-baseline.txt`, and `nolints.json` for the three moved declaration names —
      expect zero hits in all five, and confirm the files are unmodified in `git status`.
- [ ] Confirm the final Directory Inventory table in `Boneyard/README.md` reports measured file and
      line counts, not estimates.
- [ ] Confirm both carve-outs are intact: `branchSatisfiableIn_s4FC_ancestor_redirect` is still in
      `FrameSoundness.lean`, and `keysOriginS4` and its relatives are still in `LoopChecking.lean`.

**Timing**: 0.75 hours

**Depends on**: 1, 2, 3, 4, 5

**Verification Tier**: full

**Commit Mode**: per-substep

**Files to modify**:

- None (verification only; any repair discovered here belongs to the phase that introduced it)

**Verification**:

- Every command above returns its expected result, with the actual figures recorded in the
  implementation summary alongside the baseline figures for comparison.

---

## Testing & Validation

The gate set, run at Phase 1 (baseline), after each code-moving phase, and in full at Phase 6:

- [ ] `lake build Cslib` — green, **3313 jobs**, no `Boneyard/` module in the output
- [ ] Modal/Tableau sorry census — exactly **1** (`branchSatisfiableIn_s4FC_ancestor_redirect`)
- [ ] `bash scripts/check-shake-residue.sh` — exit 0, **9 findings, none in Modal/Tableau**
- [ ] `bash scripts/check-axiom-census.sh` — exit 0, 43 tainted, one Modal/Tableau row (the
      carve-out)
- [ ] `lake exe checkInitImports` — exit 0
- [ ] `bash scripts/check-lint-suppressions.sh` — exit 0, 19 (ceiling 19)
- [ ] `bash scripts/check-sorry-suppressions.sh` — exit 0, markers 18, sorries 28
- [ ] `lake exe mk_all --check` — green
- [ ] `lint-style` — exit 0
- [ ] `lake test` — green
- [ ] Zero-consumer re-grep for all three moved units returns zero code hits in `Cslib/`
- [ ] `keysOriginS4` still pervasively consumed; its retraction still in live code
- [ ] No baseline file and no workflow file modified

## Artifacts & Outputs

- `Boneyard/README.md` — convention, Directory Inventory table, three standing invariants, two
  repo-wide-scanner constraints, root-placement rationale
- `Boneyard/ModalTableauS4Keyed/README.md` — why these three units were archived, plus the
  travelling `keysRootEmpty` audit paragraphs
- `Boneyard/ModalTableauS4Keyed/RedirectOriginTransfer.lean` — the two
  `blockedRedirect_*_of_*Origin` lemmas under the `ARCHIVED` + `#exit` convention
- `Boneyard/ModalTableauS4Keyed/KeysRootEmpty.lean` — `keysRootEmpty` and `keysRootEmpty_entry`
- `Cslib/Logics/Modal/Tableau/LoopChecking.lean` — three declaration units removed; the
  `keysOriginS4` retraction retained and re-homed; four prose sites reconciled
- `ORGANISATION.md` — `Boneyard/` documented under Top-Level Structure
- `scripts/pre-pr-check.sh` (and optionally `scripts/check-boneyard-quarantine.sh`,
  `scripts/README.md`) — the quarantine self-test
- `specs/566_boneyard_creation_eligible_moves/summaries/01_boneyard-creation-eligible-moves-summary.md`

## Rollback/Contingency

Every phase is independently revertible and no phase deletes code — the moved declarations exist
verbatim in `Boneyard/` after each move, so a revert restores them from either side of the change.

- **A consumer was missed (build breaks)**: revert only the offending phase's commit. The moved
  block is verbatim in the Boneyard file, so restoring it into `LoopChecking.lean` is a copy-back.
  Then re-run the by-name consumer grep before re-attempting, and record why the first grep missed
  the consumer.
- **Job count shifts from 3313**: do not proceed. Investigate the delta first — a leaf-only move
  cannot change the job count, so any change means the scope hypothesis was wrong.
- **The `keysOriginS4` retraction is found missing from live code after Phase 3**: restore it
  immediately from the pre-phase state; this is a correctness regression on the carve-out, not a
  cosmetic one.
- **The quarantine self-test proves unstable or noisy**: Phase 5 is explicitly recommended, not
  required. It can be dropped without affecting Phases 1-4, provided the standing invariants
  remain documented in `Boneyard/README.md`.
- **Full abort**: revert all task commits. `Boneyard/` is removed and `LoopChecking.lean` returns
  to its prior state; no baseline, workflow, or config file was ever touched, so there is nothing
  else to unwind.
