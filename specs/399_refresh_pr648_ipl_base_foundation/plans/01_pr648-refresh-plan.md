# Implementation Plan: Task #399 — Refresh PR #648 (IPL-Base Foundation)

- **Task**: 399 - refresh_pr648_ipl_base_foundation
- **Status**: [COMPLETED]
- **Effort**: 4 hours
- **Dependencies**: 398 (efq/IPL-base implemented on local fork main — COMPLETE)
- **Research Inputs**: specs/399_refresh_pr648_ipl_base_foundation/reports/01_pr648-refresh-research.md
- **Artifacts**: plans/01_pr648-refresh-plan.md (this file)
- **Standards**: plan-format.md; status-markers.md; artifact-management.md; tasks.md
- **Type**: pr
- **Lean Intent**: false

## Overview

Prepare — but NOT submit — a refreshed, small, reviewable version of PR #648
(leanprover/cslib, branch `feat/propositional-v2`) containing ONLY the
propositional FOUNDATION, per Thomas Waring's closing recommendation in CSLib
Zulip thread 606970606. The plan produces three handoff artifacts for the user
to execute via the user-only `/pr` command: (1) an exact cherry-pick / branch-off-
upstream-main recipe + script, (2) a human-authored-ready PR description draft,
and (3) a human-authored-ready Zulip message draft addressing Waring's flags (a)
and (b). The task transitions to [PR READY] when these artifacts are complete and
the foundation diff has been verified to build in local isolation.

Definition of done: cherry-pick recipe is exact and locally rehearsed (builds
green off a temporary branch from upstream/main, with Theory.lean removed and the
barrel consistent); `pr-description.md` and `zulip-response.md` drafts exist,
explicitly marked for human authorship/finalization, and address Waring flags (a)
connective-typeclasses-excluded and (b) references + Zulip-thread-link present;
task is [PR READY].

### Research Integration

The plan is built directly on `reports/01_pr648-refresh-research.md`. Key findings
integrated:
- PR #648 is only **11 commits behind upstream/main** (not 239); merge base at PR
  #536; none of the 11 upstream commits touch propositional files.
- Foundation scope IN: `Defs.lean` MINUS the `Connectives` import (line 10) and the
  three typeclass instances (lines ~113-124); `NaturalDeduction/Basic.lean` (full
  local fork main version with gated `efq`, Zulip link at line ~78, design note);
  six `references.bib` entries.
- Foundation scope OUT (later stacked PRs): connective typeclasses (task 400),
  Hilbert + equivalence, algebraic semantics incl. MPL metatheory, conservativity
  chains, sequent LJ/LK, tableau.
- Structural blocker: upstream `NaturalDeduction/Theory.lean` uses the OLD
  `IsIntuitionistic` API and is in the `Cslib.lean` barrel. Research recommends
  **Option A: delete Theory.lean + remove it from the barrel** (matches local fork
  main). This is a reviewer-visible decision and must be flagged explicitly.
- Coordination: vet tasks 386/387/389 fix lint/namespace on fork main but do NOT
  block this foundation PR (they touch downstream files not in the cherry-pick).

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

No ROADMAP.md consulted (no roadmap_path provided). This task advances the
"propositional logic foundation upstreaming" effort tracked via the Zulip
"Propositional Logic" thread and the task 398/399/400 series.

## Goals & Non-Goals

**Goals**:
- Produce an exact, locally-rehearsed cherry-pick / branch-off-upstream-main recipe
  (and an executable script) that yields the foundation-only diff.
- Verify, in local isolation only, that the foundation diff builds green off a
  temporary branch from upstream/main with `Theory.lean` deleted and the barrel
  consistent.
- Draft `pr-description.md` (PR body) and `zulip-response.md` (Zulip message),
  both marked as human-authorship scaffolding, explicitly addressing Waring flags
  (a) and (b) and the Theory.lean deletion decision.
- Transition the task to [PR READY] with all handoff artifacts in place.

**Non-Goals**:
- NO pushing, NO remote branch creation, NO remote CI runs, NO posting to GitHub or
  Zulip. All of those are the user's job via the user-only `/pr` command.
- NOT auto-posting any human-facing prose — PR body and Zulip message are drafts
  clearly marked for human review/finalization per the Zulip AI policy.
- NOT bundling connective typeclasses (task 400), Hilbert/equivalence, semantics,
  conservativity, sequent calculi, or tableau — these are later stacked PRs.
- NOT modifying local fork main, references.bib, or any Cslib source as a committed
  change; any local edits are confined to a throwaway verification worktree/branch.

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Foundation diff fails to build off upstream/main (API drift since merge base) | H | M | Phase 2 rehearses the build locally in a throwaway worktree before [PR READY]; capture exact errors and fold corrections into the recipe |
| Theory.lean deletion removes derived rules other upstream files depend on | M | L | Research confirms only Theory.lean uses old `IsIntuitionistic` API and no other barrel file imports it; Phase 1 re-verifies via grep before finalizing recipe |
| `impl`->`imp` rename breaks downstream upstream consumers | M | L | Phase 1 greps upstream/main for `implI`/`implE` usage outside Theory.lean; flag any hits in PR description |
| Missing references.bib entries (Church1956 / ChagrovZakharyaschev1997) after Connectives removal | L | M | Phase 1 cross-checks which bib keys the trimmed Defs.lean/Basic.lean actually cite and includes exactly those |
| AI-drafted prose posted to Zulip violating policy | H | L | Drafts carry a prominent HUMAN-AUTHOR-REQUIRED banner; plan never posts; user finalizes wording |
| Accidental push / remote branch from verification step | H | L | Phase 2 uses an isolated local worktree/branch, explicitly never runs `git push` or `gh`; cleanup step removes it |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2, 3 | 1 |
| 3 | 4 | 2, 3 |

Phases within the same wave can execute in parallel.

### Phase 1: Determine Cherry-Pick Recipe and Precise File Subset [NOT STARTED]

**Goal**: Produce the exact branch-off-upstream-main + cherry-pick recipe and the
precise per-file change list, captured as a recipe document and an executable
script. No build yet.

**Tasks**:
- [ ] `git fetch upstream` and confirm current `upstream/main` HEAD and that the 11
  ahead-commits do not touch `Cslib/Logics/Propositional/**` (re-confirm research).
- [ ] Diff local fork main `Defs.lean` against the foundation scope; record the exact
  line to drop (the `public import Cslib.Foundations.Logic.Connectives`) and the
  exact instance block to drop (`PropositionalConnectives`, `HasAnd`, `HasOr` — ~lines 113-124). Capture current line numbers from the live file (do not trust stale numbers).
- [ ] Confirm `NaturalDeduction/Basic.lean` foundation version is taken as-is (gated
  `efq`, `## Implementation notes` IPL-as-base design note, Zulip link, restored
  references); record the Zulip-link line for flag (b) traceability.
- [ ] Enumerate the six `references.bib` entries to add (Johansson1937, Gentzen1935,
  Prawitz1965, TroelstraVanDalen1988, SorensenUrzyczyn2006, Avigad2022); cross-check
  whether the trimmed Defs.lean/Basic.lean also cite Church1956 / ChagrovZakharyaschev1997
  and include those bib keys only if actually referenced.
- [ ] Confirm the `Cslib.lean` barrel line to remove
  (`public import Cslib.Logics.Propositional.NaturalDeduction.Theory`).
- [ ] Grep upstream/main for any other consumer of the old `IsIntuitionistic` API or
  `implI`/`implE` naming outside Theory.lean; record findings as PR-description flags.
- [ ] Write `cherry-pick-recipe.md` (human-readable recipe + Option A rationale +
  reviewer-visible Theory.lean-deletion note) and `prepare-foundation-branch.sh`
  (idempotent script that creates a LOCAL branch `feat/propositional-foundation` off
  `upstream/main`, applies the file changes, deletes Theory.lean, edits the barrel,
  adds bib entries — with NO push and NO gh calls).

**Timing**: 1 hour

**Depends on**: none

**Files to read (reference only, not modified here)**:
- `Cslib/Logics/Propositional/Defs.lean` — locate exact import + instance lines
- `Cslib/Logics/Propositional/NaturalDeduction/Basic.lean` — confirm Zulip link line
- `Cslib/Logics/Propositional/NaturalDeduction/Theory.lean` — confirm deletion target
- `Cslib.lean` — locate Theory import line
- `references.bib` — confirm six entries present locally

**Files to create**:
- `specs/399_refresh_pr648_ipl_base_foundation/cherry-pick-recipe.md`
- `specs/399_refresh_pr648_ipl_base_foundation/prepare-foundation-branch.sh`

**Verification**:
- Recipe lists every modified file, every deleted file, and the exact lines
  added/removed, with no reference to out-of-scope content (Connectives, semantics,
  Hilbert, sequent, tableau).
- Script is non-destructive to fork main and contains no `git push` / `gh` / remote
  CI invocation (grep the script to confirm).

---

### Phase 2: Stage and Locally Verify the Foundation Diff Builds in Isolation [NOT STARTED]

**Goal**: Rehearse the Phase 1 recipe in a throwaway LOCAL git worktree branched
from `upstream/main`, and confirm the foundation builds green with Theory.lean
removed and the barrel consistent. Local only — no push, no remote CI.

**Tasks**:
- [ ] Create an isolated worktree/branch off `upstream/main` (e.g.
  `git worktree add ../cslib-foundation-verify upstream/main`) so fork main is
  untouched.
- [ ] Run `prepare-foundation-branch.sh` (or apply the recipe steps) inside the
  worktree.
- [ ] Run `lake build` for the foundation modules and the barrel
  (`Cslib/Logics/Propositional/Defs.lean`, `.../NaturalDeduction/Basic.lean`,
  `Cslib.lean`) and confirm green.
- [ ] Confirm barrel consistency: no dangling import of the deleted Theory.lean; no
  unresolved references to removed Connectives typeclasses.
- [ ] Run available local CI checks that are cheap and offline-safe
  (`lake exe checkInitImports`, `lake exe lint-style` on the touched files) to
  surface issues the user's `/pr` CI would catch.
- [ ] Record build/CI results into `cherry-pick-recipe.md` (a "Local Verification"
  section); if any step fails, fold the fix back into the recipe + script and re-run.
- [ ] Remove the throwaway worktree/branch when done (no push, no remote artifacts).

**Timing**: 1.5 hours

**Depends on**: 1

**Files to modify**:
- `specs/399_refresh_pr648_ipl_base_foundation/cherry-pick-recipe.md` — add Local
  Verification results
- `specs/399_refresh_pr648_ipl_base_foundation/prepare-foundation-branch.sh` — patch
  if rehearsal reveals recipe gaps

**Verification**:
- `lake build` of the foundation + barrel is green in the isolated worktree.
- No reference to deleted Theory.lean or excluded Connectives remains.
- Throwaway worktree/branch removed; fork main unchanged (`git status` clean on main).
- No `git push` or remote CI was executed.

---

### Phase 3: Draft PR Description and Zulip Message (Human-Authorship Scaffolding) [NOT STARTED]

**Goal**: Produce `pr-description.md` (the PR body) and `zulip-response.md` (the
Zulip reply to Waring 606970606), both clearly marked as drafts requiring human
authorship/finalization, explicitly addressing Waring flags (a) and (b) and the
Theory.lean-deletion decision.

**Tasks**:
- [ ] Draft `pr-description.md` with: what changed (primitive `⊥`, gated `efq`,
  IPL-as-base with MPL retained as fragment, `impl`->`imp` rename, references
  restored, Zulip-thread link added); what's excluded and why (connective
  typeclasses -> task 400 / PR #607; semantics, Hilbert, conservativity, sequent,
  tableau -> stacked PRs); the **Theory.lean deletion as an explicit reviewer-visible
  decision** (Option A rationale); the design trade-off note location in Basic.lean;
  and the pending namespace `PL`->`Propositional` flag (task 387, upstream-gated).
- [ ] Draft `zulip-response.md` responding to Waring 606970606: efq implemented as
  gated primitive per his closing suggestion (CI green on fork main); connective
  typeclasses removed from the foundation PR — flag (a); references + Zulip-thread
  link now present — flag (b); foundation cherry-pick is a single focused commit;
  welcome his formal review once the PR is updated.
- [ ] Add a prominent HUMAN-AUTHOR-REQUIRED banner to BOTH files stating the content
  is AI-assisted scaffolding to be reviewed and reworded by the user before posting
  (Zulip AI policy), and that the plan/agent will not post them.
- [ ] Include a draft single-commit message (from research) inside `pr-description.md`
  as a fenced block for the user to reuse.

**Timing**: 1 hour

**Depends on**: 1

**Files to create**:
- `specs/399_refresh_pr648_ipl_base_foundation/pr-description.md`
- `specs/399_refresh_pr648_ipl_base_foundation/zulip-response.md`

**Verification**:
- Both files contain the HUMAN-AUTHOR-REQUIRED banner.
- `pr-description.md` explicitly covers flags (a) and (b), the Theory.lean deletion
  decision, and the excluded scope with future homes.
- `zulip-response.md` directly answers Waring's two flags and references task 398's
  completed efq work.
- Neither file is posted anywhere; both are drafts only.

---

### Phase 4: Final Verification and Transition to [PR READY] [NOT STARTED]

**Goal**: Confirm all handoff artifacts are present and internally consistent, then
transition the task to [PR READY] for the user to run `/pr`.

**Tasks**:
- [ ] Confirm presence of all four artifacts: `cherry-pick-recipe.md`,
  `prepare-foundation-branch.sh`, `pr-description.md`, `zulip-response.md`.
- [ ] Reconcile the recipe's Local Verification result (Phase 2) into
  `pr-description.md` so the PR body's build claim matches the rehearsed outcome.
- [ ] Confirm the recipe contains no push / remote-branch / remote-CI / posting
  steps (those belong to the user's `/pr`).
- [ ] Write a short "User Next Steps" block (run `prepare-foundation-branch.sh` or
  follow the recipe, then `/pr 399` to create the branch/PR; finalize wording of
  `pr-description.md` and `zulip-response.md` before posting).
- [ ] Transition task 399 to [PR READY] via
  `bash .claude/scripts/update-task-status.sh postflight 399 implement <session_id>`
  (or the project's [PR READY] transition path) — performed by the orchestrating
  skill postflight, not pushed remotely.

**Timing**: 0.5 hour

**Depends on**: 2, 3

**Files to modify**:
- `specs/399_refresh_pr648_ipl_base_foundation/pr-description.md` — reconcile build
  status, add User Next Steps

**Verification**:
- All four artifacts exist and are mutually consistent.
- Task status is [PR READY].
- No remote operation was performed by the plan; `/pr` remains the user's action.

---

## Testing & Validation

- [ ] Phase 2 `lake build` of foundation modules + barrel is green in the isolated
  worktree (Theory.lean removed, Connectives excluded).
- [ ] `lake exe checkInitImports` and `lake exe lint-style` pass on the touched
  foundation files (offline-safe subset of the CI pipeline).
- [ ] `prepare-foundation-branch.sh` contains no `git push`, no `gh`, no remote CI.
- [ ] `pr-description.md` and `zulip-response.md` both carry the
  HUMAN-AUTHOR-REQUIRED banner and address Waring flags (a) and (b).
- [ ] Fork main `git status` is clean (verification worktree removed).

## Artifacts & Outputs

- `specs/399_refresh_pr648_ipl_base_foundation/plans/01_pr648-refresh-plan.md` (this plan)
- `specs/399_refresh_pr648_ipl_base_foundation/cherry-pick-recipe.md` (recipe + Option A rationale + local verification results)
- `specs/399_refresh_pr648_ipl_base_foundation/prepare-foundation-branch.sh` (local, no-push branch-prep script)
- `specs/399_refresh_pr648_ipl_base_foundation/pr-description.md` (PR body draft — human to finalize)
- `specs/399_refresh_pr648_ipl_base_foundation/zulip-response.md` (Zulip reply draft — human to finalize)
- `specs/399_refresh_pr648_ipl_base_foundation/summaries/01_pr648-refresh-summary.md` (implementation summary, written at /implement time)

## Rollback/Contingency

- All work is confined to the task directory plus a throwaway git worktree/branch.
  To roll back: delete the generated artifacts in the task directory and remove the
  verification worktree (`git worktree remove ../cslib-foundation-verify`).
- Fork main and references.bib are never committed against; no remote state is
  touched, so there is nothing to revert upstream.
- If Phase 2 build verification cannot be made green, mark the phase [BLOCKED],
  record the blocking build error in `cherry-pick-recipe.md`, and do NOT transition
  to [PR READY] — instead escalate (possible follow-up task) since submitting a
  non-building foundation would waste reviewer time.
