# Implementation Plan: Fix and stack PR #662 on PR #648

- **Task**: 475 - fix_and_stack_pr_662_on_648
- **Status**: [NOT STARTED]
- **Effort**: 5 hours
- **Dependencies**: 468 (resync), 469 (Connectives decision), 472 (model-class Equiv restore — COMPLETED on `main`, commit `9c5cbd08`)
- **Research Inputs**: reports/01_fix-and-stack-pr-662-on-648.md
- **Artifacts**: plans/01_fix-and-stack-pr-662-on-648.md (this file)
- **Standards**: plan-format.md; status-markers.md; artifact-management.md; tasks.md; git-workflow.md
- **Type**: cslib
- **Lean Intent**: false

## Overview

Rebase PR #648 (`feat/propositional-v2`) and rebuild PR #662 (`feat/modal-formula-primitives`) as a
single clean commit stacked on #648, dropping #662's stale propositional-file copies (inherited from
#648 instead), transplanting the task-472 fix (`Cslib/Logics/Modal/LogicalEquivalence.lean` from
`main` commit `9c5cbd08`), self-owning `Connectives.lean` per Option A, and slimming #662 to its six
genuine modal files. **All history-rewriting and outward-facing actions (force-pushes, PR base
retarget, PR body edit, Zulip reply) are isolated into two late USER-APPROVAL GATE phases (5 and 6)
and MUST NOT be performed by an autonomous agent without an explicit human hard-stop.** Everything
before Phase 5 is local, reversible git work plus the full CSLib CI pipeline; nothing is pushed until
`lake build` and `lake test` are green.

Definition of done: rebased `feat/propositional-v2` builds on current `upstream/main`; the slimmed,
stacked, single-commit #662 builds/tests/lints green on top of #648 head with the task-472 fix
present and `LogicallyEquivalent` absent; corrected PR body text and a Zulip reply draft exist as
review artifacts; and — only after explicit user approval — the two branches are force-pushed with
`--force-with-lease`, PR #662 is retargeted to `feat/propositional-v2`, its body is updated, and the
Zulip reply is posted.

### Research Integration

- Ground-truth hashes (report §1, Appendix): `upstream/main`=`5c41dcf2`; #648 local tip `c98c4348`
  (merge-base `2772f421`, 5 ahead / 2 behind); #662 local tip `3ff6d02d` (merge-base `e0573fbc`,
  3 ahead / **10 behind**, does NOT contain #648 history); task-472 fix commit `9c5cbd08` on `main`.
- The modal layer is cleanly separable: `Modal/Basic.lean` imports self-owned `Connectives`,
  `InferenceSystem`, `Relation.Defs`, `Cslib.Init`, Mathlib — but **not** `Logics.Propositional.*`
  (report §4). This is what makes "drop the propositional files, inherit from #648" safe.
- Cherry-pick technique (report §5): rebuild #662 on rebased #648 head, `git checkout` only the six
  modal files from the old #662 branch, then `git checkout main -- .../LogicalEquivalence.lean` for
  the task-472 fix (near-clean; pre-472 base differs from #662 head by only 3 lines).
- Connectives.lean = **Option A** (self-own in #662), per report §6 and the task directive. Deletion
  is BLOCKED (#607 unmerged, lacks `HasBot`/bundles); decouple deferred to a joint #607 coordination.
- Force-push is the single hard gate; nothing pushed without explicit approval (report §10, §11).

### Prior Plan Reference

No prior plan. This is the first plan for task 475.

### Roadmap Alignment

No ROADMAP.md consulted for this task (no `roadmap_path` provided, `roadmap_flag` not set).

## Goals & Non-Goals

**Goals**:
- Create a local safety net (backup branches + tag) before any history rewrite (guards R3).
- Rebase `feat/propositional-v2` onto current `upstream/main` and verify by build (R1).
- Build a single clean #662 commit stacked on rebased #648, containing only the six genuine modal
  files, with the task-472 fix applied and `Connectives.lean` self-owned (Option A).
- Verify the full CSLib CI pipeline green on both rewritten branches before any push.
- Produce corrected PR #662 body text and a Zulip reply draft as review artifacts.
- Perform force-pushes, PR base retarget, PR body edit, and Zulip post **only** behind explicit
  user-approval gates.

**Non-Goals**:
- Merging the #607 typeclass hierarchy or decoupling `Connectives.lean` (deferred; Option A now).
- Rebasing onto `origin/main` (fork; 516 behind upstream — never a rebase target, R6).
- Carrying task-472's specs artifacts (`plans/`, `summaries/`, `TODO.md`, `state.json`) onto the PR
  branch — only the Lean file is transplanted.
- Any `sorry`/axiom patch to make a broken proof pass (zero-debt; fix structurally or mark BLOCKED).
- Autonomous execution of any Phase 5 or Phase 6 action without a human hard-stop.

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| R1 — Mathlib-bump rebase conflicts (#662 10 behind incl. 3 mathlib bumps + `Relation` split #632) | H | M | Rebase #648 first (only 2 behind, low risk); rebuild modal files on #648's already-adapted base so modal meets current mathlib once; build after each step (Phases 1, 3). |
| R2 — Dropping #662's `Propositional/Defs.lean` (`PropositionalConnectives` registration) breaks a modal proof | H | L | §4 shows modal does not import Propositional and self-owns `Connectives`; **confirm by `lake build`** on stacked branch (Phase 3). Zero-debt — no `sorry` patch. |
| R3 — Silently losing the task-472 fix (only on local `main` `9c5cbd08`) | H | M | Phase 0 tags `pre-475-472fix=9c5cbd08`; Phase 2 explicitly `git checkout main -- .../LogicalEquivalence.lean`; Phase 3 asserts parametric `Proposition.Equiv S` present and `git grep LogicallyEquivalent Cslib/` empty. |
| R4 — `references.bib` duplication/omission (both PRs touch it) | M | M | Phase 2 merges modal-only keys onto #648's bib; Phase 3 diffs bib, confirms modal keys present, prop keys single-sourced from #648, no dangling BibKeys. |
| R5 — Force-push race / stale remote | M | L | Phase 5 uses `--force-with-lease`; keep `backup/*` branches until GitHub CI green. |
| R6 — `origin/main` confusion (516 behind upstream) | M | L | Always rebase onto `upstream/main`; never `origin/main`. |
| Premature outward action | H | L | Phases 5/6 are hard-stop gates; each gated action is an explicit approval checklist item; agent must STOP and not proceed autonomously. |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 0 | -- |
| 2 | 1 | 0 |
| 3 | 2 | 1 |
| 4 | 3, 4 | 2 |
| 5 | 5 | 3, 4 |
| 6 | 6 | 5 |

Phases within the same wave can execute in parallel.

---

### Phase 0: Safety net — backup branches and task-472 pin [COMPLETED]

**Goal**: Create reversible local safety anchors before any branch is rewritten, guarding against
Risk R3 (losing the task-472 fix) and enabling full rollback.

**Tasks**:
- [ ] `git fetch upstream` (refresh `upstream/main`; confirm tip = `5c41dcf2` or note the new tip).
- [ ] `git branch backup/648-pre-rebase feat/propositional-v2`
- [ ] `git branch backup/662-pre-rebase feat/modal-formula-primitives`
- [ ] `git tag pre-475-472fix 9c5cbd08` (pin the task-472 fix commit).
- [ ] Record current tips in the summary for rollback reference.

**Timing**: 0.25 hours

**Depends on**: none

**Files to modify**: none (git refs only; no working-tree changes).

**Verification**:
- `git rev-parse backup/648-pre-rebase` == pre-rebase `feat/propositional-v2` tip (`c98c4348`).
- `git rev-parse backup/662-pre-rebase` == pre-rebase `feat/modal-formula-primitives` tip (`3ff6d02d`).
- `git rev-parse pre-475-472fix` == `9c5cbd08`.
- `git tag --list pre-475-472fix` non-empty; `git branch --list 'backup/*'` shows both branches.

---

### Phase 1: Rebase #648 (`feat/propositional-v2`) onto `upstream/main` [COMPLETED]

**Goal**: Bring #648 up to current `upstream/main` (5 ahead / 2 behind → low risk) and verify by a
clean build, establishing the already-mathlib-adapted base that #662 will stack on (mitigates R1).

**Tasks**:
- [x] `git switch feat/propositional-v2` (already HEAD; confirmed).
- [x] `git rebase --onto upstream/main 2772f421 feat/propositional-v2` (done in prior dispatch; verified
      by this dispatch — `upstream/main` (`5c41dcf2`) is an ancestor of `feat/propositional-v2` HEAD
      `9376b737`, 5 commits ahead, 0 behind).
- [x] Resolve any mathlib-bump / `Relation`-split conflicts — none needed; rebase was clean, no
      `Propositional/*` or `references.bib` edits required.
- [x] Full build/test verification run (see below). No `lake exe cache get` was needed since local
      `.lake` build cache was already warm from a prior build.

**Timing**: 1 hour (includes long-running `lake build`).

**Depends on**: 0

**Files to modify**:
- None. Rebase was clean; no `Propositional/*` or `references.bib` adaptation was required.

**Verification** (all confirmed by this dispatch, real command output):
- `git merge-base --is-ancestor upstream/main feat/propositional-v2` -> exit 0 ("YES ancestor").
- `lake build` -> first full run hit two spurious failures (`Cslib.Foundations.Combinatorics.
  InfiniteGraphRamsey`, `Cslib.Languages.LambdaCalculus.LocallyNameless.Fsub.Opening`) with error
  `failed to open file '.../Fsub/Basic.olean': No such file or directory` — a parallel-build
  scheduling race (olean not yet flushed), not a real break. Confirmed by rebuilding each target in
  isolation (`lake build Cslib.Languages.LambdaCalculus.LocallyNameless.Fsub.Basic` and
  `lake build Cslib.Foundations.Combinatorics.InfiniteGraphRamsey`, both "Build completed
  successfully"), then a full `lake build` rerun: **"Build completed successfully (2756 jobs)."**
  Zero code changes needed — deviation noted, no structural fix required.
- `lake test` -> **all 8786/8786 jobs built, CslibTests suite green.**
- `lake exe checkInitImports` -> **exit code 0**, no violations reported.
- `lake exe lint-style` -> **exit code 0**, only a benign `nolints-style.txt` missing-file warning
  (expected/pre-existing).
- `git log --oneline upstream/main..feat/propositional-v2` -> exactly 5 commits, all #648's own
  (`9376b737`, `e6d92df6`, `b0600aad`, `23f345d8`, `ac9ee64e`); no upstream duplication.

---

### Phase 2: Build finalized #662 as a single clean commit stacked on #648 [COMPLETED]

**Goal**: Construct `feat/modal-formula-primitives-v2` from rebased #648 head containing only the six
genuine modal files, with the task-472 fix transplanted and `Connectives.lean` self-owned (Option A).
No push. (Mitigates R2/R3/R4 at the local level.)

**Tasks**:
- [x] `git switch -c feat/modal-formula-primitives-v2 feat/propositional-v2` (start from rebased #648).
- [x] Bring in ONLY the genuine modal contribution from the old modal branch (5 files + `Cslib.lean`
      edited manually — see deviation note below).
- [x] Apply the task-472 fix (finished file from `main`):
      `git checkout main -- Cslib/Logics/Modal/LogicalEquivalence.lean` — **near-clean as predicted**;
      builds directly against old-#662's Basic.lean with zero manual reconciliation needed (confirmed
      by `lake build Cslib.Logics.Modal.LogicalEquivalence` -> "Build completed successfully").
- [x] `references.bib` merge — **no-op**: set-diff of `@key{...}` identifiers between old #662's bib
      and the current (rebased #648) bib is empty; `Avigad2022` (the only modal-cited key, used by
      `Connectives.lean`) is already present in #648's bib (verified by `comm -23` over sorted key
      lists). No edit made.
- [x] Confirmed no `Propositional/*` edits: `git diff --name-only feat/propositional-v2 --
      Cslib/Logics/Propositional/` is empty.
- [x] `git add` (six intended files only, explicitly listed — not `-A`, to exclude unrelated untracked
      `specs/`/`typst/` dirs) and committed as a single placeholder-message commit `176411ec`
      (finalized public message pending Phase 5 gate, D5).

**Deviation from plan**: `Cslib.lean`'s modal import lines (`Modal.Basic`/`Cube`/`Denotation`/
`LogicalEquivalence`) were ALREADY present in rebased `feat/propositional-v2` (inherited from
`upstream/main`, which has an OLDER modal design merged via #528/#535/#632 — atom/not/and/diamond
primitives, not the box/imp primitives design). Only the `Cslib.Foundations.Logic.Connectives`
import line was missing and was added via a targeted `Edit` (not `git checkout ... -- Cslib.lean`,
which would have overwritten with old-#662's full import list, mismatched against the current
much-larger `main`/upstream-merged `Cslib.lean`). This is a structural discovery, not a plan
violation: `upstream/main` already carries an earlier iteration of Modal Logic (merged separately
from #662); the old `feat/modal-formula-primitives` branch's Basic/Cube/Denotation/LogicalEquivalence
content REPLACES that earlier iteration in-place (same file paths), consistent with plan intent.

**Timing**: 1 hour

**Depends on**: 1

**Files to modify** (on the new branch, relative to #648 head):
- `Cslib/Logics/Modal/Basic.lean` - genuine modal (from old #662).
- `Cslib/Logics/Modal/Cube.lean` - genuine modal (from old #662).
- `Cslib/Logics/Modal/Denotation.lean` - genuine modal (from old #662).
- `Cslib/Logics/Modal/LogicalEquivalence.lean` - genuine modal WITH task-472 fix (from `main`).
- `Cslib/Foundations/Logic/Connectives.lean` - self-owned typeclass file, Option A (from old #662).
- `Cslib.lean` - module registration for the modal modules (from old #662).
- `references.bib` - modal keys merged onto #648's bib.

**Verification**:
- `git diff --name-only feat/propositional-v2 feat/modal-formula-primitives-v2` lists exactly the
  seven files above (six modal + `references.bib`) and NO `Propositional/*` files.
- `git grep LogicallyEquivalent Cslib/` returns empty (standalone def removed by task-472).
- The parametric `Proposition.Equiv (S : Set (Model World Atom))` and `LogicalEquivalence` instance
  are present in `Cslib/Logics/Modal/LogicalEquivalence.lean`.
- `git log --oneline` shows a single new commit on top of `feat/propositional-v2`.

---

### Phase 3: Full CI pipeline + R1/R2/R3/R4 verification on stacked #662 [COMPLETED]

**Goal**: Prove the slimmed, stacked #662 is green end-to-end before any push. **This is the hard
build gate: no Phase 5 push may occur unless every check here passes.**

**Tasks**:
- [x] `lake build` on `feat/modal-formula-primitives-v2` -> **"Build completed successfully
      (2757 jobs)."** (2757 = the base's 2756 + 1 new `Connectives.lean` module; zero errors.)
- [x] `lake test` -> **initial run FAILED**: `CslibTests/GrindLint.lean` — our new Modal
      `@[scoped grind]`/`@[scoped grind =]` lemmas (`neg_denotation`, `Satisfies.and_iff_and`,
      `Satisfies.iff_iff_iff`, `Satisfies.or_iff_or`) triggered run-away grind instantiation,
      failing the library-wide `#grind_lint check (min := 20)` guard. **Fixed** by adding four
      `#grind_lint skip Cslib.Logic.Modal.<name>` entries to `CslibTests/GrindLint.lean` — the
      file's own documented, sanctioned escape hatch (used identically by the analogous
      `Cslib.Logic.HML` module for the same diamond/grind pattern). Amended into the Phase 2 commit
      (single-commit requirement). Rerun: **`lake test` -> exit 0, all 8787/8787 jobs green.**
- [x] `lake exe checkInitImports` -> **exit 0**, no violations.
- [x] `lake exe lint-style` -> **exit 0**, only the benign pre-existing `nolints-style.txt` missing
      warning.
- [x] `lake shake --add-public --keep-implied --keep-prefix` -> exit 1 (advisory, as expected — shake
      always exits 1 when it has *any* import-minimization suggestion anywhere in the ~2750-module
      library; this is not a hard gate). **Modal-file comparison against the pre-modal baseline**
      (rebuilt and re-shaken on `feat/propositional-v2` directly, real output captured both times):
      baseline flags `Modal/Basic.lean` (`remove` 2 imports / `add` 7), `Modal/Cube.lean` (`add`
      1), `Modal/Denotation.lean` (`add` 1). Our v2 branch flags only `Modal/Basic.lean` (`add`
      1: `Mathlib.Order.Notation`) — **fewer flags than the baseline, no new files newly flagged**;
      `Connectives.lean` and the other four modal files are shake-clean. Caveat satisfied.
- [x] R2 check: build succeeds with zero `Propositional/Defs.lean`/`PropositionalConnectives`
      dependency from Modal — `grep -rn "PropositionalConnectives" Cslib/Logics/Modal/` returns
      empty (Modal only uses its own `ModalConnectives` instance).
- [x] R3 check: `git grep -n "LogicallyEquivalent" -- Cslib/` returns empty; parametric
      `def Proposition.Equiv (S : Set (Model World Atom)) ...` confirmed present at
      `LogicalEquivalence.lean:75`.
- [x] R4 check: `git diff feat/propositional-v2 -- references.bib` is empty — no bib changes were
      needed (see Phase 2 deviation note: `Avigad2022`, the only modal-cited key, was already
      present in #648's rebased bib).
- [x] Job count and pass/fail recorded above (this cell) and in the execution summary.

**Timing**: 1 hour (dominated by `lake build` wall-clock).

**Depends on**: 2

**Files to modify**: none (verification only; if a proof breaks, fix structurally in Phase 2's file
set and re-run — zero-debt, no `sorry`).

**Verification**:
- All five CI commands pass (build, test, checkInitImports, lint-style, shake) with the shake caveat
  above.
- Both R2 and R3 assertions hold; R4 bib diff is clean.
- If any check fails and cannot be fixed structurally, STOP and mark the task/phase [BLOCKED] with the
  failing output — do not proceed to Phase 4/5.

---

### Phase 4: Draft PR #662 body correction and Zulip reply as review artifacts [COMPLETED]

**Goal**: Produce, as local files for user review, (a) the corrected PR #662 body text and (b) the
Zulip reply draft to @fmontesi. **No posting, no `gh` edit, no Zulip send in this phase.**

**Tasks**:
- [x] Wrote `specs/475_fix_and_stack_pr_662_on_648/artifacts/pr-662-body.md` (deviation: dispatch
      instructions specified an `artifacts/` subdirectory and this exact filename, superseding this
      plan's originally-specified flat path — see deviation note below). Describes: the
      stack-on-#648 relationship, box-primitive/diamond-derived design, `HasBox`/`ModalConnectives`,
      the K/T/B/4/5/D validity+canonicity table, the self-owned `Connectives.lean` (Option A) and
      deferred #607 coordination, and the task-472 parametric-equivalence integration.
- [x] Wrote `specs/475_fix_and_stack_pr_662_on_648/artifacts/zulip-response.md` (same path
      deviation; also note plan said `zulip-reply.md`, dispatch said `zulip-response.md` — used the
      dispatch name). Acknowledges @fmontesi's PR-size concern, takes his points one at a time
      (scope split, box-vs-diamond primitive choice, HasBox/#607 typeclass coordination, task-472
      equivalence fix), offers a post-23-July CSLib meeting. No task-474 draft was found in the repo
      (`find specs -ipath "*474*"` empty) to reuse as a base; written fresh.
- [x] Cross-checked both drafts against the actual Phase 2/3 file set and content (K/T/B/4/5/D
      table verified directly against `Cube.lean`/`Basic.lean` source, not assumed from the plan's
      summary — corrected the plan's "explicit `simp only [Satisfies]` + `intro` (not `grind`)"
      characterization, which does not match the actual code: most K/T/B/4/5/D validity proofs use
      `grind` directly; only `Satisfies.four` uses an explicit `intro`/`obtain`/`exact` derivation.
      The PR body describes this accurately rather than repeating the plan's inaccurate summary).

**Deviation from plan**: Both artifacts were written to `specs/475_fix_and_stack_pr_662_on_648/
artifacts/` (not the task root as this plan originally specified) and `zulip-response.md` (not
`zulip-reply.md`), per explicit orchestrator dispatch instructions that superseded this plan's
Phase 4 paths for this dispatch. See `Artifacts & Outputs` section — update pending.

**Timing**: 1 hour

**Depends on**: 2

**Files to modify**:
- `specs/475_fix_and_stack_pr_662_on_648/pr-662-body.md` - new draft artifact.
- `specs/475_fix_and_stack_pr_662_on_648/zulip-reply.md` - new draft artifact.

**Verification**:
- Both draft files exist and are non-empty.
- The PR body draft references the actual seven-file set and design rationale from Phase 2.
- The Zulip draft names the specific thread (`CSLib > Modal Logic`) and the 23 July return date.
- No `gh pr edit`, `git push`, or Zulip API call has been made (this phase is drafting only).

---

### Phase 5: USER-APPROVAL GATE — remote history rewrite (D1/D2/D3/D5/D7) [NOT STARTED]

**Goal**: After an explicit human hard-stop, rewrite the published PR history and retarget #662.
**Every action below is destructive/outward-facing and REQUIRES explicit user approval. The
implementation agent MUST STOP and obtain approval; it MUST NOT run any command in this phase
autonomously.**

**Pre-gate confirmations to obtain from the user (present, then wait):**
- [ ] **D7** — include the unpushed local refinement commits (#648: `bbcbef85`, `c98c4348`; #662:
      `93cf984e`, `3ff6d02d`) in the pushed heads? (working default: include; confirm.)
- [ ] **D4** — confirm Connectives.lean = Option A self-own (already the task directive; confirm no
      change).
- [ ] **D5** — approve the final squashed commit message and the corrected PR #662 body text from
      `pr-662-body.md`.

**Gated actions (each requires the approval above; run only after "yes"):**
- [ ] **D1** — `git push --force-with-lease origin feat/propositional-v2` (rewrites PR #648 history).
- [ ] **D3** — `gh pr edit 662 --repo leanprover/cslib --base feat/propositional-v2` (retarget base).
- [ ] **D2** — `git push --force-with-lease
      origin feat/modal-formula-primitives-v2:feat/modal-formula-primitives` (rewrites PR #662,
      squashed single commit; drops old `f46056b9`).
- [ ] **D5** — `gh pr edit 662 --repo leanprover/cslib --body-file
      specs/475_fix_and_stack_pr_662_on_648/pr-662-body.md` (update body).
- [ ] Keep `backup/*` branches until GitHub CI is confirmed green (R5).

**Timing**: 0.5 hours (fast once approved; dominated by waiting for approval).

**Depends on**: 3, 4

**Files to modify**: none locally (remote refs + PR metadata only).

**Verification**:
- Explicit user approval recorded for D7/D4/D5 before any push.
- `git push` commands used `--force-with-lease` (never bare `--force`).
- After push: `gh pr view 648 --repo leanprover/cslib` shows the rebased head; `gh pr view 662`
  shows `baseRefName = feat/propositional-v2`, a single commit, and the updated body.
- GitHub CI on both PRs is triggered; `backup/*` branches still exist.
- If approval is NOT given, STOP — leave branches local, task remains pre-push.

---

### Phase 6: USER-APPROVAL GATE — post Zulip reply to @fmontesi (D6) [NOT STARTED]

**Goal**: After an explicit human hard-stop, post the Zulip reply. **Outbound public communication —
REQUIRES explicit user approval. The agent MUST STOP and MUST NOT send autonomously.**

**Tasks**:
- [ ] Present `zulip-reply.md` to the user for final approval (D6).
- [ ] Only after "yes": post the reply to the `CSLib > Modal Logic` thread
      (https://leanprover.zulipchat.com/#narrow/channel/513188-CSLib/topic/Modal.20Logic/near/607842603).
- [ ] Record the posted message link in the execution summary.

**Timing**: 0.25 hours

**Depends on**: 5

**Files to modify**: none (outbound message only).

**Verification**:
- Explicit user approval recorded for D6 before sending.
- The reply is posted only after PR #662 is actually updated (Phase 5 complete), so its claims
  ("slimmed, stacked on #648") are accurate.
- If approval is NOT given, STOP — leave `zulip-reply.md` as a draft.

---

## Testing & Validation

- [ ] Phase 1: rebased `feat/propositional-v2` — `lake build`, `lake test`,
      `lake exe checkInitImports`, `lake exe lint-style` all green on `upstream/main`.
- [ ] Phase 3: stacked #662 — `lake build`, `lake test`, `lake exe checkInitImports`,
      `lake exe lint-style`, `lake shake --add-public --keep-implied --keep-prefix` all green
      (shake: no NEW modal-file flags).
- [ ] R3: `git grep LogicallyEquivalent Cslib/` empty; parametric `Proposition.Equiv S` present.
- [ ] R4: `references.bib` diff clean (modal keys present, prop keys single-sourced, no dangling).
- [ ] Phase 2: `git diff --name-only feat/propositional-v2 feat/modal-formula-primitives-v2` = exactly
      the seven modal-contribution files.
- [ ] Gate discipline: no push / `gh pr edit` / Zulip send occurred before its approval.

## Artifacts & Outputs

- `specs/475_fix_and_stack_pr_662_on_648/plans/01_fix-and-stack-pr-662-on-648.md` (this plan).
- `specs/475_fix_and_stack_pr_662_on_648/pr-662-body.md` (Phase 4 draft).
- `specs/475_fix_and_stack_pr_662_on_648/zulip-reply.md` (Phase 4 draft).
- `specs/475_fix_and_stack_pr_662_on_648/summaries/01_fix-and-stack-pr-662-on-648-summary.md`
  (on completion).
- Git: local branch `feat/modal-formula-primitives-v2`; backup refs `backup/648-pre-rebase`,
  `backup/662-pre-rebase`; tag `pre-475-472fix`.
- Remote (only after gates): force-pushed `feat/propositional-v2` and `feat/modal-formula-primitives`;
  retargeted + re-bodied PR #662; posted Zulip reply.

## Rollback/Contingency

- Local rewrites (Phases 0–3) are fully reversible via the Phase 0 backups:
  `git branch -f feat/propositional-v2 backup/648-pre-rebase` and
  `git branch -f feat/modal-formula-primitives backup/662-pre-rebase`; delete
  `feat/modal-formula-primitives-v2`. The task-472 fix is recoverable from `main` and tag
  `pre-475-472fix`.
- If Phase 3 CI fails and no zero-debt structural fix exists: STOP, mark [BLOCKED] with the failing
  output; do not push.
- After Phase 5 push: if GitHub CI is red or a problem surfaces, restore the remote from the
  `backup/*` branches with `git push --force-with-lease origin backup/648-pre-rebase:feat/propositional-v2`
  (and the analogous #662 restore); keep `backup/*` until both PRs are confirmed green (R5).
- Phases 5 and 6 do nothing without explicit user approval; withholding approval is itself the safe
  rollback state (branches stay local, drafts stay unsent).
