# Implementation Plan: Task #440

- **Task**: 440 - review_pr_leanprover_cslib_648
- **Status**: [PR READY]
- **Effort**: 3 hours
- **Dependencies**: None
- **Research Inputs**: specs/440_review_pr_leanprover_cslib_648/reports/01_pr-review-research.md
- **Artifacts**: plans/01_ctchou-review-response.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: pr
- **Lean Intent**: false

## Overview

PR #648 (`feat/propositional-v2` -> `leanprover/cslib:main`) carries a standing
CHANGES_REQUESTED review from ctchou dated 2026-06-15 that has never been re-reviewed, despite
the 2026-06-29 rework and thomaskwaring's 2026-07-06 approval. The deliverable is
`pr-response.md`: a targeted `@ctchou` reply that consolidates what was addressed, re-poses the
one genuinely open judgment call (whether to drop the Gentzen citation entirely), and states the
#587/#607 coordination status accurately rather than aspirationally. Three of the four
outstanding items are already substantively resolved in the code; the work here is verification
plus composition, not Lean development. Definition of done: `pr-response.md` exists, every factual
claim in it is traceable to evidence gathered in Phases 1-3, and the task is `[PR READY]` for the
user to post via `/pr 440`.

### Research Integration

From `reports/01_pr-review-research.md`:
- **References**: `Avigad2022` is in `references.bib` and cited first in `NaturalDeduction/Basic.lean`
  (lines ~52 and ~63); `Gentzen1935`'s `title` was changed to the English "Investigations into
  Logical Deduction" (commit `1956d75b`). The literal "German title" complaint is fixed; whether to
  cite a 1930s paper at all remains ctchou's call, and the author already offered to drop it.
- **Semantics**: both `Semantics/Basic.lean` and `Semantics/Bool.lean` were removed outright at the
  PR head, oversatisfying ctchou's narrower "one is enough" ask. No `Semantics/` directory exists
  under `Cslib/Logics/Propositional/` on the PR branch.
- **Reply**: a 2026-06-30 comment already addresses `@ctchou`, but predates the 07-02 binder
  cleanup, the 07-13 docstring fixes, and thomaskwaring's 07-06 approval. ctchou has posted no
  review, comment, or reaction since 2026-06-15.
- **Coordination**: #536 merged 2026-06-16 and the branch is rebased on it. #587 and #607 are both
  still open, and the research found *no evidence* that reviews were actually left on them — the
  2026-06-30 comment's coordination claim is stated intent, not executed action. This is the single
  highest-risk claim to get wrong in a reply to a maintainer.
- **New fact not in the task description**: `mergeable_state: dirty` — the branch has merge
  conflicts against `main`. Asking for a re-review of an unmergeable branch wastes the reviewer's
  time, so the reply must acknowledge this.
- **Adjacent flag**: on Zulip (2026-06-22), Chris Henson raised an AI-drafting policy concern about
  a message of the author's. This directly shapes the Zulip non-goal below.

### Prior Plan Reference

No prior plan. This is the first plan for this task.

### Roadmap Alignment

`roadmap_path` was not supplied in the delegation context, so no roadmap consultation was performed
per the delegation contract. `specs/ROADMAP.md` exists and contains no item tracking upstream PR
#648 specifically; the propositional-bases entries it does carry describe library content, not
upstream review logistics. No roadmap items are advanced by this task.

## Goals & Non-Goals

**Goals**:
- Independently verify, against the PR head (`origin/feat/propositional-v2`), the reference and
  Semantics-removal claims before asserting them to a maintainer.
- Establish the true #587/#607 coordination status so the reply claims only what actually happened.
- Determine the concrete extent of the merge conflict so the reply can state it honestly.
- Compose `specs/440_review_pr_leanprover_cslib_648/pr-response.md` as a single, self-contained
  `@ctchou` reply that also serves as the re-review request.
- Leave the task at `[PR READY]` so the user can post it via `/pr 440`.

**Non-Goals**:
- **Performing the rebase or resolving the merge conflict.** The conflict is real and must be
  reported, but rebasing `feat/propositional-v2` rewrites a fork branch whose only useful outcome
  is a force-push, and `.claude/rules/pr-prohibition.md` forbids agent pushes. Phase 3 characterizes
  the conflict; the user decides and executes.
- **Posting to GitHub or Zulip.** `pr-response.md` is composed, not posted. Only user-invoked
  `/pr 440` posts it.
- **Composing `zulip-response.md`.** No `zulip_thread` source is declared in this task's `sources`
  array, so `pr-review-implementation-agent` Stage 6 does not trigger. Independently, the research
  surfaced a maintainer's AI-drafting policy objection on that exact Zulip thread, and the author
  committed to avoiding AI drafting there. Auto-drafting a Zulip message would run against both the
  source contract and that commitment. If a Zulip reply is wanted, the user should write it directly.
- **Any Lean proof work, or changes to `Defs.lean` / `NaturalDeduction/*.lean`.** Nothing in
  ctchou's review requires code changes that are not already made.
- **Resolving `imp` vs `impl` naming.** Explicitly deferred to post-#607 by thomaskwaring and the
  author; not blocking, and not ctchou's stated concern.
- **Dropping the `Gentzen1935` citation unilaterally.** It is ctchou's judgment call; the reply
  re-poses it rather than pre-empting it.

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Reply claims #587/#607 coordination that never happened, damaging author credibility with a maintainer | H | M | Phase 2 verifies via `gh` before any claim is written; Phase 5 blocks on the claim matching Phase 2 evidence |
| Working tree is on `main`, so files "verified" are main's versions, not the PR head's | H | M | Phase 1 reads exclusively via `git show origin/feat/propositional-v2:<path>` — never the working tree |
| `origin/feat/propositional-v2` is stale relative to the real PR head (`4834be23`) | M | M | Phase 1 fetches origin first and records the resolved SHA; if it differs from `4834be23`, re-verify via `gh pr view 648 --json headRefOid` and note the discrepancy in the reply |
| Reply asks for re-review while the branch is unmergeable, wasting reviewer time | M | H (already true) | Phase 3 characterizes the conflict; Phase 4 states it up front and frames the re-review request around it |
| An agent attempts the rebase and force-push to "help" | H | L | Declared non-goal above; Phase 3 tasks are read-only (`git merge-tree`, no checkout, no push) |
| Reply duplicates the 2026-06-30 comment and reads as noise | M | M | Phase 4 explicitly diffs against the 2026-06-30 comment and leads with what is *new* since it |
| `gh` is unauthenticated or rate-limited in this environment | M | L | `gh` v2.96.0 is on PATH and was used successfully during research; on failure, mark the affected claim unverified and hedge the reply wording rather than guessing |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1, 2, 3 | -- |
| 2 | 4 | 1, 2, 3 |
| 3 | 5 | 4 |

Phases within the same wave can execute in parallel.

### Phase 1: Verify reference and Semantics claims at the PR head [COMPLETED]

**Goal**: Confirm, against the actual PR head rather than the local working tree, that the Avigad
reference is present and leading, that no German-language title remains, and that no `Semantics/`
directory exists — producing citable line references for the reply.

**Tasks**:
- [ ] `git fetch origin feat/propositional-v2` and record the resolved SHA of
      `origin/feat/propositional-v2`
- [ ] Cross-check that SHA against `gh pr view 648 --json headRefOid --jq .headRefOid`; note any
      mismatch as a caveat for the reply
- [ ] `git show origin/feat/propositional-v2:references.bib` — confirm the `Avigad2022` entry exists
      and record its fields; confirm the `Gentzen1935` `title` field reads "Investigations into
      Logical Deduction"
- [ ] `git show origin/feat/propositional-v2:Cslib/Logics/Propositional/NaturalDeduction/Basic.lean`
      — record the exact line numbers and verbatim text of the reference list and the Gentzen citation
- [ ] `git ls-tree -r --name-only origin/feat/propositional-v2 -- Cslib/Logics/Propositional/` —
      confirm no path under `Semantics/` is present
- [ ] Grep the same tree for any residual non-ASCII/German-language citation text
- [ ] Record findings as a short evidence note for Phase 4 (in-context; no separate artifact file)

**Timing**: 0.5 hours

**Depends on**: none

**Files to modify**:
- None (read-only verification)

**Verification**:
- The resolved PR-head SHA is recorded, along with whether it matches `4834be23`
- Exact line numbers for the Avigad-first reference list and the Gentzen citation are captured
- The absence of `Semantics/` at the PR head is confirmed by tree listing, not inference

---

### Phase 2: Verify #587 / #607 coordination status [COMPLETED]

**Goal**: Determine whether benbrastmckie has in fact reviewed #587 and #607, so the reply
distinguishes executed coordination from stated intent.

**Tasks**:
- [ ] `gh pr view 587 --repo leanprover/cslib --json state,mergeable,reviews,comments` and inspect
      for any review or comment authored by `benbrastmckie`
- [ ] Same for `gh pr view 607 --repo leanprover/cslib --json state,mergeable,reviews,comments`
- [ ] Confirm #536 is merged (`gh pr view 536 --repo leanprover/cslib --json state,mergedAt`) so the
      "rebased on #536" claim stands
- [ ] Classify each of #587/#607 as: reviewed by author / commented only / no engagement
- [ ] Draft the exact one-sentence coordination wording the reply will use, matched to that
      classification — no aspirational phrasing

**Timing**: 0.5 hours

**Depends on**: none

**Files to modify**:
- None (read-only verification)

**Verification**:
- Each of #587 and #607 has a definite classification backed by `gh` output
- The drafted coordination sentence claims exactly what the evidence supports; if no review exists,
  the wording is "the design overlap was removed; I intend to review these" rather than implying
  completed cross-review

---

### Phase 3: Characterize the merge conflict (read-only) [COMPLETED]

**Goal**: Establish which files conflict between `origin/feat/propositional-v2` and current
`upstream/main`, so the reply can state the rebase situation concretely without performing it.

**Tasks**:
- [ ] `git fetch upstream main`
- [ ] `git merge-base origin/feat/propositional-v2 upstream/main` — record how far behind the branch is
- [ ] `git merge-tree --write-tree origin/feat/propositional-v2 upstream/main` (or the three-arg form
      on older git) to enumerate conflicting paths **without checking out or modifying the working tree**
- [ ] Confirm current mergeability via `gh pr view 648 --json mergeable,mergeStateStatus`
- [ ] Summarize scope in one or two sentences: which files conflict, and whether the conflict looks
      mechanical (e.g. `references.bib` adjacency) or substantive
- [ ] Explicitly do NOT check out the branch, rebase, reset, or push

**Timing**: 0.5 hours

**Depends on**: none

**Files to modify**:
- None (read-only; working tree must remain on `main` and clean)

**Verification**:
- A concrete list of conflicting paths exists, or a definite "no conflicts found locally" with the
  `gh` mergeable field noted alongside it
- `git status --porcelain` is unchanged from before the phase
- No rebase, checkout, reset, or push was performed

---

### Phase 4: Compose pr-response.md [COMPLETED]

**Goal**: Write the `@ctchou` reply as a single self-contained comment that leads with what changed
since the unanswered 2026-06-30 comment and closes with an explicit re-review request.

**Tasks**:
- [ ] Write `specs/440_review_pr_leanprover_cslib_648/pr-response.md` following the
      `pr-review-implementation-agent` Stage 5 template (PR header, Changes Made, Response to
      Reviewers grouped by reviewer, Remaining Questions, Summary)
- [ ] Under "Changes Made": state "No code changes were required based on this review" — the review's
      asks were satisfied by the 2026-06-29 rework already on the branch
- [ ] Under ctchou's section, quote each of the four review points verbatim as blockquotes and answer
      each: (a) `⊥`-as-primitive — acknowledged as agreed, with the efq compromise noted;
      (b) Semantics redundancy — resolved by removing both files, with Phase 1 tree evidence;
      (c) references — Avigad2022 added and cited first with the Phase 1 line reference, Gentzen1935
      now cited by its English translation title, and the open offer to drop it entirely restated as a
      direct question; (d) coordination — #536 merged and rebased, plus the Phase 2 wording for #587/#607
- [ ] Add a short section noting thomaskwaring's 2026-07-06 approval and that the 07-02/07-13 commits
      landed after the 2026-06-30 comment ctchou has not responded to
- [ ] State the merge-conflict situation from Phase 3 plainly, with the intent to rebase before merge
- [ ] Close with an explicit, courteous re-review request
- [ ] Keep the `imp`/`impl` naming question out of the body except as a one-line note that it is
      deferred to post-#607
- [ ] Do not include AI-tooling meta-commentary; the PR body's existing "AI Tools Used" disclosure
      already covers it

**Timing**: 1 hour

**Depends on**: 1, 2, 3

**Files to modify**:
- `specs/440_review_pr_leanprover_cslib_648/pr-response.md` - created (the deliverable)

**Verification**:
- File exists and is non-empty
- All four of ctchou's review points are quoted verbatim and individually answered
- The Gentzen question is posed as an explicit question, not resolved unilaterally
- The merge conflict is mentioned
- The document ends with a re-review request

---

### Phase 5: Cross-check claims and finalize [COMPLETED]

**Goal**: Ensure no unverified assertion reaches a maintainer, and hand off cleanly for `/pr 440`.

**Tasks**:
- [ ] Walk each factual claim in `pr-response.md` back to its Phase 1/2/3 evidence; hedge or delete
      any claim that cannot be traced
- [ ] Specifically re-read the #587/#607 sentence against Phase 2's classification — this is the
      claim most likely to overstate
- [ ] Confirm no task numbers, `specs/` paths, or internal agent-system references appear in
      `pr-response.md` (it is outward-facing content quoted into a public PR)
- [ ] Confirm `git status --porcelain` shows no unintended working-tree changes outside
      `specs/440_review_pr_leanprover_cslib_648/`
- [ ] Confirm no branch, push, or `gh pr` write operation was performed at any point
- [ ] Write the implementation summary to
      `specs/440_review_pr_leanprover_cslib_648/summaries/01_ctchou-review-response-summary.md`

**Timing**: 0.5 hours

**Depends on**: 4

**Files to modify**:
- `specs/440_review_pr_leanprover_cslib_648/pr-response.md` - corrections from the cross-check
- `specs/440_review_pr_leanprover_cslib_648/summaries/01_ctchou-review-response-summary.md` - created

**Verification**:
- Every claim traces to recorded evidence, or is hedged
- No outward-facing task-number or internal-path references in `pr-response.md`
- Task is ready to transition to `[PR READY]` by the skill's postflight

---

## Testing & Validation

- [ ] `pr-response.md` exists, is non-empty, and parses as valid Markdown
- [ ] All four ctchou review points appear as verbatim blockquotes with individual responses
- [ ] Every line/file reference cited in the reply resolves at `origin/feat/propositional-v2`
- [ ] The #587/#607 sentence matches Phase 2's classification exactly
- [ ] The merge-conflict status is stated and matches `gh pr view 648 --json mergeable`
- [ ] `pr-response.md` contains no `specs/` paths, task numbers, or agent-system terminology
- [ ] No `.lean` file, `references.bib`, or any repository source file was modified
- [ ] `git status --porcelain` shows changes only under `specs/440_review_pr_leanprover_cslib_648/`
- [ ] No `git push`, `git rebase`, `git checkout` of the PR branch, or `gh pr create` was executed

## Artifacts & Outputs

- `specs/440_review_pr_leanprover_cslib_648/plans/01_ctchou-review-response.md` (this plan)
- `specs/440_review_pr_leanprover_cslib_648/pr-response.md` (primary deliverable)
- `specs/440_review_pr_leanprover_cslib_648/summaries/01_ctchou-review-response-summary.md`
- Task status transitions to `[PR READY]`; the user posts via `/pr 440`

## Rollback/Contingency

All phases except Phase 4 and Phase 5 are read-only, so rollback is confined to deleting
`pr-response.md` and the summary — no repository source file is touched, and the working tree stays
on `main`. If Phase 1 finds the local `origin/feat/propositional-v2` ref materially diverges from the
live PR head, stop and re-run research rather than compose a reply against stale evidence. If Phase 2
cannot reach GitHub, compose the reply with the #587/#607 sentence omitted entirely rather than
guessed — an absent claim is recoverable, a false one posted to a maintainer is not. If the merge
conflict in Phase 3 turns out to be substantive rather than mechanical, the reply should say so and
defer the re-review request until after the rebase, since a re-review of an unmergeable branch would
be immediately stale.
