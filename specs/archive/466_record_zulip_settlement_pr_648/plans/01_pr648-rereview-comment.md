# Implementation Plan: Task #466 — Draft PR #648 re-review comment

- **Task**: 466 - record_zulip_settlement_pr_648
- **Status**: [COMPLETED]
- **Effort**: 1.25 hours
- **Dependencies**: None
- **Research Inputs**: reports/01_pr-review-research.md
- **Artifacts**: plans/01_pr648-rereview-comment.md (this file)
- **Standards**:
  - .claude/rules/artifact-formats.md
  - .claude/rules/state-management.md
  - .claude/rules/git-workflow.md
- **Type**: pr
- **Lean Intent**: false

## Overview

Task #466 closes one precise gap on PR #648: the already-posted 2026-06-30 GitHub
comment references "the CSLib Zulip thread" only in prose, without a permalink to the
message where the `⊥`/`efq` design was actually settled. This plan produces a single
reviewable **draft** GitHub PR comment file that addresses ctchou, links Thomas Waring's
settlement permalink, recaps how the three CHANGES_REQUESTED items were resolved, and
requests a re-review. **This task is DRAFT-ONLY**: no phase pushes the branch, posts the
comment, or runs any `gh`/`git`/`zulip` write command. Definition of done is a committed
draft file plus this plan and the execution summary. Posting and pushing happen later via
`/pr` under explicit user approval and are out of scope for `/implement`.

### Research Integration

The research report (`reports/01_pr-review-research.md`) is the sole and complete input.
Key facts carried into the draft:
- **Settlement permalink** (primary): Thomas Waring, 2026-06-28, message 606970606 —
  `https://leanprover.zulipchat.com/#narrow/channel/513188-CSLib/topic/Propositional.20Logic/near/606970606`
- **Optional acceptance permalink**: benbrastmckie, 2026-06-29, message 607217129 —
  `https://leanprover.zulipchat.com/#narrow/channel/513188-CSLib/topic/Propositional.20Logic/near/607217129`
- **Do NOT link** message 604219492 (Benjamin's own 2026-06-17 position statement, not the
  settlement — a documented common mistake).
- ctchou's three CHANGES_REQUESTED items (2026-06-15) and their resolutions (report's
  "Requested Changes" table): references (Avigad 2022 cited first, German titles
  de-emphasized/English-glossed), semantics (both `Semantics/` files removed from the PR,
  which also answers "why both files"), coordination (#536 merged and rebased; #587/#607
  overlap resolved by removing semantics/connectives from #648).
- **Pushed-vs-local distinction**: GitHub head is `c9364b65`; two polish commits
  `bbcbef85` and `c98c4348` are local-only and unpushed (design-neutral polish only). The
  safest framing is push-then-comment, so the draft can describe a settled state without
  hedging. Documenting this ordering is in scope; executing the push is not.
- No re-review from ctchou since 2026-06-15 despite two rounds of rework.
- House-style sensitivity: the CSLib Zulip has an AI-content policy (flagged by Chris
  Henson, 2026-06-22). The draft must read as plain first-person prose in Benjamin's voice.

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

`roadmap_flag` is false; no roadmap phases required. ROADMAP.md was not consulted for phase
structure. This task advances the PR #648 review-closure workstream but adds no roadmap
items.

## Goals & Non-Goals

**Goals**:
- Produce one committed draft file (`pr-comment-draft.md`) containing the exact comment
  text Benjamin will paste into GitHub.
- Draft addresses ctchou, links the 606970606 settlement permalink, recaps the three-item
  resolution, and explicitly requests a re-review.
- Draft reads as concise, plain, first-person prose (no LLM-tells, minimal bullet lists in
  the comment body itself).
- Capture open decisions and the push-before-post ordering in a separate reviewer-notes
  section so the user decides at review time.

**Non-Goals**:
- Posting the comment to GitHub (out of scope — handled later via `/pr`).
- Pushing `feat/propositional-v2` or running any `git`/`gh`/`zulip` write command.
- Resolving the open decisions unilaterally (Waring @-mention, 606970606-only vs. also
  607217129, push ordering) — these are surfaced for the user, not decided.
- Editing PR source files, `references.bib`, or any Lean code.
- Re-fetching GitHub or Zulip; the research report is authoritative.

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Accidentally linking 604219492 instead of the settlement | M | L | Phase 2 verifies every permalink/SHA against the report; the wrong link is explicitly enumerated as forbidden |
| Draft reads as LLM-generated, tripping the Zulip AI-content sensitivity | M | M | Phase 1 mandates first-person plain prose, minimal bullets, concise voice; Phase 2 re-reads for tone |
| Comment describes local-only polish as if on GitHub, causing reviewer confusion | M | M | Draft uses push-then-comment framing; reviewer-notes records "push feat/propositional-v2 before posting so GitHub head matches" as a user prerequisite |
| An implementation step performs a write operation | H | L | Plan forbids all writes; the only file operations are creating the draft `.md` and the summary; Rollback section confirms nothing is posted |
| Over-claiming ctchou's items are "resolved" without his sign-off | L | M | Draft frames items as "addressed" and notes no re-review has occurred since 2026-06-15, not as maintainer-confirmed |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2 | 1 |

Phases within the same wave can execute in parallel.

### Phase 1: Compose the draft comment body [COMPLETED]

**Goal**: Write the exact GitHub-comment prose Benjamin will paste, addressing ctchou,
first-person and concise, with the correct settlement permalink and the three-item recap.

**Tasks**:
- [ ] Create `specs/466_record_zulip_settlement_pr_648/pr-comment-draft.md`.
- [ ] Write the comment body as plain first-person prose (Benjamin's voice), opening by
      addressing ctchou and noting there has been no re-review since the 2026-06-15
      CHANGES_REQUESTED despite two rounds of rework.
- [ ] Link the settlement permalink inline:
      `https://leanprover.zulipchat.com/#narrow/channel/513188-CSLib/topic/Propositional.20Logic/near/606970606`
      (Thomas Waring's compromise, 2026-06-28), framing it as the agreed `⊥`-primitive +
      `efq`-rule design that postdates the original review.
- [ ] Briefly recap the resolution of the three CHANGES_REQUESTED items in prose (not a
      heavy bullet list): (a) references — Avigad 2022 now cited first, German-title papers
      de-emphasized/English-glossed; (b) semantics — both `Semantics/` files removed from
      the PR (deferred to a follow-up), which also answers the "why both files" question;
      (c) coordination — #536 merged and branch rebased, #587/#607 overlap resolved by
      removing semantics/connectives from #648.
- [ ] Phrase the described PR state as push-then-comment (i.e., assume the branch is pushed
      first) so the text is accurate without hedging; keep design-neutral polish
      (`bbcbef85`, `c98c4348`) out of the design narrative.
- [ ] End with an explicit, courteous request for a re-review from ctchou.

**Timing**: 45 minutes

**Depends on**: none

**Files to modify**:
- `specs/466_record_zulip_settlement_pr_648/pr-comment-draft.md` - new draft comment file
  (comment body section).

**Verification**:
- Draft file exists and contains the settlement permalink `.../near/606970606` exactly.
- Comment addresses ctchou and contains an explicit re-review request.
- All three CHANGES_REQUESTED items are recapped.
- Message 604219492 does NOT appear anywhere in the comment body.
- No `gh`, `git`, or `zulip` command was run; no write to GitHub/Zulip occurred.

---

### Phase 2: Add reviewer notes and verify facts [COMPLETED]

**Goal**: Append a "Reviewer notes / decisions" section (separate from the comment body)
capturing the open decisions and push-before-post ordering, and verify all permalinks and
SHAs against the research report.

**Tasks**:
- [ ] In the same `pr-comment-draft.md`, add a clearly separated "Reviewer notes /
      decisions" appendix (explicitly marked as NOT part of the text to paste).
- [ ] Record the three open decisions for the user to settle at review time: (a) whether to
      also @-mention Thomas Waring, given his "I'll review properly once the design settles"
      commitment; (b) whether to link only 606970606 or also the acceptance 607217129;
      (c) confirm push-before-post ordering.
- [ ] Add the ordering note verbatim in intent: "push `feat/propositional-v2` before posting
      so GitHub head matches" — as documentation for the user, NOT an executed action.
      Note that GitHub head is currently `c9364b65` and commits `bbcbef85`, `c98c4348` are
      local-only polish.
- [ ] Verify against `reports/01_pr-review-research.md`: settlement permalink 606970606,
      optional acceptance 607217129, forbidden link 604219492, head SHA `c9364b65`, unpushed
      SHAs `bbcbef85`/`c98c4348`, PR number #648, coordinated PRs #536/#587/#607.
- [ ] Re-read the comment body for tone: concise, first-person, no LLM-tells, minimal bullet
      lists in the pasteable portion.

**Timing**: 30 minutes

**Depends on**: 1

**Files to modify**:
- `specs/466_record_zulip_settlement_pr_648/pr-comment-draft.md` - append reviewer-notes
  appendix; no change to the comment body beyond tone fixes.

**Verification**:
- Reviewer-notes section exists, is clearly separated from the pasteable comment body, and
  lists all three open decisions plus the push-before-post ordering note.
- Every permalink and SHA in the draft matches the research report exactly.
- Comment body tone re-confirmed as plain first-person prose.
- Still no write operations of any kind performed.

## Testing & Validation

- [ ] `pr-comment-draft.md` exists under `specs/466_record_zulip_settlement_pr_648/`.
- [ ] The comment body links `.../near/606970606` and does not link `.../near/604219492`.
- [ ] The comment addresses ctchou and explicitly requests a re-review.
- [ ] All three CHANGES_REQUESTED items (references, semantics, coordination) are recapped.
- [ ] Reviewer-notes appendix records the three open decisions and the push-before-post
      ordering, clearly separated from the pasteable text.
- [ ] No `gh`/`git`/`zulip` write command appears in the execution transcript; nothing was
      posted or pushed.
- [ ] Draft reads as concise first-person prose consistent with the Zulip AI-content policy.

## Artifacts & Outputs

- `specs/466_record_zulip_settlement_pr_648/pr-comment-draft.md` — the draft GitHub PR
  comment (pasteable body + reviewer-notes appendix).
- `specs/466_record_zulip_settlement_pr_648/plans/01_pr648-rereview-comment.md` — this plan.
- `specs/466_record_zulip_settlement_pr_648/summaries/01_*-summary.md` — execution summary
  (produced by `/implement`).

## Rollback/Contingency

Nothing to roll back: this task performs no writes to GitHub, Zulip, or the git branch. The
only outputs are local draft/plan/summary files. If the draft is unsatisfactory, edit or
delete `pr-comment-draft.md` and re-run — no external state is affected. Posting the comment
and pushing `feat/propositional-v2` are deferred entirely to the separate `/pr` command
under explicit user approval, and are out of scope here.
