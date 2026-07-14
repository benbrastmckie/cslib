# Implementation Plan: Task #476 — Divide Modal PRs & Coordinate with #607

- **Task**: 476 - divide_modal_prs_coordinate_607
- **Status**: [IMPLEMENTING]
- **Effort**: ~4.75 hours (Phases 4-5 conditional; gated on external agreement)
- **Dependencies**: Task 475 (`specs/475_fix_and_stack_pr_662_on_648/`)
- **Research Inputs**: `specs/476_divide_modal_prs_coordinate_607/reports/01_divide-modal-prs.md`
- **Artifacts**: plans/02_divide-modal-prs.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: cslib

## Overview

This is a **coordination task, not a code-first task**. Four overlapping modal/connective PRs
(#607, #648, #649, #662) share one real conflict point — the `Modal/Basic.lean` primitive
constructor set — and the deciding call belongs to maintainer @fmontesi, who is the author of the
earlier PR #607 and **returns 23 July**. The plan produces two human-approval-pending draft
communications (a polished #607 review comment and a Zulip coordination note), then **holds**: no
GitHub or Zulip posting, and no touching of any branch, happens without EXPLICIT user approval, and
the substantive #662 code migration is GATED behind (a) design agreement on box-vs-diamond and (b)
#607's operator layer landing. Definition of done for the unblocked portion: two reviewed drafts
exist and the gate/contingency structure is recorded; the conditional migration phases remain
[NOT STARTED] until the gate opens.

### Research Integration

- **PR-state table & overlap matrix** (research §1, §1.1): only #607↔#662 hard-conflict on
  `Modal/Basic.lean`; #648/#649 overlaps are soft/reconcilable.
- **#607 CI is upstream drift, not #607's fault** (research §4.3): the red `ci-checks` is
  `HML/LogicalEquivalence.lean` failing because #607 is ~15 commits behind `main`; a rebase clears
  it. This framing leads the #607 review.
- **DRAFT #607 review** (research §4.4) and **DRAFT Zulip note** (research §7) are the seeds for
  Phases 1-2.
- **Box-vs-diamond tradeoff table** (research §5) is fmontesi's maintainer decision, surfaced with
  tradeoffs, never asserted.
- **Conditional 7-step migration** (research §6) is the gated body of Phases 4-5.

### Prior Plan Reference

No prior plan for task 476. Task 475 is the substantive predecessor: it stacked #662 on #648 with a
**self-owned** `Foundations/Logic/Connectives.lean` (Option A) precisely to avoid coupling #662 to
the unmerged #607, and established the gated-force-push discipline (task-475 §11 gates) plus the
already-drafted, approval-pending Zulip response reused as a base here. Effort calibration: task 475
confirmed that coordination/drafting work is fast but the *posting* and *push* steps are the risk
surface and must stay behind explicit user gates.

### Roadmap Alignment

No ROADMAP.md consulted for this task (no roadmap_path in delegation context).

### Naming decision (USER DIRECTIVE — resolves research §8 open question)

Use **`imp`**, NOT `impl`, throughout. This resolves the `HasImpl.impl` (#607) vs `HasImp.imp`
(#662/#648) open decision (research §2.5, §8/D1) in favor of `imp` (matches `impI`/`impE` rule
prefixes and FormalizedFormalLogic). Consequences baked into this plan:
- The #662 migration imports the operator layer as `Operators/{Box,Imp,Bot}` (`imp` spelling).
- #607 currently ships `Operators/Impl.lean`; because #607 is @fmontesi's PR, any rename toward
  `imp` is framed **only as a suggestion to him** in the review comment — never a direct edit to his
  branch. `imp` is treated as the target convention that downstream (#648/#649/#662) conform to.

## Goals & Non-Goals

**Goals**:
- Produce a polished, human-approval-pending **#607 review comment** (Phase 1) that leads with
  what's good, makes the CI-drift-is-not-#607's-fault point, and offers concrete help
  (`HasBot` + `PropositionalConnectives`/`ModalConnectives` bundles, `imp` naming suggestion).
- Produce a polished, human-approval-pending **Zulip coordination note** (Phase 2) framing the
  box-vs-diamond decision as fmontesi's maintainer call with the §5 tradeoff summary, and proposing
  the clean layer-ownership division.
- Establish an explicit **HOLD gate** (Phase 3): nothing posted to GitHub/Zulip and no branch
  touched without EXPLICIT user approval; migration waits for design agreement + #607 landing.
- Record the **conditional #662-on-#607 migration** (Phases 4-5) as a fully specified but
  blocked-until-approval sequence, ready to execute post-agreement.

**Non-Goals**:
- Posting anything to GitHub or Zulip in this planning/execution cycle (gated on user approval).
- Editing, rebasing, or pushing to #607's branch (`fmontesi/connectives`) — ever.
- Making the box-vs-diamond decision on fmontesi's behalf (offer tradeoffs, do not assert).
- Coupling #662 to the still-unmerged #607 before the gate opens (task 469's avoided anti-pattern).
- Rebasing #649 (out of scope here; noted as downstream-of-#648/#607 future work).

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Editing/pushing/rebasing #607 (@fmontesi's PR) | H | L | HARD CONSTRAINT: coordinate ONLY via review comment / Zulip; NEVER push, rebase, or edit `fmontesi/connectives`. Encoded in Phases 1, 3, and every gate. |
| Posting a draft to GitHub/Zulip without approval | H | M | Drafts stay in-repo; Phase 3 gate requires EXPLICIT user approval before any post; posting is a manual gated step, never automated. |
| Prematurely coupling #662 to unmerged #607 | H | M | Phase 4 precondition (hard gate): migration blocked until fmontesi agrees direction AND #607's operator layer lands; until then #662 keeps its self-owned `Connectives.lean` (task-475 Option A). |
| Force-push to #662/#648 without approval | H | L | Any `--force-with-lease` is a gated Phase 5 step requiring EXPLICIT user approval; `backup/*` branches retained until GitHub CI green (task-475 §11 gates D1-D7). |
| Local build/test mutating a real working branch | M | L | HARD CONSTRAINT: all local build/test runs happen in a THROWAWAY worktree only; never on the live checkout or a tracked branch. |
| Advocating `impl` and contradicting the user directive | M | L | `imp` is fixed by user directive; imports use `Operators/{Box,Imp,Bot}`; the #607 rename is framed as a suggestion to fmontesi, not an edit. |
| Draft claims go stale before posting (e.g. #607 rebased, #662 retargeted) | M | M | Re-verify claims against live PR state at approval time (task-475 zulip-response pattern: only post after the described actions are true). |
| box-vs-diamond decision stalls past 23 July | M | M | Gate is time-tolerant: drafts note "no rush, you're back on the 23rd"; migration simply stays [NOT STARTED]; offer a CSLib meeting to unblock. |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1, 2 | -- |
| 2 | 3 | 1, 2 |
| 3 | 4 | 3 |
| 4 | 5 | 4 |

Phases within the same wave can execute in parallel. Phases 1 and 2 are independent drafting tasks.
Phases 4 and 5 are CONDITIONAL and remain [NOT STARTED] until the Phase 3 gate opens (design
agreement reached, #607 landed, and explicit user approval given).

### Phase 1: Draft #607 review comment [COMPLETED]

**Completed**: 2026-07-03T12:07:16Z

**Goal**: Produce a polished, human-approval-pending review comment for PR #607 building on research
§4.4 — leading with what's good, making the CI-drift point, and offering concrete help.

**Tasks**:
- [x] Write draft to `specs/476_divide_modal_prs_coordinate_607/artifacts/pr-607-review.md` (create
      `artifacts/` lazily).
- [x] Lead with genuine praise (research §4.1): clean one-class-per-operator layer, the
      `@[scoped grind =] _def` bridge-lemma pattern, Mathlib `Bot`/`Top` reuse, readable `rfl`
      characterisations.
- [x] Make the **CI-drift-is-not-#607's-fault** point (research §4.3): red `ci-checks` is
      `HML/LogicalEquivalence.lean` failing because the branch is ~15 commits behind `main` (Mathlib
      bumps + `Relation` split already fixed HML on `main`); a rebase onto `main` should turn it
      green. Frame as friendly and low-effort.
- [x] Offer the `HasBot` class plus bundled `PropositionalConnectives`/`ModalConnectives` classes
      (research §2.3) so the operator layer lands complete in #607 and everything downstream imports
      it — answering the chenson2018/ctchou "should these be bundled?" and eric-wieser "one file"
      threads.
- [x] Surface the **`imp` naming suggestion**: note `HasImpl.impl` (#607) vs `HasImp.imp`
      (downstream), state a lean toward `imp` with rationale, and explicitly frame it as **his call
      as owner of the layer** / a suggestion — NOT a code edit on his branch.
- [x] Reference the separate box-vs-diamond modal question (defer detail to the Zulip note).
- [x] Add a header banner: DRAFT — do NOT post; requires EXPLICIT user approval; post #1 as plain
      comment and #2-#4 as review discussion, never as code "suggestions" on his branch.

**Timing**: 1 hour

**Depends on**: none

**Files to modify**:
- `specs/476_divide_modal_prs_coordinate_607/artifacts/pr-607-review.md` - new draft (in-repo only)

**Verification**:
- Draft exists, leads with praise, contains the CI-drift framing, the bundle offer, the `imp`
  suggestion (framed as suggestion-to-fmontesi), and a DRAFT/approval-required banner.
- No GitHub API mutation performed; nothing posted.

---

### Phase 2: Draft Zulip coordination note [COMPLETED]

**Completed**: 2026-07-03T12:07:16Z

**Goal**: Produce a polished, human-approval-pending Zulip note building on research §7, framing the
box-vs-diamond decision as fmontesi's maintainer call and proposing the clean ownership division.

**Tasks**:
- [x] Write draft to `specs/476_divide_modal_prs_coordinate_607/artifacts/zulip-coordination.md`,
      reusing the task-475 `zulip-response.md` as the stylistic base.
- [x] Acknowledge the "one at a time" / PR-size-overwhelm ask; note the modal work is now split
      cleanly: operator layer = #607 (his), modal semantics = #662, propositional = #648, LTL = #649
      (downstream) — research §2 layer map.
- [x] Present the **box-vs-diamond primitive** choice as *his* maintainer call, attaching the §5
      tradeoff summary (necessitation/K purity, `⊥`/free-algebra, IK/CK forward-compat vs. minimal
      near-term churn / `rfl` characterisations). Offer, do not assert; note downstream #648/#662
      already point box-primitive and are CI-green.
- [x] Offer the prototyped `HasBot` + bundled classes for #607; propose the clean ownership division
      as a concrete suggestion.
- [x] Keep it short, defer to him on ordering and naming (`imp` mentioned but his call); offer to
      sync at a CSLib meeting after the 23rd.
- [x] Add a header banner: DRAFT — not posted; requires EXPLICIT user approval AND must only be sent
      after any described PR actions are actually true at post time (task-475 accuracy discipline).

**Timing**: 0.75 hour

**Depends on**: none

**Files to modify**:
- `specs/476_divide_modal_prs_coordinate_607/artifacts/zulip-coordination.md` - new draft (in-repo)

**Verification**:
- Draft exists, frames box-vs-diamond as fmontesi's call with §5 tradeoffs, proposes ownership
  division, offers the bundles, includes DRAFT/approval-required banner.
- Nothing posted to Zulip.

---

### Phase 3: Approval & coordination gate (HOLD) [NOT STARTED]

**Goal**: Explicit HOLD point. Govern any posting of the Phase 1-2 drafts (only after EXPLICIT user
approval) and hold the #662 migration until design direction is agreed and #607's operator layer
lands. This phase is a checkpoint, not automated work.

**Tasks**:
- [ ] Present both drafts (pr-607-review.md, zulip-coordination.md) to the user for review.
- [ ] HOLD: post NOTHING to GitHub or Zulip and touch NO branch until the user EXPLICITLY approves.
- [ ] If/when the user approves posting: re-verify each draft's factual claims against live PR state
      (e.g. #607 not yet rebased, #662 still stacked as described) before posting; post the #607
      review via review/comment only (never a code suggestion on his branch) and/or send the Zulip
      note.
- [ ] Record the outstanding external preconditions that gate Phases 4-5: (a) fmontesi agrees the
      box-primitive direction (or a joint plan is settled), AND (b) #607's operator layer lands on
      `main` (or is stable enough to target). fmontesi returns 23 July.
- [ ] Do NOT open Phases 4-5 until both preconditions hold AND the user explicitly approves starting
      the migration.

**Timing**: 0.5 hour (excluding indefinite external wait)

**Depends on**: 1, 2

**Files to modify**:
- None (checkpoint / optional gated posting of existing drafts)

**Verification**:
- No GitHub/Zulip post occurred without a recorded explicit user approval.
- No branch was rebased/pushed/edited.
- The two external preconditions for Phases 4-5 are recorded and confirmed unmet-or-met before
  proceeding.

---

### Phase 4: Conditional #662-on-#607 migration — restructure [NOT STARTED, BLOCKED until gate]

**Goal**: (POST-AGREEMENT ONLY) In a THROWAWAY worktree, rebase #662 onto landed #607/main and
restructure it to import #607's operator layer, per research §6 steps 1-5. Every task below is
blocked-until-approval and must not begin until the Phase 3 gate opens.

**Tasks** (all blocked-until-approval):
- [ ] BLOCKED-UNTIL-APPROVAL: Confirm Phase 3 preconditions (fmontesi direction agreed; #607 operator
      layer landed) and obtain explicit user go-ahead.
- [ ] BLOCKED-UNTIL-APPROVAL: Create a THROWAWAY worktree/backup branch; all work happens there.
- [ ] Step 1 — Rebase #662 onto landed #607/main
      (`git rebase --onto <607-merged-main> e0573fbc feat/modal-formula-primitives`, or rebuild on
      the #648 stack per task-475 §10); resolve Mathlib-bump drift.
- [ ] Step 2 — `git rm Cslib/Foundations/Logic/Connectives.lean` (interim self-owned file; role now
      filled by #607's `Operators/*` + bundles).
- [ ] Step 3 — Re-point `Modal/Basic.lean` imports: replace
      `public import Cslib.Foundations.Logic.Connectives` with
      `public import Cslib.Foundations.Logic.Operators.{Box,Imp,Bot}` (+ `And`/`Or`/`Not` as needed),
      matching #607's `Cslib.Logic` namespace and the **`imp`** spelling (per user directive).
- [ ] Step 4 — Register `ModalConnectives` for `Modal.Proposition` against #607's classes (or the
      accepted bundle); adjust `not`/`diamond` derivations to #607's `HasBox`/`HasImp` API (`imp`).
- [ ] Step 5 — Reconcile `references.bib`: keep `ChagrovZakharyaschev1997` (#662-unique); drop the
      duplicate `Avigad2022` (inherit the canonical entry from whichever propositional PR landed
      first).

**Timing**: 1.5 hours

**Depends on**: 3

**Files to modify** (in throwaway worktree only):
- `Cslib/Foundations/Logic/Connectives.lean` - removed
- `Cslib/Logics/Modal/Basic.lean` - re-pointed imports (`Operators/{Box,Imp,Bot}`, `imp` spelling)
- `Cslib/Logics/Modal/{Denotation,LogicalEquivalence}.lean` - reconciled to #607's operator API
- `references.bib` - de-duplicated (`ChagrovZakharyaschev1997` kept, `Avigad2022` inherited)

**Verification**:
- Work occurred only in a throwaway worktree; no live/tracked branch mutated outside it.
- Imports use `imp` (`Operators/{Box,Imp,Bot}`), not `impl`.
- `#607` (`fmontesi/connectives`) untouched.

---

### Phase 5: Conditional migration — CI verification & gated push [NOT STARTED, BLOCKED until gate]

**Goal**: (POST-AGREEMENT ONLY) Verify the restructured #662 branch through full CI in the throwaway
worktree, then push ONLY after explicit user approval, per research §6 steps 6-7. All tasks
blocked-until-approval.

**Tasks** (all blocked-until-approval):
- [ ] Step 6 — Run the full CI pipeline in the throwaway/backup branch first:
      `lake build && lake test && lake exe checkInitImports && lake exe lint-style &&
      lake shake --add-public --keep-implied --keep-prefix`. Zero-debt: no `sorry`/axiom patch — if a
      modal proof breaks under #607's derived `box`, fix structurally or mark the phase [BLOCKED].
- [ ] BLOCKED-UNTIL-APPROVAL: Obtain EXPLICIT user approval before any push.
- [ ] Step 7 — Push only with `--force-with-lease`; retain `backup/*` branches until GitHub CI is
      green (task-475 §11 gates D1-D7 apply). Never force-push to main; never touch #607.

**Timing**: 1 hour

**Depends on**: 4

**Files to modify**:
- None locally beyond Phase 4 (this phase verifies + gated-pushes the Phase 4 result)

**Verification**:
- Full CI pipeline green in the throwaway worktree before any push.
- No push occurred without a recorded explicit user approval.
- Force-push (if any) used `--force-with-lease`; backups retained until GitHub CI green.

---

## Testing & Validation

- [ ] Phase 1 draft leads with praise, contains CI-drift framing, bundle offer, and `imp` suggestion
      framed as a suggestion-to-fmontesi; carries a DRAFT/approval banner.
- [ ] Phase 2 draft frames box-vs-diamond as fmontesi's call with §5 tradeoffs, proposes ownership
      division, carries a DRAFT/approval banner.
- [ ] No GitHub or Zulip post occurred without recorded explicit user approval (audit).
- [ ] No branch (especially `fmontesi/connectives`) was rebased/pushed/edited (audit).
- [ ] (Conditional) Migration imports use `Operators/{Box,Imp,Bot}` with `imp` spelling.
- [ ] (Conditional) Full CI green in throwaway worktree before any push:
      `lake build && lake test && lake exe checkInitImports && lake exe lint-style && lake shake …`.
- [ ] (Conditional) Any force-push used `--force-with-lease` with backups retained until GitHub CI
      green.

## Artifacts & Outputs

- `specs/476_divide_modal_prs_coordinate_607/plans/02_divide-modal-prs.md` — this plan.
- `specs/476_divide_modal_prs_coordinate_607/artifacts/pr-607-review.md` — DRAFT #607 review comment
  (Phase 1; approval-pending, unposted).
- `specs/476_divide_modal_prs_coordinate_607/artifacts/zulip-coordination.md` — DRAFT Zulip note
  (Phase 2; approval-pending, unposted).
- (Conditional, Phases 4-5) A restructured #662 branch in a throwaway worktree — NOT pushed without
  explicit user approval.

## Rollback/Contingency

- **Phases 1-3 (drafts + gate)**: purely additive in-repo drafts; rollback = delete the draft files.
  No external side effects since nothing is posted without approval.
- **Posting (Phase 3, if approved)**: GitHub review comments and Zulip messages can be edited/deleted
  after posting; re-verify claims before posting to minimize the need for correction.
- **Phase 4 (restructure)**: all work in a throwaway worktree; rollback = discard the worktree; the
  live #662 branch (task-475 Option A, self-owned `Connectives.lean`) remains the fallback.
- **Phase 5 (push)**: retain `backup/*` branches until GitHub CI is green; if post-push CI fails,
  restore from backup and, if unrecoverable, mark the phase [BLOCKED] and revert to the pre-push
  state (`--force-with-lease` from backup). Never force-push to main.
- **Design stalls past 23 July**: leave Phases 4-5 [NOT STARTED]; the drafts already say "no rush";
  optionally propose a CSLib meeting to unblock direction.
