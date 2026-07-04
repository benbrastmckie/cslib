# Implementation Plan: Task #476 — Divide Modal PRs & Coordinate with #607

- **Task**: 476 - divide_modal_prs_coordinate_607
- **Status**: [IMPLEMENTING]
- **Effort**: ~6.5 hours (Phases 4-6 conditional; gated on external agreement)
- **Dependencies**: Task 475 (`specs/475_fix_and_stack_pr_662_on_648/`)
- **Research Inputs**: `specs/476_divide_modal_prs_coordinate_607/reports/01_divide-modal-prs.md`
- **Artifacts**: plans/03_divide-modal-prs.md (this file)
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
#607's operator layer landing. A newly verified fact about #607's head branch (see Research
Integration) opens a second, cleaner contribution avenue beyond a plain review comment: **offering
the missing `HasBot` + bundle classes as a PR whose base is #607's own branch**, which Fabrizio
reviews and merges — leaving him fully in control while giving him working, CI-tested code. That
offer is itself an approval-gated, conditional phase. Definition of done for the unblocked portion:
two reviewed drafts exist and the gate/contingency structure is recorded; every conditional phase
(bundles-PR offer and #662 migration) remains [NOT STARTED] until the gate opens.

### Research Integration

- **PR-state table & overlap matrix** (research §1, §1.1): only #607↔#662 hard-conflict on
  `Modal/Basic.lean`; #648/#649 overlaps are soft/reconcilable.
- **#607's head branch is in-org, not a fork** (research §1 notes, re-verified via `gh pr view 607`:
  `isCrossRepository: false`, `maintainerCanModify: false`): `fmontesi/connectives` lives **inside
  `leanprover/cslib`**. This is what enables the new **PR-against-his-branch offer** — one can open a
  PR whose *base* is `fmontesi/connectives` and whose *head* is a new in-org branch of one's own
  (e.g. `benbrastmckie/connectives-bundles`), carrying the `HasBot` + bundle classes #607 lacks.
  Fabrizio reviews and merges it into his branch; the commits flow into #607 with authorship
  preserved, and he stays fully in control (he does the merge; nothing is ever pushed to, rebased, or
  edited on his branch). This is the concrete "give him working, CI-tested code" alternative to
  merely describing the bundles, and is strictly better than the "cherry-pickable follow-up" framing
  because it is reviewable and CI-runnable in situ.
- **#607 CI is upstream drift, not #607's fault** (research §4.3): the red `ci-checks` is
  `HML/LogicalEquivalence.lean` failing because #607 is ~15 commits behind `main`; a rebase clears
  it. This framing leads the #607 review.
- **DRAFT #607 review** (research §4.4) and **DRAFT Zulip note** (research §7) are the seeds for
  Phases 1-2.
- **Box-vs-diamond tradeoff table** (research §5) is fmontesi's maintainer decision, surfaced with
  tradeoffs, never asserted.
- **`HasBot` + `PropositionalConnectives`/`ModalConnectives` bundles** (research §2.3) are the two
  things #607's operator layer currently lacks; #662 already built them. They are the payload of the
  Phase 4 bundles-PR offer.
- **Conditional 7-step migration** (research §6) is the gated body of Phases 5-6.

### Prior Plan Reference

Prior plan: `plans/02_divide-modal-prs.md` (this revision supersedes it). Phases 1-2 there are already
[COMPLETED] (drafts `artifacts/pr-607-review.md`, `artifacts/zulip-coordination.md` written
2026-07-03) and are carried forward verbatim here. Task 475 is the substantive predecessor: it
stacked #662 on #648 with a **self-owned** `Foundations/Logic/Connectives.lean` (Option A) precisely
to avoid coupling #662 to the unmerged #607, and established the gated-force-push discipline
(task-475 §11 gates) plus the already-drafted, approval-pending Zulip response reused as a base here.
Effort calibration: task 475 confirmed that coordination/drafting work is fast but the *posting* and
*push* steps are the risk surface and must stay behind explicit user gates.

### Roadmap Alignment

No ROADMAP.md consulted for this task (no roadmap_path in delegation context).

### Naming decision (USER DIRECTIVE — resolves research §8 open question)

Use **`imp`**, NOT `impl`, throughout. This resolves the `HasImpl.impl` (#607) vs `HasImp.imp`
(#662/#648) open decision (research §2.5, §8/D1) in favor of `imp` (matches `impI`/`impE` rule
prefixes and FormalizedFormalLogic). Consequences baked into this plan:
- The #662 migration imports the operator layer as `Operators/{Box,Imp,Bot}` (`imp` spelling).
- The Phase 4 bundles PR uses the `imp` spelling (`HasImp`/`imp`) throughout.
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
  touched without EXPLICIT user approval; migration and the bundles-PR offer wait for design
  agreement + #607's return.
- Prepare and **offer the `HasBot` + bundle classes as a PR against #607's branch** (Phase 4,
  conditional): build them on a new in-org branch, CI-test in a throwaway worktree, and — only after
  explicit user approval — open a PR with base = `fmontesi/connectives`, so Fabrizio can review and
  merge working code into #607. Never push to or edit his branch; he merges.
- Record the **conditional #662-on-#607 migration** (Phases 5-6) as a fully specified but
  blocked-until-approval sequence, ready to execute post-agreement.

**Non-Goals**:
- Posting anything to GitHub or Zulip in this planning/execution cycle (gated on user approval).
- Editing, rebasing, or pushing to #607's branch (`fmontesi/connectives`) — ever. (The Phase 4 PR
  respects this: only one's own branch is pushed; Fabrizio does the merge.)
- Making the box-vs-diamond decision on fmontesi's behalf (offer tradeoffs, do not assert).
- Coupling #662 to the still-unmerged #607 before the gate opens (task 469's avoided anti-pattern).
- Preparing the bundles or opening the Phase 4 PR before fmontesi is back / has agreed direction
  (same premature-coupling caution as task 469).
- Rebasing #649 (out of scope here; noted as downstream-of-#648/#607 future work).

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Editing/pushing/rebasing #607 (@fmontesi's PR) | H | L | HARD CONSTRAINT: coordinate ONLY via review comment / Zulip / a PR against his branch; NEVER push, rebase, or edit `fmontesi/connectives`. Encoded in Phases 1, 3, 4, and every gate. |
| Posting a draft to GitHub/Zulip without approval | H | M | Drafts stay in-repo; Phase 3 gate requires EXPLICIT user approval before any post; posting is a manual gated step, never automated. |
| Opening the bundles PR against his branch prematurely or without approval | H | M | Opening the PR is itself a gated, approval-required action (Phase 4); it is an OFFER Fabrizio can decline/merge/adapt. Safe by construction (base is his branch, head is one's own; he controls the merge; no push to his branch), but still gated on his wanting the bundles and on explicit user approval. |
| Prematurely coupling #662 to unmerged #607 | H | M | Phase 5 precondition (hard gate): migration blocked until fmontesi agrees direction AND #607's operator layer lands; until then #662 keeps its self-owned `Connectives.lean` (task-475 Option A). |
| Force-push to #662/#648 without approval | H | L | Any `--force-with-lease` is a gated Phase 6 step requiring EXPLICIT user approval; `backup/*` branches retained until GitHub CI green (task-475 §11 gates D1-D7). |
| Local build/test mutating a real working branch | M | L | HARD CONSTRAINT: all local build/test runs (Phase 4 and Phase 6) happen in a THROWAWAY worktree only; never on the live checkout or a tracked branch. |
| Advocating `impl` and contradicting the user directive | M | L | `imp` is fixed by user directive; imports and the Phase 4 bundle classes use the `imp` spelling; the #607 rename is framed as a suggestion to fmontesi, not an edit. |
| Draft/PR claims go stale before posting (e.g. #607 rebased, #662 retargeted) | M | M | Re-verify claims and live branch state (`gh pr view 607`) at approval time (task-475 zulip-response pattern: only post/open after the described actions are true). |
| box-vs-diamond decision stalls past 23 July | M | M | Gate is time-tolerant: drafts note "no rush, you're back on the 23rd"; migration and bundles PR simply stay [NOT STARTED]; offer a CSLib meeting to unblock. |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1, 2 | -- |
| 2 | 3 | 1, 2 |
| 3 | 4, 5 | 3 |
| 4 | 6 | 5 |

Phases within the same wave can execute in parallel. Phases 1 and 2 are independent drafting tasks.
Phase 4 (bundles-PR offer) and Phase 5 (#662 restructure) are BOTH gated on the Phase 3 gate and are
**independent of each other** — they may proceed in either order (or only one) once the gate opens.
Phase 6 (CI verification + gated push of the #662 migration) depends only on Phase 5. All of Phases
4-6 remain [NOT STARTED] until the Phase 3 gate opens (design agreement reached, #607 landed/back,
and explicit user approval given).

### Phase 1: Draft #607 review comment [COMPLETED — SUPERSEDED]

**Completed**: 2026-07-03T12:07:16Z
**Superseded**: 2026-07-04 — the substantive #607 coordination was carried by the already-posted
comment https://github.com/leanprover/cslib/pull/607#issuecomment-4837502740 (benbrastmckie,
2026-06-29), verified accurate against the current #607/#648 heads. The `pr-607-review.md` draft is
retained for reference only and will NOT be posted (its box-vs-diamond point lives in the Zulip note;
its bundle/`imp` nits are minor thread replies if they arise). Note: the draft's original CI point
("just rebase") was found FALSE — the red `ci-checks` is #607's own `LogicalEquivalence`
parametrisation leaving `HML/LogicalEquivalence.lean` on the old signature (an in-PR fix, not drift).

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

**Note (no rewrite required)**: The completed draft may, at the user's discretion, be lightly
extended at approval time to mention the concrete Phase 4 offer ("I can open a small PR against your
branch with the `HasBot` + bundle classes so you can review and merge working code"). This is an
optional approval-time addition; the completed draft itself is NOT rewritten by this plan.

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

**Goal**: Explicit HOLD point. The #607 review draft is SUPERSEDED (Phase 1 note) — the substantive
propositional/#648 coordination is already posted (comment 4837502740), so the ONE live gated
communication item is the Zulip note (`zulip-coordination.md`, box-vs-diamond). Govern its posting
(only after EXPLICIT user approval) and hold BOTH the bundles-PR offer (Phase 4) and the #662
migration (Phases 5-6) until design direction is agreed and #607 is back / its operator layer is
stable. This phase is a checkpoint, not automated work.

**Tasks**:
- [x] Present both drafts to the user for review; the #607 review draft is superseded by the posted
      comment and will not be posted. Zulip note remains the one live gated item.
- [ ] HOLD: post NOTHING to Zulip and touch NO branch until the user EXPLICITLY approves.
- [ ] If/when the user approves sending the Zulip note: re-verify its factual claims against live
      state (done 2026-07-04 — #607 diamond-inclusive `{atom,not,and,diamond}`, #662 box-primitive
      `{atom,bot,imp,box}`, #648/#662 CI-green, #649 LTL/downstream all confirmed) and re-confirm at
      send time, then send.
- [ ] Record the outstanding external preconditions that gate Phases 4-6: (a) fmontesi agrees the
      box-primitive direction / wants the bundles (or a joint plan is settled), AND (b) #607's
      operator layer is landing/stable and fmontesi is back (returns 23 July).
- [ ] Do NOT open Phase 4 (bundles PR) or Phases 5-6 (migration) until the applicable preconditions
      hold AND the user explicitly approves starting that specific work.

**Timing**: 0.5 hour (excluding indefinite external wait)

**Depends on**: 1, 2

**Files to modify**:
- None (checkpoint / optional gated posting of existing drafts)

**Verification**:
- No GitHub/Zulip post occurred without a recorded explicit user approval.
- No branch was rebased/pushed/edited.
- The external preconditions for Phases 4-6 are recorded and confirmed unmet-or-met before
  proceeding.

---

### Phase 4: Conditional — prepare `connectives-bundles` PR against #607 (offer) [NOT STARTED, BLOCKED until gate]

**Goal**: (POST-AGREEMENT ONLY, OFFER) Give Fabrizio working, CI-tested code for the two things
#607's operator layer lacks — `HasBot` and the `PropositionalConnectives`/`ModalConnectives` bundles
(research §2.3) — by building them on a new in-org branch and, after explicit approval, opening a PR
whose **base is `fmontesi/connectives`**. He reviews and merges; nothing is ever pushed to or edited
on his branch. This is an OFFER: opening the PR is itself a gated, approval-required action, and
fmontesi is free to decline, merge, or adapt.

**Tasks** (all blocked-until-approval):
- [ ] BLOCKED-UNTIL-APPROVAL: Confirm Phase 3 preconditions (fmontesi is back / has agreed he wants
      the bundles and a design direction) and obtain explicit user go-ahead. Do NOT prepare the
      bundles before he is back / has agreed direction (same premature-coupling caution as task 469).
- [ ] BLOCKED-UNTIL-APPROVAL: Re-verify via `gh pr view 607` that #607's head branch is still in-org
      (`isCrossRepository: false`), confirming the PR-against-his-branch pattern is available.
- [ ] Create a new in-org branch `benbrastmckie/connectives-bundles` off `fmontesi/connectives` (or
      off `main` targeting his branch). Never check out, push to, rebase, or edit `fmontesi/connectives`
      itself.
- [ ] Add `HasBot` (atomic class in the `Operators` family) plus the bundled
      `PropositionalConnectives` (`extends HasBot, HasImp`) and `ModalConnectives`
      (`extends PropositionalConnectives, HasBox`) classes, using the **`imp`** (NOT `impl`) spelling
      throughout, matching #607's `Operators/*` layout and `Cslib.Logic` namespace (research §2.3).
- [ ] Run the full CI pipeline in a THROWAWAY worktree only:
      `lake build && lake test && lake exe checkInitImports && lake exe lint-style &&
      lake shake --add-public --keep-implied --keep-prefix`. Zero-debt: no `sorry`/axiom; fix
      structurally or mark the phase [BLOCKED].
- [ ] BLOCKED-UNTIL-APPROVAL: Obtain EXPLICIT user approval before any GitHub action.
- [ ] Push ONLY the new `benbrastmckie/connectives-bundles` branch, then open a PR with
      **base = `fmontesi/connectives`, head = `benbrastmckie/connectives-bundles`**. Frame the PR body
      as an offer (he reviews/merges/adapts). Never push to or edit his branch; he merges.

**Timing**: 1.75 hours

**Depends on**: 3

**Files to modify** (on the new `benbrastmckie/connectives-bundles` branch / throwaway worktree only):
- `Cslib/Foundations/Logic/Operators/Bot.lean` - new `HasBot` class (`imp`-consistent family)
- `Cslib/Foundations/Logic/Operators/*` (bundle home) - new `PropositionalConnectives` /
  `ModalConnectives` bundled classes
- `Cslib.lean` (module registry) - register the new operator/bundle modules as needed

**Verification**:
- Work occurred only on the new in-org branch / throwaway worktree; `fmontesi/connectives` untouched
  (never pushed to, rebased, or edited).
- Bundle classes use `imp` (`HasImp`/`imp`), not `impl`.
- Full CI pipeline green in the throwaway worktree before any push.
- Any PR opened has base = `fmontesi/connectives`, head = the new own branch, and was opened only
  after recorded explicit user approval; the PR is framed as an offer.

---

### Phase 5: Conditional #662-on-#607 migration — restructure [NOT STARTED, BLOCKED until gate]

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
      filled by #607's `Operators/*` + bundles — the same bundles offered in Phase 4).
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

### Phase 6: Conditional migration — CI verification & gated push [NOT STARTED, BLOCKED until gate]

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

**Depends on**: 5

**Files to modify**:
- None locally beyond Phase 5 (this phase verifies + gated-pushes the Phase 5 result)

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
- [ ] (Conditional, Phase 4) Bundle classes (`HasBot`, `PropositionalConnectives`, `ModalConnectives`)
      use the `imp` spelling; full CI green in throwaway worktree before push; any PR opened has
      base = `fmontesi/connectives`, head = own branch, opened only after explicit approval.
- [ ] (Conditional, Phase 5) Migration imports use `Operators/{Box,Imp,Bot}` with `imp` spelling.
- [ ] (Conditional, Phase 6) Full CI green in throwaway worktree before any push:
      `lake build && lake test && lake exe checkInitImports && lake exe lint-style && lake shake …`.
- [ ] (Conditional, Phase 6) Any force-push used `--force-with-lease` with backups retained until
      GitHub CI green.

## Artifacts & Outputs

- `specs/476_divide_modal_prs_coordinate_607/plans/03_divide-modal-prs.md` — this plan (supersedes
  `plans/02_divide-modal-prs.md`).
- `specs/476_divide_modal_prs_coordinate_607/artifacts/pr-607-review.md` — DRAFT #607 review comment
  (Phase 1; approval-pending, unposted).
- `specs/476_divide_modal_prs_coordinate_607/artifacts/zulip-coordination.md` — DRAFT Zulip note
  (Phase 2; approval-pending, unposted).
- (Conditional, Phase 4) A new in-org branch `benbrastmckie/connectives-bundles` with the `HasBot` +
  bundle classes, and — only after explicit approval — a PR against base `fmontesi/connectives`. NOT
  opened without explicit user approval.
- (Conditional, Phases 5-6) A restructured #662 branch in a throwaway worktree — NOT pushed without
  explicit user approval.

## Rollback/Contingency

- **Phases 1-3 (drafts + gate)**: purely additive in-repo drafts; rollback = delete the draft files.
  No external side effects since nothing is posted without approval.
- **Posting (Phase 3, if approved)**: GitHub review comments and Zulip messages can be edited/deleted
  after posting; re-verify claims before posting to minimize the need for correction.
- **Phase 4 (bundles PR offer)**: all local work in a throwaway worktree; rollback before the PR =
  discard the worktree and delete the unpushed `benbrastmckie/connectives-bundles` branch. After the
  PR is opened (approved), it can be closed/edited; #607's branch is never touched, so there is
  nothing to roll back on his side — he simply declines or does not merge.
- **Phase 5 (restructure)**: all work in a throwaway worktree; rollback = discard the worktree; the
  live #662 branch (task-475 Option A, self-owned `Connectives.lean`) remains the fallback.
- **Phase 6 (push)**: retain `backup/*` branches until GitHub CI is green; if post-push CI fails,
  restore from backup and, if unrecoverable, mark the phase [BLOCKED] and revert to the pre-push
  state (`--force-with-lease` from backup). Never force-push to main.
- **Design stalls past 23 July**: leave Phases 4-6 [NOT STARTED]; the drafts already say "no rush";
  optionally propose a CSLib meeting to unblock direction.
