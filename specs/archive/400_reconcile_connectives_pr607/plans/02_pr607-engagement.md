# Implementation Plan: Task #400 — Engage PR #607 (connective typeclasses)

- **Task**: 400 - Unbundle connective typeclasses; reconcile with fmontesi PR #607 (Waring's flag a)
- **Status**: [SUPERSEDED] (2026-08-10)
- **Effort**: ~9.5 hours agent-doable work (plus human-authored review + external upstream wait)
- **Dependencies**: None (independent of the 407-409 IPL-base refactor)
- **Research Inputs**: reports/01_pr607-engagement.md; reports/02_engagement-strategy.md (primary, live-PR-grounded)
- **Artifacts**: plans/02_pr607-engagement.md (this file)
- **Standards**: plan-format.md; status-markers.md; artifact-management.md; tasks.md; CONTRIBUTING.md; NOTATION.md; ORGANISATION.md
- **Type**: cslib
- **Lean Intent**: false

> ## ⚠ SUPERSEDED — 2026-08-10. Do not execute this plan.
>
> This plan was written to help PR #607 land while it was still OPEN. **#607 merged on 2026-08-03**
> (commit `b8ad3923`), which makes its central deliverable — a human-authored review helping that PR
> land — unreachable. Phases 5–8 are moot, not pending.
>
> It is also built on a premise later verified FALSE: that #607 would settle the falsum
> representation question. It did not. Bot-as-atom traces to commit `61785643` (#89), the original
> definitions commit, four PRs earlier; #607's only constructor-level change to `Proposition` was
> the rename `impl` -> `imp`. #607 is **orthogonal** to falsum, so Phase 6's "await upstream
> resolution of the falsum question" was waiting on a decision that was never in flight.
>
> **Superseded by**: `reports/03_falsum-representation-decision.md`, which recommends OPTION B
> (keep the fork's primitive `bot`) and carries a standalone action checklist in section 9. The
> task's own description in `specs/state.json` was corrected against the live record the same day.
>
> **What remains valid and should be reused, not rewritten**: Phases 1–4 are genuinely [COMPLETED]
> and their output files under `review-scaffolding/` stand on their own merits —
> `01_comparison-tables.md`, `02_falsum-bridge-sketch.md` (whose retraction of the `HasBot`
> recommendation was correct and is now confirmed), `03_grind-direction-finding.md`, and
> `04_review-packet.md`. Phase 2's Mathlib-`Bot`/`Top`-reuse finding is load-bearing for the Option B
> recommendation.
>
> **What is moot**: Phase 5 (post a review on an already-merged PR), Phase 6 (await a resolution that
> was never pending), and Phases 7–8 (conditional on Phase 6). The live successor work is the PR #648
> rebase, the Connectives/Operators reconciliation, and the `infix` -> `infixr` notation change — all
> three named in the corrected task description, none started.

## Overview

This is a **coordination / engagement task**, not a pure code task. Per Waring's Zulip guidance
(msg 606970606), the headline deliverable is a **human-authored review** on GitHub PR #607
(`fmontesi/connectives`, OPEN) and/or the CSLib Zulip "Propositional Logic" thread, helping that PR
land the connective typeclasses instead of #648. Our prerequisite is already DONE: `Connectives.lean`
was removed from #648 (commit `85db79a6`).

The plan separates three clearly distinct kinds of work, in this order:
1. **Agent-doable factual scaffolding** — option tables, precedence/naming comparison, a
   Mathlib-`Bot`/`Top`-reuse + derived-`¬` bridge sketch, and an empirical `grind`-through-notation
   check. These produce *factual scaffolding files* (tables, code sketches, findings) for the human
   to adapt — never finished external prose.
2. **Human gate** — the human author rewrites the scaffolding in their own words and posts the
   review on #607/Zulip. Human-only (CSLib Zulip AI policy #605827029: agents MUST NOT author
   PR/Zulip prose).
3. **Conditional downstream code** — once the falsum/naming questions settle upstream, register the
   fork's five-primitive `Proposition` instances against #607's merged typeclasses and drop local
   notation #607 supersedes. These phases are **blocked-pending-upstream**.

**Definition of done**: a complete, human-ready scaffolding packet exists; the human review is
posted (human gate); and the conditional code phases are documented and ready to execute once
upstream resolves (they remain [BLOCKED] until then).

### Research Integration

Report 02 (primary) supersedes report 01 on two points that shape this plan:
- **Do NOT propose a `HasBot` class.** Mathlib already ships `Bot`/`Top` (`Mathlib/Order/Notation.lean`)
  and the fork's `Defs.lean` already uses them (`instance : Bot (Proposition Atom)`,
  `instance : Top ...`). Reuse-first + eric-wieser's "`Has` prefix is a Lean-3-ism" both point to
  **reusing Mathlib `Bot`/`Top`**, plus a derived-`¬` bridge lemma `(A → ⊥) = ¬A`.
- **Primitive `HasNot` does NOT block faithful registration.** `HasNot.not : α → α` can be filled by
  the derived `Proposition.neg = (· → ⊥)`; #607's own diff already does `instance : HasNot ... :=
  {not := Proposition.neg}`. The real gaps are notation (`⊥`/`⊤`) and a `grind`/`simp` bridge.

Other live-PR facts driving the plan: `benbrastmckie` already posted a coordination comment
(2026-06-17), so the next review must *build on* it, not restate it; eric-wieser/ctchou/chenson all
want file consolidation; chenson's `_def`-direction CHANGES_REQUESTED is open and unresolved; #607's
Propositional hunk targets the *upstream* `Proposition`, not the fork's five-primitive
`PL.Proposition`, so the registration ask must be forward-looking.

### Prior Plan Reference

No prior plan (this is plan round 02; the 01 round was research-only).

### Roadmap Alignment

No ROADMAP.md consulted (roadmap_flag false). This task is explicitly independent of tasks 407-409
(IPL-base refactor); connective-typeclass work MUST NOT be folded into 407.

## Goals & Non-Goals

**Goals**:
- Produce a factual, human-ready scaffolding packet (tables, code sketches, empirical findings)
  organised to report 02's §6 review skeleton, that the human can adapt into a posted review.
- Settle, with evidence, the three high-leverage technical questions: (1) falsum/verum via Mathlib
  `Bot`/`Top` + derived-`¬` bridge; (2) `_def` normal-form direction (`grind`-through-notation);
  (3) naming (`Has` prefix; `impl` vs `imp`).
- Document the conditional downstream code (register `PL.Proposition` against #607's typeclasses;
  drop superseded local notation) so it is ready to execute once upstream resolves.

**Non-Goals**:
- Do NOT author or post PR/Zulip prose from an agent (Zulip AI policy). Prose is human-authored.
- Do NOT propose a competing full architecture or push the bundled
  `PropositionalConnectives`/`ModalConnectives` hierarchy into #607 (offer bundles as a follow-up PR).
- Do NOT propose minting a `HasBot` class (corrected by report 02 — reuse Mathlib `Bot`/`Top`).
- Do NOT fold connective-typeclass work into tasks 407-409.
- Do NOT register the fork's `PL.Proposition` against #607 *now* (it does not exist upstream; the ask
  is forward-looking until #607 merges and the fork rebases).

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Agent drafts external prose, violating Zulip AI policy | H | M | All Phase 1-4 outputs are tables/sketches/findings marked "points to make, not prose to paste"; Phase 5 is human-only |
| `grind`-through-notation cannot be made to work (Waring already reverted to `_def` rewrites) | M | M | Phase 3 verifies empirically before the review commits to chenson's orientation; report the negative result honestly if it fails |
| Upstream naming flips (drop `Has`) after review, raising fork rebase cost | M | M | Phase 1 surfaces the naming decision and the `And`/`Or`/`Iff` core-collision counter-argument; force a decision rather than leave open |
| Default `[HasImpl][Bot] → HasNot` instance causes resolution ambiguity | M | L | Float as a question only (never assume safe); document the diamond-inheritance hazard |
| #607's Propositional hunk conflicts heavily with fork's `PL.Proposition` on rebase | M | H | Keep the #607 ask forward-looking; isolate fork-rebase registration as conditional Phase 7, gated on merge |
| Restating benbrastmckie's existing comment wastes reviewer goodwill | L | M | Phase 4 explicitly anchors on the 2026-06-17 comment and de-dupes against it |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1, 2 | -- |
| 2 | 3 | 2 |
| 3 | 4 | 1, 2, 3 |
| 4 | 5 | 4 |
| 5 | 6 | 5 |
| 6 | 7 | 6 |
| 7 | 8 | 7 |

Phases within the same wave can execute in parallel. Phases 1-4 and 7-8 are agent-doable; Phases 5-6
are human/external gates.

---

### Phase 1: Design-comparison and option tables (factual scaffolding) [COMPLETED] (2026-06-29)

**Goal**: Produce the factual comparison tables the human review needs, building on the live-PR data
in report 02 and anchored to benbrastmckie's 2026-06-17 comment (do not restate it).

**Tasks**:
- [ ] Tabulate #607's eight `HasX` classes: class, method, notation declaration, precedence/assoc,
      file (from report 02 §1.1) versus the fork's `PL.Defs` notation (`∧`36 infix, `∨`35 infix,
      `→`30 infix, `↔`20, `¬`40) — highlight the `infixr` vs `infix` and precedence divergences.
- [ ] Build a **naming options table**: keep `HasX` (matches CSLib `HasFresh`/`HasContext`/
      `HasSubstitution`; avoids core/Mathlib `And`/`Or`/`Iff` collision) vs drop `Has` (Mathlib-idiom,
      eric-wieser); and `impl`/`HasImpl` vs `imp`/`HasImp` — with the pro/con for each, ending in a
      "decision requested" framing.
- [ ] Build a **notation-precedence ladder table**: endorse #607's `infixr` ladder (→25, ∨30, ⊗35,
      ∧36, ¬/□/◇40, ↔20); note NOTATION.md is currently silent on connectives; flag the `→` at 25
      shadowing core `→` question for fmontesi to confirm.
- [ ] Build a **file-organisation options table** (single `Operators.lean` vs ctchou's 3-file split)
      noting eric-wieser/ctchou/chenson consensus.
- [ ] Mark the whole output "factual scaffolding — points to make, not prose to paste".

**Timing**: 2 hours

**Depends on**: none

**Files to modify**:
- `specs/400_reconcile_connectives_pr607/review-scaffolding/01_comparison-tables.md` (new) — factual
  tables only, no external prose.

**Verification**:
- Tables match report 02 §1.1/§3 verbatim on the verified facts; naming/precedence/file-org options
  each carry the counter-argument; no paragraph reads as ready-to-post prose.

---

### Phase 2: Falsum/verum scaffolding — Mathlib `Bot`/`Top` reuse + derived-`¬` bridge sketch [COMPLETED] (2026-06-29)

**Goal**: Produce a verified Lean sketch showing that a bot-primitive formula type registers
faithfully against #607's classes by reusing Mathlib `Bot`/`Top` and a derived-`¬` bridge — the
corrected primary technical point (NOT a new `HasBot` class).

**Tasks**:
- [ ] Write a minimal Lean sketch (against the fork's `PL.Proposition` or a small stand-in) showing:
      (i) `⊥`/`⊤` via Mathlib `Bot`/`Top` (already present in `Defs.lean`); (ii)
      `instance : HasNot (PL.Proposition Atom) := {not := Proposition.neg}`; (iii) the bridge
      `@[grind =] lemma (A → ⊥) = ¬A := rfl`.
- [ ] Confirm the sketch elaborates with `lake build` (or `lean_multi_attempt`/`lean_goal`); capture
      the exact instance/lemma text as a code block for the human review.
- [ ] Draft (as a *question*, not a demand) the optional default instance
      `instance [HasImpl α] [Bot α] : HasNot α := ⟨(· → ⊥)⟩`, with an explicit note on the
      diamond-inheritance / notation-ambiguity hazard.
- [ ] Write the explicit retraction note: "do NOT mint `HasBot` — reuse Mathlib `Bot`/`Top`" with the
      reuse-first + Lean-3-ism justification.

**Timing**: 2 hours

**Depends on**: none

**Files to modify**:
- `specs/400_reconcile_connectives_pr607/review-scaffolding/02_falsum-bridge-sketch.md` (new) —
  verified Lean snippets + risk notes.

**Verification**:
- The `HasNot := {not := neg}` instance and `(A → ⊥) = ¬A` bridge elaborate without error against the
  fork's `Bot`/`Top` instances; the default-instance is framed as a question with its hazard stated.

---

### Phase 3: `_def` normal-form direction — empirical `grind`-through-notation check [COMPLETED] (2026-06-29)

**Goal**: Settle, with evidence, chenson's open CHANGES_REQUESTED point: whether the `simp`/`grind`
normal form can be "the notation" (collapse `φ.and ψ ⤳ φ ∧ ψ`) so the modal `Satisfies.*_iff_*`
proofs do not need `=_ *_def` rewrites.

**Tasks**:
- [ ] On the Phase 2 scaffold, set the bridge lemmas to orient *into* the notation (per chenson /
      `List.append_eq` / `Nat.add_eq`) and test whether `grind`/`simp` closes a representative goal
      (e.g. a `Satisfies.*_iff_*`-shaped goal) — Waring reported this blocker; reproduce it.
- [ ] Record the empirical result (works / does not work, with the exact tactic state) as a factual
      finding the human can cite.
- [ ] If it fails, document the minimal fallback (keep `_def` as-is / a `grind` configuration that
      sees through notation) so the review can offer concrete help rather than a bare assertion.
- [ ] Note the leftover commented-out `grind only` block in `Satisfies.dual` as a cleanup item.

**Timing**: 1.5 hours

**Depends on**: 2

**Files to modify**:
- `specs/400_reconcile_connectives_pr607/review-scaffolding/03_grind-direction-finding.md` (new) —
  empirical finding (positive or negative), with reproduction.

**Verification**:
- The finding states a concrete, reproducible outcome (not speculation); if the orientation fails, a
  fallback is documented; no claim about chenson's orientation is made without evidence.

---

### Phase 4: Consolidate the human-review scaffolding packet [COMPLETED] (2026-06-29)

**Goal**: Merge Phases 1-3 into one ordered scaffolding packet structured to report 02's §6 review
skeleton, ready for the human to adapt — explicitly not finished prose.

**Tasks**:
- [ ] Order points by report 02 §6 priority: (1) consensus/low-friction wins (file consolidation,
      tidier instance syntax); (2) naming decision (ask, don't dictate); (3) falsum/verum via Mathlib
      `Bot`/`Top` + bridge (Phase 2); (4) `_def` direction (Phase 3); (5) precedence ladder →
      NOTATION.md; (6) bundles as a follow-up PR, not a blocker; (7) modality note (low priority);
      (8) close with concrete offers to unblock.
- [ ] Anchor explicitly on benbrastmckie's 2026-06-17 comment; mark each point "new" vs "already
      raised" to avoid restating.
- [ ] Embed the verified Lean snippets from Phases 2-3 as factual exhibits.
- [ ] Prominent header: "Factual scaffolding for a HUMAN-AUTHORED review. Rewrite in your own words
      before posting (CSLib Zulip AI policy #605827029). No paragraph is ready-to-post prose."

**Timing**: 1 hour

**Depends on**: 1, 2, 3

**Files to modify**:
- `specs/400_reconcile_connectives_pr607/review-scaffolding/04_review-packet.md` (new) — consolidated
  packet (points + exhibits, not prose).

**Verification**:
- Packet covers all eight §6 items in priority order, anchors on the prior comment, embeds the verified
  snippets, and carries the AI-policy header; nothing reads as ready-to-post.

---

### Phase 5: HUMAN GATE — author and post the review on #607 / Zulip [SUPERSEDED] (moot: #607 merged 2026-08-03)

**Goal**: The human author rewrites the scaffolding in their own words and posts the review on PR #607
(and/or the Zulip "Propositional Logic" thread).

**Owner**: Human (human-only — agents MUST NOT author or post PR/Zulip prose; Zulip AI policy
#605827029).

**Tasks**:
- [ ] Human reviews `04_review-packet.md` and the existing `zulip-response.md` draft.
- [ ] Human rewrites the points in their own words (build on the 2026-06-17 comment, do not restate).
- [ ] Human posts the review on #607 and/or replies on the Zulip thread.
- [ ] Human records the posted permalink(s) back into the task directory for traceability.

**Timing**: ~1 hour (human, not agent)

**Depends on**: 4

**Files to modify**:
- None by agent. Human may update `specs/400_reconcile_connectives_pr607/zulip-response.md` and add a
  posted-links note.

**Verification**:
- A human-authored review exists on #607 and/or Zulip; the agent does not produce this artifact.

---

### Phase 6: HUMAN/EXTERNAL GATE — await upstream resolution [SUPERSEDED] (moot: no falsum decision was ever in flight upstream)

**Goal**: Wait for #607's maintainers to resolve the two gating questions: (a) falsum/verum +
derived-`¬` approach, and (b) naming (`Has` prefix; `impl` vs `imp`), and ideally for #607 to merge.

**Owner**: External (upstream maintainers) + human monitoring.

**Tasks**:
- [ ] Monitor #607 for maintainer decisions on naming and the falsum/verum bridge.
- [ ] Record the resolved conventions (class names, notation ladder, bridge-lemma orientation) once
      decided.
- [ ] Confirm whether/when #607 merges upstream and the fork is ready to rebase.

**Timing**: External (unbounded; not agent effort)

**Depends on**: 5

**Files to modify**:
- None by agent. Human records resolved conventions into the task directory.

**Verification**:
- Upstream conventions are documented; Phases 7-8 stay [BLOCKED] until this records a resolution.

---

### Phase 7: CONDITIONAL — register `PL.Proposition` against #607's merged typeclasses [SUPERSEDED] (was conditional on Phase 6)

**Goal**: Once #607 merges and conventions settle (Phase 6), re-point the fork's five-primitive
`Cslib.Logic.PL.Proposition` at the upstream atomic classes and drop superseded local notation.
**Gated on Phase 6 — do not start until upstream resolves.**

**Tasks**:
- [ ] Replace the fork-local typeclass registrations in `Logics/Propositional/Defs.lean` (currently
      `PropositionalConnectives`, `HasAnd`, `HasOr` against local `Connectives.lean`) with instances
      against #607's merged classes, using the resolved names (`HasImpl`/`imp`/bare per Phase 6).
- [ ] Register negation via the derived `neg` (`HasNot := {not := Proposition.neg}`) and add the
      `(A → ⊥) = ¬A` bridge with the Phase-6-agreed orientation; keep Mathlib `Bot`/`Top` for `⊥`/`⊤`.
- [ ] Drop the fork's per-type `scoped infix`/`prefix` notation (`Defs.lean` lines ~107-111) that
      #607 supersedes; keep instances + bridge lemmas only.
- [ ] Rebuild the bundled hierarchy (`PropositionalConnectives` etc.) on top of the upstream atomic
      classes if retained (or defer to the separate follow-up bundle PR).
- [ ] CI: `lake build`, `lake exe checkInitImports`, `lake exe lint-style`,
      `lake shake --add-public --keep-implied --keep-prefix`, `lake test`.

**Timing**: 2 hours (when unblocked)

**Depends on**: 6

**Files to modify**:
- `Cslib/Logics/Propositional/Defs.lean` — swap local registrations/notation for upstream-class
  instances + bridge lemmas.
- `Cslib/Foundations/Logic/Connectives.lean` — reconcile or remove once #607 supersedes (per upstream
  decision).

**Verification**:
- `lake build` green; the propositional development compiles against #607's classes; no duplicate
  notation; CI pipeline passes.

---

### Phase 8: CONDITIONAL — record connective notation in NOTATION.md; reconcile ORGANISATION.md [SUPERSEDED] (was conditional on Phase 6)

**Goal**: Capture the agreed connective precedence ladder in NOTATION.md (currently silent on
connectives) and fix the ORGANISATION.md drift (it lists `Axioms.lean` as the typeclass home and
`Connectives.lean` as "derived abbreviations"). **Gated on Phase 6/7.**

**Tasks**:
- [ ] Add the agreed `infixr` ladder (→25, ∨30, ⊗35, ∧36, ¬/□/◇40, ↔20) to NOTATION.md as the
      library-wide connective convention.
- [ ] Update ORGANISATION.md to reflect where connective typeclasses actually live post-#607.
- [ ] CI: `lake exe lint-style` (text linters) on the docs touched.

**Timing**: 1 hour (when unblocked)

**Depends on**: 7

**Files to modify**:
- `NOTATION.md` — add connective precedence section.
- `ORGANISATION.md` — correct the connective-typeclass location.

**Verification**:
- NOTATION.md documents the ladder; ORGANISATION.md matches the post-#607 code layout; lint-style
  passes.

## Testing & Validation

- [ ] Phase 2 Lean snippets (`HasNot := {not := neg}`, `(A → ⊥) = ¬A` bridge) elaborate via
      `lake build` / `lean_multi_attempt`.
- [ ] Phase 3 `grind`-through-notation finding is reproducible (positive or negative).
- [ ] Phase 4 packet covers all eight §6 review items and carries the AI-policy header.
- [ ] No agent-produced artifact contains ready-to-post PR/Zulip prose (AI policy compliance).
- [ ] Conditional Phases 7-8: full CSLib CI pipeline green (`lake build`, `checkInitImports`,
      `lint-style`, `shake`, `lake test`).

## Artifacts & Outputs

- `review-scaffolding/01_comparison-tables.md` — design/naming/precedence/file-org tables.
- `review-scaffolding/02_falsum-bridge-sketch.md` — verified `Bot`/`Top`-reuse + derived-`¬` snippets.
- `review-scaffolding/03_grind-direction-finding.md` — empirical `_def`-direction result.
- `review-scaffolding/04_review-packet.md` — consolidated human-ready scaffolding (points + exhibits).
- Human-authored review posted on #607 / Zulip (Phase 5, human-only).
- Conditional code: updated `Defs.lean` / `Connectives.lean`, `NOTATION.md`, `ORGANISATION.md`.

## Rollback/Contingency

- Phases 1-4 produce only new scaffolding files under `review-scaffolding/`; delete them to revert —
  no source code touched.
- Phase 5/6 are human/external; nothing to roll back.
- Conditional Phases 7-8 are isolated to a fork rebase after #607 merges; perform on a feature branch
  and revert via git if CI fails. If #607 stalls or is rejected, Phases 7-8 stay [BLOCKED] and the
  fork's existing local `Connectives.lean` + notation remain the fallback (no regression).
- If `grind`-through-notation (Phase 3) proves impossible, the review reports the negative result and
  defers to keeping the `_def` lemmas as-is — chenson's CHANGES_REQUESTED may then persist upstream,
  which is an upstream decision, not a fork blocker.
