# Implementation Plan: Task #391

- **Task**: 391 - Strip docstring jargon & fix stale counts
- **Status**: [COMPLETED]
- **Effort**: 1.5 hours
- **Dependencies**: None (coordinate-only with task 400, which owns Connectives.lean)
- **Research Inputs**: specs/391_strip_docstring_jargon_fix_stale_counts/reports/01_docstring-jargon-stale-counts.md
- **Artifacts**: plans/01_strip-jargon-fix-counts.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: cslib
- **Lean Intent**: false

## Overview

Comment/docstring-only cleanup across a fixed set of pre-verified sites. Two work groups:
(A) strip internal task/process jargon (task NNN references, "Route A2", "rung", "4-for-4",
"from day one", "N proof files") from 6 public-docstring modules plus one in-proof-comment
module; (B) fix genuinely-stale counts and one misattached docstring, replacing brittle
line-number citations with lemma/role descriptions so they survive future edits by task 317.
Zero proof-logic changes and zero new sorries. Every edit site, its current text, and its exact
replacement are enumerated in the research report; this plan sequences them by risk and adds a
`lake build` + residual-jargon-grep verification gate.

### Research Integration

The research report (`reports/01_docstring-jargon-stale-counts.md`) verified every named site
against live code (constructor counts, `grep -c sorry`, referenced line numbers). It supplies
exact CURRENT and REPLACE text for each edit, classifies each count site as STALE (fix) or
CORRECT (leave), and gives a recommended implementation ordering. This plan adopts that ordering
and inlines the site inventory so the implementer works from a single sequenced list. The report's
"Verification checklist for implementer" becomes the Phase 2 verification gate.

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

No ROADMAP.md consulted for this task (roadmap_flag not set).

## Goals & Non-Goals

**Goals**:
- Remove internal task/process jargon from all 6 public-docstring sites (A1-A6) and the one
  in-proof-comment site (A7).
- Fix the two genuinely-stale case counts (IntSoundness 3->9, MinSoundness 2->8) by rewording
  to count-free prose that will not re-stale.
- Correct the misattached consistency docstring on `lift_int_to_cl` (IntLindenbaum.lean:262).
- Replace brittle `Scheme.lean:246/519` line references (actual 409/1070) with lemma/role
  descriptions in both DecisionProcedure modules; correct the wrong "4 sorries in
  Minimal/Completeness.lean" count in Minimal/DecisionProcedure.lean:23.
- Strip the "handed to task 317" jargon in Minimal/Completeness.lean:49.
- Keep the build green and confirm no residual jargon remains via grep.

**Non-Goals**:
- No proof-logic, tactic, or term changes anywhere (comment/docstring text only).
- No editing of `Cslib/Foundations/Logic/Connectives.lean` (owned by task 400).
- No change to the StrongCompleteness "3 cases: atom, bot, imp" phrases
  (IntStrongCompleteness.lean:107, MinStrongCompleteness.lean:121) — verified CORRECT.
- No change to `int_consistent` at IntLindenbaum.lean:274 — correctly attached.
- No filling of the pre-existing deferred sorries (owned by task 317, on hold).
- No aggressive trimming of the ListImplication L126-139 derivation block beyond the three
  named conversational-line edits.

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Damaging a `/-! -/` or `/-- -/` delimiter breaks the build | M | L | Edit text inside delimiters only; run `lake build` per edited module in Phase 2 gate |
| Accidentally editing a tactic/term line in ListImplication.lean | M | L | A7 isolated to Phase 2, comment-text only; immediate `lake build`; git diff review of that file's changed lines |
| Editing Connectives.lean (task 400 territory) | H | L | Connectives.lean explicitly out of scope; Phase 2 asserts `git diff` does not list it |
| Changing a CORRECT "3 cases" phrase (StrongCompleteness) | M | L | Enumerated in leave-unchanged list; grep gate excludes those files from jargon sweep |
| Line-number-based fixes re-staling later | L | M | Replace line numbers with lemma/role descriptions per research recommendation |
| Reworded count prose re-staling if axioms change | L | L | Use count-free prose (list connective groups, not a number) per research B1/B2 |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2 | 1 |

Phases within the same wave can execute in parallel.

### Phase 1: Docstring & Header Edits (A1-A6, B1-B6) [COMPLETED]

**Goal**: Apply all jargon-strip and stale-count edits that live entirely within `/-! -/` or
`/-- -/` docstring/header blocks (mechanically safe — no proof-body proximity). Follow the
research report's exact CURRENT->REPLACE text for each site.

**Tasks**:

Part A — jargon strips (public docstrings):
- [x] A1 `Cslib/Logics/Propositional/Metalogic/ClassicalConjImpCompleteness.lean` — strip "task 352" / "CL-B rung" at L19, L23, L51, L57 (drop `Task 352:` prefix, keep file ref). Per report A1.
- [x] A2 `Cslib/Logics/Propositional/Metalogic/ClassicalConjImpBotCompleteness.lean` — strip "task 352/378" and "CL-C rung" at L18, L23, L37, L52, L55, L61-65, L178, L182, L476-477. Keep CL-A/CL-B/CL-C table labels; drop trailing `(task NNN)` and `Task NNN:` prefixes. Per report A2 + decision note. *(deviation: altered -- also stripped a stale "4-for-4" phrase at the conservativity docstring L479 in this same file, mirroring the A3 fix in ConservativeChain.lean; the table immediately below lists exactly 3 items (CL-A/B/C), so "4-for-4" was inaccurate and would otherwise have failed the Phase 2 residual-jargon grep gate.)*
- [x] A3 `Cslib/Logics/Propositional/Semantics/Algebra/ConservativeChain.lean:44` — replace "4-for-4" scorekeeping (also stale) with "All three classical conservativity results (CL-A, CL-B, CL-C)". Per report A3.
- [x] A4 `Cslib/Logics/Propositional/Semantics/Algebra/HilbertLindenbaumRel.lean:21-22` — strip "Route A2" and "341 proof files"; reword to the fresh-relativized-copy phrasing. Per report A4.
- [x] A5 `Cslib/Foundations/Logic/Tableau/RuleResult.lean:34-35` — strip "from day one" and "(tasks 299-301)". Per report A5.
- [x] A6 `Cslib/Foundations/Logic/PropositionalTableau.lean:7` — strip "See task 297." from the DEPRECATED comment; keep the successor-module pointer. Per report A6.

Part B — stale-count / misattached / line-ref fixes (docstrings):
- [x] B1 `Cslib/Logics/Propositional/Metalogic/IntSoundness.lean:41` — replace "The 3 cases are:" (+3-item list) with count-free prose covering all 9 axiom cases. Per report B1 (prefer reworded prose).
- [x] B2 `Cslib/Logics/Propositional/Metalogic/MinSoundness.lean:42` — replace "The 2 cases are:" (+2-item list) with count-free prose covering all 8 axiom cases. Per report B2.
- [x] B3 `Cslib/Logics/Propositional/Metalogic/IntLindenbaum.lean:262` — replace the misattached `IntPropAxiom is consistent` docstring on `lift_int_to_cl` with the derivation-tree-lifter docstring. Leave L274 (`int_consistent`) untouched. Per report B3.
- [x] B4 `Cslib/Logics/Propositional/Tableau/Intuitionistic/DecisionProcedure.lean:38-42,44-46,56-59` — rewrite "Notes on sorry" to drop brittle line numbers (Scheme.lean:246/519 -> role descriptions), strip task 317/422 jargon. Per report B4.
- [x] B5 `Cslib/Logics/Propositional/Tableau/Minimal/DecisionProcedure.lean:23,44-52,63-66` — fix wrong "4 sorries in Minimal/Completeness.lean" (L23) to defer to Notes block; replace Scheme line refs with role descriptions; strip task 317/422 jargon. Per report B5.
- [x] B6 `Cslib/Logics/Propositional/Tableau/Minimal/Completeness.lean:49` — strip "handed to task 317" -> "deferred completeness obligations" (jargon-only, no count present). Per report B6. *(deviation: altered -- also stripped three additional "task 317" mentions in this same file (docstrings at L69, L89, L103, and an in-proof scratch comment at L109) that were not in the original site enumeration; these were the same jargon category and were required to satisfy the Phase 2 residual-jargon grep gate, which scans the whole file.)*

**Timing**: 1 hour

**Depends on**: none

**Files to modify**:
- `Cslib/Logics/Propositional/Metalogic/ClassicalConjImpCompleteness.lean` - strip task/rung jargon (A1)
- `Cslib/Logics/Propositional/Metalogic/ClassicalConjImpBotCompleteness.lean` - strip task/rung jargon, keep CL-x labels (A2)
- `Cslib/Logics/Propositional/Semantics/Algebra/ConservativeChain.lean` - replace "4-for-4" stale scorekeeping (A3)
- `Cslib/Logics/Propositional/Semantics/Algebra/HilbertLindenbaumRel.lean` - strip Route A2 / N-proof-files (A4)
- `Cslib/Foundations/Logic/Tableau/RuleResult.lean` - strip "from day one" / task refs (A5)
- `Cslib/Foundations/Logic/PropositionalTableau.lean` - strip "See task 297" (A6)
- `Cslib/Logics/Propositional/Metalogic/IntSoundness.lean` - stale 3->9 case count reworded (B1)
- `Cslib/Logics/Propositional/Metalogic/MinSoundness.lean` - stale 2->8 case count reworded (B2)
- `Cslib/Logics/Propositional/Metalogic/IntLindenbaum.lean` - fix misattached docstring on lift_int_to_cl (B3)
- `Cslib/Logics/Propositional/Tableau/Intuitionistic/DecisionProcedure.lean` - stale line refs -> role descriptions + jargon strip (B4)
- `Cslib/Logics/Propositional/Tableau/Minimal/DecisionProcedure.lean` - wrong sorry count + stale line refs + jargon strip (B5)
- `Cslib/Logics/Propositional/Tableau/Minimal/Completeness.lean` - jargon-only strip at L49 (B6)

**Verification**:
- All edits confined to `/-! -/` or `/-- -/` blocks; no tactic/term/definition lines changed.
- `git diff` does NOT list `Cslib/Foundations/Logic/Connectives.lean`.
- `IntStrongCompleteness.lean:107`, `MinStrongCompleteness.lean:121`, `IntLindenbaum.lean:274`
  remain untouched.
- Spot-read each edited docstring to confirm the REPLACE text matches the research report and
  reads cleanly (delimiters intact).

---

### Phase 2: In-Proof Comments (A7) + Verification Gate [COMPLETED]

**Goal**: Apply the three isolated in-proof comment edits in ListImplication.lean (highest-risk
site — sits inside tactic proofs), then run the full build + grep verification gate over all
edited modules to confirm the build is green and no residual jargon remains.

**Tasks**:
- [x] A7 `Cslib/Foundations/Logic/Metalogic/ListImplication.lean` — COMMENT-TEXT ONLY, do NOT touch any tactic line:
  - L83: replace `-- Need: ⊢ (φ → ψ) → φ → ψ ... no.` with the base-case identity comment (report A7).
  - L131: delete the discarded-attempt line `--   from ⊢ (A → B) → C ... that's not right.`
  - L133: replace `-- Let me think differently. We need:` with `-- Correct route. We need:`
  - (Optional L126-139 trimming is OUT OF SCOPE; keep edits minimal to protect proof bodies.)
- [x] Run `lake build` for `Cslib.Foundations.Logic.Metalogic.ListImplication` immediately after A7.
- [x] Run `lake build` (scoped to each edited module, or whole project) to confirm all comment
      edits compile green. Full project `lake build` (3189 jobs) green.
- [x] Run residual-jargon grep over the edited files:
      `grep -rnE "task [0-9]+|Route A2|[0-9]+ proof files|day one|4-for-4|CL-. rung"`
      — no hits (0 lines).
- [x] Confirm `git diff --name-only` does NOT include `Cslib/Foundations/Logic/Connectives.lean`.
      Confirmed absent from diff.
- [x] Confirm no tactic/term lines changed in `ListImplication.lean` (git diff shows only
      comment lines). Confirmed via `git diff`.

**Timing**: 0.5 hours

**Depends on**: 1

**Files to modify**:
- `Cslib/Foundations/Logic/Metalogic/ListImplication.lean` - in-proof scratch comments L83, L131, L133 (comment-text only)

**Verification**:
- `lake build` green for ListImplication and every other edited module (comment edits are inert;
  a green build is expected and confirms delimiters intact).
- Residual-jargon grep returns nothing except retained CL-x table labels.
- `git diff` excludes Connectives.lean and shows only comment/docstring line changes.

---

## Testing & Validation

- [x] `lake build` succeeds for all edited modules (no delimiter damage, no proof-body change).
      Full project build green (3189 jobs).
- [x] `git diff --name-only` does not list `Cslib/Foundations/Logic/Connectives.lean`. Confirmed.
- [x] `IntStrongCompleteness.lean:107` and `MinStrongCompleteness.lean:121` "(3 cases: atom, bot,
      imp)" phrases unchanged. Confirmed (no diff on either file).
- [x] `IntLindenbaum.lean:274` (`int_consistent`) docstring unchanged; only L262 fixed. Confirmed.
- [x] Residual-jargon grep over edited files returns nothing (except retained CL-x row labels).
      Confirmed (0 hits after also fixing an extra "4-for-4" stale phrase found by the grep in
      ClassicalConjImpBotCompleteness.lean and extra task-317 mentions in Minimal/Completeness.lean;
      see deviation notes on A2/B6 above).
- [x] No tactic/term lines changed in `ListImplication.lean`. Confirmed via `git diff`.
- [x] No new `sorry` and no axiom introduced (`git diff` shows comment text only). Confirmed:
      `lake test` passes, `lake exe checkInitImports` clean, `lake exe lint-style` clean, `lake lint`
      shows zero new warnings in edited files (2 pre-existing unrelated warnings in
      Temporal/Theorems.lean, not touched by this task).

## Artifacts & Outputs

- 12 edited `.lean` files with jargon-free / count-accurate docstrings and comments.
- Green `lake build` across all edited modules.
- No new task artifacts beyond this plan and the eventual execution summary.

## Rollback/Contingency

All changes are comment/docstring text with no logic impact. If `lake build` fails after any
edit, a delimiter was damaged: inspect the failing module's `git diff`, restore the delimiter
(or `git checkout -- <file>` to revert that single file) and re-apply the text edit carefully.
Because edits are per-file independent, reverting one file does not affect the others. Full
rollback is `git checkout -- <list of edited files>`; no state or build artifacts persist.
