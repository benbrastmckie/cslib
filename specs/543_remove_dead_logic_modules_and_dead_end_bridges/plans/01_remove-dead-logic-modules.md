# Implementation Plan: Remove Dead Logic Modules and Dead-End Bridges

- **Task**: 543 - remove_dead_logic_modules_and_dead_end_bridges
- **Status**: [IMPLEMENTING]
- **Effort**: 2 hours
- **Dependencies**: None
- **Research Inputs**: reports/01_dead-logic-modules-triage.md
- **Artifacts**: plans/01_remove-dead-logic-modules.md (this file)
- **Standards**: plan-format.md; status-markers.md; artifact-management.md; tasks.md
- **Type**: cslib

## Overview

The 2026-07-23 logic-trees review flagged three module groups (M5-M7) as candidate dead or
dead-end code. The triage report resolved each group to a concrete, evidence-backed decision:
exactly one group is genuinely dead and deleted; the other two are retained (one because its
"unused" premise was refuted, one because it is a mathematically substantive showcase) with only
their overclaiming docstrings corrected. This plan implements those three decisions verbatim and
records the per-module rationale for the completion summary. Definition of done: the confirmed
dead module and its single barrel entry are removed, all four groups of docstrings tell the
truth, `lake build` + `lake exe checkInitImports` + `lake shake` + `lake test` are green, and the
net `git diff --stat` LOC delta (down) is recorded.

### Research Integration

Integrated `reports/01_dead-logic-modules-triage.md`. Per-group decisions carried directly into
phases:
- **Group 1 — `Foundations/Logic/PropositionalTableau.lean` (212 L): DELETE.** Confirmed dead:
  header self-declares deprecation; successor `Foundations/Logic/Tableau.lean` re-exports the
  refactored generic infrastructure; the only build reference is barrel `Cslib.lean:104`; the two
  remaining grep hits are provenance *prose* in `Tableau/PropositionalRules.lean:15` and
  `Tableau/Sign.lean:19`, not imports.
- **Group 2 — `Foundations/Logic/Automation/HilbertSearch.lean` (268 L): KEEP.** Task premise
  refuted — it is a live tactic exercised by a wired-in `lake test` suite
  (`CslibTests/HilbertSearch.lean`, registered at `CslibTests.lean:11`, testDriver per
  `lakefile.toml:4`). No code change; Phase 3 `lake test` proves the keep decision.
- **Group 3 — `Propositional/Semantics/Algebra/Bridge.lean` (130 L) + `KripkeBridge.lean`:
  KEEP as independent showcase + fix overclaiming docstrings.** Routing consumers through them was
  rejected as net-negative (layering inversion for `Bool.lean`; major refactor discarding the
  working derivability-route completeness proof for `KripkeBridge.lean`). Barrel entries
  `Cslib.lean:538` and `:560` are retained.

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

No ROADMAP.md consulted (no roadmap_path in delegation context).

## Goals & Non-Goals

**Goals**:
- Delete the one confirmed-dead module (`PropositionalTableau.lean`) and its sole barrel entry.
- Remove the two now-dangling provenance references to the deleted module path from
  `Tableau/PropositionalRules.lean` and `Tableau/Sign.lean` docstrings.
- Correct the overclaiming Group-3 docstrings so no docstring asserts a consumer/reuse relationship
  that does not exist (`Bool.lean`, `Algebra.lean`, `Bridge.lean` header, `KripkeBridge.lean`
  header).
- Keep the build clean: no new `sorry`, no new axiom, no broken imports; net LOC down.
- Record each per-module decision and the final LOC delta for the summary.

**Non-Goals**:
- Deleting `HilbertSearch.lean` (premise refuted — would delete a passing test suite).
- Deleting `Bridge.lean` / `KripkeBridge.lean` (substantive dualities; git already preserves
  history — deletion is explicitly not recommended).
- Wiring `HilbertSearch` into Modal/Bimodal derivations (additive enhancement; out of scope for a
  dead-code sweep — a separate feature task if desired).
- Re-routing `Bool.lean` or the IPL completeness chain through the bridge modules (net-negative;
  rejected in triage).
- Any change to proof terms, definitions, or theorem statements.

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| A hidden consumer of `PropositionalTableau` exists beyond the barrel | H | L | Triage grep found only barrel + prose; Phase 1 re-greps for residual `import`/symbol references before deletion, and `lake build` + `checkInitImports` + `shake` catch any dangling import |
| Manual barrel edit leaves `Cslib.lean` malformed or mis-ordered | M | L | Edit exactly one line (`:104`); verify with `lake exe checkInitImports`; do not run `mk_all` (regenerates only for additions) |
| Docstring reword accidentally alters a doc-comment that gates elaboration (e.g. `/-!` module doc vs `/--` decl doc) | M | L | Edits are prose-only inside existing comment blocks; `lake build` after edits confirms no elaboration change |
| `lake shake` proposes unrelated import removals | L | M | Only act on `shake` findings tied to the deleted module; leave unrelated suggestions for a separate task |
| `lake test` was already red before this change | M | L | If red, capture baseline and confirm the failure is unrelated to touched files before proceeding; the Group-2 keep claim only needs the `HilbertSearch` suite green |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1, 2 | -- |
| 2 | 3 | 1, 2 |

Phases within the same wave can execute in parallel. Phase 1 (Group 1 deletion, under
`Foundations/Logic/`) and Phase 2 (Group 3 docstrings, under `Logics/Propositional/Semantics/`)
touch disjoint files and may run in parallel; Phase 3 verifies the combined result.

### Phase 1: Delete PropositionalTableau and fix provenance docstrings [COMPLETED]

- **Goal:** Remove the confirmed-dead Group-1 module, its single barrel entry, and the two
  dangling provenance references to its module path.
- **Tasks:**
  - [x] Re-grep to confirm no non-barrel, non-prose reference remains:
        `grep -rn "PropositionalTableau" --include=*.lean Cslib Cslib.lean CslibTests` — expect only
        `Cslib.lean:104` (import), `Tableau/PropositionalRules.lean:15` (prose),
        `Tableau/Sign.lean:19` (prose). Confirmed exact match.
  - [x] Delete file `Cslib/Foundations/Logic/PropositionalTableau.lean` (~212 lines).
  - [x] Delete barrel line `Cslib.lean:104`
        (`public import Cslib.Foundations.Logic.PropositionalTableau`).
  - [x] Reword `Cslib/Foundations/Logic/Tableau/PropositionalRules.lean:15`: replace "refactored
        from `Cslib.Foundations.Logic.PropositionalTableau` into the generic ..." with "refactored
        from the original monolithic propositional-tableau module into the generic ..." (drop the
        dead module path).
  - [x] Reword `Cslib/Foundations/Logic/Tableau/Sign.lean:19`: replace "unifies the `PropSign`
        from `Cslib.Foundations.Logic.PropositionalTableau` and the ..." to drop the dead module
        path (e.g. "unifies the earlier `PropSign` and the ..."); the following sentence about a
        single canonical definition already carries the point.
  - [x] `lake build` (targeted: `Cslib.Foundations.Logic.Tableau` and dependents) to confirm the
        deletion breaks nothing. Green (718 jobs); also confirmed with full `lake build Cslib`
        (3249 jobs) after a transient concurrent-build olean staleness resolved on retry.
  - [x] `lake exe checkInitImports` and `lake shake` to confirm the barrel is consistent and no
        stale import lingers. `checkInitImports` clean (no output). `shake` reports many
        pre-existing unrelated import-minimization findings across the library, but none
        reference `PropositionalTableau`, `Cslib.lean`, `PropositionalRules.lean`, or
        `Sign.lean` — nothing tied to this deletion; left untouched per plan.
- **Timing:** ~45 min
- **Depends on:** none
- **Files to modify:**
  - `Cslib/Foundations/Logic/PropositionalTableau.lean` — delete entirely.
  - `Cslib.lean` — delete line 104 only (retain 538, 560).
  - `Cslib/Foundations/Logic/Tableau/PropositionalRules.lean` — reword line 15 provenance prose.
  - `Cslib/Foundations/Logic/Tableau/Sign.lean` — reword line 19 provenance prose.
- **Verification:**
  - `grep -rn "PropositionalTableau" --include=*.lean Cslib Cslib.lean` returns nothing.
  - Targeted `lake build` green; `checkInitImports` and `shake` report no issue tied to the deletion.
  - No `sorry`/axiom introduced (pure deletion + prose).

---

### Phase 2: Truth-fix Group-3 overclaiming docstrings [COMPLETED]

- **Goal:** Make the Group-3 docstrings honest — remove claims that `Bridge.lean` /
  `KripkeBridge.lean` are reused by downstream work, and point future work at the actual in-tree
  bridge. No code, definition, or proof changes.
- **Tasks:**
  - [x] `Cslib/Logics/Propositional/Semantics/Bool.lean` (~lines 41-46 and the follow-on
        "three-evaluator story" sentence ~47-49): redirect future DPLL/Tseitin work to Bool.lean's
        *own* direct Bool↔Prop bridge (`BoolEvaluate_eq_iff`, `Evaluate_eq_BoolEvaluate`,
        `tautology_iff_boolEvaluate_true`) as the thing to reuse, and demote the
        `Semantics/Algebra/Bridge.lean` mention to a "see also (algebraic reformulation)" rather
        than the canonical bridge to reuse.
  - [x] `Cslib/Logics/Propositional/Semantics/Algebra.lean` (~lines 49-51): reframe "The canonical
        narrative tying all three evaluators together lives in `Semantics/Algebra/Bridge.lean`" to
        a neutral pointer describing `Bridge.lean` as a self-contained development of the
        `Evaluate`/`BoolEvaluate` ↔ `AlgEvaluate` correspondence with no in-tree consumer.
  - [x] `Cslib/Logics/Propositional/Semantics/Algebra/Bridge.lean` (module header `/-! ... -/`):
        reframe from "canonical bridge reused by downstream work" to "self-contained development of
        the three-evaluator correspondence; no in-tree consumer."
  - [x] `Cslib/Logics/Propositional/Semantics/Algebra/KripkeBridge.lean` (module header; the design
        note at ~lines 59-62 already half-states this): add an explicit "independent showcase — the
        IPL completeness chain uses the derivability route in `Algebra.Completeness`, not this
        semantic duality; no chain routes through this module" note.
  - [x] `lake build` (targeted: `Cslib.Logics.Propositional.Semantics.Algebra` and the two bridge
        modules) to confirm the doc-comment edits change no elaboration. Green (715 jobs,
        `Bool.lean` built transitively as a dependency of `Bridge.lean`).
- **Timing:** ~30 min
- **Depends on:** none
- **Files to modify:**
  - `Cslib/Logics/Propositional/Semantics/Bool.lean` — reword docstring lines ~41-49.
  - `Cslib/Logics/Propositional/Semantics/Algebra.lean` — reword docstring lines ~49-51.
  - `Cslib/Logics/Propositional/Semantics/Algebra/Bridge.lean` — reword module header.
  - `Cslib/Logics/Propositional/Semantics/Algebra/KripkeBridge.lean` — add showcase note to header.
- **Verification:**
  - No docstring in these four files asserts a consumer/reuse relationship that the import graph
    does not support.
  - Targeted `lake build` green; no proof terms or statements changed (diff is comment-only).

---

### Phase 3: Full verification and LOC accounting [NOT STARTED]

- **Goal:** Prove the combined change is clean library-wide, confirm the Group-2 keep decision via
  the test suite, and record the net LOC delta and per-module decisions for the summary.
- **Tasks:**
  - [ ] Full `lake build` — entire library compiles with `PropositionalTableau` removed.
  - [ ] `lake test` — confirms the `HilbertSearch` suite (`CslibTests/HilbertSearch.lean`) is still
        green, empirically validating the Group-2 KEEP decision.
  - [ ] Final `lake exe checkInitImports` + `lake shake` clean.
  - [ ] Record `git diff --stat` net LOC delta (expected: down, driven by the ~213-line Group-1
        removal; Groups 2-3 net near-zero, comment-only).
  - [ ] Compile the per-module decision record for the completion summary: Group 1 DELETE
        (evidence), Group 2 KEEP (premise refuted — test suite green), Group 3 KEEP + docstring
        truth-fix (routing rejected).
- **Timing:** ~30 min
- **Depends on:** 1, 2
- **Files to modify:** none (verification and reporting only).
- **Verification:**
  - Full `lake build` and `lake test` green.
  - `checkInitImports` + `shake` clean.
  - Net LOC delta recorded and negative; per-module decision table captured for the summary.

## Testing & Validation

- [ ] `grep -rn "PropositionalTableau" --include=*.lean Cslib Cslib.lean` returns no matches.
- [ ] Full `lake build` succeeds.
- [ ] `lake test` succeeds; the `HilbertSearch` suite is green.
- [ ] `lake exe checkInitImports` reports no missing/extra barrel entries.
- [ ] `lake shake` reports no stale imports tied to the deletion.
- [ ] No new `sorry` and no new axiom introduced (`git diff` shows deletions + comment rewords only).
- [ ] The four Group-3 docstrings no longer overclaim a nonexistent consumer relationship.

## Artifacts & Outputs

- `plans/01_remove-dead-logic-modules.md` (this file).
- `summaries/01_remove-dead-logic-modules-summary.md` (produced by /implement) — must include the
  per-module decision table (Group 1 DELETE / Group 2 KEEP / Group 3 KEEP + docstring fix) and the
  recorded net LOC delta.
- Deleted: `Cslib/Foundations/Logic/PropositionalTableau.lean`.
- Edited: `Cslib.lean`, `Cslib/Foundations/Logic/Tableau/PropositionalRules.lean`,
  `Cslib/Foundations/Logic/Tableau/Sign.lean`,
  `Cslib/Logics/Propositional/Semantics/Bool.lean`,
  `Cslib/Logics/Propositional/Semantics/Algebra.lean`,
  `Cslib/Logics/Propositional/Semantics/Algebra/Bridge.lean`,
  `Cslib/Logics/Propositional/Semantics/Algebra/KripkeBridge.lean`.

## Rollback/Contingency

- All changes are on a single branch; `git` preserves the deleted `PropositionalTableau.lean` in
  history, so restoration is `git checkout <sha> -- Cslib/Foundations/Logic/PropositionalTableau.lean`
  plus re-adding the barrel line if the deletion must be reverted.
- If the full `lake build` in Phase 3 fails due to an unforeseen consumer of `PropositionalTableau`,
  restore the file and barrel line, keep the Phase 2 docstring fixes (independent), and re-open the
  Group-1 dead-code claim for a follow-up investigation rather than forcing the build green by
  discarding changes.
- Docstring-only edits (Phase 2 and the two Phase-1 rewords) carry no build risk and need no
  special rollback beyond `git restore --staged` / re-editing.
