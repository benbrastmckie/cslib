# Implementation Summary: Remove Dead Logic Modules and Dead-End Bridges

- **Task**: 543 - remove_dead_logic_modules_and_dead_end_bridges
- **Status**: [COMPLETED]
- **Started**: 2026-07-23T18:33:01Z
- **Completed**: 2026-07-23T19:10:00Z
- **Effort**: ~1.5 hours
- **Dependencies**: None
- **Artifacts**: plans/01_remove-dead-logic-modules.md, reports/01_dead-logic-modules-triage.md

## Overview

Task 543 executed the three per-group decisions from the 2026-07-23 logic-trees review triage
(`reports/01_dead-logic-modules-triage.md`) verbatim: deleted the one confirmed-dead module
(Group 1), left the falsely-flagged-as-dead `HilbertSearch.lean` untouched (Group 2, premise
refuted), and corrected four overclaiming docstrings on the two independent-showcase bridge
modules (Group 3) without touching any proof term. All three phases of
`plans/01_remove-dead-logic-modules.md` are complete.

## Per-Module Decision Record

| Group | Module(s) | Decision | Evidence |
|-------|-----------|----------|----------|
| 1 | `Cslib/Foundations/Logic/PropositionalTableau.lean` (212 lines) | **DELETE** | Header self-declared deprecation; successor `Foundations/Logic/Tableau.lean` re-exports the refactored generic infrastructure; only build reference was barrel `Cslib.lean:104`; two remaining grep hits were provenance *prose*, not imports (`Tableau/PropositionalRules.lean:15`, `Tableau/Sign.lean:19`) — now reworded to drop the dead path. |
| 2 | `Cslib/Foundations/Logic/Automation/HilbertSearch.lean` (268 lines) | **KEEP** (no change) | Task premise refuted — this is a live tactic exercised by a wired-in `lake test` suite (`CslibTests/HilbertSearch.lean`, registered at `CslibTests.lean:11`). Verified empirically: `lake build CslibTests.HilbertSearch` green (664 jobs) and full `lake test` exit code 0. |
| 3 | `Cslib/Logics/Propositional/Semantics/Algebra/Bridge.lean` (130 lines) + `KripkeBridge.lean` | **KEEP** as independent showcase + docstring truth-fix | Routing consumers through them was rejected as net-negative (layering inversion for `Bool.lean`; major refactor discarding the working derivability-route completeness proof for `KripkeBridge.lean`). Four docstrings (in `Bool.lean`, `Algebra.lean`, `Bridge.lean`, `KripkeBridge.lean`) reworded to state there is no in-tree consumer instead of claiming a canonical/reused-bridge relationship. Barrel entries `Cslib.lean:538` and `:560` (renumbered after the Group-1 line deletion, but unchanged in content) retained. |

## What Changed

- Deleted `Cslib/Foundations/Logic/PropositionalTableau.lean` (212 lines).
- Deleted the corresponding barrel line in `Cslib.lean`
  (`public import Cslib.Foundations.Logic.PropositionalTableau`).
- Reworded provenance prose in `Cslib/Foundations/Logic/Tableau/PropositionalRules.lean:15` and
  `Cslib/Foundations/Logic/Tableau/Sign.lean:19` to drop the now-dead module path reference.
- Reworded four docstrings to remove overclaiming consumer/reuse language:
  - `Cslib/Logics/Propositional/Semantics/Bool.lean` — points future DPLL/Tseitin work at
    `Bool.lean`'s own direct bridge (`BoolEvaluate_eq_iff`, `Evaluate_eq_BoolEvaluate`,
    `tautology_iff_boolEvaluate_true`), demotes `Bridge.lean` to a "see also" note.
  - `Cslib/Logics/Propositional/Semantics/Algebra.lean` — reframes the `Bridge.lean` reference
    as a self-contained development with no in-tree consumer.
  - `Cslib/Logics/Propositional/Semantics/Algebra/Bridge.lean` — module header reframed from
    "canonical bridge reused by downstream work" to "self-contained development ... no in-tree
    consumer."
  - `Cslib/Logics/Propositional/Semantics/Algebra/KripkeBridge.lean` — added an explicit
    "independent showcase" note: the IPL completeness chain uses the derivability route in
    `Algebra.Completeness`, not this semantic duality.
- No proof terms, definitions, or theorem statements were changed anywhere in this task.

## Decisions

- Group 1 deletion executed exactly as triaged; no hidden consumer found (re-grep before
  deletion matched the triage's predicted three hits exactly).
- Group 2 left untouched — deleting it would have removed a passing test suite; the plan's
  Non-Goals explicitly excluded this.
- Group 3 modules kept as independent showcases rather than refactored/routed, per the triage's
  net-negative assessment of routing `Bool.lean` and `KripkeBridge.lean` through the bridge
  layer.

## Verification

- `grep -rn "PropositionalTableau" --include=*.lean Cslib Cslib.lean CslibTests` — no matches.
- Targeted `lake build` after Phase 1 (`Cslib.Foundations.Logic.Tableau` and dependents): green
  (718 jobs).
- Targeted `lake build` after Phase 2 (`Semantics.Algebra`, `Semantics.Algebra.Bridge`,
  `Semantics.Algebra.KripkeBridge`, transitively `Semantics.Bool`): green (715 jobs).
- Full `lake build`: green (3249 jobs). One transient failure occurred on the first attempt
  (`error: target is out-of-date and needs to be rebuilt`), traced to concurrent-build olean
  contention from other in-flight agents in the same checkout (tasks 541/547); it was not
  reproducible and resolved cleanly on a single retry after a short wait, per the
  concurrent-work protocol in this task's delegation instructions.
- `lake exe checkInitImports`: clean (no output).
- `lake shake --add-public --keep-implied --keep-prefix`: no findings reference any file touched
  by this task (`PropositionalTableau`, `Cslib.lean`, `Tableau/PropositionalRules.lean`,
  `Tableau/Sign.lean`, `Semantics/Bool.lean`, `Semantics/Algebra.lean`,
  `Semantics/Algebra/Bridge.lean`, `Semantics/Algebra/KripkeBridge.lean`). Remaining findings are
  pre-existing, unrelated import-minimization suggestions across the wider library, left
  untouched per the plan.
- `lake test`: exit code 0. `CslibTests.HilbertSearch` additionally built directly as a targeted
  confirmation of the Group-2 KEEP decision (664 jobs, green).
- `git diff` across both source-touching commits (`5d1a8e5a`, `2794a102`) contains no added
  `sorry` or `axiom` lines (checked via `grep -E "^\+.*(sorry|axiom)"` against the diff — no
  matches).
- Net LOC delta: **8 files changed, 24 insertions(+), 228 deletions(-) = -204 lines net**,
  consistent with the plan's expectation (down, driven by the ~213-line Group-1 removal; Groups
  2-3 net near-zero, comment-only).

## Impacts

- Library-wide LOC reduced by 204 lines with no behavioral change.
- Two provenance docstrings and four Group-3 docstrings no longer reference a deleted module
  path or overclaim a nonexistent consumer relationship — future contributors reading
  `Bool.lean`, `Algebra.lean`, `Bridge.lean`, or `KripkeBridge.lean` will not be misdirected
  toward routing new work through the bridge modules.
- No change to any downstream consumer, test, or proof term.

## Plan Deviations

None. All three phases executed exactly as specified in
`plans/01_remove-dead-logic-modules.md`, with all tasks checked off `[x]` and no altered,
skipped, or deferred steps.

## Follow-ups

- None required by this task. The plan's Non-Goals (wiring `HilbertSearch` into Modal/Bimodal
  derivations; re-routing `Bool.lean`/IPL completeness through the bridge modules) remain
  explicitly out of scope and are candidate separate feature tasks if desired in the future.

## References

- `specs/543_remove_dead_logic_modules_and_dead_end_bridges/reports/01_dead-logic-modules-triage.md`
- `specs/543_remove_dead_logic_modules_and_dead_end_bridges/plans/01_remove-dead-logic-modules.md`
- Commits: `5d1a8e5a` (Phase 1), `2794a102` (Phase 2), `9b756156` (Phase 3)
