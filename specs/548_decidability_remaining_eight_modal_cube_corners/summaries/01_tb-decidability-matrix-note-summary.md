# Implementation Summary: TB Decidability + Intentional-Completeness Matrix Note

- **Task**: 548 - Decidability for the remaining modal-cube corners (SCOPE NARROWED)
- **Status**: [COMPLETED]
- **Plan**: `plans/01_tb-decidability-matrix-note.md`

## Overview

Landed both deliverables the plan committed to: TB decidability end-to-end (frame condition,
validity predicate, extractor, rule, full `RuleApplicationSpec` discharge, truth lemma,
soundness, completeness, `tbValid_decides`, `instDecidableTBValid`), taking the modal-cube
decidability matrix from 7/15 to 8/15; and the intentional-completeness matrix note documenting
the remaining seven corners (D, DB, K4, D4, K45, D5, D45) with frame condition, tier, named
gate, and cost estimate.

## Phases Completed

All 11 phases completed, none blocked, none partial.

| Phase | Name | Result |
|-------|------|--------|
| 1 | Intentional-completeness matrix note | Landed in a prior dispatch |
| 2 | TB frame condition, validity, extraction | Landed in a prior dispatch |
| 3 | TB rule and agreement lemma | Landed in a prior dispatch |
| 4 | `TBDriver.lean` skeleton, shape lemmas, barrel | New module, `Cslib.lean` entry |
| 5 | `RuleApplicationSpecCore` F1-F7 | Termination fields (rankStep/outDegStep/knownWorldsStep) discharged without incident |
| 6 | F8-F12 + `modalApplyOneTB_spec` assembly | Full `RuleApplicationSpec`, not Core-only |
| 7 | Generic Hintikka/saturation chain instantiation | `modalExpandBranchesTB_hintikka` one-liner; `accSourcesKnown`/`accTargetsKnown` reuse confirmed, not re-derived |
| 8 | TB modal truth lemma + open-branch countermodel | Three-way `.refl`/`.single (.inl)`/`.single (.inr)` decomposition as predicted |
| 9 | TB soundness | `hAgreeTB`/`modalApplyOneTB_boxPos_soundIn`/`_diaNeg_soundIn`/`modalTableauTB_sound` |
| 10 | TB completeness, `tbValid_decides`, `instDecidableTBValid` | Plus `CslibTests/` smoke checks |
| 11 | Final verification gate + matrix-note reconciliation | All audits pass (see below) |

## Key Implementation Decisions

- **`TBDriver.lean` treats `modalApplyOneB`'s own result as an opaque witness** satisfying the
  already-proven `modalApplyOneB_spec`, rather than re-deriving B's contribution from
  `FrameRules.lean` primitives the way `BDriver.lean` had to re-derive from K's. Every field
  discharge consumes `modalApplyOneB_spec.<field>` directly. This is a deviation from the plan's
  literal Phase 4 task list (which anticipated re-deriving B's cross-world predecessor-membership
  helpers) but is a strictly stronger reuse of `modalApplyOneB_spec`, consistent with the plan's
  own stated rationale for the B-inner layering (Phase 3).
- **Phase 9's "`modalApplyOneTB_sound` combining the four" landed as the `hAgreeTB`/
  `modalApplyOneTB_boxPos_soundIn`/`modalApplyOneTB_diaNeg_soundIn` triple**, mirroring exactly
  how T and B are each instantiated (neither has a single combining theorem of that name either).
- The three termination fields (the plan's highest-named risk) discharged cleanly on the first
  attempt — the "conjunction of independently-terminating arm families" argument held exactly as
  the risk-mitigation table predicted.

## Verification Evidence

- `lake build Cslib`: green, 0 errors.
- `lake exe checkInitImports`: passes.
- Zero live `sorry` in `Cslib/Logics/Modal/Tableau/` (`grep -rnE` for both single-line and
  trailing-`sorry` forms returns no matches; all textual "sorry" occurrences are prose/docstring
  mentions).
- Standard axiom triple (`propext`, `Classical.choice`, `Quot.sound`) confirmed via
  `lean_verify`/`#print axioms`-equivalent on all six capstone declarations:
  `modalApplyOneTB_spec`, `modalTruthLemmaTB`, `modalOpenBranchTB_countermodel`,
  `modalTableauTB_sound`, `modalTableauTB_complete`, `tbValid_decides`, `instDecidableTBValid`.
- Frozen-declaration audit: `git diff` against the pre-task base across every file this task
  touched (`Cslib.lean`, `FrameRules.lean`, `FrameSoundness.lean`, `FrameCompleteness.lean`,
  `TBDriver.lean` (new), `CslibTests/ModalFrameSeparation.lean`) totals **2124 insertions(+), 0
  deletions(-)** — purely additive across the whole task span, not just per-file. `S4/` and
  `LoopChecking.lean` show an empty diff (untouched).
- `FmpMeasure.lean` no-touch audit: empty diff against the pre-task base.
- Scope audit: no `dValid`/`k4Valid`/`k45Valid`/`d4Valid`/`d5Valid`/`d45Valid`/`dbValid` added.
- Matrix-note reconciliation: the Phase 1 note already stated 8/15 and named
  `instDecidableTBValid`/`modalTableauTB` correctly (written prospectively in the earlier
  dispatch); every declaration-name anchor cited in the "Covered (8/15)" table resolves in-tree.
- Regression tests green: `CslibTests.S4LoopGuardRegression`, `CslibTests.ModalFrameSeparation`
  (including the three new TB smoke-check rows: T axiom, B axiom, 4-axiom countermodel),
  `CslibTests.TableauConformance`.
- No task-number citations in any file outside `specs/**` touched by this task (confirmed by
  direct grep; the repo-wide `check-task-references.sh` lint gate does report pre-existing,
  unrelated violations in `.memory/` from prior tasks 317/426/427/552/557 — none in files this
  task modified, and fixing them is out of scope).

## Plan Deviations

- Phase 4's "local universe-membership helpers" task item was not needed as a separate step
  (see "Key Implementation Decisions" above) — annotated inline in the plan file.
- Phase 9's "`modalApplyOneTB_sound`" landed as a three-theorem triple rather than one combining
  theorem — annotated inline in the plan file, consistent with T/B precedent.
- Phase 2's docstring records that the front-loaded `tbFC`-relative `branchSatisfiableIn_tbFC_*`/
  `modalTBoxSelf_tbFC_sound`/`modalBBoxBack_tbFC_sound` lemmas (landed in a prior dispatch) are
  genuine in-tree semantic infrastructure but, matching T's own `branchSatisfiableIn_reflFC_*`
  precedent, are not directly invoked by the `sfSat`/`RuleResultSat`-based chain
  `modalTableauTB_sound` actually uses.

## Files Modified

- `Cslib/Logics/Modal/Tableau/TBDriver.lean` (new, ~910 lines)
- `Cslib/Logics/Modal/Tableau/FrameRules.lean` (append, Phase 3, prior dispatch)
- `Cslib/Logics/Modal/Tableau/FrameSoundness.lean` (append, Phase 2, prior dispatch)
- `Cslib/Logics/Modal/Tableau/FrameCompleteness.lean` (append: extraction (prior dispatch), TB
  truth lemma, TB soundness discharges, TB completeness, `tbValid_decides`,
  `instDecidableTBValid`, matrix note (prior dispatch))
- `Cslib.lean` (one barrel import line for `TBDriver`)
- `CslibTests/ModalFrameSeparation.lean` (append: TB smoke checks)

## Non-Goals Honored

D, DB, K4, D4, K45, D5, D45 remain undocumented-as-implemented (documented only, per the matrix
note). No generic-driver abstraction was built. No serial-rule spec, Euclidean combinator, or S4
stepper-stack work was attempted — these remain named, out-of-scope gates for successor tasks.
`FmpMeasure.lean` was not touched.
