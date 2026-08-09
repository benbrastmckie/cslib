# Implementation Summary: Promote the three cited-but-absent propositional refutation witnesses into CslibTests/

- **Task**: 592
- **Status**: [COMPLETED]
- **Plan**: `specs/592_promote_propositional_refutations_to_cslibtests/plans/01_promote-refutation-witnesses-cslibtests.md`
- **Research**: `specs/592_promote_propositional_refutations_to_cslibtests/reports/01_promote-refutation-witnesses-cslibtests.md`

## Overview

All seven plan phases completed. Two refutation witnesses previously living unbuilt under
`specs/archive/430_prove_atom_persistence_upward_closure_for_intexpan/scratch/` are now
CI-protected regression tests in `CslibTests/`, and all fourteen in-source citations across
`Cslib/Logics/Propositional/Tableau/` that pointed at the old, unresolvable `scratch/`-relative
paths now resolve from the repository root.

## What was built

- `CslibTests/HvalidShapeRefutation.lean` (new) -- module-mode promotion of the `hvalid`-shape
  refutation witness, namespace `CslibTests.HvalidShapeRefutation`, every declaration
  docstringed, zero warnings/info under `--wfail --iofail`.
- `CslibTests/BetaSplitRefutation.lean` (new) -- module-mode promotion of the beta-split
  closure-asymmetry witness, namespace `CslibTests.BetaSplitRefutation`. Nine load-bearing
  `#eval`s converted to `#guard_msgs`-asserted regression checks (values derived from a live
  `lake env lean` run and cross-checked against the research report, not hand-transcribed);
  seven non-load-bearing `#eval`s dropped (their `def`s retained for interactive inspection).
  Every declaration docstringed. Zero warnings/info under `--wfail --iofail`.
- `CslibTests.lean` -- two `public import` lines added in ASCII sort order.
- Fourteen citations repointed across four files in `Cslib/Logics/Propositional/Tableau/`:
  `Minimal/Completeness.lean` (2 sites), `Intuitionistic/Completeness.lean` (4 sites),
  `Intuitionistic/Expansion.lean` (1 site), `Intuitionistic/Scheme.lean` (7 sites, including the
  `:3474` `PersistPrototype.lean` site repaired to the full archive path per Finding 8). Every
  verdict word (`REFUTED`, `PERMANENTLY DEFERRED`, `DISPOSITION UNDECIDED`, `[UNVERIFIED]`) left
  byte-identical; only path characters and line-wrapping changed.
- `gate-baseline.txt` / `gate-baseline-targets.txt` (Phase 1) and `gate-final.txt` /
  `gate-final-targets.txt` (Phase 7) -- the HEAD baseline and final `--wfail --iofail`
  failing-target snapshots used for the set-difference acceptance check.

## Verification

- `lake build --wfail --iofail CslibTests.HvalidShapeRefutation` / `CslibTests.BetaSplitRefutation`:
  `✔ Built`, zero warnings, zero `info:` lines.
- `lake test`: `✔ [9391/9391] Built CslibTests`.
- `lake build --wfail --iofail` (full repo): failing-target set byte-identical to the Phase 1
  baseline (5 pre-existing targets, none newly introduced by this task).
- Sorry census in `Cslib/Logics/Propositional/Tableau/`: exactly 4, same four declarations as
  Phase 1 baseline. Zero new axioms.
- `bash scripts/check-shake-residue.sh`: 12 flagged files, matching baseline.
- `lake exe lint-style` (whole repo): zero findings.
- `lake exe checkInitImports`: clean.
- `grep -rn "scratch/" Cslib/Logics/Propositional/Tableau/`: exactly one legitimate hit (the
  archive-path reference at `Intuitionistic/Scheme.lean:3475`, see Plan Deviations below); zero
  unresolvable bare `scratch/`-relative citations remain.

## Plan Deviations

- **Phases 3 and 4 merged into a single commit.** `CslibTests/BetaSplitRefutation.lean` was
  authored once, in full (imports/`#guard_msgs` wrapping from Phase 3's scope, plus every
  declaration's docstring from Phase 4's scope), since writing the file twice would have been
  pure re-edit churn with no behavioural difference. Both phases' verification criteria were
  independently re-checked and both are marked `[COMPLETED]` / `[COMPLETED WITH EXCLUSIONS]`
  respectively in the plan, with the merge documented as a Reasoned Exclusion on Phase 4.
- **Phase 6's own verification bullet was found to be textually unsatisfiable** given Finding
  8's own prescribed repair: the correct repaired form for the `PersistPrototype.lean` citation
  is the full archive path `specs/archive/430_prove_atom_persistence_upward_closure_for_intexpan/scratch/PersistPrototype.lean`,
  which legitimately contains the substring `scratch/` (a real subdirectory of the archived task
  directory). The bullet "`grep -rn "scratch/" ...` returns nothing" (repeated in the plan's
  top-level Testing & Validation section) cannot hold without reintroducing Finding 8's original
  defect (stripping `scratch/` would make the citation unresolvable again). Documented as a
  Reasoned Exclusion on Phase 6; the phase's actual goal (the citation resolves from the
  repository root, confirmed via `test -f`) is met.
- **A second, unrelated, out-of-scope `430_...`-ellipsis citation was discovered** at
  `Intuitionistic/Scheme.lean:3324` (`` `specs/430_.../handoffs/` ``), not one of Finding 9's 14
  inventoried sites and not part of this task's three-witness citation inventory. Left untouched;
  documented as a Reasoned Exclusion on Phase 6.
- **Phase 1's baseline failing-target set was wider than hypothesized**: 5 targets instead of the
  hypothesized 1 (`Cslib.Logics.Modal.Tableau.FrameCompleteness` and
  `Cslib.Logics.Modal.Tableau.S4.Driver` are also pre-existing red at HEAD, unrelated to this
  task). Per the phase's own Scope Hypothesis instruction, the wider set was recorded as-is and
  used as the Phase 7 comparison point; the diff came back empty, confirming no new regressions.

## Zero-Debt Confirmation

- Sorry count: 4 (unchanged from HEAD baseline).
- New axioms: 0.
- Vacuous definitions: none introduced.
- No verdict/annotation text was re-adjudicated; only citation paths were repaired.

## AI Tools Used

This task was implemented with the assistance of Claude Code (Anthropic) via the
`cslib-implementation-agent`. The agent wrote both promoted `CslibTests/` files, applied the
fourteen citation-path edits, ran the CSLib CI verification pipeline, and composed this summary.
