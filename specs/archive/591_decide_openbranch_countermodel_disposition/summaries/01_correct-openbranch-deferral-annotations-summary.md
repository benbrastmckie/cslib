# Implementation Summary: Correct the `openBranch_countermodel` deferral annotations

- **Task**: 591 - Decide the openBranch_countermodel upward-closure disposition (root of DP-3/DP-4/DP-5)
- **Plan**: `specs/591_decide_openbranch_countermodel_disposition/plans/01_correct-openbranch-deferral-annotations.md`
- **Status**: Implemented — all 6 phases completed

## What changed

This was a pure annotation-correction task: comments and docstrings only, across three files,
zero tactic/statement/signature changes. All 10 hunks the plan identified (H1-H10) were
corrected, replacing the false "PERMANENTLY DEFERRED / unprovable as stated / REFUTED / terminal
deferral / no follow-up scheduled / DISPOSITION UNDECIDED" framing with the corrected framing:
**open, augmented-frame route known-bad, admissible edge space characterised.**

- `Cslib/Logics/Propositional/Tableau/Intuitionistic/Scheme.lean` (H1-H4): the
  `openBranch_countermodel` docstring and its proof-site comment now lead with the structural
  argument (any refutation needs an IPC-valid `φ` on which the algorithm opens; `phiRef1` is not
  even classically valid) and the admissible-edge-space characterisation (`𝒫(⊑)`, conjunct 1
  needs no algorithm invariant). The "No change to this statement is authorized" freeze is
  lifted. DP-5's counterexample is re-annotated as a refutation of the augmented-frame
  *instantiation*, not of the goal (`truthLemma`'s frame is a parameter). The stale
  DP-3/DP-4/DP-5 cross-reference is corrected: only DP-5's augmented-frame instantiation
  genuinely depends on the refuted invariant.
- `Cslib/Logics/Propositional/Tableau/Intuitionistic/Completeness.lean` (H5-H7): DP-3's module
  notes, theorem docstring, and in-proof comment are re-annotated as open, pointing at
  `Scheme.lean`'s corrected docstring. The `exact h Nat (intExtractValuation _b) _huc 0`
  prohibition is preserved verbatim in effect, with the corrected reason (launders an
  undischarged conjunct, not a refuted one).
- `Cslib/Logics/Propositional/Tableau/Minimal/Completeness.lean` (H8-H10): DP-4's "refuted
  independently of DP-3" claim is retracted — under `isMinimallyClosed`, the pruned witness
  `[(1, 0)]` discharges both upward-closure obligations and still falsifies `phiRef1`, so DP-4
  shares DP-3's bad augmented-frame witness choice rather than being independently refuted.
  `minBranchBotForces b`'s own upward-closure is promoted to a named, genuinely separate open
  residual (holds at the `[(1, 0)]` witness, not established in general).

Every corrected hunk states the honesty bound (C4): the general `∀ φ` statement remains
unproved, the maximal inclusion frame `⊑` is not a uniform witness (fails at
`phiRef1`/`phiRef3`), and proving the general statement is equivalent to proving the tableau
procedure complete. Every corrected hunk also preserves (C5) the genuine survivors: the
`BetaSplitRefutation.lean` counterexample remains described as a real refutation of
augmented-frame positive-formula persistence, and the `intFImpReuseWitnessAnc?`
frame-construction defect remains named as real and unfixed.

## Sorry/axiom ratchets — zero delta, confirmed byte-identical

Pre-edit baseline (Phase 1, `scripts/check-sorry-suppressions.sh --list --scope`):
```
0 2 Cslib/Logics/Propositional/Tableau/Intuitionistic/Scheme.lean
0 1 Cslib/Logics/Propositional/Tableau/Intuitionistic/Completeness.lean
0 1 Cslib/Logics/Propositional/Tableau/Minimal/Completeness.lean
```
Post-edit (Phase 6): identical, confirmed via `diff` against the Phase 1 baseline file. All four
`sorry`s are present and in their original positions:
- `Scheme.lean:768` (truthLemma's T-imp/persistence case, DP-5's `sorry`)
- `Scheme.lean:7965` (`openBranch_countermodel`'s conjunct-1 `sorry`)
- `Intuitionistic/Completeness.lean:164` (DP-3)
- `Minimal/Completeness.lean:160` (DP-4)

`scripts/check-axiom-census.sh`: 42 sorryAx-tainted declarations, matches baseline exactly — no
new axiom taint. `awk 'length($0)>100'`: 0 lines over 100 columns in all three files, matching
the Phase 1 baseline.

## CI gate (`scripts/pre-pr-check.sh`)

Steps 1, 6, 7, 8, 9 (the ratchet-based steps: scoped sorry ratchet, blanket linter-suppression
ratchet, shake import-debt ratchet, whole-tree sorry-suppression ratchet, axiom-census ratchet)
all pass with **zero delta** from baseline. Step 10 (Boneyard quarantine self-test) passes.

Step 5 (`lake build --wfail --iofail`, the full-repo warning gate) reports FAIL. This is a
**pre-existing, documented condition, not a regression from this task**: `pre-pr-check.sh`'s own
inline comment above step 8 states "the three `Propositional/Tableau/*` files trip step 5
(repo-wide) but are invisible to step 1 (its four named trees never include
Propositional/Tableau)" — i.e. step 5 is known to fail whenever any sorry exists anywhere in the
repo (`--wfail` promotes every `declaration uses 'sorry'` warning to a build failure), and the
four sorries in the three in-scope files predate this task and are a hard constraint that they
stay. The step-5 log additionally shows unrelated pre-existing `flexible` linter warnings in
`Cslib/Logics/Modal/Tableau/FrameCompleteness.lean` and `S4/Driver.lean`, confirming this is a
whole-repo condition, not something introduced by the three edited files. Scoped builds of all
three modified modules (`lake build Cslib.Logics.Propositional.Tableau.Intuitionistic.Scheme`,
`...Intuitionistic.Completeness`, `...Minimal.Completeness`) each succeed cleanly, with no
warnings beyond the four pre-existing `sorry` declarations.

## Residual repo-wide grep

`PERMANENTLY DEFERRED` and `DISPOSITION UNDECIDED` no longer occur anywhere under `Cslib/`
(repo-wide grep, not just the three in-scope files).

`.claude/scripts/check-task-references.sh` reports 23 pre-existing task-reference occurrences,
all confined to `.memory/**` frontmatter (`source`/`title`/`tags` fields from unrelated prior
tasks) — none in the three files this task touched. A direct grep for `\btask[s]? [0-9]+` over
the three in-scope files returns nothing. This pre-existing `.memory/**` condition is unrelated
to and out of scope for this annotation-correction task.

## Plan Deviations

None. All 10 hunks (H1-H10) were corrected exactly as the plan's content rules (C1-C8)
specified; no phase was skipped, altered, or deferred.

## Tracker corrections (report only, no tracker edits made here)

1. **The task description's stated prerequisite is false.** `CslibTests/BetaSplitRefutation.lean`
   is present and CI-protected (22 KB, `#guard_msgs`-asserted); it was promoted out of `scratch/`
   by prior evidentiary-repair work. No blocking dependency remains for this or related work.
2. **The restatement task** (`restate_propositional_tableau_completeness_theorems`) rests on the
   premise that the `∃ edges` conjunct is refuted. That premise is now disproved by this task's
   research and the corrected in-source annotations; the restatement task should be re-scoped or
   blocked rather than executed as originally written.

## Follow-up recommendation (not done here, outside `file_scope`)

Promote the research scratch probes (`WitnessProbe.lean`, `WitnessSearch2.lean`,
`WitnessSearch3.lean`, `MinProbe.lean`, preserved at
`specs/591_decide_openbranch_countermodel_disposition/scratch/`) into `CslibTests/`, mirroring
`BetaSplitRefutation.lean`'s promotion, so the corrected annotations' computed evidence (the
`[(1, 0)]` witness, the 40-witness enumeration, the maximal-frame failure at `phiRef1`/`phiRef3`)
becomes CI-protected rather than merely reported in comments.

## Named residuals (reported, not resolved — matches plan's Artifacts & Outputs)

(a) The general `∀ φ` `openBranch_countermodel` statement remains open and is equivalent to
proving the tableau procedure complete. (b) `minBranchBotForces b`'s own upward-closure is a
separate, unproved obligation. (c) The `intFImpReuseWitnessAnc?` frame-construction defect is
real and unfixed. (d) The research probes are not CI-protected (see follow-up above). (e) The
restatement task's premise is now false and should be re-scoped or blocked.

## Files changed

- `Cslib/Logics/Propositional/Tableau/Intuitionistic/Scheme.lean`
- `Cslib/Logics/Propositional/Tableau/Intuitionistic/Completeness.lean`
- `Cslib/Logics/Propositional/Tableau/Minimal/Completeness.lean`
- `specs/591_decide_openbranch_countermodel_disposition/scratch/01-baseline.md` (new)
- `specs/591_decide_openbranch_countermodel_disposition/scratch/02-canonical-wording.md` (new)
- `specs/591_decide_openbranch_countermodel_disposition/plans/01_correct-openbranch-deferral-annotations.md`
  (phase status markers)
