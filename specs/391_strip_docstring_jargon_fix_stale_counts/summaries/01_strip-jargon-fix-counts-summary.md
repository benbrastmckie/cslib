# Implementation Summary: Task #391

- **Task**: 391 - Strip docstring jargon & fix stale counts
- **Status**: Implemented
- **Plan**: `specs/391_strip_docstring_jargon_fix_stale_counts/plans/01_strip-jargon-fix-counts.md`
- **Report**: `specs/391_strip_docstring_jargon_fix_stale_counts/reports/01_docstring-jargon-stale-counts.md`

## What Was Done

Comment/docstring-only cleanup across 13 files (12 planned + 0 new files). Zero proof-logic
changes, zero new sorries, zero new axioms.

**Phase 1 (A1-A6, B1-B6)**: Stripped internal task/process jargon ("task NNN", "Route A2",
"rung", "4-for-4", "from day one", "N proof files") from 6 public-docstring modules, and fixed
6 genuinely-stale items:
- IntSoundness.lean / MinSoundness.lean: reworded stale "3 cases" / "2 cases" counts (verified
  live: 9 and 8 constructors respectively) to count-free prose.
- IntLindenbaum.lean: fixed a misattached `IntPropAxiom is consistent` docstring on
  `lift_int_to_cl` (L262) with an accurate derivation-tree-lifter docstring; left the correctly
  attached copy on `int_consistent` (L274-275) untouched.
- Intuitionistic/DecisionProcedure.lean and Minimal/DecisionProcedure.lean: replaced brittle
  `Scheme.lean:246/519` line citations (actual sorries verified at L409/L1070) with lemma/role
  descriptions; corrected the wrong "4 sorries in Minimal/Completeness.lean" claim.
- Minimal/Completeness.lean: stripped "handed to task 317" jargon.

**Phase 2 (A7)**: Applied the three isolated in-proof scratch-comment edits in
`ListImplication.lean` (comment-text only, no tactic/term lines touched), then ran the full
CSLib CI pipeline.

## Plan Deviations

- **A2 (altered)**: Beyond the enumerated sites, also stripped a stale "4-for-4" phrase at
  `ClassicalConjImpBotCompleteness.lean:479` (the conservativity-column docstring lists exactly
  3 items — CL-A/B/C — immediately below, mirroring the same staleness pattern already fixed
  in `ConservativeChain.lean` under A3). This was required to satisfy the Phase 2 residual-jargon
  grep gate, which scans the whole file rather than just the enumerated line ranges.
- **B6 (altered)**: Beyond L49, also stripped three additional "task 317" mentions in the same
  file (`Minimal/Completeness.lean` docstrings at L69, L89, L103, plus an in-proof scratch
  comment at L109) that were not in the original site enumeration but were the same jargon
  category, and were required to satisfy the whole-file residual-jargon grep gate.

No other deviations. All other checklist items (A1, A3-A6, B1-B5, A7) were applied exactly as
specified in the plan/report.

## Verification Results

- `lake build` (full project, 3189 jobs): green.
- `lake exe checkInitImports`: clean (exit 0).
- `lake lint`: 2 pre-existing errors in `Cslib/Logics/Temporal/Theorems.lean` (defsWithUnderscore),
  unrelated to this task's files (not touched). Zero lint findings in any of the 13 edited files.
- `lake exe lint-style`: clean (exit 0).
- `lake shake --add-public --keep-implied --keep-prefix`: pre-existing repo-wide import-hygiene
  suggestions unrelated to this task (this task made zero import changes; `git diff` confirms no
  `import`/`public import` lines were touched in any edited file).
- `lake exe mk_all --module`: "No update necessary" (no new files added).
- `lake test`: `CslibTests` suite passes.
- Residual-jargon grep (`grep -rnE "task [0-9]+|Route A2|[0-9]+ proof files|day one|4-for-4|CL-. rung"`
  over all 13 edited files): 0 hits.
- `Cslib/Foundations/Logic/Connectives.lean` (owned by task 400): absent from `git diff` — untouched.
- `IntStrongCompleteness.lean:107` and `MinStrongCompleteness.lean:121` "(3 cases: atom, bot, imp)":
  no diff on either file — untouched.
- `IntLindenbaum.lean:274` (`int_consistent`): unchanged; only the misattached L262 docstring
  (on `lift_int_to_cl`) was fixed.
- `git diff` on `ListImplication.lean`: only comment lines changed, no tactic/term lines.
- No new `sorry` introduced (grep of added diff lines finds only the word "sorry" inside prose,
  never a new `sorry` tactic). No new `axiom` declarations.

## Files Modified

- `Cslib/Foundations/Logic/PropositionalTableau.lean`
- `Cslib/Foundations/Logic/Tableau/RuleResult.lean`
- `Cslib/Foundations/Logic/Metalogic/ListImplication.lean`
- `Cslib/Logics/Propositional/Metalogic/ClassicalConjImpCompleteness.lean`
- `Cslib/Logics/Propositional/Metalogic/ClassicalConjImpBotCompleteness.lean`
- `Cslib/Logics/Propositional/Metalogic/IntSoundness.lean`
- `Cslib/Logics/Propositional/Metalogic/MinSoundness.lean`
- `Cslib/Logics/Propositional/Metalogic/IntLindenbaum.lean`
- `Cslib/Logics/Propositional/Semantics/Algebra/ConservativeChain.lean`
- `Cslib/Logics/Propositional/Semantics/Algebra/HilbertLindenbaumRel.lean`
- `Cslib/Logics/Propositional/Tableau/Intuitionistic/DecisionProcedure.lean`
- `Cslib/Logics/Propositional/Tableau/Minimal/DecisionProcedure.lean`
- `Cslib/Logics/Propositional/Tableau/Minimal/Completeness.lean`

## Coordination Note (Task 392 Overlap)

`Cslib/Logics/Propositional/Metalogic/IntLindenbaum.lean` also appears in task 392's
(remove-deadcode/fix-naming) plan file list, which intends to rename `lift_int_to_cl` ->
`liftIntToCl` (decl + call sites) in Phase 2/4. This task's edit to that same file was
docstring-only (fixed the misattached consistency docstring immediately above the
`lift_int_to_cl` declaration at L262-263) and did not touch the declaration name itself, so
task 392's rename should apply cleanly on top. Flagging per instructions since both tasks touch
this file; no action taken beyond noting it.
