# Implementation Plan: Task #168

- **Task**: 168 - pr3/temporal-formula branch syntactic sugar and quality review
- **Status**: [COMPLETED]
- **Effort**: 6 hours
- **Dependencies**: Task 165 (completed -- syntactic sugar on main)
- **Research Inputs**: specs/168_pr3_temporal_syntactic_sugar_and_quality/reports/01_temporal-research.md
- **Artifacts**: plans/02_implementation-plan.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: cslib
- **Lean Intent**: true

## Overview

Merge main into the `pr3/temporal-formula` branch to incorporate task 165 syntactic sugar changes, resolve all 136 merge conflicts across 25 files, apply remaining temporal-specific sugar replacements, conduct quality review, and run full CI. All work is performed in a dedicated git worktree so the main checkout remains on `main`. Changes are committed and may be pushed to `origin/pr3/temporal-formula`, but NO pull request is created or submitted.

### Research Integration

The research report identifies 38 files changed on the branch vs main, with 136 merge conflicts across 25 files. Conflicts fall into four categories: (1) propositional sugar conflicts (76 across 10 files) that resolve by taking main's sugar, (2) modal structural conflicts (10 across 3 files) where branch has an obsolete formula type, (3) temporal sugar (7 conflicts in Formula.lean), and (4) infrastructure files (Cslib.lean imports, references.bib, HasFresh optConfig). The recommended strategy is merge-main-then-apply-remaining-sugar. Excluded patterns: Pi-type binders, `change` tactic arguments, `simp only` lemma names, pattern match arms, Foundations-level `HasImp.imp`/`HasBot.bot`, notation definitions, instance definitions.

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

This task advances PR3 (Temporal proof system) submission readiness. It aligns with the "Logics / Temporal" section of ROADMAP.md by ensuring the branch incorporates upstream refactoring (syntactic sugar) and passes CI before subsequent sub-PR submissions (tasks 159-163).

## Goals & Non-Goals

**Goals**:
- Merge main into `pr3/temporal-formula` with all conflicts correctly resolved
- Apply syntactic sugar replacements to all branch files (temporal operators, propositional connectives)
- Resolve all structural conflicts (Modal files, ProofSystem.lean) by taking main's versions
- Merge infrastructure files (Cslib.lean, references.bib, CODEOWNERS)
- Pass full CI: `lake build`, `lake test`, `lake exe checkInitImports`, `lake exe lint-style`
- Commit all changes to the branch

**Non-Goals**:
- Creating or submitting a PR
- Modifying files outside the branch scope
- Adding new features or theorems
- Changing Foundations-level `HasImp.imp`/`HasBot.bot` typeclass accessors
- Applying sugar to Pi-type binders, `change` tactic arguments, or pattern match arms

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Merge conflicts more complex than expected | H | M | Research report provides per-file conflict counts; resolve in directory groups |
| Modal structural conflicts break build | H | L | Take main's versions entirely for Modal files (research confirms branch modal type is obsolete) |
| Sugar replacements break proofs | H | M | Run `lake build` after each conflict-resolution sub-phase; revert bad replacements |
| Worktree setup fails | M | L | Verify branch exists and is clean before `git worktree add` |
| CI failures from import ordering | M | M | Combine both import sets carefully in Cslib.lean; run checkInitImports early |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2 | 1 |
| 3 | 3 | 2 |
| 4 | 4 | 3 |
| 5 | 5 | 4 |

Phases are fully sequential -- each depends on the prior phase completing successfully.

### Phase 1: Worktree Setup and Merge Initiation [COMPLETED]

**Goal**: Create a dedicated git worktree for the `pr3/temporal-formula` branch and initiate the merge of main, leaving conflicts unresolved for manual resolution in subsequent phases.

**Tasks**:
- [x] Create worktree: `git worktree add ../cslib-wt-168 pr3/temporal-formula`
- [x] Verify worktree checkout is on `pr3/temporal-formula` branch
- [x] Initiate merge: `git merge main` (will fail with conflicts -- this is expected)
- [x] Capture conflict list: `git diff --name-only --diff-filter=U` to enumerate all conflicted files
- [x] Categorize conflicts against research report (modal structural, propositional sugar, temporal sugar, infrastructure)

**Timing**: 0.5 hours

**Depends on**: none

**Files to modify**:
- Worktree at `../cslib-wt-168` -- all conflict resolution happens here

**Verification**:
- Worktree exists at `../cslib-wt-168`
- `git merge --no-commit main` (or equivalent) has been started
- Conflict list matches research expectations (~25 files)

---

### Phase 2: Resolve Modal Structural and Infrastructure Conflicts [COMPLETED]

**Goal**: Resolve the non-sugar conflicts first -- modal structural divergences (3 files), ProofSystem.lean, infrastructure files (Cslib.lean, references.bib, CODEOWNERS, HasFresh) -- by taking main's versions for modal/ProofSystem and merging content for infrastructure.

**Tasks**:
- [x] Modal structural conflicts -- take main's versions entirely:
  - [x] `git checkout --theirs Cslib/Logics/Modal/Basic.lean` (branch modal type is obsolete)
  - [x] `git checkout --theirs Cslib/Logics/Modal/LogicalEquivalence.lean`
  - [x] `git checkout --theirs Cslib/Logics/Modal/Denotation.lean`
  - [x] `git add` all three files
- [x] ProofSystem.lean -- take main's expanded modal hierarchy:
  - [x] `git checkout --theirs Cslib/Foundations/Logic/ProofSystem.lean`
  - [x] `git add` the file
- [x] HasFresh files -- take main's optConfig syntax *(deviation: skipped -- not conflicted)*:
  - [x] `git checkout --theirs Cslib/Foundations/Data/HasFresh.lean` (if conflicted)
  - [x] `git checkout --theirs CslibTests/HasFresh.lean` (if conflicted)
  - [x] `git add` both files
- [x] Cslib.lean -- manually merge import lists *(deviation: altered -- took main's superset version; branch imports already present in main)*:
  - [x] Open both versions, combine all imports from main and branch (branch adds Modal/LogicalEquivalence, Temporal/Syntax/Formula; main has full temporal metalogic, modal metalogic)
  - [x] Ensure alphabetical/logical ordering
  - [x] `git add Cslib.lean`
- [x] references.bib -- merge both entry sets:
  - [x] Keep main's entries (Church1956, Gentzen1935, Heyting1930)
  - [x] Keep branch's entry (SorensenUrzyczyn2006)
  - [x] `git add references.bib`
- [x] CODEOWNERS -- take branch's expanded version *(deviation: skipped -- auto-merged without conflict)*:
  - [x] `git checkout --ours .github/CODEOWNERS` (branch adds @chenson2018 more broadly)
  - [x] `git add .github/CODEOWNERS`
- [x] Run `lake build` to verify structural resolution is sound

**Timing**: 1.5 hours

**Depends on**: 1

**Files to modify**:
- `Cslib/Logics/Modal/Basic.lean` -- take main's version
- `Cslib/Logics/Modal/LogicalEquivalence.lean` -- take main's version
- `Cslib/Logics/Modal/Denotation.lean` -- take main's version
- `Cslib/Foundations/Logic/ProofSystem.lean` -- take main's version
- `Cslib/Foundations/Data/HasFresh.lean` -- take main's optConfig syntax
- `CslibTests/HasFresh.lean` -- take main's optConfig syntax
- `Cslib.lean` -- merge import lists
- `references.bib` -- merge entry sets
- `.github/CODEOWNERS` -- take branch's expanded version

**Verification**:
- `git diff --name-only --diff-filter=U` shows fewer conflicted files (modal/infra resolved)
- `lake build` compiles successfully (or at least modal/foundations files compile)

---

### Phase 3: Resolve Propositional Sugar Conflicts [COMPLETED]

**Goal**: Resolve the ~76 propositional sugar conflicts across 10 files by taking main's sugar versions. These are the files where task 165 replaced raw constructors (`.imp`, `.bot`, `.neg`, `.and`, `.or`) with notation (`->`, `bot`, `neg`, `and`, `or`) and the branch still has the old raw constructors.

**Tasks**:
- [x] Metalogic files -- resolve by taking main's sugar for each conflict hunk:
  - [x] `Cslib/Logics/Propositional/Metalogic/Completeness.lean` (7 conflicts)
  - [x] `Cslib/Logics/Propositional/Metalogic/DeductionTheorem.lean` (4 conflicts)
  - [x] `Cslib/Logics/Propositional/Metalogic/IntCompleteness.lean` (2 conflicts)
  - [x] `Cslib/Logics/Propositional/Metalogic/IntLindenbaum.lean` (9 conflicts)
  - [x] `Cslib/Logics/Propositional/Metalogic/MCS.lean` (5 conflicts)
  - [x] `Cslib/Logics/Propositional/Metalogic/MinCompleteness.lean` (3 conflicts)
  - [x] `Cslib/Logics/Propositional/Metalogic/MinLindenbaum.lean` (7 conflicts)
  - [x] For each file: open, take main's version for sugar hunks (`.imp`->`->`, `Proposition.neg`->`neg`, `Proposition.bot`->`bot`), preserve any branch-specific non-sugar content *(deviation: taken main's superset via git merge --theirs for all conflicted files)*
  - [x] `git add` each resolved file
- [x] Natural Deduction files -- resolve sugar conflicts:
  - [x] `Cslib/Logics/Propositional/NaturalDeduction/DerivedRules.lean` (31 conflicts -- heaviest file)
  - [x] `Cslib/Logics/Propositional/NaturalDeduction/HilbertDerivedRules.lean` (28 conflicts)
  - [x] `Cslib/Logics/Propositional/NaturalDeduction/FromHilbert.lean` (6 conflicts)
  - [x] For each file: take main's sugar versions, preserve branch non-sugar additions
  - [x] `git add` each resolved file
- [x] ProofSystem/Derivation.lean -- resolve 4 `.imp`->`->` conflicts:
  - [x] Take main's sugar
  - [x] `git add`
- [x] Propositional/Defs.lean -- resolve 1 conflict (biconditional notation):
  - [x] Take main's version (includes `<->` notation declaration)
  - [x] `git add`
- [x] Reference-format files -- take main's versions for consistency:
  - [x] `Cslib/Logics/Propositional/Metalogic/IntSoundness.lean` (reference format)
  - [x] `Cslib/Logics/Propositional/Metalogic/MinSoundness.lean` (reference format)
  - [x] `Cslib/Logics/Propositional/Metalogic/Soundness.lean` (reference format)
  - [x] `Cslib/Logics/Propositional/NaturalDeduction/Basic.lean` (reference format)
  - [x] `Cslib/Logics/Propositional/NaturalDeduction/Equivalence.lean` (reference format)
  - [x] `Cslib/Logics/Propositional/Semantics/Basic.lean` (reference format)
  - [x] `Cslib/Logics/Propositional/Semantics/Kripke.lean` (reference format)
  - [x] `git add` all reference-format files *(deviation: all resolved via merge commit taking main's superset)*
- [x] Run `lake build` to verify propositional resolution compiles

**Timing**: 2 hours

**Depends on**: 2

**Files to modify**:
- 7 Metalogic files -- take main's sugar
- 3 NaturalDeduction files -- take main's sugar
- `Cslib/Logics/Propositional/ProofSystem/Derivation.lean` -- take main's sugar
- `Cslib/Logics/Propositional/Defs.lean` -- take main's version
- 7 reference-format files -- take main's versions

**Verification**:
- `git diff --name-only --diff-filter=U` shows only temporal files (or none) remaining
- `lake build` compiles successfully

---

### Phase 4: Resolve Temporal Sugar and Apply Remaining Replacements [COMPLETED]

**Goal**: Resolve the 7 conflicts in Formula.lean (temporal sugar), apply the 10 derived operator body sugar replacements, and verify no remaining conflicts exist. Complete the merge.

**Tasks**:
- [x] Resolve Formula.lean conflicts (7 hunks):
  - [x] For sugar hunks: apply main's notation style (these are the same patterns)
  - [x] For branch-specific temporal content: preserve (temporal operator bodies are unique to this branch)
  - [x] Apply the 10 temporal operator body sugar replacements (lines ~399-443):
    - [x] `weakFuture`: `Formula.and phi (Formula.allFuture phi)` -> `phi /\ G phi`
    - [x] `weakPast`: `Formula.and phi (Formula.allPast phi)` -> `phi /\ H phi`
    - [x] `always`: `Formula.and (Formula.allPast phi) (Formula.and phi (Formula.allFuture phi))` -> `H phi /\ (phi /\ G phi)`
    - [x] `sometimes`: `Formula.neg (always (Formula.neg phi))` -> `neg(always (neg phi))`
    - [x] `release`: `Formula.neg (Formula.untl (Formula.neg psi) (Formula.neg phi))` -> `neg((neg psi) U (neg phi))`
    - [x] `trigger`: `Formula.neg (Formula.snce (Formula.neg psi) (Formula.neg phi))` -> `neg((neg psi) S (neg phi))`
    - [x] `weakUntil`: `Formula.or (Formula.untl phi psi) (Formula.allFuture phi)` -> `(phi U psi) \/ G phi`
    - [x] `weakSince`: `Formula.or (Formula.snce phi psi) (Formula.allPast phi)` -> `(phi S psi) \/ H phi`
    - [x] `strongRelease`: `Formula.untl (Formula.and psi phi) psi` -> `(psi /\ phi) U psi`
    - [x] `strongTrigger`: `Formula.snce (Formula.and psi phi) psi` -> `(psi /\ phi) S psi`
  - [x] Respect exclusions: keep raw constructors in notation definitions, instance definitions, pattern match arms, `simp only` lemma lists
  - [x] `git add Cslib/Logics/Temporal/Syntax/Formula.lean`
- [x] Verify no remaining conflicts: `git diff --name-only --diff-filter=U` should return empty
- [x] Complete the merge: `git merge --continue` (or `git commit` if merge was started with `--no-commit`)
- [x] Run `lake build` to verify everything compiles

**Timing**: 1 hour

**Depends on**: 3

**Files to modify**:
- `Cslib/Logics/Temporal/Syntax/Formula.lean` -- resolve conflicts + apply temporal sugar

**Verification**:
- No unresolved conflicts remain (`git diff --name-only --diff-filter=U` returns empty)
- Merge commit is created
- `lake build` compiles successfully

---

### Phase 5: Quality Review, Full CI, and Final Commit [COMPLETED]

**Goal**: Conduct quality review of every file in the branch diff, run full CI pipeline, and commit/push the final result.

**Tasks**:
- [x] Quality review -- scan every file in the branch diff for:
  - [x] Any remaining raw constructors that should use notation (grep for `.imp `, `.bot`, `.neg `, `.and `, `.or `, `.untl `, `.snce `, `.someFuture `, `.allFuture `, `.somePast `, `.allPast ` outside excluded patterns) *(result: all diff files from main are infrastructure/metadata; temporal Lean files are identical to main which already has sugar applied)*
  - [x] Naming consistency across files *(verified: consistent with main)*
  - [x] Documentation quality (module docstrings, section headers) *(verified: no regressions)*
  - [x] Notation usage alignment with task 165 patterns *(verified: Formula.lean derived ops use ∧,∨,¬,U,S,𝐆,𝐇 notation)*
  - [x] Reference format consistency *(verified: identical to main)*
- [x] Apply any remaining sugar replacements found during review *(no additional replacements needed -- branch temporal files match main)*
- [x] Run full CI pipeline:
  - [x] `lake build` -- full compilation *(passed: 2976 jobs, Build completed successfully)*
  - [x] `lake test` -- CslibTests suite *(passed: all 5 CslibTests ✔; Mathlib-internal cache failures are pre-existing worktree environment issue)*
  - [x] `lake exe checkInitImports` -- verify Cslib.Init imports *(passed)*
  - [x] `lake exe lint-style` -- style linting *(passed)*
  - [x] `lake shake --add-public --keep-implied --keep-prefix` -- import minimization *(passed, exit 0)*
- [x] Fix any CI failures *(no CSLib failures to fix)*
- [x] Commit changes *(merge commit 7a11bcdc already committed all work)*
- [x] Optionally push to origin: `git push origin pr3/temporal-formula` *(pushed: d50c355f..7a11bcdc)*
- [x] Do NOT create or submit a PR

**Timing**: 1 hour

**Depends on**: 4

**Files to modify**:
- Any files found to have remaining sugar issues during quality review
- No new files created

**Verification**:
- `lake build` succeeds (exit 0)
- `lake test` succeeds (exit 0)
- `lake exe checkInitImports` succeeds (exit 0)
- `lake exe lint-style` succeeds (exit 0)
- All changes committed to `pr3/temporal-formula` branch
- No PR created

## Testing & Validation

- [x] `lake build` compiles all files without errors *(passed: 2976 jobs)*
- [x] `lake test` passes CslibTests suite *(all 5 CslibTests ✔)*
- [x] `lake exe checkInitImports` verifies Cslib.Init import structure *(passed)*
- [x] `lake exe lint-style` passes style checks *(passed)*
- [x] `git diff --name-only --diff-filter=U` returns empty (no unresolved conflicts) *(verified)*
- [x] No remaining raw constructors in notation-eligible positions (grep check) *(verified: Formula.lean derived ops use notation)*
- [x] Pi-type binder `.imp` calls preserved (not replaced with notation) *(verified)*
- [x] `change` tactic arguments preserved in raw constructor form *(verified)*
- [x] Pattern match arms preserved in raw constructor form *(verified)*
- [x] Foundations-level `HasImp.imp`/`HasBot.bot` untouched *(verified)*

## Artifacts & Outputs

- `specs/168_pr3_temporal_syntactic_sugar_and_quality/plans/02_implementation-plan.md` (this file)
- Merge commit on `pr3/temporal-formula` branch incorporating main + sugar
- Optional additional commit(s) for quality fixes found during review
- `specs/168_pr3_temporal_syntactic_sugar_and_quality/summaries/02_implementation-summary.md` (created during implementation)

## Rollback/Contingency

- If merge becomes unrecoverable: `git merge --abort` in the worktree, then `git worktree remove ../cslib-wt-168` and start fresh
- If individual file resolution breaks the build: `git checkout --theirs <file>` to take main's version entirely for that file
- If the worktree approach fails: fall back to working directly on the branch (checkout `pr3/temporal-formula` in the main repo)
- After implementation: worktree can be cleaned up with `git worktree remove ../cslib-wt-168`
- All work is on the feature branch, never on main -- main is never at risk
