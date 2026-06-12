# Implementation Plan: Task #166

- **Task**: 166 - PR #633 syntactic sugar and quality review
- **Status**: [COMPLETED]
- **Effort**: 3.5 hours
- **Dependencies**: Task 165 (completed)
- **Research Inputs**: specs/166_pr633_syntactic_sugar_and_quality/reports/01_pr633-research.md
- **Artifacts**: plans/02_implementation-plan.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: cslib
- **Lean Intent**: true

## Overview

Apply syntactic sugar replacements from task 165 to all eligible Propositional files on the
`pr1/foundations-logic` PR branch (#633), add the missing biconditional notation to Defs.lean,
respond to reviewer comment r3403944952 explaining the Pi-type binder constraint, and push
the changes after full CI verification. All work is performed in a dedicated git worktree
so the main checkout stays on `main`.

### Research Integration

Key findings from research report `01_pr633-research.md`:
- 14 Propositional files need ~141 sugar replacements (`.imp`->`->`, `.bot`->`bot`, `.neg`->`neg`, `.and`->`and`, `.or`->`or`, `.iff`->`iff`)
- Defs.lean on PR branch is missing `@[inherit_doc] scoped infix:20 " <-> " => Proposition.iff` -- must add first
- Pi-type binder constraint: `->` in `forall ... Axioms (phi.imp ...)` positions parses as function arrow and must stay as `.imp`
- ~50+ lines in HilbertDerivedRules.lean are Pi-type constrained
- Modal and Foundations files are EXCLUDED (different primitives / typeclass layer)
- Cherry-pick not feasible; manual reapply required
- Reviewer comment r3403944952 asks for sugar on a line that is Pi-type constrained; respond explaining the constraint while applying sugar everywhere else

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

No ROADMAP.md found.

## Goals & Non-Goals

**Goals**:
- Add missing biconditional notation to Defs.lean on the PR branch
- Replace ~141 raw constructors with scoped notation across 13 Propositional files
- Update proof comments to use notation instead of raw constructor names
- Respond to reviewer comment r3403944952 on Completeness.lean
- Pass full CI: `lake build`, `lake test`, `lake exe checkInitImports`, `lake exe lint-style`
- Push commit(s) to the existing `pr1/foundations-logic` branch

**Non-Goals**:
- Modifying Modal files (different primitive set, handled by PRs #635/#637)
- Modifying Foundations files (typeclass layer, notation not applicable)
- Changing proof structure or logic (sugar only)
- Adding new theorems or proofs
- Restructuring files or directories

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| `->` parsed as function arrow in overlooked Pi-type context | H | M | `lake build` after each file group; compare with main's version |
| `<->` notation not resolving in some contexts | M | L | All Propositional files import Defs transitively; verify build |
| `bot` notation not resolving without Bot instance in scope | M | L | Verify imports provide Bot instance |
| Worktree setup fails (branch not available locally) | M | L | Fetch branch first; verify with `git branch -a` |
| Merge conflicts with ongoing main changes | M | M | Work on PR branch directly; push promptly |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2 | 1 |
| 3 | 3, 4 | 2 |
| 4 | 5 | 3, 4 |
| 5 | 6 | 5 |

Phases within the same wave can execute in parallel.

---

### Phase 1: Worktree Setup and Notation Prerequisite [COMPLETED]

**Goal**: Create a dedicated git worktree on the `pr1/foundations-logic` branch and add the missing biconditional notation to Defs.lean.

**Tasks**:
- [ ] Fetch latest remote branches: `git fetch origin pr1/foundations-logic`
- [ ] Create worktree: `git worktree add ../cslib-wt-166 pr1/foundations-logic`
- [ ] Verify worktree is on correct branch: `cd ../cslib-wt-166 && git log --oneline -3`
- [ ] Add `@[inherit_doc] scoped infix:20 " <-> " => Proposition.iff` to `Cslib/Logics/Propositional/Defs.lean` after the existing `neg` notation (after the line `@[inherit_doc] scoped prefix:75 "neg " => Proposition.neg`)
- [ ] Run `lake build` in worktree to verify the notation addition compiles

**Timing**: 20 minutes

**Depends on**: none

**Files to modify**:
- `Cslib/Logics/Propositional/Defs.lean` - Add biconditional notation line

**Verification**:
- Worktree exists at `../cslib-wt-166` on branch `pr1/foundations-logic`
- `lake build` passes with new notation
- `grep -c 'scoped infix:20 " <-> "' Cslib/Logics/Propositional/Defs.lean` returns 1

---

### Phase 2: ProofSystem Sugar Replacements [COMPLETED]

**Goal**: Apply syntactic sugar to the ProofSystem/ files (lowest risk, fewest replacements).

**Tasks**:
- [ ] Apply 4 replacements in `Cslib/Logics/Propositional/ProofSystem/Derivation.lean`: replace `phi.imp psi` -> `phi -> psi` in non-Pi positions (parameter annotations)
- [ ] Verify `Axioms.lean`, `Instances.lean`, `IntMinInstances.lean` need 0 changes (all constructors in constrained positions: inductive return types or pattern arms)
- [ ] Run `lake build` to verify

**Timing**: 15 minutes

**Depends on**: 1

**Files to modify**:
- `Cslib/Logics/Propositional/ProofSystem/Derivation.lean` - ~4 replacements

**Verification**:
- `lake build` passes
- No raw constructors remain in expression positions in Derivation.lean

---

### Phase 3: Metalogic Sugar Replacements [COMPLETED]

**Goal**: Apply syntactic sugar to all 8 Metalogic files, including the Pi-type-constrained Completeness.lean.

**Tasks**:
- [ ] `MCS.lean` (~7 replacements): Replace `Proposition.imp phi psi` -> `phi -> psi`, `Proposition.neg phi` -> `neg phi`, `Proposition.bot` -> `bot`
- [ ] `DeductionTheorem.lean` (~8 replacements): Replace `A.imp phi` -> `A -> phi`, `phi.imp psi` -> `phi -> psi` in non-Pi positions
- [ ] `Completeness.lean` (~10 replacements):
  - Replace `Proposition.neg phi` -> `neg phi` (~8 occurrences)
  - Replace `Proposition.bot` -> `bot` in expression positions (~2-3)
  - Replace `.imp` in non-Pi positions: `h_mcs (phi.imp psi)` -> `h_mcs (phi -> psi)` (~2)
  - KEEP `.imp` in `h_implyK` and `h_implyS` Pi-type binder lines
  - Add comment above `h_implyK`: `-- NB: .imp is needed here because -> is parsed as function arrow inside forall`
- [ ] `IntLindenbaum.lean` (~12 replacements): `Proposition.neg`, `Proposition.bot`, `.imp` in non-Pi positions
- [ ] `MinLindenbaum.lean` (~7 replacements): Same pattern as IntLindenbaum
- [ ] `IntCompleteness.lean` (~1 replacement): `Proposition.neg phi` -> `neg phi`
- [ ] `MinCompleteness.lean` (~2 replacements): `Proposition.neg`, `Proposition.bot`
- [ ] Update proof comments in affected files to use notation instead of raw names
- [ ] Run `lake build` after completing all Metalogic files

**Timing**: 1 hour

**Depends on**: 2

**Files to modify**:
- `Cslib/Logics/Propositional/Metalogic/MCS.lean` - ~7 replacements
- `Cslib/Logics/Propositional/Metalogic/DeductionTheorem.lean` - ~8 replacements
- `Cslib/Logics/Propositional/Metalogic/Completeness.lean` - ~10 replacements + Pi-type comment
- `Cslib/Logics/Propositional/Metalogic/IntLindenbaum.lean` - ~12 replacements
- `Cslib/Logics/Propositional/Metalogic/MinLindenbaum.lean` - ~7 replacements
- `Cslib/Logics/Propositional/Metalogic/IntCompleteness.lean` - ~1 replacement
- `Cslib/Logics/Propositional/Metalogic/MinCompleteness.lean` - ~2 replacements

**Verification**:
- `lake build` passes
- No raw `.neg`/`.bot`/`.imp` in expression positions (outside Pi-type binders)
- `Soundness.lean`, `IntSoundness.lean`, `MinSoundness.lean` confirmed clean (0 changes needed)

---

### Phase 4: NaturalDeduction Sugar Replacements [COMPLETED]

**Goal**: Apply syntactic sugar to the 4 NaturalDeduction files (highest replacement count, most Pi-type constraints in HilbertDerivedRules.lean).

**Tasks**:
- [ ] `DerivedRules.lean` (~34 replacements):
  - `Proposition.neg A` -> `neg A` (~15 occurrences)
  - `A.and B` -> `A and B` (~3)
  - `A.or B` -> `A or B` (~2)
  - `A.iff B` -> `A <-> B` (~6, enabled by Phase 1 notation)
  - `.imp` in non-Pi positions
  - Update proof comments: "neg" -> "neg", "A.or B" -> "A or B", etc.
- [ ] `HilbertDerivedRules.lean` (~39 replacements):
  - `Proposition.neg A` -> `neg A` (~7 non-Pi occurrences)
  - `Proposition.bot` -> `bot` (~5 non-Pi occurrences)
  - `A.iff B` -> `A <-> B` (~6)
  - Various `.imp` in non-Pi positions
  - KEEP ALL Pi-type binder lines (~50+ lines with `forall ... Axioms (phi.imp ...)`) unchanged
- [ ] `FromHilbert.lean` (~8 replacements): `A.imp B` -> `A -> B`, `Proposition.bot` -> `bot`
- [ ] `Equivalence.lean` (~9 replacements): `.iff` -> `<->` (~3), `Proposition.neg` -> `neg` (~2), `.imp` in non-Pi positions (~4)
- [ ] Run `lake build` after completing all NaturalDeduction files

**Timing**: 1.5 hours

**Depends on**: 2

**Files to modify**:
- `Cslib/Logics/Propositional/NaturalDeduction/DerivedRules.lean` - ~34 replacements
- `Cslib/Logics/Propositional/NaturalDeduction/HilbertDerivedRules.lean` - ~39 replacements (many Pi-type exempt)
- `Cslib/Logics/Propositional/NaturalDeduction/FromHilbert.lean` - ~8 replacements
- `Cslib/Logics/Propositional/NaturalDeduction/Equivalence.lean` - ~9 replacements

**Verification**:
- `lake build` passes
- All `.iff` replaced with `<->` in expression positions
- Pi-type binder lines in HilbertDerivedRules.lean unchanged
- `Basic.lean` confirmed clean (already has sugar / identical to main)

---

### Phase 5: Review Comment Response and Quality Review [COMPLETED]

**Goal**: Respond to xcthulhu's review comment r3403944952 explaining the Pi-type constraint, and perform a final quality review of all PR files.

**Tasks**:
- [ ] Respond to review comment r3403944952 via GitHub API:
  ```
  gh api repos/leanprover/cslib/pulls/633/comments/3403944952/replies \
    -f body="Applied syntactic sugar throughout the file. The specific line you flagged (\`h_implyK\`) uses \`.imp\` inside a \`forall\`-quantified type signature where \`->\` would be parsed as the function type arrow (Pi type) rather than \`Proposition.imp\`. This is a Lean parsing constraint -- the scoped notation cannot override the built-in arrow in Pi-type binder position. The same constraint applies to \`h_implyS\` and similar definitions throughout the Hilbert proof system. All other occurrences in the file have been replaced with notation."
  ```
- [ ] Quality review pass: scan all 14 modified files for:
  - Any remaining raw constructors in expression positions that were missed
  - Comment consistency (no raw constructor names in comments where notation would be clearer)
  - Reference format consistency (keep Mathlib-style `[Author, *Title*][BibKey]`)
  - No accidental changes to Modal or Foundations files
- [ ] Fix any issues found during quality review

**Timing**: 20 minutes

**Depends on**: 3, 4

**Files to modify**:
- None expected (quality review is read-only unless issues found)

**Verification**:
- Review comment posted successfully (verify via `gh api`)
- Quality review checklist completed with no remaining issues

---

### Phase 6: CI Verification, Commit, and Push [IN PROGRESS]

**Goal**: Run full CI pipeline, commit all changes, and push to the PR branch.

**Tasks**:
- [ ] Run `lake build` (full build, should already pass from incremental checks)
- [ ] Run `lake test` (CslibTests suite)
- [ ] Run `lake exe checkInitImports` (verify Cslib.Init imports)
- [ ] Run `lake exe lint-style` (style linting)
- [ ] Stage all modified files: `git add` the specific files changed
- [ ] Commit with message: `task 166: apply syntactic sugar to PR #633 Propositional files`
- [ ] Push to remote: `git push origin pr1/foundations-logic`
- [ ] Remove worktree: `git worktree remove ../cslib-wt-166` (from main checkout)

**Timing**: 25 minutes

**Depends on**: 5

**Files to modify**:
- All files modified in phases 1-4 (committed together)

**Verification**:
- All 4 CI commands pass with zero errors
- Commit exists on `pr1/foundations-logic` branch
- Push successful
- Worktree cleaned up

---

## Testing & Validation

- [ ] `lake build` passes in worktree (checked incrementally after each phase)
- [ ] `lake test` passes (CslibTests suite)
- [ ] `lake exe checkInitImports` passes
- [ ] `lake exe lint-style` passes
- [ ] No `.imp`/`.bot`/`.neg`/`.and`/`.or`/`.iff` remaining in expression positions across all 14 files
- [ ] All Pi-type binder lines unchanged (`.imp` preserved)
- [ ] No changes to Modal or Foundations files
- [ ] Review comment r3403944952 responded to on GitHub
- [ ] Commit pushed to `pr1/foundations-logic` branch

## Artifacts & Outputs

- `specs/166_pr633_syntactic_sugar_and_quality/plans/02_implementation-plan.md` (this file)
- `specs/166_pr633_syntactic_sugar_and_quality/summaries/02_sugar-quality-summary.md` (after implementation)
- Git commit on `pr1/foundations-logic` branch with sugar changes
- GitHub review comment reply on PR #633

## Rollback/Contingency

If the sugar replacements break the build:
1. Identify the specific file and line causing the failure from `lake build` output
2. Revert the individual replacement (likely a Pi-type binder that was incorrectly changed)
3. Re-run `lake build`

If the entire approach fails:
1. `git checkout -- .` in the worktree to revert all changes
2. `git worktree remove ../cslib-wt-166` from main checkout
3. No damage to main branch or remote PR branch (changes only pushed in final phase)

## Worktree Instructions

**IMPORTANT**: All implementation work MUST be done in a dedicated git worktree, not the main checkout.

```bash
# Setup (Phase 1)
git fetch origin pr1/foundations-logic
git worktree add ../cslib-wt-166 pr1/foundations-logic

# All file edits happen in ../cslib-wt-166/
# All lake commands run from ../cslib-wt-166/

# Cleanup (Phase 6, after push)
cd /home/benjamin/Projects/cslib
git worktree remove ../cslib-wt-166
```

The main checkout at `/home/benjamin/Projects/cslib` stays on `main` throughout.
