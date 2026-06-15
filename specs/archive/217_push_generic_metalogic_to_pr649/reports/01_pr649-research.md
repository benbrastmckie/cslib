# Research Report: Push Generic Metalogic to PR #649

- **Task**: 217 -- push_generic_metalogic_to_pr649
- **Session**: sess_1781549007_3bd2f7
- **Date**: 2026-06-15

## 1. PR #649 Current State

**Title**: feat(Logics/Temporal): temporal formula type with propositional structure
**Branch**: `feat/temporal-formula-propositional`
**State**: OPEN (no reviews yet, review requested from arademaker, fmontesi, chenson2018)
**Stacked on**: PR #648 (propositional connectives typeclass hierarchy)

### Current PR Files (6 files, ~678 additions)

| File | Type | Additions |
|------|------|-----------|
| `Cslib.lean` | Modified | +2 |
| `Cslib/Foundations/Logic/Connectives.lean` | New | +93 |
| `Cslib/Logics/Propositional/Defs.lean` | Modified | +66/-35 |
| `Cslib/Logics/Propositional/NaturalDeduction/Basic.lean` | Modified | +82/-70 |
| `Cslib/Logics/Temporal/Syntax/Formula.lean` | New | +334 |
| `references.bib` | Modified | +101 |

### Reviewer Feedback

No formal review comments exist on PR #649 or PR #648 yet. However, the task description and task 207 research reports document reviewer feedback from Zulip:

> "Looking at your MCS and Deduction Theorem proofs for temporal logic, I think we can abstract away from proving this stuff repeatedly by using classes. For instance, all you need is `|- phi -> psi -> phi`, `|- (phi -> psi -> chi) -> (phi -> psi) -> phi -> chi`, and `|- phi -> psi ==> |- phi ==> |- psi` and you can prove the deduction theorem. Similarly, we could show, given those same axioms, that if `Gamma not-derives phi` then `Gamma` can be extended to an MCS `Omega` where `Omega not-derives phi`, and prove common results like `phi in Omega <=> Omega |- phi`."

The reviewer linked the Isabelle `Propositional_Logic_Class` formalization as a reference.

### PR #649 Roadmap Context

PR #649 is PR 1 of ~9 planned temporal logic PRs. The generic metalogic infrastructure would be referenced by PR 7 (canonical model construction) and PR 8 (completeness theorem), which depend on MCS theory. Pushing the generic metalogic now prepares the foundation for those later PRs and directly addresses the reviewer's feedback.

## 2. Task 207 Implementation: What Was Built

Task 207 (and its predecessor task 202) implemented the generic metalogic layer. Task 202 created the core files; task 207 made minor fixes to GenericMCS.lean and SetDeduction.lean.

### Direct Deliverables (5 new files + 1 modification)

| File | LOC | Created By | Purpose |
|------|-----|-----------|---------|
| `Cslib/Foundations/Logic/Metalogic/ListImplication.lean` | 169 | Task 202 | `listImp`, flip lemmas for algebraic DT |
| `Cslib/Foundations/Logic/Metalogic/ListDeduction.lean` | 153 | Task 202 | `ListDeriv`, algebraic deduction theorem, monotonicity |
| `Cslib/Foundations/Logic/Metalogic/SetDeduction.lean` | 145 | Task 202+207 | `SetDeriv`, set-level deduction theorem |
| `Cslib/Foundations/Logic/Metalogic/GenericMCS.lean` | 88 | Task 202+207 | `algebraicDerivationSystem`, free `HasDeductionTheorem` |
| `Cslib/Foundations/Logic/Metalogic/MCSProperties.lean` | 128 | Task 202 | Generic MCS bot/neg/membership lemmas |
| `Cslib/Foundations/Logic/Theorems/Combinators.lean` | +22 LOC | Task 202 | `implication_absorption` combinator |

**Total new content**: ~683 LOC (5 new files) + 22 LOC modification to Combinators.lean

## 3. Dependency Analysis

### Import Chain

```
MCSProperties.lean
  -> GenericMCS.lean
       -> ListDeduction.lean
       |    -> ListImplication.lean
       |         -> Combinators.lean
       |              -> ProofSystem.lean
       |                   -> Axioms.lean
       |                   |    -> Connectives.lean
       |                   -> InferenceSystem.lean
       -> Consistency.lean
            -> Mathlib.Order.Zorn
            -> Connectives.lean

SetDeduction.lean
  -> ListDeduction.lean (same chain as above)
  -> Mathlib.Tactic.SetLike
  -> Mathlib.Data.Set.Insert
```

### Required Dependencies NOT on PR Branch

The PR branch only has `Connectives.lean`, `InferenceSystem.lean`, and `LogicalEquivalence.lean` in `Foundations/Logic/`. The following files exist on main but NOT on the PR branch and are required by the metalogic import chain:

| File | LOC | Why Needed |
|------|-----|-----------|
| `Cslib/Foundations/Logic/Axioms.lean` | 359 | Defines `Axioms.ImplyK`, `Axioms.ImplyS`, etc. -- used by ProofSystem.lean |
| `Cslib/Foundations/Logic/ProofSystem.lean` | 524 | Defines `MinimalHilbert`, `ModusPonens`, etc. -- used by Combinators.lean |
| `Cslib/Foundations/Logic/Metalogic/Consistency.lean` | 285 | Defines `DerivationSystem`, `SetMaximalConsistent`, Lindenbaum's lemma -- used by GenericMCS.lean |
| `Cslib/Foundations/Logic/Metalogic/DeductionHelpers.lean` | 120 | Defines `HasHilbertTree` -- not directly imported by new files but in same directory |

**Key issue**: `Axioms.lean` and `ProofSystem.lean` on main use `HasBox`, `HasUntil`, `HasSince` -- connective classes that exist on the PR branch's `Connectives.lean` for Until/Since but NOT for `HasBox`.

### Connectives.lean Compatibility

The PR branch's `Connectives.lean` has:
- `HasBot`, `HasImp`, `HasUntil`, `HasSince`, `HasAnd`, `HasOr`
- `PropositionalConnectives`, `TemporalConnectives`

The main branch adds:
- `HasBox`
- `ModalConnectives`, `BimodalConnectives`

**The metalogic files themselves only need `HasBot` and `HasImp`** -- they don't reference any modal or temporal connectives. However, their transitive dependencies (Axioms.lean, ProofSystem.lean) contain definitions that use `HasBox` etc.

## 4. Recommended Approach

### Option A: Update Connectives.lean + Push Full Dependency Chain (Recommended)

1. Update `Connectives.lean` on the PR branch to the main-branch version (adds `HasBox`, `ModalConnectives`, `BimodalConnectives`)
2. Add `Axioms.lean` (full version)
3. Add `ProofSystem.lean` (full version)
4. Add `Combinators.lean` (full version including `implication_absorption`)
5. Add `Consistency.lean`
6. Add the 5 new metalogic files
7. Update `Cslib.lean` barrel imports
8. Optionally add `DeductionHelpers.lean` (same directory, small, pre-existing)

**Pros**: Clean, complete, matches main. All files can be cherry-picked from main commits.
**Cons**: Large PR growth (~1800 LOC of dependencies + ~683 LOC of new content). May overwhelm reviewers.

### Option B: Create Minimal Dependency Versions

1. Create stripped versions of `Axioms.lean` and `ProofSystem.lean` with only propositional content (remove modal/temporal sections)
2. Push only the minimal set needed

**Pros**: Smaller PR. Only pushes what's directly relevant.
**Cons**: Diverges from main. Creates merge debt. Future PRs would need to update these files.

### Option C: Create a Separate PR for Generic Metalogic (Recommended if LOC is a concern)

1. Create a new PR (stacked on PR #649) dedicated to the generic metalogic layer
2. This keeps PR #649 focused on the formula type
3. The metalogic PR can include the full dependency chain since it's a dedicated PR

**Pros**: Clean separation of concerns. Each PR is reviewable independently. Directly addresses the reviewer's feedback in its own PR.
**Cons**: Another PR to manage in the stack.

### Recommendation

**Option C** is the cleanest approach. The task description says to push to PR #649, but adding ~2500 LOC to an already-scoped PR may not be ideal. If the user prefers to stay with PR #649, then **Option A** is the right path.

Either way, the files to push are:

**Required new files** (13 files total):
1. `Cslib/Foundations/Logic/Connectives.lean` -- UPDATE (add HasBox, ModalConnectives, BimodalConnectives)
2. `Cslib/Foundations/Logic/Axioms.lean` -- NEW to PR
3. `Cslib/Foundations/Logic/ProofSystem.lean` -- NEW to PR
4. `Cslib/Foundations/Logic/Theorems/Combinators.lean` -- NEW to PR
5. `Cslib/Foundations/Logic/Metalogic/Consistency.lean` -- NEW to PR
6. `Cslib/Foundations/Logic/Metalogic/DeductionHelpers.lean` -- NEW to PR (optional but recommended)
7. `Cslib/Foundations/Logic/Metalogic/ListImplication.lean` -- NEW to PR
8. `Cslib/Foundations/Logic/Metalogic/ListDeduction.lean` -- NEW to PR
9. `Cslib/Foundations/Logic/Metalogic/SetDeduction.lean` -- NEW to PR
10. `Cslib/Foundations/Logic/Metalogic/GenericMCS.lean` -- NEW to PR
11. `Cslib/Foundations/Logic/Metalogic/MCSProperties.lean` -- NEW to PR
12. `Cslib.lean` -- UPDATE (add import lines)
13. `Cslib/Foundations/Logic/InferenceSystem.lean` -- UPDATE (minor doc fix)

**NOT needed** (barrel and downstream files):
- `Cslib/Foundations/Logic/Theorems.lean` -- barrel file importing ALL theorem files; would pull in Modal/Temporal theorem files not on PR branch
- `Cslib/Foundations/Logic/Theorems/Propositional/` -- not needed by metalogic chain
- `Cslib/Foundations/Logic/Theorems/Modal/` -- not needed by metalogic chain
- `Cslib/Foundations/Logic/Theorems/Temporal/` -- not needed by metalogic chain
- `Cslib/Foundations/Logic/Theorems/BigConj.lean` -- not needed by metalogic chain

## 5. Conflicts and Issues

### 5.1 PR Branch is ~1369 Files Behind Main

The PR branch diverged from upstream `main` significantly. However, the files we need to add are all NEW files (not modifications to existing files already on the PR branch), except for:
- `Connectives.lean` -- needs update (additive, no destructive changes)
- `InferenceSystem.lean` -- needs minor doc update
- `Cslib.lean` -- needs import line additions

### 5.2 The Theorems.lean Barrel File

The `Cslib/Foundations/Logic/Theorems.lean` barrel file on main imports ALL theorem submodules (Modal, Temporal, Propositional, BigConj). These submodule files don't exist on the PR branch. Do NOT push the Theorems.lean barrel file. Combinators.lean can be imported directly.

### 5.3 Connectives.lean Version

The main branch's `Connectives.lean` is a strict superset of the PR branch's version (adds `HasBox`, `ModalConnectives`, `BimodalConnectives`; updates docstrings). The update is safe -- it only adds new classes and does not modify existing ones.

### 5.4 references.bib

The main branch has additional bibliography entries referenced by docstrings in the new files (e.g., `ChagrovZakharyaschev1997`, `Heyting1930`). Some are already in the PR branch's `references.bib` (added by the temporal formula commit). Check for duplicates before pushing.

### 5.5 Cslib.lean Barrel Imports

The PR branch's `Cslib.lean` does NOT have entries for any of the new `Foundations/Logic/` files. Need to add ~12 import lines. The existing Cslib.lean on the PR branch has entries in alphabetical order; maintain this ordering.

### 5.6 `mk_all` Verification

After adding files, run `lake exe mk_all --module` to ensure `Cslib.lean` is synchronized, or manually add the imports.

## 6. Implementation Steps

1. Checkout `feat/temporal-formula-propositional` branch
2. Cherry-pick or copy the updated `Connectives.lean` (adds `HasBox`, `ModalConnectives`, `BimodalConnectives`)
3. Copy `Axioms.lean`, `ProofSystem.lean` from main
4. Copy `Combinators.lean` (full version with `implication_absorption`) from main
5. Copy `Consistency.lean`, `DeductionHelpers.lean` from main
6. Copy the 5 new metalogic files from main
7. Update `InferenceSystem.lean` (minor doc fix)
8. Update `Cslib.lean` with new import lines
9. Check `references.bib` for needed entries
10. Run `lake build` to verify everything compiles
11. Run full CI pipeline (`lake test`, `lake exe checkInitImports`, etc.)
12. Create commit with conventional PR message format
13. Push to `origin/feat/temporal-formula-propositional`

## 7. LOC Impact Estimate

| Category | Files | LOC |
|----------|-------|-----|
| New metalogic files (task 207 deliverables) | 5 | ~683 |
| Modified Combinators.lean | 1 | +22 |
| Dependency files (Axioms, ProofSystem, Consistency, DeductionHelpers) | 4 | ~1288 |
| Updated Connectives.lean (additive) | 1 | ~+40 |
| Updated InferenceSystem.lean (doc only) | 1 | ~+2 |
| Cslib.lean updates | 1 | ~+12 |
| **Total** | **13** | **~2047** |

This is a substantial addition. If the ~300 LOC soft limit per PR is a concern (per task 216 research), this should be a separate stacked PR rather than an addition to PR #649.
