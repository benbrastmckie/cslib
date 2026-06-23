# Implementation Plan: Fix Missing Docstrings in ND/Inference

- **Task**: 294 - fix_missing_docstrings_nd_inference
- **Status**: [NOT STARTED]
- **Effort**: 0.5 hours
- **Dependencies**: None
- **Research Inputs**: reports/01_docstring-research.md
- **Artifacts**: plans/01_docstring-fix-plan.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: cslib
- **Lean Intent**: false

## Overview

Add missing `/-- ... -/` docstrings to 6 declarations across two files to satisfy the `docBlame` linter. All edits are mechanical single-line doc comments with no code or proof changes. One declaration (`equiv.refl`) may already have a docstring and needs verification before editing.

### Research Integration

Research report (`reports/01_docstring-research.md`) identified all 6 declarations, their exact line numbers, and drafted suggested docstring text. Key finding: `equiv.refl` at line 361 of `NaturalDeduction/Basic.lean` already appears to have a docstring on line 360, so the linter may no longer flag it.

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

No ROADMAP.md found.

## Goals & Non-Goals

**Goals**:
- Add docstrings to all declarations flagged by `/vet 266` in InferenceSystem.lean and NaturalDeduction/Basic.lean
- Follow CONTRIBUTING.md docstring conventions (backtick code references, concise descriptions)
- Pass `lake build` and `lake exe lint-style` after changes

**Non-Goals**:
- Modifying any code or proof logic
- Adding docstrings to declarations not flagged by the linter
- Refactoring or restructuring the target files

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Line numbers shifted since research | L | M | Verify actual line numbers before editing |
| `equiv.refl` already has docstring | L | H | Check linter output; skip if already documented |
| Docstring wording inconsistent with surroundings | L | L | Review adjacent docstrings for style before writing |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |

Phases within the same wave can execute in parallel.

### Phase 1: Add Docstrings and Verify [COMPLETED]

**Goal**: Add missing docstrings to all flagged declarations and verify the linter is satisfied.

**Tasks**:
- [ ] Read `Cslib/Foundations/Logic/InferenceSystem.lean` and locate the two anonymous `Coe` instances (around lines 74, 81)
- [ ] Add docstring before the `Coe` instance (derivation to derivability): `/-- Coercion from a derivation `S⇓a` to `DerivableIn S a`. Wraps `DerivableIn.fromDerivation`. -/`
- [ ] Add docstring before the noncomputable `Coe` instance (derivability to derivation): `/-- Noncomputable coercion from `DerivableIn S a` to `S⇓a`, extracting a derivation via `Classical.choice`. Wraps `DerivableIn.toDerivation`. -/`
- [ ] Read `Cslib/Logics/Propositional/NaturalDeduction/Basic.lean` and locate `emptySequent_eq`, `iff_derivableIn_empty`, `derivableIn_top`, and `equiv.refl`
- [ ] Add docstring before `emptySequent_eq`: `/-- A derivation `T⇓A` is definitionally equal to a derivation of the empty sequent `T⇓(∅ ⊢ A)`. -/`
- [ ] Add docstring before `iff_derivableIn_empty`: `/-- Derivability `DerivableIn T A` is equivalent to derivability of the empty sequent `DerivableIn T (∅ ⊢ A)`. -/`
- [ ] Add docstring before `derivableIn_top`: `/-- The verum `⊤` is derivable in any theory. -/`
- [ ] Check whether `equiv.refl` already has a docstring; add one only if missing
- [ ] Run `lake build Cslib.Foundations.Logic.InferenceSystem` and `lake build Cslib.Logics.Propositional.NaturalDeduction.Basic` to verify no build errors
- [ ] Run `lake exe lint-style` to confirm `docBlame` warnings are resolved for these declarations

**Timing**: 0.5 hours

**Depends on**: none

**Files to modify**:
- `Cslib/Foundations/Logic/InferenceSystem.lean` - Add 2 docstrings (Coe instances)
- `Cslib/Logics/Propositional/NaturalDeduction/Basic.lean` - Add 3-4 docstrings (emptySequent_eq, iff_derivableIn_empty, derivableIn_top, possibly equiv.refl)

**Verification**:
- `lake build` succeeds for both files
- `lake exe lint-style` reports no `docBlame` warnings for the 6 target declarations
- No existing code or proofs modified

## Testing & Validation

- [ ] `lake build Cslib.Foundations.Logic.InferenceSystem` passes
- [ ] `lake build Cslib.Logics.Propositional.NaturalDeduction.Basic` passes
- [ ] `lake exe lint-style` shows no docBlame warnings for target declarations
- [ ] `lake exe checkInitImports` passes (no import changes expected)

## Artifacts & Outputs

- `plans/01_docstring-fix-plan.md` (this file)
- Modified: `Cslib/Foundations/Logic/InferenceSystem.lean`
- Modified: `Cslib/Logics/Propositional/NaturalDeduction/Basic.lean`

## Rollback/Contingency

Revert the two modified files with `git checkout -- Cslib/Foundations/Logic/InferenceSystem.lean Cslib/Logics/Propositional/NaturalDeduction/Basic.lean`. No other files are affected.
