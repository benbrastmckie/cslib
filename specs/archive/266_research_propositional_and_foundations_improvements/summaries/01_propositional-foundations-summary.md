# Implementation Summary: Propositional and Foundations Improvements (Task 266)

- **Task**: 266 - Research Propositional and Foundations Improvements
- **Status**: Implemented
- **Date**: 2026-06-23
- **Session**: sess_1782207443_50e0cd_266

## Overview

All 6 phases of the implementation plan completed successfully. The implementation adds the `HasDia` primitive, `Decidable (Tautology phi)`, propositional tableau abstraction, and GenericMCS bridge analysis to CSLib's Propositional/ and Foundations/Logic/ modules.

## Phase Summary

### Phase 1: Fix Documentation, Stale Comments, and Spurious Import [COMPLETED]

**Files modified**:
- `Cslib/Foundations/Logic/ProofSystem.lean`: Fixed stale "will be registered" comment (lines 44-45) to accurately state instances are registered in their respective `Instances.lean` files, with note on modal/temporal/bimodal tags having full instances.
- `Cslib/Logics/Propositional/NaturalDeduction/Basic.lean`: Replaced capture-avoidance TODO in `subs` docstring with a note that PL has no binding operators.
- `Cslib/Logics/Propositional/Semantics/Algebra/Conservative.lean`: Removed spurious `import Mathlib.Tactic.ToAdditive` (confirmed zero usage).
- `Cslib/Foundations/Logic/InferenceSystem.lean`: Filled empty `/-! -/` module docstring with 15 lines explaining `InferenceSystem`, `Default`, `DerivableIn`, `Derivable`, and notation `⇓`.
- `Cslib/Foundations/Logic/Axioms.lean`: Added docstring note to `DNE` explaining it is not separately axiomatized in `ClassicalHilbert` but derived from Peirce's law.

### Phase 2: Add HasDia Primitive [COMPLETED]

**Files modified**:
- `Cslib/Foundations/Logic/Connectives.lean`: Added `class HasDia (F : Type*) where dia : F → F` after `HasBox`. Docstring explains its role for non-classical modal logics where box and diamond are independent operators.
- `Cslib/Foundations/Logic/Axioms.lean`:
  - Updated comments on `AxiomB`, `Axiom5`, `AxiomD` to reference `HasDia` and `AxiomDiaDualityFwd`/`AxiomDiaDualityBack` rather than saying "HasDia is not yet a primitive"
  - Added `AxiomDiaDualityFwd`: `◇φ → ¬□¬φ`
  - Added `AxiomDiaDualityBack`: `¬□¬φ → ◇φ` (together these state the duality)

### Phase 3: Add Decidable (Tautology phi) Instance [COMPLETED]

**Files modified**:
- `Cslib/Logics/Propositional/Semantics/Bool.lean`:
  - Added `import Mathlib.Data.Fintype.Pi` (required for `Fintype (Bool → Bool)`)
  - Added `tautology_iff_boolEvaluate_true`: bridge lemma `Tautology φ ↔ ∀ v : BoolValuation Atom, BoolEvaluate v φ = true`
  - Added `instDecidableTautology [Fintype Atom] [DecidableEq Atom] (φ : Proposition Atom) : Decidable (Tautology φ)` using `decidable_of_iff` and `Fintype.decidableForallFintype` over `BoolValuation Atom = Atom → Bool`

### Phase 4: Extract Propositional Tableau Rules to Foundations/ [COMPLETED]

**Files created**:
- `Cslib/Foundations/Logic/PropositionalTableau.lean`: New generic propositional tableau infrastructure with:
  - `PropSign`: The two-element sign type (pos/neg)
  - `PropSignedFormula F`: A formula paired with a sign
  - `PropTableauRule`: The 8 standard analytic tableau rules as an inductive type
  - `PropRuleResult F`: Result type (linear/branching/notApplicable)
  - `applyPropRule`: Generic rule application parameterized over decomposition functions

**Files modified**:
- `Cslib.lean`: Added `public import Cslib.Foundations.Logic.PropositionalTableau`

The bimodal `Tableau.lean` was NOT modified (additive approach: created new reusable abstraction without breaking existing code).

### Phase 5: Scope GenericMCS Concretization for Modal Logic [COMPLETED]

**Files created**:
- `Cslib/Logics/Modal/Metalogic/GenericMCSBridge.lean`: Gap analysis documentation showing:
  - `algebraicDerivationSystem` and `modalDerivationSystem` serve complementary roles
  - `algebraicDerivationSystem` is directly usable for propositional MCS properties with modal logics
  - Main gap: `algebraicDerivationSystem` has no necessitation rule (uses `ListDeriv` = list implications only), while `modalDerivationSystem` includes necessitation via `DerivationTree`
  - Conclusion: modal logics can use algebraic path for propositional MCS reasoning today; necessitation-requiring MCS properties require `modalDerivationSystem`

**Files modified**:
- `Cslib/Foundations/Logic/Metalogic/GenericMCS.lean`: Added comment noting modal logics can use `algebraicDerivationSystem` for propositional MCS reasoning and pointing to `GenericMCSBridge.lean` for the gap analysis
- `Cslib.lean`: Added `public import Cslib.Logics.Modal.Metalogic.GenericMCSBridge`

### Phase 6: Add Propositional Test Coverage [COMPLETED]

**Files created**:
- `CslibTests/Propositional.lean`: Test coverage for:
  - BoolEvaluate on concrete formulas (atom, bot, and, or, imp)
  - Tautology decidability (`decide` and `native_decide` replaced with `decide` due to CSLib linter)
  - Tautology positive tests: `p ∨ ¬p`, `p → p`, `p → q → p`, DNE, De Morgan
  - Tautology negative tests: `p` alone, `p ∧ q` alone
  - Soundness round-trip theorem
  - Completeness bridge direction theorem

**Files modified**:
- `CslibTests.lean`: Added `public import CslibTests.Propositional`

## CI Verification

All CI pipeline steps passed:
- `lake exe cache get`: Cache hit (no downloads needed)
- `lake build`: Build completed successfully (3043 jobs)
- `lake exe checkInitImports`: Pass (no output)
- `lake lint`: "Linting passed for Cslib."
- `lake exe lint-style`: Pass (no output)
- `lake shake --add-public --keep-implied --keep-prefix`: No issues (fixed unused `Connectives` import in `PropositionalTableau.lean`, added `-- shake: keep-all` to `GenericMCSBridge.lean`)
- `lake exe mk_all --module`: "No update necessary"
- `lake test`: Pass (no errors)

## Verification Checks

- **Sorry count in modified files**: 0
- **New axioms introduced**: 0 (the `AxiomDiaDualityFwd/Back` are `abbrev` formula definitions, not Lean axiom declarations)
- **Vacuous definitions introduced**: 0

## Plan Deviations

1. **Phase 2**: Added `AxiomDiaDualityFwd` and `AxiomDiaDualityBack` as two separate implications instead of a biconditional `AxiomDiaDuality`, since encoding `↔` requires `HasAnd` which is not a constraint in the `DiaDuality` section.

2. **Phase 4**: Did not modify `Bimodal/Decidability/Tableau.lean` to import from the new module (the plan allowed the fallback "keep rules in place and create aliases"). The new `PropositionalTableau.lean` is additive infrastructure that can be adopted by the bimodal tableau in a separate future task.

3. **Phase 5**: The bridge was not proved (as the plan allowed for the NOT equivalent case). The gap analysis is documented in `GenericMCSBridge.lean` with the specific types and constraints explaining why the two systems are architecturally distinct.

4. **Phase 6**: Replaced `native_decide` with `decide` throughout the test file because CSLib's linter forbids `native_decide` (Mathlib style policy). The tests still verify the Decidable instance works via kernel reduction.
