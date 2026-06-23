# Implementation Plan: IPL Conservative over IPL⟨∧,→,⊤⟩

- **Task**: 308 - IPL Conservative over IPL⟨∧,→,⊤⟩
- **Status**: [NOT STARTED]
- **Effort**: 1 hour
- **Dependencies**: 306 (Brouwerian completeness), 307 (free join completion) -- both complete
- **Research Inputs**: specs/308_ipl_conservative_over_conj_imp/reports/01_conservative-extension-research.md
- **Artifacts**: plans/01_conservative-extension-plan.md (this file)
- **Standards**:
  - .claude/rules/artifact-formats.md
  - .claude/rules/state-management.md
- **Type**: cslib

## Overview

Prove the conservative extension theorem: IPL is conservative over IPL⟨∧,→,⊤⟩ for or-bot-free formulas. The proof chains existing algebraic completeness infrastructure through the free join completion (LowerSet embedding). All building blocks exist; this task assembles them into a single new file with four theorems plus one utility combinator. Definition of done: `ConjImpConservative.lean` builds without sorry, passes lint, and is registered in `Cslib.lean`.

### Research Integration

- Report `01_conservative-extension-research.md` (integrated): Full proof chain analysis, template comparison with `hilbertIplConservativeOverMpl`, universe verification, import analysis, and estimated complexity (~70-80 lines).

## Goals & Non-Goals

- **Goals**:
  - Prove `hilbertIplConservativeOverConjImp`: main conservative extension theorem
  - Prove `derivableConjImpOfDerivableInt`: subsumption direction via axiom monotonicity
  - Prove `hilbertIplConservativeOverConjImp_iff`: biconditional combining both directions
  - Prove `ipl_conservative_over_conjImp`: ND corollary via algebraic bridge
  - Define `liftDerivationTree`: generic axiom-monotonicity combinator for PL derivation trees
  - Register the module in `Cslib.lean` barrel imports
- **Non-Goals**:
  - Proving conservative extension for the purely implicational fragment (IPL over IPL⟨→,⊤⟩)
  - Adding new Mathlib dependencies beyond what is already imported
  - Modifying existing proof infrastructure files

## Risks & Mitigations

- **Risk**: `LowerSet B` HeytingAlgebra instance not inferred automatically. **Mitigation**: The existing `FreeJoinCompletion.lean` already uses `AlgEvaluate` over `LowerSet B` without issues, confirming typeclass inference works.
- **Risk**: Universe mismatch between `HAValid.{u,u}` and `BrouwerianValid.{u,u}`. **Mitigation**: Research verified `LowerSet B : Type u` when `B : Type u`, preserving universe level.
- **Risk**: Noncomputability propagation from `conjImp_brouwerian_complete`. **Mitigation**: Wrap theorems in `noncomputable section`.

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |

Phases within the same wave can execute in parallel.

### Phase 1: Create ConjImpConservative.lean and register module [NOT STARTED]

- **Goal:** Create the complete `ConjImpConservative.lean` file with all theorems and register it in barrel imports.
- **Tasks:**
  - [ ] Create `Cslib/Logics/Propositional/Semantics/Algebra/ConjImpConservative.lean` with module header and imports (`HilbertCompleteness`, `BrouwerianCompleteness`, `FreeJoinCompletion`, `HilbertConservativeGlivenko`)
  - [ ] Define `liftDerivationTree` combinator: structural recursion on `DerivationTree` with 4 constructors (ax, assumption, modus_ponens, weakening), mapping axioms via a subsumption callback
  - [ ] Prove `hilbertIplConservativeOverConjImp`: chain `IPL.hilbert_alg_complete.mp` -> instantiate at `LowerSet B` -> `brouwerianEmbeddingLemma.mpr` -> `conjImp_brouwerian_complete`
  - [ ] Prove `derivableConjImpOfDerivableInt`: apply `liftDerivationTree` with `ConjImpAxiom.toMinPropAxiom.toIntPropAxiom`
  - [ ] Prove `hilbertIplConservativeOverConjImp_iff`: combine both directions
  - [ ] Prove `ipl_conservative_over_conjImp`: apply `derivableInIplIffDerivableInt.mp` then main theorem
  - [ ] Add `ConjImpConservative` to `Cslib.lean` barrel import
  - [ ] Run `lake build Cslib.Logics.Propositional.Semantics.Algebra.ConjImpConservative`
  - [ ] Run `lake exe checkInitImports` and `lake exe lint-style`
  - [ ] Add docstrings to all public declarations (docBlame compliance)
- **Timing:** 45 minutes
- **Depends on:** none

## Testing & Validation

- [ ] `lake build Cslib.Logics.Propositional.Semantics.Algebra.ConjImpConservative` passes
- [ ] `lake exe checkInitImports` passes (barrel import registered)
- [ ] `lake exe lint-style` passes (no style violations)
- [ ] No `sorry` in the file
- [ ] All public declarations have docstrings

## Artifacts & Outputs

- `Cslib/Logics/Propositional/Semantics/Algebra/ConjImpConservative.lean` (new file, ~75-85 lines)
- `plans/01_conservative-extension-plan.md` (this file)
- `summaries/01_conservative-extension-summary.md` (post-implementation)

## Rollback/Contingency

- Delete `ConjImpConservative.lean` and revert the `Cslib.lean` barrel import entry. No other files are modified by this task.
