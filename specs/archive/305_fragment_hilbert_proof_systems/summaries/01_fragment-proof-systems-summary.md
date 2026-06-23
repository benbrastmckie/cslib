# Implementation Summary: Fragment Hilbert Proof Systems (Task 305)

- **Task**: 305 - Fragment Hilbert Proof Systems
- **Status**: [COMPLETED]
- **Date**: 2026-06-23
- **Phases**: 1/1 completed

## What Was Implemented

Three files were created or modified to define fragment-specific Hilbert proof systems:

### 1. `Cslib/Foundations/Logic/ProofSystem.lean` (modified)

Added two new opaque tag types following the existing pattern at lines 491-497:
- `Propositional.HilbertConjImp`: Tag for IPL⟨∧,→,⊤⟩ conjunctive-implicational Hilbert system
- `Propositional.HilbertImp`: Tag for IPL⟨→,⊤⟩ implicational Hilbert system

### 2. `Cslib/Logics/Propositional/ProofSystem/FragmentAxioms.lean` (new file)

Defines the core fragment axiom predicates and proves their properties:

**Inductive Predicates**:
- `ConjImpAxiom`: 5 constructors (implyK, implyS, andI, andE1, andE2)
- `ImpAxiom`: 2 constructors (implyK, implyS)

**Subsumption Chain**:
- `ImpAxiom.toConjImpAxiom`: ImpAxiom → ConjImpAxiom
- `ConjImpAxiom.toMinPropAxiom`: ConjImpAxiom → MinPropAxiom

**Implication Witnesses** (for `hasDeductionTheorem`):
- `ConjImpAxiom.mem_implyK`, `ConjImpAxiom.mem_implyS`
- `ImpAxiom.mem_implyK`, `ImpAxiom.mem_implyS`

**Substitution Closure**:
- `subst_preserves_conjImpAxiom`: substitution preserves ConjImpAxiom
- `subst_preserves_impAxiom`: substitution preserves ImpAxiom

**Fragment Predicate Compatibility** (per-constructor lemmas):
- `conjImpAxiom_implyK_isOrBotFree`, `conjImpAxiom_implyS_isOrBotFree`
- `conjImpAxiom_andI_isOrBotFree`, `conjImpAxiom_andE1_isOrBotFree`, `conjImpAxiom_andE2_isOrBotFree`
- `impAxiom_implyK_isImpTopOnly`, `impAxiom_implyS_isImpTopOnly`

**Deduction Theorem Instances**:
- `conjImpAxiom_hasDeductionTheorem`
- `impAxiom_hasDeductionTheorem`

### 3. `Cslib/Logics/Propositional/ProofSystem/FragmentInstances.lean` (new file)

Registers typeclass instances for the new tag types:

**HilbertConjImp**: InferenceSystem, ModusPonens, HasAxiomImplyK, HasAxiomImplyS, HasAxiomAndI, HasAxiomAndE1, HasAxiomAndE2, MinimalHilbert

**HilbertImp**: InferenceSystem, ModusPonens, HasAxiomImplyK, HasAxiomImplyS, MinimalHilbert

## Plan Deviations

**Fragment predicate compatibility design**: The plan specified `ConjImpAxiom.isOrBotFree` and `ImpAxiom.isImpTopOnly` as single bundled lemmas. However, the predicates `IsOrBotFree` and `IsImpTopOnly` are `Bool`-valued recursively defined functions; they are NOT true for arbitrary propositions (e.g., `bot.IsOrBotFree = false`). The axiom constructors take arbitrary propositions as arguments, so a single lemma `ConjImpAxiom.isOrBotFree : ConjImpAxiom φ → φ.IsOrBotFree = true` would be false in general.

The correct formulation is conditional: "if the argument propositions are or-bot-free, then the axiom instance is or-bot-free." This was implemented as **per-constructor lemmas** (7 lemmas total) using `imp_isOrBotFree`, `and_isOrBotFree`, and `imp_isImpTopOnly` from `FragmentPredicates.lean`. This is cleaner and more useful for downstream consumers.

## Verification

- `lake build Cslib.Logics.Propositional.ProofSystem.FragmentAxioms` — ✔ passes
- `lake build Cslib.Logics.Propositional.ProofSystem.FragmentInstances` — ✔ passes
- `lake build Cslib.Foundations.Logic.ProofSystem` — ✔ passes
- `lake exe checkInitImports` — ✔ passes (Init imported transitively via Defs.lean)
- `lake exe lint-style` — ✔ passes (no style issues)
- `lake exe mk_all --module` — ✔ ran, Cslib.lean updated
- Sorry count in new files: 0
- Axiom count increase: 0
- Pre-existing CI failures (Tableau/Classical/Soundness, SequentCalculus/LK/CutElimination) are unrelated to this task

## Subsumption Chain

The full axiom subsumption chain is now:
```
ImpAxiom → ConjImpAxiom → MinPropAxiom → IntPropAxiom → PropositionalAxiom
```
