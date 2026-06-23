/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module  -- shake: keep-all

public import Cslib.Foundations.Logic.Metalogic.GenericMCS
public import Cslib.Logics.Modal.Metalogic.DerivationTree

/-! # GenericMCS Bridge Analysis for Normal Modal Logics

This module analyzes the relationship between two derivation systems available for
normal modal logics:

1. **`algebraicDerivationSystem (S := Modal.HilbertK)`**: Constructed from `ListDeriv`
   via the generic MCS framework. Available for any `MinimalHilbert` proof system.

2. **`modalDerivationSystem (@KAxiom Atom)`**: Constructed from explicit `DerivationTree`
   induction. Specific to modal logics with named axiom predicates.

## Gap Analysis

The two systems are **not** equivalent. The gap has two components:

### Component 1: Propositional Fragment Match

For the propositional fragment (no modal rules, derivation from finite list premises):

  `algebraicDerivationSystem.Deriv Γ φ` (`ListDeriv (S := Modal.HilbertK) Γ φ`)
  ≅
  `modalDerivationSystem.Deriv Γ φ` (`Nonempty (DerivationTree KAxiom Γ φ)`)

These two are equivalent on the propositional fragment. Both derive exactly the
classically provable propositional formulas from a list context, using K, S, MP,
EFQ, and Peirce. The proof would be:

  (→) Induction on `ListDeriv`: each `ListDeriv` constructor maps to a `DerivationTree`
      constructor via the K instance's `HasAxiomImplyK`, `HasAxiomImplyS`, etc.

  (←) Induction on `DerivationTree`: axiom/assumption/mp/weakening cases map to
      corresponding `ListDeriv` construction. The necessitation case is the gap (see below).

### Component 2: Necessitation Gap (Main Blocker)

**`algebraicDerivationSystem` has NO necessitation rule.**

`ListDeriv (S := S) Γ φ` is provability via list implications only. It is defined as
`DerivableIn S (listImp Γ φ)`, where `listImp` unfolds to `φ₁ → (φ₂ → ... → (φₙ → φ))`.
This captures propositional contextual derivability but does NOT include necessitation.

`modalDerivationSystem` explicitly includes necessitation via the `necessitation` constructor
of `DerivationTree`, which derives `□φ` from `⊢ φ` (empty context proof).

**Consequence**: The two systems disagree on formulas requiring necessitation:
- `□(φ → φ)` is provable in `modalDerivationSystem` (apply necessitation to `⊢ φ → φ`)
- `□(φ → φ)` is NOT derivable in `algebraicDerivationSystem` from `[]` because `ListDeriv`
  has no way to introduce the box.

### Component 3: MCS Reuse Scope

**For the propositional MCS properties** (lindenbaum, closed_under_derivation,
implication_property, negation_complete), the algebraic path IS directly usable:

  `algebraicDerivationSystem (S := Modal.HilbertK)` makes all `SetMaximalConsistent`
  properties from `Consistency.lean` available to modal logics for their propositional
  fragment reasoning. This is already achieved: `GenericMCS.algebraic_mcs_closed_under_derivation`
  etc. compose with modal `HilbertK` instances.

**For modal MCS properties** (box closure, box-box, etc.), the custom `modalDerivationSystem`
path remains necessary because necessitation is required.

## Conclusion

The `algebraicDerivationSystem` and `modalDerivationSystem` serve complementary roles
and cannot replace each other:

| Role | System | Notes |
|------|--------|-------|
| Propositional MCS lemmas | `algebraicDerivationSystem` | Generic, no modal rules needed |
| Modal MCS lemmas (box closure, etc.) | `modalDerivationSystem` | Requires necessitation |
| Deduction theorem | Both (independent proofs) | |
| Consistency/lindenbaum | Both | `algebraicDerivationSystem` is simpler |

## Follow-up Tasks

To fully unify the two systems, a future task should:
1. Extend `algebraicDerivationSystem` (or `ListDeriv`) with a necessitation rule
   parameterized over `[Necessitation S]`
2. Prove equivalence between the extended algebraic system and `modalDerivationSystem`
   for normal modal logics
3. Retire `modalDerivationSystem` in favor of the unified algebraic path

A future task should extend `ListDeriv` with a necessitation rule and prove equivalence.

## Using GenericMCS with Modal Logics Today

Despite the gap, modal logics CAN already use the algebraic MCS path for their propositional
reasoning. The instance chain `Modal.HilbertK → MinimalHilbert → algebraicDerivationSystem`
works without any new code, since `Modal.HilbertK` satisfies `MinimalHilbert`:

```lean
-- Already works (no new code needed):
#check @algebraicDerivationSystem (Modal.Proposition Atom) _ _ (S := Modal.HilbertK) _
-- : Metalogic.DerivationSystem (Modal.Proposition Atom)

#check @algebraic_mcs_negation_complete (Modal.Proposition Atom) _ _ (S := Modal.HilbertK) _
-- : ∀ {G : Set (Modal.Proposition Atom)}, SetMaximalConsistent (...) G → ∀ φ, φ ∈ G ∨ φ.neg ∈ G
```

The comment in `GenericMCS.lean` notes this directly.
-/

/-! NOTE: This file contains no Lean code (only documentation).
   The gap analysis above explains why no bridge theorem is proved here.
   The two derivation systems are architecturally distinct:
   - `algebraicDerivationSystem` captures propositional contextual derivability
   - `modalDerivationSystem` additionally captures necessitation

   Future work: extend `ListDeriv` with a necessitation rule and prove equivalence.
-/
