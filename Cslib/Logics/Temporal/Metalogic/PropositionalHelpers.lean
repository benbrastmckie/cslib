/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Temporal.ProofSystem.Instances
public import Cslib.Foundations.Logic.Theorems.DerivationCombinators

/-!
# Propositional Helpers for Temporal Logic

Propositional combinator derivations needed by Chronicle files.
All theorems delegate to the generic `Cslib.Logic.Theorems.DerivationCombinators` raw-typed
layer, which is directly applicable since `Temporal.HilbertBX⇓φ` (the `InferenceSystem`
instance's raw derivation type) is definitionally `DerivationTree .Base [] φ` -- no local
`wrap`/`unwrap` bridge is needed.

## References

* Cslib/Foundations/Logic/Theorems/DerivationCombinators.lean -- generic raw-typed layer
* Cslib/Foundations/Logic/Theorems/Propositional/Core.lean -- generic theorems
* Cslib/Foundations/Logic/Theorems/Combinators.lean -- generic combinators
-/

@[expose] public section

namespace Cslib.Logic.Temporal.Metalogic

open Cslib.Logic
open Cslib.Logic.Temporal

variable {Atom : Type*}

noncomputable section

/-! ## Propositional Delegations -/

-- NOTE: `Temporal` is open in this file, and `S` is scoped prefix notation for the temporal
-- "Since" operator (see `Cslib.Logics.Temporal.ProofSystem.Instances`'s module-level warning),
-- so the generic layer's `S` type-tag argument MUST be supplied positionally via `@` rather
-- than as `(S := Temporal.HilbertBX)`, which the parser misreads as an application of the `S`
-- notation.

/-- Double negation elimination: ⊢ ¬¬φ → φ. -/
def doubleNegation (φ : Formula Atom) :
    DerivationTree FrameClass.Base [] (¬¬φ → φ) :=
  @Theorems.DerivationCombinators.doubleNegation _ _ _ Temporal.HilbertBX _ _ φ

/-- Ex falso quodlibet: ⊢ ⊥ → φ. -/
def efqAxiom (φ : Formula Atom) :
    DerivationTree FrameClass.Base [] (⊥ → φ) :=
  @Theorems.DerivationCombinators.efqAxiom _ _ _ Temporal.HilbertBX _ _ φ

/-- Implication transitivity: from ⊢ A → B and ⊢ B → C derive ⊢ A → C. -/
def impTrans {A B C : Formula Atom}
    (h1 : DerivationTree FrameClass.Base [] (A → B))
    (h2 : DerivationTree FrameClass.Base [] (B → C)) :
    DerivationTree FrameClass.Base [] (A → C) :=
  @Theorems.DerivationCombinators.impTransD _ _ _ Temporal.HilbertBX _ _ A B C h1 h2

/-- Pairing: ⊢ φ → ψ → (φ ∧ ψ). -/
def pairing (φ ψ : Formula Atom) :
    DerivationTree FrameClass.Base [] (φ.imp (ψ.imp (Formula.and φ ψ))) :=
  @Theorems.DerivationCombinators.pairing _ _ _ Temporal.HilbertBX _ _ φ ψ

/-- Left conjunction elimination: ⊢ (φ ∧ ψ) → φ. -/
def lceImp (φ ψ : Formula Atom) :
    DerivationTree FrameClass.Base [] (φ ∧ ψ → φ) :=
  @Theorems.DerivationCombinators.lceImp _ _ _ Temporal.HilbertBX _ _ φ ψ

/-- Right conjunction elimination: ⊢ (φ ∧ ψ) → ψ. -/
def rceImp (φ ψ : Formula Atom) :
    DerivationTree FrameClass.Base [] (φ ∧ ψ → ψ) :=
  @Theorems.DerivationCombinators.rceImp _ _ _ Temporal.HilbertBX _ _ φ ψ

/-- Double negation introduction: ⊢ φ → ¬¬φ. -/
def dni (φ : Formula Atom) :
    DerivationTree FrameClass.Base [] (φ → ¬¬φ) :=
  @Theorems.DerivationCombinators.dni _ _ _ Temporal.HilbertBX _ _ φ

/-- Identity combinator: ⊢ A → A. -/
def identity (A : Formula Atom) :
    DerivationTree FrameClass.Base [] (A → A) :=
  @Theorems.DerivationCombinators.identity _ _ _ Temporal.HilbertBX _ _ A

/-- De Morgan backward: ⊢ (¬A ∧ ¬B) → ¬(A ∨ B). -/
def demorganDisjNegBackward (A B : Formula Atom) :
    DerivationTree FrameClass.Base [] (¬A ∧ ¬B → ¬(A ∨ B)) :=
  @Theorems.DerivationCombinators.demorganDisjNegBackward _ _ _ Temporal.HilbertBX _ _ A B

end -- noncomputable section

end Cslib.Logic.Temporal.Metalogic
