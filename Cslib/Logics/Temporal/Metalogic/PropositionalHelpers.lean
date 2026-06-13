/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Temporal.Metalogic.MCS
public import Cslib.Logics.Temporal.ProofSystem.Instances
public import Cslib.Foundations.Logic.Theorems.Propositional.Core
public import Cslib.Foundations.Logic.Theorems.Propositional.Connectives
public import Cslib.Foundations.Logic.Theorems.Combinators

/-!
# Propositional Helpers for Temporal Logic

Propositional combinator derivations needed by Chronicle files.
All theorems delegate to the generic Foundations versions via the wrap/unwrap
bridge pattern, following the approach established in Bimodal/Theorems/Perpetuity/Helpers.lean.

## Bridge Pattern

The `InferenceSystem` instance for `Temporal.HilbertBX` maps
`HilbertBX⇓φ` to `DerivationTree .Base [] φ`, so:
- `wrap`: `DerivationTree .Base [] φ → Nonempty (DerivationTree .Base [] φ)`
- `unwrap`: `Nonempty (DerivationTree .Base [] φ) → DerivationTree .Base [] φ`

## References

* Cslib/Logics/Bimodal/Theorems/Perpetuity/Helpers.lean -- established pattern
* Cslib/Foundations/Logic/Theorems/Propositional/Core.lean -- generic theorems
* Cslib/Foundations/Logic/Theorems/Combinators.lean -- generic combinators
-/

set_option linter.style.emptyLine false

@[expose] public section

namespace Cslib.Logic.Temporal.Metalogic

open Cslib.Logic
open Cslib.Logic.Temporal

variable {Atom : Type*}

noncomputable section

/-! ## Typeclass Bridge -/

/-- Convert a derivation tree to a Nonempty (for typeclass functions). -/
def wrap {φ : Formula Atom}
    (d : DerivationTree FrameClass.Base [] φ) :
    InferenceSystem.DerivableIn Temporal.HilbertBX φ := ⟨d⟩

/-- Extract a derivation tree from Nonempty (from typeclass functions). -/
def unwrap {φ : Formula Atom}
    (h : InferenceSystem.DerivableIn Temporal.HilbertBX φ) :
    DerivationTree FrameClass.Base [] φ := h.some

/-! ## Propositional Delegations -/

/-- Double negation elimination: ⊢ ¬¬φ → φ. -/
def doubleNegation (φ : Formula Atom) :
    DerivationTree FrameClass.Base [] (¬¬φ → φ) :=
  unwrap (@Theorems.Propositional.Core.double_negation
    _ _ _ Temporal.HilbertBX _ _ (φ := φ))

/-- Ex falso quodlibet: ⊢ ⊥ → φ. -/
def efqAxiom (φ : Formula Atom) :
    DerivationTree FrameClass.Base [] (⊥ → φ) :=
  unwrap (@Theorems.Propositional.Core.efq_axiom
    _ _ _ Temporal.HilbertBX _ _ (φ := φ))

/-- Implication transitivity: from ⊢ A → B and ⊢ B → C derive ⊢ A → C. -/
def impTrans {A B C : Formula Atom}
    (h1 : DerivationTree FrameClass.Base [] (A → B))
    (h2 : DerivationTree FrameClass.Base [] (B → C)) :
    DerivationTree FrameClass.Base [] (A → C) :=
  unwrap (Theorems.Combinators.imp_trans (wrap h1) (wrap h2))

/-- Pairing: ⊢ φ → ψ → (φ ∧ ψ). -/
def pairing (φ ψ : Formula Atom) :
    DerivationTree FrameClass.Base [] (φ.imp (ψ.imp (Formula.and φ ψ))) :=
  unwrap (HasAxiomAndI.andI (φ := φ) (ψ := ψ) :
    InferenceSystem.DerivableIn Temporal.HilbertBX _)

/-- Left conjunction elimination: ⊢ (φ ∧ ψ) → φ. -/
def lceImp (φ ψ : Formula Atom) :
    DerivationTree FrameClass.Base [] (φ ∧ ψ → φ) :=
  unwrap (HasAxiomAndE1.andE1 (φ := φ) (ψ := ψ) :
    InferenceSystem.DerivableIn Temporal.HilbertBX _)

/-- Right conjunction elimination: ⊢ (φ ∧ ψ) → ψ. -/
def rceImp (φ ψ : Formula Atom) :
    DerivationTree FrameClass.Base [] (φ ∧ ψ → ψ) :=
  unwrap (HasAxiomAndE2.andE2 (φ := φ) (ψ := ψ) :
    InferenceSystem.DerivableIn Temporal.HilbertBX _)

/-- Double negation introduction: ⊢ φ → ¬¬φ. -/
def dni (φ : Formula Atom) :
    DerivationTree FrameClass.Base [] (φ → ¬¬φ) :=
  unwrap (@Theorems.Combinators.dni _ _ _ Temporal.HilbertBX _ _ φ)

/-- Identity combinator: ⊢ A → A. -/
def identity (A : Formula Atom) :
    DerivationTree FrameClass.Base [] (A → A) :=
  unwrap (@Theorems.Combinators.identity _ _ _ Temporal.HilbertBX _ _ A)

/-- De Morgan backward: ⊢ (¬A ∧ ¬B) → ¬(A ∨ B).

    Proof: OrE gives `¬A → (¬B → ¬(A ∨ B))`. Compose with AndE1 and AndE2
    via S combinator to derive `(¬A ∧ ¬B) → ¬(A ∨ B)`. -/
def demorganDisjNegBackward (A B : Formula Atom) :
    DerivationTree FrameClass.Base [] (¬A ∧ ¬B → ¬(A ∨ B)) :=
  -- d_or_e: ⊢ ¬A → (¬B → ¬(A ∨ B))
  let d_or_e := unwrap (HasAxiomOrE.orE (φ := A) (ψ := B) (χ := Formula.bot) :
    InferenceSystem.DerivableIn Temporal.HilbertBX _)
  -- d_and_e1: ⊢ (¬A ∧ ¬B) → ¬A
  let d_and_e1 := unwrap (HasAxiomAndE1.andE1 (φ := Formula.neg A) (ψ := Formula.neg B) :
    InferenceSystem.DerivableIn Temporal.HilbertBX _)
  -- d_and_e2: ⊢ (¬A ∧ ¬B) → ¬B
  let d_and_e2 := unwrap (HasAxiomAndE2.andE2 (φ := Formula.neg A) (ψ := Formula.neg B) :
    InferenceSystem.DerivableIn Temporal.HilbertBX _)
  -- step1: ⊢ (¬A ∧ ¬B) → (¬B → ¬(A ∨ B))  [impTrans d_and_e1 d_or_e]
  let step1 := impTrans d_and_e1 d_or_e
  -- s_ax: ⊢ ((¬A∧¬B) → (¬B → ¬(A∨B))) → ((¬A∧¬B → ¬B) → (¬A∧¬B → ¬(A∨B)))
  let s_ax := unwrap (HasAxiomImplyS.implyS
    (φ := Formula.and (Formula.neg A) (Formula.neg B))
    (ψ := Formula.neg B)
    (χ := Formula.neg (Formula.or A B)) :
    InferenceSystem.DerivableIn Temporal.HilbertBX _)
  -- step2: ⊢ (¬A ∧ ¬B → ¬B) → (¬A ∧ ¬B → ¬(A ∨ B))
  let step2 := DerivationTree.modus_ponens [] _ _ s_ax step1
  -- conclusion: ⊢ (¬A ∧ ¬B) → ¬(A ∨ B)
  DerivationTree.modus_ponens [] _ _ step2 d_and_e2

end -- noncomputable section

end Cslib.Logic.Temporal.Metalogic
