/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module
public import Cslib.Logics.Bimodal.ProofSystem.Instances
public import Cslib.Foundations.Logic.Theorems.DerivationCombinators

/-! # Perpetuity Helper Lemmas

This module contains helper lemmas for proving the perpetuity principles (P1-P6).
These helpers derive each temporal component of the always operator from box:
- `boxToFuture`: `⊢ □φ → Gφ` (MF + MT)
- `boxToPast`: `⊢ □φ → Hφ` (temporal duality on MF)
- `boxToPresent`: `⊢ □φ → φ` (MT axiom)
- `tempFutureDerived`: `⊢ □φ → G(□φ)` (M4 + MF + MT)

The propositional combinators below delegate to the generic
`Cslib.Logic.Theorems.DerivationCombinators` raw-typed layer, which is directly applicable since
`Bimodal.HilbertTM⇓φ` is definitionally `DerivationTree .Base [] φ` -- no local `wrap`/`unwrap`
bridge is needed.

## References

* Ported from BimodalLogic/Theories/Bimodal/Theorems/Perpetuity/Helpers.lean
-/

-- Do not open Cslib.Logic.Bimodal to avoid scoped notation conflicts
-- (F, G, H, P are prefix notation for temporal operators)

@[expose] public section

namespace Cslib.Logic.Bimodal.Theorems.Perpetuity

open Cslib.Logic

variable {Atom : Type u}

-- Local notation for derivability at Base frame class
local notation:50 "⊢ " phi =>
  Bimodal.DerivationTree Bimodal.FrameClass.Base ([] : List (Bimodal.Formula Atom)) phi

-- Context derivability notation
local notation:50 Gamma " ⊢ " phi =>
  Bimodal.DerivationTree Bimodal.FrameClass.Base Gamma phi

noncomputable section

-- NOTE: `Bimodal` is not opened in this file (its scoped notation for temporal operators would
-- conflict with local names); qualified `Bimodal.` access and positional `@`-application below
-- match the pre-existing convention in this file.

/-- Transitivity: from `⊢ φ → ψ` and `⊢ ψ → χ`, derive `⊢ φ → χ`. -/
def impTrans {φ ψ χ : Bimodal.Formula Atom}
    (h1 : ⊢ φ.imp ψ) (h2 : ⊢ ψ.imp χ) : ⊢ φ.imp χ :=
  @Theorems.DerivationCombinators.impTransD _ _ _ Bimodal.HilbertTM _ _ φ ψ χ h1 h2

/-- Identity: `⊢ φ → φ`. -/
def identity (φ : Bimodal.Formula Atom) : ⊢ φ.imp φ :=
  @Theorems.DerivationCombinators.identity _ _ _ Bimodal.HilbertTM _ _ φ

/-- Combine three implications into conjunction. -/
def combineImpConj3 {φ₀ φ₁ φ₂ φ₃ : Bimodal.Formula Atom}
    (h1 : ⊢ φ₀.imp φ₁) (h2 : ⊢ φ₀.imp φ₂) (h3 : ⊢ φ₀.imp φ₃) :
    ⊢ φ₀.imp (φ₁.and (φ₂.and φ₃)) :=
  @Theorems.DerivationCombinators.combineImpConj3 _ _ _ Bimodal.HilbertTM _ _ φ₀ φ₁ φ₂ φ₃ h1 h2 h3

/-- Combine two implications into conjunction. -/
def combineImpConj {φ₀ φ₁ φ₂ : Bimodal.Formula Atom}
    (h1 : ⊢ φ₀.imp φ₁) (h2 : ⊢ φ₀.imp φ₂) :
    ⊢ φ₀.imp (φ₁.and φ₂) :=
  @Theorems.DerivationCombinators.combineImpConj _ _ _ Bimodal.HilbertTM _ _ φ₀ φ₁ φ₂ h1 h2

/-- DNI: `⊢ φ → ¬¬φ`. -/
def dni (φ : Bimodal.Formula Atom) : ⊢ φ.imp φ.neg.neg :=
  @Theorems.DerivationCombinators.dni _ _ _ Bimodal.HilbertTM _ _ φ

/-- Contraposition: from `⊢ φ → ψ`, derive `⊢ ¬ψ → ¬φ`. -/
def contraposition {φ ψ : Bimodal.Formula Atom}
    (h : ⊢ φ.imp ψ) : ⊢ ψ.neg.imp φ.neg :=
  @Theorems.DerivationCombinators.contraposition _ _ _ Bimodal.HilbertTM _ _ φ ψ h

/-- Double negation elimination: `⊢ ¬¬φ → φ`. -/
def doubleNegation (φ : Bimodal.Formula Atom) : ⊢ φ.neg.neg.imp φ :=
  @Theorems.DerivationCombinators.doubleNegation _ _ _ Bimodal.HilbertTM _ _ φ

/-- Left conjunction elimination: `⊢ (φ₁ ∧ φ₂) → φ₁`. -/
def lceImp (φ₁ φ₂ : Bimodal.Formula Atom) : ⊢ (φ₁.and φ₂).imp φ₁ :=
  @Theorems.DerivationCombinators.lceImp _ _ _ Bimodal.HilbertTM _ _ φ₁ φ₂

/-- Right conjunction elimination: `⊢ (φ₁ ∧ φ₂) → φ₂`. -/
def rceImp (φ₁ φ₂ : Bimodal.Formula Atom) : ⊢ (φ₁.and φ₂).imp φ₂ :=
  @Theorems.DerivationCombinators.rceImp _ _ _ Bimodal.HilbertTM _ _ φ₁ φ₂

/-! ## Helper Lemmas: Temporal Components -/

/-- Box implies future: `⊢ □φ → Gφ`. MF + MT composed. -/
def boxToFuture (φ : Bimodal.Formula Atom) : ⊢ φ.box.imp φ.allFuture :=
  impTrans
    (Bimodal.DerivationTree.axiom [] _ (Bimodal.Axiom.modal_future φ) trivial)
    (Bimodal.DerivationTree.axiom [] _ (Bimodal.Axiom.modal_t φ.allFuture) trivial)

/-- Box implies past: `⊢ □φ → Hφ`. Via temporal duality on boxToFuture. -/
def boxToPast (φ : Bimodal.Formula Atom) : ⊢ φ.box.imp φ.allPast := by
  have h1 := boxToFuture φ.swapTemporal
  have h2 := Bimodal.DerivationTree.temporal_duality _ h1
  simp only [Bimodal.Formula.swapTemporal, Bimodal.Formula.swapTemporal_involution,
    Bimodal.Formula.swapTemporal_allFuture] at h2
  exact h2

/-- Box implies present: `⊢ □φ → φ` (MT axiom). -/
def boxToPresent (φ : Bimodal.Formula Atom) : ⊢ φ.box.imp φ :=
  Bimodal.DerivationTree.axiom [] _ (Bimodal.Axiom.modal_t φ) trivial

/-- `tempFutureDerived`: `⊢ □φ → G(□φ)`. M4 + MF + MT composed. -/
def tempFutureDerived (φ : Bimodal.Formula Atom) : ⊢ φ.box.imp φ.box.allFuture :=
  impTrans
    (impTrans
      (Bimodal.DerivationTree.axiom [] _ (Bimodal.Axiom.modal_4 φ) trivial)
      (Bimodal.DerivationTree.axiom [] _ (Bimodal.Axiom.modal_future φ.box) trivial))
    (Bimodal.DerivationTree.axiom [] _ (Bimodal.Axiom.modal_t φ.box.allFuture) trivial)

end -- noncomputable section

end Cslib.Logic.Bimodal.Theorems.Perpetuity
