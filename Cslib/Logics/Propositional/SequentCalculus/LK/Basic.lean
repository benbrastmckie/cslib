/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

import Cslib.Init
public import Cslib.Logics.Propositional.SequentCalculus.Defs
public import Cslib.Foundations.Logic.InferenceSystem

/-! # Classical Propositional Sequent Calculus LK

We define the LK proof system for classical propositional logic using an all-additive
Finset-based presentation following Negri and von Plato (2001). In this style every rule
conclusion has explicit contexts `Γ` and `Δ` containing all side formulas; structural rules
(weakening, contraction) are admissible, with weakening proved here as a derived rule.

## Main Definitions

- `LKProof`: An inductive type of LK proofs with 11 constructors:
  `ax`, `botL`, `andL`, `andR`, `orL`, `orR`, `impL`, `impR`,
  `weakL`, `weakR`, `cut`.
- `LKProof.height`: The height (depth) of an LK proof tree.
- `LKProof.mono`: Monotonicity — weakening both the antecedent and succedent.
- `CutFree`: A predicate on `LKProof` asserting the proof tree contains no `cut` steps.

## Implementation Notes

Contexts are `Finset (Proposition Atom)`. The `insert` of a formula into a set is used
throughout, with `Finset.insert_comm` enabling commutativity when needed.

The `ax` rule requires `A ∈ Γ` and `A ∈ Δ` simultaneously, matching the all-additive
presentation where both sides explicitly contain the principal formula.

## References

* [S. Negri, J. von Plato, *Structural Proof Theory*][NegriVonPlato2001], Ch. 3
* [A. S. Troelstra, H. Schwichtenberg,
  *Basic Proof Theory*][TroelstraSchwichtenberg2000], Ch. 4
-/

@[expose] public section

universe u

namespace Cslib.Logic.PL

open Proposition LKSequent

variable {Atom : Type u} [DecidableEq Atom]

/-- LK proof trees for classical propositional logic. The presentation is all-additive:
every rule has explicit context sets `Γ` (antecedent) and `Δ` (succedent), and principal
formulas appear in both the premise and conclusion contexts.

Constructors:
- `ax`: identity axiom — `A` appears in both antecedent and succedent.
- `botL`: left falsum — `⊥` in the antecedent proves anything.
- `andL`: left conjunction — from `A, B, Γ ⊢ₛ Δ` derive `A ∧ B, Γ ⊢ₛ Δ`.
- `andR`: right conjunction — from `Γ ⊢ₛ A, Δ` and `Γ ⊢ₛ B, Δ` derive `Γ ⊢ₛ A ∧ B, Δ`.
- `orL`: left disjunction — from `A, Γ ⊢ₛ Δ` and `B, Γ ⊢ₛ Δ` derive `A ∨ B, Γ ⊢ₛ Δ`.
- `orR`: right disjunction — from `Γ ⊢ₛ A, B, Δ` derive `Γ ⊢ₛ A ∨ B, Δ`.
- `impL`: left implication — from `Γ ⊢ₛ A, Δ` and `B, Γ ⊢ₛ Δ` derive `(A → B), Γ ⊢ₛ Δ`.
- `impR`: right implication — from `A, Γ ⊢ₛ B, Δ` derive `Γ ⊢ₛ (A → B), Δ`.
- `weakL`: left weakening — add a formula to the antecedent.
- `weakR`: right weakening — add a formula to the succedent.
- `cut`: cut rule — eliminate a formula `A` using a left and right proof. -/
inductive LKProof : LKSequent Atom → Type u where
  /-- Identity axiom: formula `A` appears on both sides. -/
  | ax (A : Proposition Atom) (Γ Δ : Finset (Proposition Atom))
      (_ : A ∈ Γ) (_ : A ∈ Δ) :
      LKProof (Γ ⊢ₛ Δ)
  /-- Left falsum: bottom in the antecedent derives anything. -/
  | botL (Γ Δ : Finset (Proposition Atom)) (_ : (⊥ : Proposition Atom) ∈ Γ) :
      LKProof (Γ ⊢ₛ Δ)
  /-- Left conjunction: from `A, B, Γ ⊢ₛ Δ` derive `A ∧ B, Γ ⊢ₛ Δ`. -/
  | andL {Γ Δ : Finset (Proposition Atom)} (A B : Proposition Atom)
      (_ : (A ∧ B) ∈ Γ)
      (_ : LKProof ((insert A (insert B Γ)) ⊢ₛ Δ)) :
      LKProof (Γ ⊢ₛ Δ)
  /-- Right conjunction: from `Γ ⊢ₛ A, Δ` and `Γ ⊢ₛ B, Δ` derive `Γ ⊢ₛ A ∧ B, Δ`. -/
  | andR {Γ Δ : Finset (Proposition Atom)} (A B : Proposition Atom)
      (_ : (A ∧ B) ∈ Δ)
      (_ : LKProof (Γ ⊢ₛ insert A Δ))
      (_ : LKProof (Γ ⊢ₛ insert B Δ)) :
      LKProof (Γ ⊢ₛ Δ)
  /-- Left disjunction: from `A, Γ ⊢ₛ Δ` and `B, Γ ⊢ₛ Δ` derive `A ∨ B, Γ ⊢ₛ Δ`. -/
  | orL {Γ Δ : Finset (Proposition Atom)} (A B : Proposition Atom)
      (_ : (A ∨ B) ∈ Γ)
      (_ : LKProof ((insert A Γ) ⊢ₛ Δ))
      (_ : LKProof ((insert B Γ) ⊢ₛ Δ)) :
      LKProof (Γ ⊢ₛ Δ)
  /-- Right disjunction: from `Γ ⊢ₛ A, B, Δ` derive `Γ ⊢ₛ A ∨ B, Δ`. -/
  | orR {Γ Δ : Finset (Proposition Atom)} (A B : Proposition Atom)
      (_ : (A ∨ B) ∈ Δ)
      (_ : LKProof (Γ ⊢ₛ insert A (insert B Δ))) :
      LKProof (Γ ⊢ₛ Δ)
  /-- Left implication: from `Γ ⊢ₛ A, Δ` and `B, Γ ⊢ₛ Δ` derive `A → B, Γ ⊢ₛ Δ`. -/
  | impL {Γ Δ : Finset (Proposition Atom)} (A B : Proposition Atom)
      (_ : (A → B) ∈ Γ)
      (_ : LKProof (Γ ⊢ₛ insert A Δ))
      (_ : LKProof ((insert B Γ) ⊢ₛ Δ)) :
      LKProof (Γ ⊢ₛ Δ)
  /-- Right implication: from `A, Γ ⊢ₛ B, Δ` derive `Γ ⊢ₛ A → B, Δ`. -/
  | impR {Γ Δ : Finset (Proposition Atom)} (A B : Proposition Atom)
      (_ : (A → B) ∈ Δ)
      (_ : LKProof ((insert A Γ) ⊢ₛ insert B Δ)) :
      LKProof (Γ ⊢ₛ Δ)
  /-- Left weakening: add a formula to the antecedent. -/
  | weakL {Γ Δ : Finset (Proposition Atom)} (A : Proposition Atom)
      (_ : LKProof (Γ ⊢ₛ Δ)) :
      LKProof ((insert A Γ) ⊢ₛ Δ)
  /-- Right weakening: add a formula to the succedent. -/
  | weakR {Γ Δ : Finset (Proposition Atom)} (A : Proposition Atom)
      (_ : LKProof (Γ ⊢ₛ Δ)) :
      LKProof (Γ ⊢ₛ insert A Δ)
  /-- Cut rule: cut on formula `A`. -/
  | cut {Γ Δ : Finset (Proposition Atom)} (A : Proposition Atom)
      (_ : LKProof (Γ ⊢ₛ insert A Δ))
      (_ : LKProof ((insert A Γ) ⊢ₛ Δ)) :
      LKProof (Γ ⊢ₛ Δ)

/-- The height of an LK proof tree (maximum rule depth). -/
def LKProof.height {seq : LKSequent Atom} : LKProof seq → Nat
  | .ax _ _ _ _ _ => 0
  | .botL _ _ _ => 0
  | .andL _ _ _ d => d.height + 1
  | .andR _ _ _ d₁ d₂ => max d₁.height d₂.height + 1
  | .orL _ _ _ d₁ d₂ => max d₁.height d₂.height + 1
  | .orR _ _ _ d => d.height + 1
  | .impL _ _ _ d₁ d₂ => max d₁.height d₂.height + 1
  | .impR _ _ _ d => d.height + 1
  | .weakL _ d => d.height + 1
  | .weakR _ d => d.height + 1
  | .cut _ d₁ d₂ => max d₁.height d₂.height + 1

/-- Weakening is admissible: if `Γ ⊢ₛ Δ` then `Γ' ⊢ₛ Δ'` whenever `Γ ⊆ Γ'` and `Δ ⊆ Δ'`.

This follows by structural induction on the proof, inserting additional weakening steps
at axiom and `botL` leaves and propagating context extensions upward through the rules. -/
def LKProof.mono {Γ Δ Γ' Δ' : Finset (Proposition Atom)}
    (hL : Γ ⊆ Γ') (hR : Δ ⊆ Δ') : LKProof (Γ ⊢ₛ Δ) → LKProof (Γ' ⊢ₛ Δ')
  | .ax A _ _ hA hB =>
      ax A Γ' Δ' (hL hA) (hR hB)
  | .botL _ _ hbot =>
      botL Γ' Δ' (hL hbot)
  | .andL A B hAB d =>
      andL A B (hL hAB)
        (d.mono (Finset.insert_subset_insert _ (Finset.insert_subset_insert _ hL)) hR)
  | .andR A B hAB d₁ d₂ =>
      andR A B (hR hAB)
        (d₁.mono hL (Finset.insert_subset_insert _ hR))
        (d₂.mono hL (Finset.insert_subset_insert _ hR))
  | .orL A B hAB d₁ d₂ =>
      orL A B (hL hAB)
        (d₁.mono (Finset.insert_subset_insert _ hL) hR)
        (d₂.mono (Finset.insert_subset_insert _ hL) hR)
  | .orR A B hAB d =>
      orR A B (hR hAB)
        (d.mono hL (Finset.insert_subset_insert _ (Finset.insert_subset_insert _ hR)))
  | .impL A B hAB d₁ d₂ =>
      impL A B (hL hAB)
        (d₁.mono hL (Finset.insert_subset_insert _ hR))
        (d₂.mono (Finset.insert_subset_insert _ hL) hR)
  | .impR A B hAB d =>
      impR A B (hR hAB)
        (d.mono (Finset.insert_subset_insert _ hL) (Finset.insert_subset_insert _ hR))
  | .weakL A d =>
      d.mono ((Finset.subset_insert A _).trans hL) hR
  | .weakR A d =>
      d.mono hL ((Finset.subset_insert A _).trans hR)
  | .cut A d₁ d₂ =>
      cut A
        (d₁.mono hL (Finset.insert_subset_insert _ hR))
        (d₂.mono (Finset.insert_subset_insert _ hL) hR)

/-- A predicate asserting that an LK proof is cut-free (contains no `cut` steps). -/
def CutFree : LKProof (Atom := Atom) seq → Prop
  | .ax _ _ _ _ _ => True
  | .botL _ _ _ => True
  | .andL _ _ _ d => CutFree d
  | .andR _ _ _ d₁ d₂ => CutFree d₁ ∧ CutFree d₂
  | .orL _ _ _ d₁ d₂ => CutFree d₁ ∧ CutFree d₂
  | .orR _ _ _ d => CutFree d
  | .impL _ _ _ d₁ d₂ => CutFree d₁ ∧ CutFree d₂
  | .impR _ _ _ d => CutFree d
  | .weakL _ d => CutFree d
  | .weakR _ d => CutFree d
  | .cut _ _ _ => False

/-- An `LKProof` that is cut-free. -/
def CutFreeLKProof (seq : LKSequent Atom) : Type u :=
  { d : LKProof seq // CutFree d }

/-- LK inference system instance for `LKSequent`. -/
instance : InferenceSystem InferenceSystem.Default (LKSequent (Atom := Atom)) where
  derivation seq := LKProof seq

end Cslib.Logic.PL
