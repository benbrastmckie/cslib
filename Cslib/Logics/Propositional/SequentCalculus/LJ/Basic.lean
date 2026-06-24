/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

import Cslib.Init
public import Cslib.Logics.Propositional.NaturalDeduction.Basic
public import Cslib.Foundations.Logic.InferenceSystem

/-! # Intuitionistic Propositional Sequent Calculus LJ

We define the LJ proof system for intuitionistic propositional logic using an all-additive
Finset-based presentation following Negri and von Plato (2001). In this style every rule
conclusion has an explicit context `Γ` (antecedent) and a single conclusion formula; structural
rules (weakening, contraction) are admissible, with weakening proved here as a derived rule.

LJ sequents reuse the ND `Sequent` type: `Ctx Atom × Proposition Atom`, notated `Γ ⊢ A`.
Unlike LK, LJ has a single-conclusion succedent, which eliminates `weakR` and splits the
right disjunction rule into `orR1` and `orR2`.

## Main Definitions

- `LJProof`: An inductive type of LJ proofs with 11 constructors:
  `ax`, `botL`, `andL`, `andR`, `orL`, `orR1`, `orR2`, `impL`, `impR`,
  `weakL`, `cut`.
- `LJProof.height`: The height (depth) of an LJ proof tree.
- `LJProof.mono`: Monotonicity — weakening the antecedent (left side only).
- `CutFree`: A predicate on `LJProof` asserting the proof tree contains no `cut` steps.
- `CutFreeLJProof`: A subtype of `LJProof` restricted to cut-free proofs.

## Implementation Notes

Contexts are `Finset (Proposition Atom)`. The `insert` of a formula into a set is used
throughout, with `Finset.insert_comm` enabling commutativity when needed.

The `ax` rule requires `A ∈ Γ`, matching the all-additive presentation where the antecedent
explicitly contains the principal formula.

Unlike LK, LJ has no succedent Finset: the conclusion is always a single `Proposition Atom`.
This means:
- No `weakR` constructor (no succedent to weaken)
- `orR` is split into `orR1` and `orR2` (no succedent membership needed)
- `andR` and `impR` take no membership proof for the conclusion
- `LJProof.mono` takes only one subset argument (left side)

## References

* [S. Negri, J. von Plato, *Structural Proof Theory*][NegriVonPlato2001], Ch. 3
* [A. S. Troelstra, H. Schwichtenberg,
  *Basic Proof Theory*][TroelstraSchwichtenberg2000], Ch. 4
-/

@[expose] public section

universe u

namespace Cslib.Logic.PL

open Proposition

variable {Atom : Type u} [DecidableEq Atom]

/-- LJ proof trees for intuitionistic propositional logic. The presentation is all-additive:
every rule has an explicit context set `Γ` (antecedent) and a single conclusion formula.
Principal formulas appear in both premise and conclusion contexts.

LJ uses single-conclusion sequents (`Γ ⊢ A` where `A : Proposition Atom`) rather than
two-sided multi-conclusion sequents as in LK. This means there is no `weakR` constructor,
and right disjunction splits into `orR1` and `orR2`.

Constructors:
- `ax`: identity axiom — `A` appears in the antecedent.
- `botL`: left falsum — `⊥` in the antecedent derives anything.
- `andL`: left conjunction — from `A, B, Γ ⊢ C` derive `A ∧ B, Γ ⊢ C`.
- `andR`: right conjunction — from `Γ ⊢ A` and `Γ ⊢ B` derive `Γ ⊢ A ∧ B`.
- `orL`: left disjunction — from `A, Γ ⊢ C` and `B, Γ ⊢ C` derive `A ∨ B, Γ ⊢ C`.
- `orR1`: right disjunction left — from `Γ ⊢ A` derive `Γ ⊢ A ∨ B`.
- `orR2`: right disjunction right — from `Γ ⊢ B` derive `Γ ⊢ A ∨ B`.
- `impL`: left implication — from `Γ ⊢ A` and `B, Γ ⊢ C` derive `(A → B), Γ ⊢ C`.
- `impR`: right implication — from `A, Γ ⊢ B` derive `Γ ⊢ A → B`.
- `weakL`: left weakening — add a formula to the antecedent.
- `cut`: cut rule — eliminate a formula `A` using a left and right proof. -/
inductive LJProof : @Sequent Atom → Type u where
  /-- Identity axiom: formula `A` appears in the antecedent. -/
  | ax (A : Proposition Atom) (Γ : Ctx Atom) (_ : A ∈ Γ) :
      LJProof (Γ ⊢ A)
  /-- Left falsum: bottom in the antecedent derives anything. -/
  | botL (Γ : Ctx Atom) (C : Proposition Atom) (_ : (⊥ : Proposition Atom) ∈ Γ) :
      LJProof (Γ ⊢ C)
  /-- Left conjunction: from `A, B, Γ ⊢ C` derive `A ∧ B, Γ ⊢ C`. -/
  | andL {Γ : Ctx Atom} {C : Proposition Atom} (A B : Proposition Atom)
      (_ : (A ∧ B) ∈ Γ)
      (_ : LJProof (insert A (insert B Γ) ⊢ C)) :
      LJProof (Γ ⊢ C)
  /-- Right conjunction: from `Γ ⊢ A` and `Γ ⊢ B` derive `Γ ⊢ A ∧ B`. -/
  | andR {Γ : Ctx Atom} (A B : Proposition Atom)
      (_ : LJProof (Γ ⊢ A))
      (_ : LJProof (Γ ⊢ B)) :
      LJProof (Γ ⊢ A ∧ B)
  /-- Left disjunction: from `A, Γ ⊢ C` and `B, Γ ⊢ C` derive `A ∨ B, Γ ⊢ C`. -/
  | orL {Γ : Ctx Atom} {C : Proposition Atom} (A B : Proposition Atom)
      (_ : (A ∨ B) ∈ Γ)
      (_ : LJProof (insert A Γ ⊢ C))
      (_ : LJProof (insert B Γ ⊢ C)) :
      LJProof (Γ ⊢ C)
  /-- Right disjunction left: from `Γ ⊢ A` derive `Γ ⊢ A ∨ B`. -/
  | orR1 {Γ : Ctx Atom} (A B : Proposition Atom)
      (_ : LJProof (Γ ⊢ A)) :
      LJProof (Γ ⊢ A ∨ B)
  /-- Right disjunction right: from `Γ ⊢ B` derive `Γ ⊢ A ∨ B`. -/
  | orR2 {Γ : Ctx Atom} (A B : Proposition Atom)
      (_ : LJProof (Γ ⊢ B)) :
      LJProof (Γ ⊢ A ∨ B)
  /-- Left implication: from `Γ ⊢ A` and `B, Γ ⊢ C` derive `(A → B), Γ ⊢ C`. -/
  | impL {Γ : Ctx Atom} {C : Proposition Atom} (A B : Proposition Atom)
      (_ : (A → B) ∈ Γ)
      (_ : LJProof (Γ ⊢ A))
      (_ : LJProof (insert B Γ ⊢ C)) :
      LJProof (Γ ⊢ C)
  /-- Right implication: from `A, Γ ⊢ B` derive `Γ ⊢ A → B`. -/
  | impR {Γ : Ctx Atom} (A B : Proposition Atom)
      (_ : LJProof (insert A Γ ⊢ B)) :
      LJProof (Γ ⊢ A → B)
  /-- Left weakening: add a formula to the antecedent. -/
  | weakL {Γ : Ctx Atom} {C : Proposition Atom} (A : Proposition Atom)
      (_ : LJProof (Γ ⊢ C)) :
      LJProof (insert A Γ ⊢ C)
  /-- Cut rule: cut on formula `A`. -/
  | cut {Γ : Ctx Atom} {C : Proposition Atom} (A : Proposition Atom)
      (_ : LJProof (Γ ⊢ A))
      (_ : LJProof (insert A Γ ⊢ C)) :
      LJProof (Γ ⊢ C)

/-- The height of an LJ proof tree (maximum rule depth). -/
def LJProof.height {seq : @Sequent Atom} : LJProof seq → Nat
  | .ax _ _ _ => 0
  | .botL _ _ _ => 0
  | .andL _ _ _ d => d.height + 1
  | .andR _ _ d₁ d₂ => max d₁.height d₂.height + 1
  | .orL _ _ _ d₁ d₂ => max d₁.height d₂.height + 1
  | .orR1 _ _ d => d.height + 1
  | .orR2 _ _ d => d.height + 1
  | .impL _ _ _ d₁ d₂ => max d₁.height d₂.height + 1
  | .impR _ _ d => d.height + 1
  | .weakL _ d => d.height + 1
  | .cut _ d₁ d₂ => max d₁.height d₂.height + 1

/-- Left-side monotonicity (weakening): if `Γ ⊆ Γ'` then any LJ proof of `Γ ⊢ C` yields
an LJ proof of `Γ' ⊢ C`.

Unlike LK's two-sided `mono`, LJ has a single-conclusion succedent so only the antecedent
needs to be weakened. This follows by structural induction on the proof, inserting additional
weakening steps at axiom and `botL` leaves and propagating context extensions upward through
the rules. -/
def LJProof.mono {Γ Γ' : Ctx Atom} {C : Proposition Atom}
    (hL : Γ ⊆ Γ') : LJProof (Γ ⊢ C) → LJProof (Γ' ⊢ C)
  | .ax A _ hA =>
      ax A Γ' (hL hA)
  | .botL _ _ hbot =>
      botL Γ' _ (hL hbot)
  | .andL A B hAB d =>
      andL A B (hL hAB)
        (d.mono (Finset.insert_subset_insert _ (Finset.insert_subset_insert _ hL)))
  | .andR A B d₁ d₂ =>
      andR A B
        (d₁.mono hL)
        (d₂.mono hL)
  | .orL A B hAB d₁ d₂ =>
      orL A B (hL hAB)
        (d₁.mono (Finset.insert_subset_insert _ hL))
        (d₂.mono (Finset.insert_subset_insert _ hL))
  | .orR1 A B d =>
      orR1 A B (d.mono hL)
  | .orR2 A B d =>
      orR2 A B (d.mono hL)
  | .impL A B hAB d₁ d₂ =>
      impL A B (hL hAB)
        (d₁.mono hL)
        (d₂.mono (Finset.insert_subset_insert _ hL))
  | .impR A B d =>
      impR A B (d.mono (Finset.insert_subset_insert _ hL))
  | .weakL A d =>
      d.mono ((Finset.subset_insert A _).trans hL)
  | .cut A d₁ d₂ =>
      cut A
        (d₁.mono hL)
        (d₂.mono (Finset.insert_subset_insert _ hL))

/-- A predicate asserting that an LJ proof is cut-free (contains no `cut` steps). -/
def LJCutFree : LJProof (Atom := Atom) seq → Prop
  | .ax _ _ _ => True
  | .botL _ _ _ => True
  | .andL _ _ _ d => LJCutFree d
  | .andR _ _ d₁ d₂ => LJCutFree d₁ ∧ LJCutFree d₂
  | .orL _ _ _ d₁ d₂ => LJCutFree d₁ ∧ LJCutFree d₂
  | .orR1 _ _ d => LJCutFree d
  | .orR2 _ _ d => LJCutFree d
  | .impL _ _ _ d₁ d₂ => LJCutFree d₁ ∧ LJCutFree d₂
  | .impR _ _ d => LJCutFree d
  | .weakL _ d => LJCutFree d
  | .cut _ _ _ => False

/-- An `LJProof` that is cut-free. -/
def CutFreeLJProof (seq : @Sequent Atom) : Type u :=
  { d : LJProof seq // LJCutFree d }

/-- LJ inference system instance for `@Sequent Atom`. -/
instance : InferenceSystem InferenceSystem.Default (@Sequent (Atom := Atom)) where
  derivation seq := LJProof seq

end Cslib.Logic.PL
