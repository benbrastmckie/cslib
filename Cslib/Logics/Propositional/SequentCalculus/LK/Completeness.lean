/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Propositional.SequentCalculus.LK.Soundness
public import Cslib.Logics.Propositional.NaturalDeduction.Equivalence
public import Cslib.Logics.Propositional.Metalogic.StrongCompleteness

/-! # Completeness of LK for Classical Propositional Logic

This module proves that LK is complete for classical propositional logic by:
1. Translating ND derivations to LK proofs (`ndToLK`), establishing the forward direction
   of the ND–LK bridge.
2. Using LK soundness plus Hilbert completeness for the backward direction.
3. Composing with the existing Hilbert–ND bridge (`hilbert_iff_nd_ctx`) to yield
   `hilbert_iff_lk`.
4. Deriving `lk_completeness` and `lk_iff_tautology` as corollaries.

## Main Results

- `ndToLK`: Every ND derivation of `Γ ⊢ A` translates to an LK proof of `Γ ⊢ₛ {A}`.
- `nd_iff_lk`: `DerivableIn (AxiomTheory PropositionalAxiom) (Γ ⊢ A) ↔
  Nonempty (LKProof (Γ ⊢ₛ {A}))`.
- `hilbert_iff_lk`: Hilbert derivability from `Γ.toList` ↔ LK provability of `Γ ⊢ₛ {A}`.
- `lk_completeness`: Every tautology has an LK proof.
- `lk_iff_tautology`: `Tautology φ ↔ Nonempty (LKProof (∅ ⊢ₛ {φ}))`.

## Strategy

**Forward (`ndToLK`)**: Structural induction on `Theory.Derivation`.
- `ax h_mem`: Each `PropositionalAxiom` constructor translates to an LK proof of the
  corresponding sequent `∅ ⊢ₛ {axiom}`, then weakened to `Γ ⊢ₛ {axiom}`.
- `ass h_mem`: The assumption rule maps to `LKProof.ax` with singleton succedent.
- Logical rules map to the corresponding LK rules.

**Backward (`nd_iff_lk` ← direction)**: Via semantics.
- An LK proof of `Γ ⊢ₛ {A}` witnesses `(Γ ⊢ₛ {A}).valid` (by `LKProof.sound`).
- That validity says: for all valuations satisfying `Γ`, `A` holds.
- This is exactly `SemanticEntails ↑Γ A`.
- By `prop_strong_completeness`, `SetDerivable PropositionalAxiom ↑Γ A`.
- By the Hilbert–ND bridge, `DerivableIn (AxiomTheory PropositionalAxiom) (Γ ⊢ A)`.

## References

* [S. Negri, J. von Plato, *Structural Proof Theory*][NegriVonPlato2001], Ch. 3
* [A. S. Troelstra, H. Schwichtenberg,
  *Basic Proof Theory*][TroelstraSchwichtenberg2000], Ch. 4
-/

@[expose] public section

universe u

namespace Cslib.Logic.PL

open Proposition LKSequent Theory Finset InferenceSystem

variable {Atom : Type u} [DecidableEq Atom]

/-! ## LK Proofs of Axiom Schemata

Each `PropositionalAxiom` is provable in LK from the empty antecedent.
Membership proofs use `Finset.mem_insert_self`, `Finset.mem_singleton_self`,
and `Finset.mem_insert_of_mem` to avoid dependence on propositional equality,
which is not decidable for abstract atom types.

**All-additive conventions**: `impR A B h d` proves `Γ ⊢ₛ Δ` where `(A → B) ∈ Δ`,
using `d : insert A Γ ⊢ₛ insert B Δ`.
`impL A B h d₁ d₂` proves `Γ ⊢ₛ Δ` where `(A → B) ∈ Γ`,
using `d₁ : Γ ⊢ₛ insert A Δ` and `d₂ : insert B Γ ⊢ₛ Δ`. -/

/-- LK proof of implyK axiom: `∅ ⊢ₛ {φ → ψ → φ}`. -/
def lkAxiomImplyK (φ ψ : Proposition Atom) :
    LKProof (∅ ⊢ₛ ({φ.imp (ψ.imp φ)} : Finset _)) :=
  -- impR φ (ψ.imp φ): conclude ∅ ⊢ₛ {φ → (ψ → φ)}, prove {φ} ⊢ₛ {ψ→φ, φ→(ψ→φ)}
  -- impR ψ φ: prove {ψ,φ} ⊢ₛ {φ, ψ→φ, φ→(ψ→φ)}; ax φ
  LKProof.impR φ (ψ.imp φ) (Finset.mem_singleton_self _) <|
    LKProof.impR ψ φ (Finset.mem_insert_self _ _) <|
      LKProof.ax φ _ _ (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
        (Finset.mem_insert_self _ _)

/-- LK proof of implyS axiom:
`∅ ⊢ₛ {(φ → ψ → χ) → (φ → ψ) → φ → χ}`. -/
def lkAxiomImplyS (φ ψ χ : Proposition Atom) :
    LKProof (∅ ⊢ₛ ({(φ.imp (ψ.imp χ)).imp ((φ.imp ψ).imp (φ.imp χ))} : Finset _)) := by
  -- Three outer impR steps wrap the core proof
  -- impR (φ.imp (ψ.imp χ)) ((φ.imp ψ).imp (φ.imp χ)): the axiom formula in succedent
  apply LKProof.impR (φ.imp (ψ.imp χ)) ((φ.imp ψ).imp (φ.imp χ)) (Finset.mem_singleton_self _)
  -- impR (φ.imp ψ) (φ.imp χ): introduce (φ→ψ) on left, (φ→χ) in succedent
  apply LKProof.impR (φ.imp ψ) (φ.imp χ) (Finset.mem_insert_self _ _)
  -- impR φ χ: introduce φ on left, χ in succedent
  apply LKProof.impR φ χ (Finset.mem_insert_self _ _)
  -- Now: {φ→ψ→χ, φ→ψ, φ} ++ succedent_context ⊢ₛ {χ, ...}
  -- impL (φ→ψ→χ) to get ψ→χ from φ
  apply LKProof.impL φ (ψ.imp χ) (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
    (Finset.mem_insert_self _ _)))
  · -- Need Γ ⊢ₛ insert φ Δ: ax φ on left and right
    exact LKProof.ax φ _ _ (Finset.mem_insert_self _ _) (Finset.mem_insert_self _ _)
  · -- Now: {ψ→χ, φ→ψ→χ, φ→ψ, φ} ⊢ₛ {χ,...}
    -- impL (φ→ψ) to get ψ from φ
    apply LKProof.impL φ ψ (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
      (Finset.mem_insert_self _ _)))
    · -- Left branch: Γ ⊢ₛ insert φ Δ
      -- Γ = insert (ψ→χ) (insert φ ...); φ is second element
      exact LKProof.ax φ _ _ (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
        (Finset.mem_insert_self _ _)
    · -- Right branch: insert ψ Γ ⊢ₛ Δ; Γ = insert (ψ→χ) (insert φ ...)
      -- Now: {ψ, ψ→χ, φ, ...} ⊢ₛ {χ,...}
      -- impL (ψ→χ): ψ→χ is second element (skip ψ)
      apply LKProof.impL ψ χ (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
      · -- Left: Γ ⊢ₛ insert ψ Δ; ψ is first element
        exact LKProof.ax ψ _ _ (Finset.mem_insert_self _ _) (Finset.mem_insert_self _ _)
      · -- Right: insert χ Γ ⊢ₛ Δ; χ is first element
        exact LKProof.ax χ _ _ (Finset.mem_insert_self _ _) (Finset.mem_insert_self _ _)

/-- LK proof of efq axiom: `∅ ⊢ₛ {⊥ → φ}`. -/
def lkAxiomEfq (φ : Proposition Atom) :
    LKProof (∅ ⊢ₛ ({Proposition.bot.imp φ} : Finset _)) :=
  LKProof.impR Proposition.bot φ (Finset.mem_singleton_self _) <|
    LKProof.botL _ _ (Finset.mem_insert_self _ _)

/-- LK proof of Peirce's law: `∅ ⊢ₛ {((φ → ψ) → φ) → φ}`. -/
def lkAxiomPeirce (φ ψ : Proposition Atom) :
    LKProof (∅ ⊢ₛ ({((φ.imp ψ).imp φ).imp φ} : Finset _)) := by
  apply LKProof.impR ((φ.imp ψ).imp φ) φ (Finset.mem_singleton_self _)
  -- Now: {(φ→ψ)→φ} ⊢ₛ {φ, ((φ→ψ)→φ)→φ}
  -- impL (φ→ψ)→φ: need Γ ⊢ₛ insert (φ→ψ) Δ and insert φ Γ ⊢ₛ Δ
  apply LKProof.impL (φ.imp ψ) φ (Finset.mem_insert_self _ _)
  · -- {(φ→ψ)→φ} ⊢ₛ {φ→ψ, φ, ((φ→ψ)→φ)→φ}
    -- impR φ ψ: introduce φ on left, ψ in succedent
    apply LKProof.impR φ ψ (Finset.mem_insert_self _ _)
    -- {φ, (φ→ψ)→φ} ⊢ₛ {ψ, φ→ψ, φ, ((φ→ψ)→φ)→φ}; ax φ
    exact LKProof.ax φ _ _ (Finset.mem_insert_self _ _) (Finset.mem_insert_of_mem
      (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)))
  · -- {φ, (φ→ψ)→φ} ⊢ₛ {φ, ...}: ax φ
    exact LKProof.ax φ _ _ (Finset.mem_insert_self _ _) (Finset.mem_insert_self _ _)

/-- LK proof of andI axiom: `∅ ⊢ₛ {φ → ψ → φ ∧ ψ}`. -/
def lkAxiomAndI (φ ψ : Proposition Atom) :
    LKProof (∅ ⊢ₛ ({φ.imp (ψ.imp (φ.and ψ))} : Finset _)) := by
  apply LKProof.impR φ (ψ.imp (φ.and ψ)) (Finset.mem_singleton_self _)
  apply LKProof.impR ψ (φ.and ψ) (Finset.mem_insert_self _ _)
  -- Now: {ψ, φ} ⊢ₛ {φ∧ψ, ψ→φ∧ψ, φ→ψ→φ∧ψ}
  -- andR: (φ∧ψ) ∈ succedent; need same Γ ⊢ₛ insert φ Δ and Γ ⊢ₛ insert ψ Δ
  apply LKProof.andR φ ψ (Finset.mem_insert_self _ _)
  · -- Γ ⊢ₛ insert φ {φ∧ψ, ψ→φ∧ψ, φ→ψ→φ∧ψ}: ax φ
    exact LKProof.ax φ _ _ (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
      (Finset.mem_insert_self _ _)
  · -- Γ ⊢ₛ insert ψ {φ∧ψ, ψ→φ∧ψ, φ→ψ→φ∧ψ}: ax ψ
    exact LKProof.ax ψ _ _ (Finset.mem_insert_self _ _) (Finset.mem_insert_self _ _)

/-- LK proof of andE1 axiom: `∅ ⊢ₛ {φ ∧ ψ → φ}`. -/
def lkAxiomAndE1 (φ ψ : Proposition Atom) :
    LKProof (∅ ⊢ₛ ({(φ.and ψ).imp φ} : Finset _)) := by
  apply LKProof.impR (φ.and ψ) φ (Finset.mem_singleton_self _)
  -- {φ∧ψ} ⊢ₛ {φ, (φ∧ψ)→φ}; andL: (φ∧ψ) ∈ antecedent
  apply LKProof.andL φ ψ (Finset.mem_insert_self _ _)
  -- {φ, ψ, φ∧ψ} ⊢ₛ {φ, (φ∧ψ)→φ}: ax φ
  exact LKProof.ax φ _ _ (Finset.mem_insert_self _ _) (Finset.mem_insert_self _ _)

/-- LK proof of andE2 axiom: `∅ ⊢ₛ {φ ∧ ψ → ψ}`. -/
def lkAxiomAndE2 (φ ψ : Proposition Atom) :
    LKProof (∅ ⊢ₛ ({(φ.and ψ).imp ψ} : Finset _)) := by
  apply LKProof.impR (φ.and ψ) ψ (Finset.mem_singleton_self _)
  apply LKProof.andL φ ψ (Finset.mem_insert_self _ _)
  exact LKProof.ax ψ _ _ (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
    (Finset.mem_insert_self _ _)

/-- LK proof of orI1 axiom: `∅ ⊢ₛ {φ → φ ∨ ψ}`. -/
def lkAxiomOrI1 (φ ψ : Proposition Atom) :
    LKProof (∅ ⊢ₛ ({φ.imp (φ.or ψ)} : Finset _)) := by
  apply LKProof.impR φ (φ.or ψ) (Finset.mem_singleton_self _)
  -- {φ} ⊢ₛ {φ∨ψ, φ→φ∨ψ}; orR: (φ∨ψ) ∈ succedent
  -- orR needs Γ ⊢ₛ insert φ (insert ψ Δ)
  apply LKProof.orR φ ψ (Finset.mem_insert_self _ _)
  -- {φ} ⊢ₛ {φ, ψ, φ∨ψ, φ→φ∨ψ}: ax φ
  exact LKProof.ax φ _ _ (Finset.mem_insert_self _ _) (Finset.mem_insert_self _ _)

/-- LK proof of orI2 axiom: `∅ ⊢ₛ {ψ → φ ∨ ψ}`. -/
def lkAxiomOrI2 (φ ψ : Proposition Atom) :
    LKProof (∅ ⊢ₛ ({ψ.imp (φ.or ψ)} : Finset _)) := by
  apply LKProof.impR ψ (φ.or ψ) (Finset.mem_singleton_self _)
  apply LKProof.orR φ ψ (Finset.mem_insert_self _ _)
  exact LKProof.ax ψ _ _ (Finset.mem_insert_self _ _)
    (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))

/-- LK proof of orE axiom: `∅ ⊢ₛ {(φ → χ) → (ψ → χ) → (φ ∨ ψ) → χ}`. -/
def lkAxiomOrE (φ ψ χ : Proposition Atom) :
    LKProof (∅ ⊢ₛ ({(φ.imp χ).imp ((ψ.imp χ).imp ((φ.or ψ).imp χ))} : Finset _)) := by
  apply LKProof.impR (φ.imp χ) ((ψ.imp χ).imp ((φ.or ψ).imp χ)) (Finset.mem_singleton_self _)
  apply LKProof.impR (ψ.imp χ) ((φ.or ψ).imp χ) (Finset.mem_insert_self _ _)
  apply LKProof.impR (φ.or ψ) χ (Finset.mem_insert_self _ _)
  -- Now: {φ∨ψ, ψ→χ, φ→χ} ⊢ₛ {χ, ...}
  -- orL on (φ∨ψ): need insert φ Γ ⊢ₛ Δ and insert ψ Γ ⊢ₛ Δ
  apply LKProof.orL φ ψ (Finset.mem_insert_self _ _)
  · -- {φ, φ∨ψ, ψ→χ, φ→χ} ⊢ₛ {χ,...}: impL on φ→χ
    apply LKProof.impL φ χ (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
      (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))))
    · exact LKProof.ax φ _ _ (Finset.mem_insert_self _ _) (Finset.mem_insert_self _ _)
    · exact LKProof.ax χ _ _ (Finset.mem_insert_self _ _) (Finset.mem_insert_self _ _)
  · -- {ψ, φ∨ψ, ψ→χ, φ→χ} ⊢ₛ {χ,...}: impL on ψ→χ
    apply LKProof.impL ψ χ (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
      (Finset.mem_insert_self _ _)))
    · exact LKProof.ax ψ _ _ (Finset.mem_insert_self _ _) (Finset.mem_insert_self _ _)
    · exact LKProof.ax χ _ _ (Finset.mem_insert_self _ _) (Finset.mem_insert_self _ _)

/-- Dispatch on `PropositionalAxiom` to produce a nonempty LK proof of `Γ ⊢ₛ {axiom}`.
Uses `Nonempty` since `PropositionalAxiom` is `Prop`-valued and cannot eliminate into `Type`. -/
theorem lkOfPropAxiom {Γ : Finset (Proposition Atom)}
    {φ : Proposition Atom} (h : PropositionalAxiom φ) :
    Nonempty (LKProof (Γ ⊢ₛ ({φ} : Finset _))) := by
  cases h with
  | implyK a b => exact ⟨(lkAxiomImplyK a b).mono (Finset.empty_subset _) Finset.Subset.rfl⟩
  | implyS a b c =>
    exact ⟨(lkAxiomImplyS a b c).mono (Finset.empty_subset _) Finset.Subset.rfl⟩
  | efq a => exact ⟨(lkAxiomEfq a).mono (Finset.empty_subset _) Finset.Subset.rfl⟩
  | peirce a b =>
    exact ⟨(lkAxiomPeirce a b).mono (Finset.empty_subset _) Finset.Subset.rfl⟩
  | andI a b => exact ⟨(lkAxiomAndI a b).mono (Finset.empty_subset _) Finset.Subset.rfl⟩
  | andE1 a b => exact ⟨(lkAxiomAndE1 a b).mono (Finset.empty_subset _) Finset.Subset.rfl⟩
  | andE2 a b => exact ⟨(lkAxiomAndE2 a b).mono (Finset.empty_subset _) Finset.Subset.rfl⟩
  | orI1 a b => exact ⟨(lkAxiomOrI1 a b).mono (Finset.empty_subset _) Finset.Subset.rfl⟩
  | orI2 a b => exact ⟨(lkAxiomOrI2 a b).mono (Finset.empty_subset _) Finset.Subset.rfl⟩
  | orE a b c =>
    exact ⟨(lkAxiomOrE a b c).mono (Finset.empty_subset _) Finset.Subset.rfl⟩

/-! ## ND to LK Translation -/

/-- Translate an ND derivation under `AxiomTheory PropositionalAxiom` into an LK proof
of the single-conclusion sequent `Γ ⊢ₛ {A}`.

Proof by structural induction on the `Theory.Derivation` constructor.
Noncomputable because `PropositionalAxiom` is `Prop`-valued, requiring
`Classical.choice` in the axiom case. -/
noncomputable def ndToLK {Γ : Finset (Proposition Atom)} {A : Proposition Atom} :
    (AxiomTheory (@PropositionalAxiom Atom) : Theory Atom).Derivation Γ A →
    LKProof (Γ ⊢ₛ ({A} : Finset _))
  | .ax h_mem => by
    simp only [AxiomTheory, Set.mem_setOf_eq] at h_mem
    exact Classical.choice (lkOfPropAxiom h_mem)
  | .ass h_mem =>
    -- A ∈ Γ; ax with singleton succedent
    LKProof.ax A Γ {A} h_mem (Finset.mem_singleton_self _)
  | @Derivation.andI _ _ _ B C G d₁ d₂ => by
    apply LKProof.andR B C (Finset.mem_singleton_self _)
    · exact (ndToLK d₁).mono Finset.Subset.rfl (by
        intro x hx; simp only [Finset.mem_singleton] at hx; subst hx
        exact Finset.mem_insert_self _ _)
    · exact (ndToLK d₂).mono Finset.Subset.rfl (by
        intro x hx; simp only [Finset.mem_singleton] at hx; subst hx
        exact Finset.mem_insert_self _ _)
  | @Derivation.andE1 _ _ _ B C G d => by
    apply LKProof.cut (B.and C)
    · exact (ndToLK d).mono Finset.Subset.rfl (by
        intro x hx; simp only [Finset.mem_singleton] at hx; subst hx
        exact Finset.mem_insert_self _ _)
    · exact LKProof.andL B C (Finset.mem_insert_self _ _)
        (LKProof.ax B _ _ (Finset.mem_insert_self _ _) (Finset.mem_singleton_self _))
  | @Derivation.andE2 _ _ _ B C G d => by
    apply LKProof.cut (B.and C)
    · exact (ndToLK d).mono Finset.Subset.rfl (by
        intro x hx; simp only [Finset.mem_singleton] at hx; subst hx
        exact Finset.mem_insert_self _ _)
    · exact LKProof.andL B C (Finset.mem_insert_self _ _)
        (LKProof.ax C _ _ (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
          (Finset.mem_singleton_self _))
  | @Derivation.orI1 _ _ _ B C G d => by
    apply LKProof.orR B C (Finset.mem_singleton_self _)
    exact (ndToLK d).mono Finset.Subset.rfl (by
      intro x hx; simp only [Finset.mem_singleton] at hx; subst hx
      exact Finset.mem_insert_self _ _)
  | @Derivation.orI2 _ _ _ B C G d => by
    apply LKProof.orR B C (Finset.mem_singleton_self _)
    exact (ndToLK d).mono Finset.Subset.rfl (by
      intro x hx; simp only [Finset.mem_singleton] at hx; subst hx
      exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
  | @Derivation.orE _ _ _ B C E G d dB dC => by
    apply LKProof.cut (B.or C)
    · exact (ndToLK d).mono Finset.Subset.rfl (by
        intro x hx; simp only [Finset.mem_singleton] at hx; subst hx
        exact Finset.mem_insert_self _ _)
    · exact LKProof.orL B C (Finset.mem_insert_self _ _)
        ((ndToLK dB).mono (Finset.insert_subset_insert _ (Finset.subset_insert _ _))
          Finset.Subset.rfl)
        ((ndToLK dC).mono (Finset.insert_subset_insert _ (Finset.subset_insert _ _))
          Finset.Subset.rfl)
  | @Derivation.impI _ _ _ B C Γ' d => by
    apply LKProof.impR B C (Finset.mem_singleton_self _)
    exact (ndToLK d).mono Finset.Subset.rfl (by
      intro x hx; simp only [Finset.mem_singleton] at hx; subst hx
      exact Finset.mem_insert_self _ _)
  | @Derivation.impE _ _ _ _ B C d₁ d₂ => by
    apply LKProof.cut (B.imp C)
    · exact (ndToLK d₁).mono Finset.Subset.rfl (by
        intro x hx; simp only [Finset.mem_singleton] at hx; subst hx
        exact Finset.mem_insert_self _ _)
    · exact LKProof.impL B C (Finset.mem_insert_self _ _)
        ((ndToLK d₂).mono (Finset.subset_insert _ _) (by
          intro x hx; simp only [Finset.mem_singleton] at hx; subst hx
          exact Finset.mem_insert_self _ _))
        (LKProof.ax C _ _ (Finset.mem_insert_self _ _) (Finset.mem_singleton_self _))
  | @Derivation.efq _ _ _ _ _ _ d => by
    -- efq: Γ ⊢ ⊥; want Γ ⊢ₛ {A} via cut on ⊥ then left falsum.
    apply LKProof.cut ⊥
    · exact (ndToLK d).mono Finset.Subset.rfl (by
        intro x hx; simp only [Finset.mem_singleton] at hx; subst hx
        exact Finset.mem_insert_self _ _)
    · exact LKProof.botL _ _ (Finset.mem_insert_self _ _)

/-! ## ND–LK Equivalence -/

/-- **ND–LK Bridge**: ND derivability under `AxiomTheory PropositionalAxiom`
from context `Γ` of formula `A` is equivalent to the existence of an LK proof of `Γ ⊢ₛ {A}`.

**Forward**: By `ndToLK`, translating the ND derivation structure to LK rules.

**Backward**: By semantics: an LK proof witnesses `(Γ ⊢ₛ {A}).valid`
(by `LKProof.sound`), which states that every valuation satisfying `Γ` satisfies `A`.
This is `SemanticEntails ↑Γ A`, so `prop_strong_completeness` gives
`SetDerivable PropositionalAxiom ↑Γ A`, and `hilbert_iff_nd_ctx` converts this
to ND derivability. -/
theorem nd_iff_lk {Γ : Finset (Proposition Atom)} {A : Proposition Atom} :
    DerivableIn (AxiomTheory (@PropositionalAxiom Atom) : Theory Atom) (Γ ⊢ A) ↔
    Nonempty (LKProof (Γ ⊢ₛ ({A} : Finset _))) := by
  constructor
  · intro ⟨d⟩
    exact ⟨ndToLK d⟩
  · intro ⟨d⟩
    -- LK soundness: (Γ ⊢ₛ {A}).valid
    have h_valid := d.sound
    -- Convert to SemanticEntails
    have h_entail : SemanticEntails (↑Γ : Set (Proposition Atom)) A := by
      intro v hv
      obtain ⟨C, hC, hCval⟩ := h_valid v (fun B hB => hv B (Finset.mem_coe.mpr hB))
      simp only [Finset.mem_singleton] at hC
      exact hC ▸ hCval
    -- Strong completeness: SemanticEntails → SetDerivable
    obtain ⟨L, hL_sub, hL_deriv⟩ := prop_strong_completeness h_entail
    obtain ⟨dtree⟩ := hL_deriv
    -- Convert from SetDerivable (List-based) to DerivableIn (Finset-based)
    rw [← hilbert_iff_nd_ctx_cl]
    exact ⟨DerivationTree.weakening L Γ.toList A dtree
      (fun x hx => Finset.mem_toList.mpr (Finset.mem_coe.mp (hL_sub x hx)))⟩

/-! ## Hilbert–LK Bridge -/

/-- **Hilbert–LK Bridge**: Hilbert derivability from context `Γ.toList` is equivalent
to the existence of an LK proof of `Γ ⊢ₛ {φ}`.

Obtained by composing `hilbert_iff_nd_ctx_cl` with `nd_iff_lk`. -/
theorem hilbert_iff_lk {Γ : Finset (Proposition Atom)} {φ : Proposition Atom} :
    Deriv PropositionalAxiom Γ.toList φ ↔
    Nonempty (LKProof (Γ ⊢ₛ ({φ} : Finset _))) :=
  hilbert_iff_nd_ctx_cl.trans nd_iff_lk

/-! ## Completeness Corollaries -/

/-- **LK Completeness**: Every tautology has an LK proof from the empty context.

Proof: `prop_completeness_iff_tautology` gives Hilbert derivability, and
`hilbert_iff_lk` converts to LK provability. -/
theorem lk_completeness {φ : Proposition Atom} (h : Tautology φ) :
    Nonempty (LKProof (∅ ⊢ₛ ({φ} : Finset _))) := by
  rw [← hilbert_iff_lk]
  simp only [Finset.toList_empty]
  exact prop_completeness_iff_tautology.mp h

/-- **LK Soundness and Completeness**: A formula is a tautology if and only if
it has an LK proof from the empty context.

Forward direction: `lk_completeness`. Backward direction: `lk_sound` composed with
semantic unfolding. -/
theorem lk_iff_tautology {φ : Proposition Atom} :
    Tautology φ ↔ Nonempty (LKProof (∅ ⊢ₛ ({φ} : Finset _))) := by
  constructor
  · exact lk_completeness
  · intro ⟨d⟩ v
    have h_valid := d.sound
    obtain ⟨C, hC, hCval⟩ := h_valid v (fun _ h => by simp at h)
    simp only [Finset.mem_singleton] at hC
    exact hC ▸ hCval

end Cslib.Logic.PL
