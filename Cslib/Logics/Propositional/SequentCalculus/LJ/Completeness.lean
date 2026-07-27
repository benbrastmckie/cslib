/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

import Cslib.Init
public import Cslib.Logics.Propositional.SequentCalculus.LJ.Soundness
public import Cslib.Logics.Propositional.NaturalDeduction.Equivalence
public import Cslib.Logics.Propositional.Metalogic.IntStrongCompleteness

/-! # Completeness of LJ for Intuitionistic Propositional Logic

This module proves that LJ is complete for intuitionistic propositional logic by:
1. Translating ND derivations to LJ proofs (`ndToLJ`), establishing the forward direction
   of the ND–LJ bridge.
2. Using LJ soundness plus Kripke completeness for the backward direction.
3. Composing with the existing Hilbert–ND bridge (`hilbert_iff_nd_ctx_int`) to yield
   `hilbert_iff_lj`.
4. Deriving `lj_iff_ivalid` as a corollary.

## Main Results

- `ndToLJ`: Every ND derivation of `Γ ⊢ A` translates to an LJ proof of `Γ ⊢ A`.
- `nd_iff_lj`: `DerivableIn (AxiomTheory IntPropAxiom) (Γ ⊢ A) ↔ Nonempty (LJProof (Γ ⊢ A))`.
- `hilbert_iff_lj`: Hilbert derivability from `Γ.toList` ↔ LJ provability of `Γ ⊢ φ`.
- `lj_iff_ivalid`: `IValid φ ↔ Nonempty (LJProof (∅ ⊢ φ))`.

## Strategy

**Forward (`ndToLJ`)**: Structural induction on `Theory.Derivation`.
- `ax h_mem`: Each `IntPropAxiom` constructor translates to an LJ proof of the
  corresponding sequent `∅ ⊢ axiom`, then weakened via `LJProof.mono`.
- `ass h_mem`: The assumption rule maps to `SeqProof.ax` directly.
- Logical rules map to the corresponding LJ rules.

**Backward (`nd_iff_lj` ← direction)**: Via Kripke semantics.
- An LJ proof of `Γ ⊢ A` witnesses `LJProof.sound`, giving Kripke forcing for all models.
- This is exactly `ISemanticEntails ↑Γ A`.
- By `int_strong_completeness`, `SetDerivable IntPropAxiom ↑Γ A`.
- By the Hilbert–ND bridge, `DerivableIn (AxiomTheory IntPropAxiom) (Γ ⊢ A)`.

## References

* [S. Negri, J. von Plato, *Structural Proof Theory*][NegriVonPlato2001], Ch. 3
* [A. S. Troelstra, H. Schwichtenberg,
  *Basic Proof Theory*][TroelstraSchwichtenberg2000], Ch. 4
* [G. Gentzen,
  *Untersuchungen über das logische Schließen*][Gentzen1935]
-/

@[expose] public section

universe u

namespace Cslib.Logic.PL

open Proposition Theory Finset InferenceSystem

variable {Atom : Type u} [DecidableEq Atom]

/-! ## LJ Proofs of IntPropAxiom Schemata

Each `IntPropAxiom` is provable in LJ from the empty antecedent. Since LJ has a
single-conclusion succedent, there are no succedent membership proofs required —
the conclusion is simply the formula being proved. -/

/-- LJ proof of implyK axiom: `∅ ⊢ φ → (ψ → φ)`. -/
def ljAxiomImplyK (φ ψ : Proposition Atom) :
    LJProof (∅ ⊢ φ.imp (ψ.imp φ)) :=
  SeqProof.impR φ (ψ.imp φ) <|
    SeqProof.impR ψ φ <|
      SeqProof.ax φ _ (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))

/-- LJ proof of implyS axiom: `∅ ⊢ (φ → ψ → χ) → (φ → ψ) → φ → χ`. -/
def ljAxiomImplyS (φ ψ χ : Proposition Atom) :
    LJProof (∅ ⊢ (φ.imp (ψ.imp χ)).imp ((φ.imp ψ).imp (φ.imp χ))) := by
  apply SeqProof.impR (φ.imp (ψ.imp χ)) ((φ.imp ψ).imp (φ.imp χ))
  apply SeqProof.impR (φ.imp ψ) (φ.imp χ)
  apply SeqProof.impR φ χ
  -- Context: {φ, φ→ψ, φ→ψ→χ} (with possible extras from impR insertions)
  -- Apply impL on (φ→ψ→χ): it's in the context
  apply SeqProof.impL φ (ψ.imp χ)
    (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)))
  · -- Need to prove φ
    exact SeqProof.ax φ _ (Finset.mem_insert_self _ _)
  · -- Now have ψ→χ in context, and φ→ψ and φ
    -- Apply impL on (φ→ψ) to get ψ
    apply SeqProof.impL φ ψ
      (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)))
    · exact SeqProof.ax φ _ (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
    · -- Context now has {ψ, ψ→χ, φ→ψ, φ→ψ→χ, φ}
      -- Apply impL on (ψ→χ) to get χ
      apply SeqProof.impL ψ χ (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
      · exact SeqProof.ax ψ _ (Finset.mem_insert_self _ _)
      · exact SeqProof.ax χ _ (Finset.mem_insert_self _ _)

/-- LJ proof of efq axiom: `∅ ⊢ ⊥ → φ`. -/
def ljAxiomEfq (φ : Proposition Atom) :
    LJProof (∅ ⊢ Proposition.bot.imp φ) :=
  SeqProof.impR Proposition.bot φ <|
    SeqProof.botL _ φ (Finset.mem_insert_self _ _)

/-- LJ proof of andI axiom: `∅ ⊢ φ → ψ → φ ∧ ψ`. -/
def ljAxiomAndI (φ ψ : Proposition Atom) :
    LJProof (∅ ⊢ φ.imp (ψ.imp (φ.and ψ))) := by
  apply SeqProof.impR φ (ψ.imp (φ.and ψ))
  apply SeqProof.impR ψ (φ.and ψ)
  -- Context: {ψ, φ} ⊢ φ ∧ ψ
  apply SeqProof.andR φ ψ
  · exact SeqProof.ax φ _ (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
  · exact SeqProof.ax ψ _ (Finset.mem_insert_self _ _)

/-- LJ proof of andE1 axiom: `∅ ⊢ φ ∧ ψ → φ`. -/
def ljAxiomAndE1 (φ ψ : Proposition Atom) :
    LJProof (∅ ⊢ (φ.and ψ).imp φ) := by
  apply SeqProof.impR (φ.and ψ) φ
  -- Context: {φ∧ψ} ⊢ φ
  apply SeqProof.andL φ ψ (Finset.mem_insert_self _ _)
  -- Context: {φ, ψ, φ∧ψ} ⊢ φ
  exact SeqProof.ax φ _ (Finset.mem_insert_self _ _)

/-- LJ proof of andE2 axiom: `∅ ⊢ φ ∧ ψ → ψ`. -/
def ljAxiomAndE2 (φ ψ : Proposition Atom) :
    LJProof (∅ ⊢ (φ.and ψ).imp ψ) := by
  apply SeqProof.impR (φ.and ψ) ψ
  apply SeqProof.andL φ ψ (Finset.mem_insert_self _ _)
  exact SeqProof.ax ψ _ (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))

/-- LJ proof of orI1 axiom: `∅ ⊢ φ → φ ∨ ψ`. -/
def ljAxiomOrI1 (φ ψ : Proposition Atom) :
    LJProof (∅ ⊢ φ.imp (φ.or ψ)) :=
  SeqProof.impR φ (φ.or ψ) <|
    SeqProof.orR1 φ ψ <|
      SeqProof.ax φ _ (Finset.mem_insert_self _ _)

/-- LJ proof of orI2 axiom: `∅ ⊢ ψ → φ ∨ ψ`. -/
def ljAxiomOrI2 (φ ψ : Proposition Atom) :
    LJProof (∅ ⊢ ψ.imp (φ.or ψ)) :=
  SeqProof.impR ψ (φ.or ψ) <|
    SeqProof.orR2 φ ψ <|
      SeqProof.ax ψ _ (Finset.mem_insert_self _ _)

/-- LJ proof of orE axiom: `∅ ⊢ (φ → χ) → (ψ → χ) → (φ ∨ ψ) → χ`. -/
def ljAxiomOrE (φ ψ χ : Proposition Atom) :
    LJProof (∅ ⊢ (φ.imp χ).imp ((ψ.imp χ).imp ((φ.or ψ).imp χ))) := by
  apply SeqProof.impR (φ.imp χ) ((ψ.imp χ).imp ((φ.or ψ).imp χ))
  apply SeqProof.impR (ψ.imp χ) ((φ.or ψ).imp χ)
  apply SeqProof.impR (φ.or ψ) χ
  -- Context: {φ∨ψ, ψ→χ, φ→χ} ⊢ χ
  -- Apply orL on (φ∨ψ)
  apply SeqProof.orL φ ψ (Finset.mem_insert_self _ _)
  · -- Left branch: {φ, φ∨ψ, ψ→χ, φ→χ} ⊢ χ
    -- Apply impL on (φ→χ)
    apply SeqProof.impL φ χ
      (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
        (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))))
    · exact SeqProof.ax φ _ (Finset.mem_insert_self _ _)
    · exact SeqProof.ax χ _ (Finset.mem_insert_self _ _)
  · -- Right branch: {ψ, φ∨ψ, ψ→χ, φ→χ} ⊢ χ
    -- Apply impL on (ψ→χ)
    apply SeqProof.impL ψ χ
      (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)))
    · exact SeqProof.ax ψ _ (Finset.mem_insert_self _ _)
    · exact SeqProof.ax χ _ (Finset.mem_insert_self _ _)

/-- Dispatch on `IntPropAxiom` to produce a nonempty LJ proof of `Γ ⊢ axiom`.
Uses `Nonempty` since `IntPropAxiom` is `Prop`-valued and cannot eliminate into `Type`. -/
theorem ljOfIntAxiom {Γ : Ctx Atom}
    {φ : Proposition Atom} (h : IntPropAxiom φ) :
    Nonempty (LJProof (Γ ⊢ φ)) := by
  cases h with
  | implyK a b => exact ⟨(ljAxiomImplyK a b).mono (Finset.empty_subset _)⟩
  | implyS a b c => exact ⟨(ljAxiomImplyS a b c).mono (Finset.empty_subset _)⟩
  | efq a => exact ⟨(ljAxiomEfq a).mono (Finset.empty_subset _)⟩
  | andI a b => exact ⟨(ljAxiomAndI a b).mono (Finset.empty_subset _)⟩
  | andE1 a b => exact ⟨(ljAxiomAndE1 a b).mono (Finset.empty_subset _)⟩
  | andE2 a b => exact ⟨(ljAxiomAndE2 a b).mono (Finset.empty_subset _)⟩
  | orI1 a b => exact ⟨(ljAxiomOrI1 a b).mono (Finset.empty_subset _)⟩
  | orI2 a b => exact ⟨(ljAxiomOrI2 a b).mono (Finset.empty_subset _)⟩
  | orE a b c => exact ⟨(ljAxiomOrE a b c).mono (Finset.empty_subset _)⟩

/-! ## ND to LJ Translation -/

/-- Translate an ND derivation under `AxiomTheory IntPropAxiom` into an LJ proof
of the single-conclusion sequent `Γ ⊢ A`.

Proof by structural induction on the `Theory.Derivation` constructor.
Noncomputable because `IntPropAxiom` is `Prop`-valued, requiring
`Classical.choice` in the axiom case. -/
noncomputable def ndToLJ {Γ : Ctx Atom} {A : Proposition Atom} :
    (AxiomTheory (@IntPropAxiom Atom) : Theory Atom).Derivation Γ A →
    LJProof (Γ ⊢ A)
  | .ax h_mem => by
    simp only [AxiomTheory, Set.mem_setOf_eq] at h_mem
    exact Classical.choice (ljOfIntAxiom h_mem)
  | .ass h_mem =>
    SeqProof.ax A Γ h_mem
  | @Derivation.andI _ _ _ B C G d₁ d₂ =>
    SeqProof.andR B C (ndToLJ d₁) (ndToLJ d₂)
  | @Derivation.andE1 _ _ _ B C G d => by
    -- Have: G ⊢ B ∧ C; want G ⊢ B
    apply SeqProof.cut (B.and C)
    · exact ndToLJ d
    · exact SeqProof.andL B C (Finset.mem_insert_self _ _)
        (SeqProof.ax B _ (Finset.mem_insert_self _ _))
  | @Derivation.andE2 _ _ _ B C G d => by
    -- Have: G ⊢ B ∧ C; want G ⊢ C
    apply SeqProof.cut (B.and C)
    · exact ndToLJ d
    · exact SeqProof.andL B C (Finset.mem_insert_self _ _)
        (SeqProof.ax C _ (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)))
  | @Derivation.orI1 _ _ _ B C G d =>
    SeqProof.orR1 B C (ndToLJ d)
  | @Derivation.orI2 _ _ _ B C G d =>
    SeqProof.orR2 B C (ndToLJ d)
  | @Derivation.orE _ _ _ B C E G d dB dC => by
    -- Have: G ⊢ B ∨ C, insert B G ⊢ E, insert C G ⊢ E; want G ⊢ E
    apply SeqProof.cut (B.or C)
    · exact ndToLJ d
    · exact SeqProof.orL B C (Finset.mem_insert_self _ _)
        ((ndToLJ dB).mono (Finset.insert_subset_insert _ (Finset.subset_insert _ _)))
        ((ndToLJ dC).mono (Finset.insert_subset_insert _ (Finset.subset_insert _ _)))
  | @Derivation.impI _ _ _ B C Γ' d =>
    SeqProof.impR B C (ndToLJ d)
  | @Derivation.impE _ _ _ _ B C d₁ d₂ => by
    -- Have: Γ ⊢ B → C and Γ ⊢ B; want Γ ⊢ C
    apply SeqProof.cut (B.imp C)
    · exact ndToLJ d₁
    · exact SeqProof.impL B C (Finset.mem_insert_self _ _)
        ((ndToLJ d₂).mono (Finset.subset_insert _ _))
        (SeqProof.ax C _ (Finset.mem_insert_self _ _))
  | @Derivation.efq _ _ _ _ _ _ d => by
    -- efq: Γ ⊢ ⊥ (intuitionistic theory); want Γ ⊢ A via cut on ⊥ then left falsum.
    apply SeqProof.cut ⊥
    · exact ndToLJ d
    · exact SeqProof.botL _ _ (Finset.mem_insert_self _ _)

/-! ## ND–LJ Equivalence -/

/-- **ND–LJ Bridge**: ND derivability under `AxiomTheory IntPropAxiom`
from context `Γ` of formula `A` is equivalent to the existence of an LJ proof of `Γ ⊢ A`.

**Forward**: By `ndToLJ`, translating the ND derivation structure to LJ rules.

**Backward**: By Kripke semantics: an LJ proof of `Γ ⊢ A` witnesses
`LJProof.sound`, which states that every Kripke model world forcing `Γ` also forces `A`.
This is `ISemanticEntails ↑Γ A`, so `int_strong_completeness` gives
`SetDerivable IntPropAxiom ↑Γ A`, and `hilbert_iff_nd_ctx_int` converts this
to ND derivability. -/
theorem nd_iff_lj {Γ : Ctx Atom} {A : Proposition Atom} :
    DerivableIn (AxiomTheory (@IntPropAxiom Atom) : Theory Atom) (Γ ⊢ A) ↔
    Nonempty (LJProof (Γ ⊢ A)) := by
  constructor
  · intro ⟨d⟩
    exact ⟨ndToLJ d⟩
  · intro ⟨d⟩
    -- LJ soundness: the proof establishes Kripke entailment
    have h_entail : ISemanticEntails (↑Γ : Set (Proposition Atom)) A := by
      intro World _ val v_uc w hant
      exact d.sound val v_uc w (fun B hB => hant B (Finset.mem_coe.mpr hB))
    -- Strong completeness: ISemanticEntails → SetDerivable
    obtain ⟨L, hL_sub, hL_deriv⟩ := int_strong_completeness h_entail
    obtain ⟨dtree⟩ := hL_deriv
    -- Convert from SetDerivable (List-based) to DerivableIn (Finset-based)
    rw [← hilbert_iff_nd_ctx_int]
    exact ⟨DerivationTree.weakening L Γ.toList A dtree
      (fun x hx => Finset.mem_toList.mpr (Finset.mem_coe.mp (hL_sub x hx)))⟩

/-! ## Hilbert–LJ Bridge -/

/-- **Hilbert–LJ Bridge**: Hilbert derivability from context `Γ.toList` is equivalent
to the existence of an LJ proof of `Γ ⊢ φ`.

Obtained by composing `hilbert_iff_nd_ctx_int` with `nd_iff_lj`. -/
theorem hilbert_iff_lj {Γ : Ctx Atom} {φ : Proposition Atom} :
    Deriv IntPropAxiom Γ.toList φ ↔ Nonempty (LJProof (Γ ⊢ φ)) :=
  hilbert_iff_nd_ctx_int.trans nd_iff_lj

/-! ## Soundness and Completeness Corollary -/

/-- **LJ Soundness and Completeness**: A formula is intuitionistically valid if and only if
it has an LJ proof from the empty context.

Forward direction: by `int_strong_completeness` (Kripke) and `hilbert_iff_lj`.
Backward direction: by `LJProof.sound` applied to all Kripke models. -/
theorem lj_iff_ivalid {φ : Proposition Atom} :
    IValid.{u, u} φ ↔ Nonempty (LJProof (∅ ⊢ φ)) := by
  constructor
  · intro h_valid
    -- h_valid : IValid.{u, u} φ — forced at every world of every Kripke model
    -- Use int_strong_completeness with ISemanticEntails ∅ φ
    have h_entail : ISemanticEntails (∅ : Set (Proposition Atom)) φ :=
      fun World _ val v_uc w _ => h_valid World val v_uc w
    obtain ⟨L, hL_sub, hL_deriv⟩ := int_strong_completeness h_entail
    obtain ⟨dtree⟩ := hL_deriv
    -- L ⊆ ∅ so L = []
    have hL_nil : L = [] := by
      by_contra hne
      obtain ⟨a, ha⟩ := List.exists_mem_of_ne_nil L hne
      exact absurd (hL_sub a ha) (fun h => h)
    subst hL_nil
    rw [← hilbert_iff_lj]
    simp only [Finset.toList_empty]
    exact ⟨dtree⟩
  · intro ⟨d⟩ World _ val v_uc w
    exact d.sound val v_uc w (fun _ h => by simp at h)

end Cslib.Logic.PL
