/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

import Cslib.Init
public import Cslib.Logics.Propositional.SequentCalculus.LM.Soundness
public import Cslib.Logics.Propositional.NaturalDeduction.Equivalence
public import Cslib.Logics.Propositional.Metalogic.MinStrongCompleteness

/-! # Completeness of LM for Minimal Propositional Logic

This module proves that LM is complete for minimal propositional logic by:
1. Translating ND derivations to LM proofs (`ndToLM`), establishing the forward direction
   of the ND–LM bridge.
2. Using LM soundness plus Kripke completeness for the backward direction.
3. Composing with the existing Hilbert–ND bridge (`hilbert_iff_nd_ctx_min`) to yield
   `hilbert_iff_lm`.
4. Deriving `lm_iff_mvalid` as a corollary.

## Main Results

- `ndToLM`: Every ND derivation of `Γ ⊢ A` (under `AxiomTheory MinPropAxiom`) translates to an
  LM proof of `Γ ⊢ A`.
- `nd_iff_lm`: `DerivableIn (AxiomTheory MinPropAxiom) (Γ ⊢ A) ↔
  Nonempty (SeqProofMinimal (Γ ⊢ A))`.
- `hilbert_iff_lm`: Hilbert derivability from `Γ.toList` ↔ LM provability of `Γ ⊢ φ`.
- `lm_iff_mvalid`: `MValid φ ↔ Nonempty (SeqProofMinimal (∅ ⊢ φ))`.

## Strategy

**Forward (`ndToLM`)**: Structural induction on `Theory.Derivation`.
- `ax h_mem`: Each `MinPropAxiom` constructor translates to an LM proof of the
  corresponding sequent `∅ ⊢ axiom`, then weakened via `SeqProof.mono`.
- `ass h_mem`: The assumption rule maps to `SeqProof.ax` directly.
- Logical rules map to the corresponding LM rules.
- `efq`: unconstructible, since `AxiomTheory MinPropAxiom` admits no `IsIntuitionistic`
  instance (mirroring `not_isIntuitionistic_mpl`); discharged via `absurd`.

**Backward (`nd_iff_lm` ← direction)**: Via Kripke semantics.
- An LM proof of `Γ ⊢ A` witnesses `SeqProofMinimal.sound`, giving minimal Kripke forcing for
  all models, i.e. `MSemanticEntails ↑Γ A`.
- By `min_strong_completeness`, `SetDerivable MinPropAxiom ↑Γ A`.
- By the Hilbert–ND bridge, `DerivableIn (AxiomTheory MinPropAxiom) (Γ ⊢ A)`.

Unlike LJ, no `ljAxiomEfq` schema exists here (`MinPropAxiom` has no `efq` constructor), and the
`efq` case of `Theory.Derivation` is unconstructible at `AxiomTheory MinPropAxiom`, so the ND→LM
translation never needs the gated `botL` rule.

## References

* [S. Negri, J. von Plato, *Structural Proof Theory*][NegriVonPlato2001], Ch. 3
* [A. S. Troelstra, H. Schwichtenberg,
  *Basic Proof Theory*][TroelstraSchwichtenberg2000], Ch. 4
* [I. Johansson, *Der Minimalkalkül, ein reduzierter intuitionistischer Formalismus*][Johansson1937]
-/

@[expose] public section

universe u

namespace Cslib.Logic.PL

open Proposition Theory Finset InferenceSystem

variable {Atom : Type u} [DecidableEq Atom]

/-! ## LM Proofs of MinPropAxiom Schemata

Each `MinPropAxiom` is provable in LM from the empty antecedent. Since LM has a
single-conclusion succedent, there are no succedent membership proofs required —
the conclusion is simply the formula being proved. These proof trees are identical to
the corresponding `ljAxiom…` trees (LJ/Completeness.lean), since none of the 8 minimal
schemata use the gated `botL` rule. -/

/-- LM proof of implyK axiom: `∅ ⊢ φ → (ψ → φ)`. -/
def lmAxiomImplyK (φ ψ : Proposition Atom) :
    LMProof (∅ ⊢ φ.imp (ψ.imp φ)) :=
  SeqProof.impR φ (ψ.imp φ) <|
    SeqProof.impR ψ φ <|
      SeqProof.ax φ _ (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))

/-- LM proof of implyS axiom: `∅ ⊢ (φ → ψ → χ) → (φ → ψ) → φ → χ`. -/
def lmAxiomImplyS (φ ψ χ : Proposition Atom) :
    LMProof (∅ ⊢ (φ.imp (ψ.imp χ)).imp ((φ.imp ψ).imp (φ.imp χ))) := by
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

/-- LM proof of andI axiom: `∅ ⊢ φ → ψ → φ ∧ ψ`. -/
def lmAxiomAndI (φ ψ : Proposition Atom) :
    LMProof (∅ ⊢ φ.imp (ψ.imp (φ.and ψ))) := by
  apply SeqProof.impR φ (ψ.imp (φ.and ψ))
  apply SeqProof.impR ψ (φ.and ψ)
  -- Context: {ψ, φ} ⊢ φ ∧ ψ
  apply SeqProof.andR φ ψ
  · exact SeqProof.ax φ _ (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
  · exact SeqProof.ax ψ _ (Finset.mem_insert_self _ _)

/-- LM proof of andE1 axiom: `∅ ⊢ φ ∧ ψ → φ`. -/
def lmAxiomAndE1 (φ ψ : Proposition Atom) :
    LMProof (∅ ⊢ (φ.and ψ).imp φ) := by
  apply SeqProof.impR (φ.and ψ) φ
  -- Context: {φ∧ψ} ⊢ φ
  apply SeqProof.andL φ ψ (Finset.mem_insert_self _ _)
  -- Context: {φ, ψ, φ∧ψ} ⊢ φ
  exact SeqProof.ax φ _ (Finset.mem_insert_self _ _)

/-- LM proof of andE2 axiom: `∅ ⊢ φ ∧ ψ → ψ`. -/
def lmAxiomAndE2 (φ ψ : Proposition Atom) :
    LMProof (∅ ⊢ (φ.and ψ).imp ψ) := by
  apply SeqProof.impR (φ.and ψ) ψ
  apply SeqProof.andL φ ψ (Finset.mem_insert_self _ _)
  exact SeqProof.ax ψ _ (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))

/-- LM proof of orI1 axiom: `∅ ⊢ φ → φ ∨ ψ`. -/
def lmAxiomOrI1 (φ ψ : Proposition Atom) :
    LMProof (∅ ⊢ φ.imp (φ.or ψ)) :=
  SeqProof.impR φ (φ.or ψ) <|
    SeqProof.orR1 φ ψ <|
      SeqProof.ax φ _ (Finset.mem_insert_self _ _)

/-- LM proof of orI2 axiom: `∅ ⊢ ψ → φ ∨ ψ`. -/
def lmAxiomOrI2 (φ ψ : Proposition Atom) :
    LMProof (∅ ⊢ ψ.imp (φ.or ψ)) :=
  SeqProof.impR ψ (φ.or ψ) <|
    SeqProof.orR2 φ ψ <|
      SeqProof.ax ψ _ (Finset.mem_insert_self _ _)

/-- LM proof of orE axiom: `∅ ⊢ (φ → χ) → (ψ → χ) → (φ ∨ ψ) → χ`. -/
def lmAxiomOrE (φ ψ χ : Proposition Atom) :
    LMProof (∅ ⊢ (φ.imp χ).imp ((ψ.imp χ).imp ((φ.or ψ).imp χ))) := by
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

/-- Dispatch on `MinPropAxiom` to produce a nonempty LM proof of `Γ ⊢ axiom`.
Uses `Nonempty` since `MinPropAxiom` is `Prop`-valued and cannot eliminate into `Type`.
No `efq` case, unlike `ljOfIntAxiom`: `MinPropAxiom` has only 8 constructors. -/
theorem lmOfMinAxiom {Γ : Ctx Atom}
    {φ : Proposition Atom} (h : MinPropAxiom φ) :
    Nonempty (LMProof (Γ ⊢ φ)) := by
  cases h with
  | implyK a b => exact ⟨(lmAxiomImplyK a b).mono (Finset.empty_subset _)⟩
  | implyS a b c => exact ⟨(lmAxiomImplyS a b c).mono (Finset.empty_subset _)⟩
  | andI a b => exact ⟨(lmAxiomAndI a b).mono (Finset.empty_subset _)⟩
  | andE1 a b => exact ⟨(lmAxiomAndE1 a b).mono (Finset.empty_subset _)⟩
  | andE2 a b => exact ⟨(lmAxiomAndE2 a b).mono (Finset.empty_subset _)⟩
  | orI1 a b => exact ⟨(lmAxiomOrI1 a b).mono (Finset.empty_subset _)⟩
  | orI2 a b => exact ⟨(lmAxiomOrI2 a b).mono (Finset.empty_subset _)⟩
  | orE a b c => exact ⟨(lmAxiomOrE a b c).mono (Finset.empty_subset _)⟩

omit [DecidableEq Atom] in
/-- The theory `AxiomTheory MinPropAxiom` is not intuitionistic: none of the 8 `MinPropAxiom`
schemata produce the explosion formula `⊥ → A` for every `A` (each schema's conclusion has a
top-level connective other than `.bot` on its antecedent side, so `⊥.imp ⊥` is never a
`MinPropAxiom` instance). Consequently the gated `efq` constructor of `Theory.Derivation` at
`T = AxiomTheory MinPropAxiom` is structurally unconstructible, mirroring
`not_isIntuitionistic_mpl`. -/
theorem not_isIntuitionistic_axiomTheory_minPropAxiom :
    ¬ Theory.IsIntuitionistic (AxiomTheory (@MinPropAxiom Atom) : Theory Atom) := by
  intro h
  have := (Theory.isIntuitionisticIff (AxiomTheory (@MinPropAxiom Atom) : Theory Atom)).mp h
  have hmem : (⊥ → ⊥ : Proposition Atom) ∈ (Theory.IPL : Theory Atom) := ⟨⊥, rfl⟩
  have hax : MinPropAxiom (⊥ → ⊥ : Proposition Atom) := this hmem
  cases hax

/-! ## ND to LM Translation -/

/-- Translate an ND derivation under `AxiomTheory MinPropAxiom` into an LM proof
of the single-conclusion sequent `Γ ⊢ A`.

Proof by structural induction on the `Theory.Derivation` constructor.
Noncomputable because `MinPropAxiom` is `Prop`-valued, requiring
`Classical.choice` in the axiom case. Unlike `ndToLJ`, there is no `efq` case to translate:
that constructor is unconstructible at `AxiomTheory MinPropAxiom`
(`not_isIntuitionistic_axiomTheory_minPropAxiom`), discharged via `absurd`. -/
noncomputable def ndToLM {Γ : Ctx Atom} {A : Proposition Atom} :
    (AxiomTheory (@MinPropAxiom Atom) : Theory Atom).Derivation Γ A →
    LMProof (Γ ⊢ A)
  | .ax h_mem => by
    simp only [AxiomTheory, Set.mem_setOf_eq] at h_mem
    exact Classical.choice (lmOfMinAxiom h_mem)
  | .ass h_mem =>
    SeqProof.ax A Γ h_mem
  | @Derivation.andI _ _ _ B C G d₁ d₂ =>
    SeqProof.andR B C (ndToLM d₁) (ndToLM d₂)
  | @Derivation.andE1 _ _ _ B C G d => by
    -- Have: G ⊢ B ∧ C; want G ⊢ B
    apply SeqProof.cut (B.and C)
    · exact ndToLM d
    · exact SeqProof.andL B C (Finset.mem_insert_self _ _)
        (SeqProof.ax B _ (Finset.mem_insert_self _ _))
  | @Derivation.andE2 _ _ _ B C G d => by
    -- Have: G ⊢ B ∧ C; want G ⊢ C
    apply SeqProof.cut (B.and C)
    · exact ndToLM d
    · exact SeqProof.andL B C (Finset.mem_insert_self _ _)
        (SeqProof.ax C _ (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)))
  | @Derivation.orI1 _ _ _ B C G d =>
    SeqProof.orR1 B C (ndToLM d)
  | @Derivation.orI2 _ _ _ B C G d =>
    SeqProof.orR2 B C (ndToLM d)
  | @Derivation.orE _ _ _ B C E G d dB dC => by
    -- Have: G ⊢ B ∨ C, insert B G ⊢ E, insert C G ⊢ E; want G ⊢ E
    apply SeqProof.cut (B.or C)
    · exact ndToLM d
    · exact SeqProof.orL B C (Finset.mem_insert_self _ _)
        ((ndToLM dB).mono (Finset.insert_subset_insert _ (Finset.subset_insert _ _)))
        ((ndToLM dC).mono (Finset.insert_subset_insert _ (Finset.subset_insert _ _)))
  | @Derivation.impI _ _ _ B C Γ' d =>
    SeqProof.impR B C (ndToLM d)
  | @Derivation.impE _ _ _ _ B C d₁ d₂ => by
    -- Have: Γ ⊢ B → C and Γ ⊢ B; want Γ ⊢ C
    apply SeqProof.cut (B.imp C)
    · exact ndToLM d₁
    · exact SeqProof.impL B C (Finset.mem_insert_self _ _)
        ((ndToLM d₂).mono (Finset.subset_insert _ _))
        (SeqProof.ax C _ (Finset.mem_insert_self _ _))
  | @Derivation.efq _ _ _ _ _ inst _ =>
    absurd inst not_isIntuitionistic_axiomTheory_minPropAxiom

/-! ## ND–LM Equivalence -/

/-- **ND–LM Bridge**: ND derivability under `AxiomTheory MinPropAxiom`
from context `Γ` of formula `A` is equivalent to the existence of an LM proof of `Γ ⊢ A`.

**Forward**: By `ndToLM`, translating the ND derivation structure to LM rules.

**Backward**: By Kripke semantics: an LM proof of `Γ ⊢ A` witnesses
`SeqProofMinimal.sound`, which states that every minimal Kripke model world forcing `Γ` also
forces `A`. This is `MSemanticEntails ↑Γ A`, so `min_strong_completeness` gives
`SetDerivable MinPropAxiom ↑Γ A`, and `hilbert_iff_nd_ctx_min` converts this
to ND derivability. -/
theorem nd_iff_lm {Γ : Ctx Atom} {A : Proposition Atom} :
    DerivableIn (AxiomTheory (@MinPropAxiom Atom) : Theory Atom) (Γ ⊢ A) ↔
    Nonempty (SeqProofMinimal (Γ ⊢ A)) := by
  constructor
  · intro ⟨d⟩
    exact ⟨ndToLM d⟩
  · intro ⟨d⟩
    -- LM soundness: the proof establishes minimal Kripke entailment
    have h_entail : MSemanticEntails (↑Γ : Set (Proposition Atom)) A :=
      lm_msemantic_entails d
    -- Strong completeness: MSemanticEntails → SetDerivable
    obtain ⟨L, hL_sub, hL_deriv⟩ := min_strong_completeness h_entail
    obtain ⟨dtree⟩ := hL_deriv
    -- Convert from SetDerivable (List-based) to DerivableIn (Finset-based)
    rw [← hilbert_iff_nd_ctx_min]
    exact ⟨DerivationTree.weakening L Γ.toList A dtree
      (fun x hx => Finset.mem_toList.mpr (Finset.mem_coe.mp (hL_sub x hx)))⟩

/-! ## Hilbert–LM Bridge -/

/-- **Hilbert–LM Bridge**: Hilbert derivability from context `Γ.toList` is equivalent
to the existence of an LM proof of `Γ ⊢ φ`.

Obtained by composing `hilbert_iff_nd_ctx_min` with `nd_iff_lm`. -/
theorem hilbert_iff_lm {Γ : Ctx Atom} {φ : Proposition Atom} :
    Deriv MinPropAxiom Γ.toList φ ↔ Nonempty (SeqProofMinimal (Γ ⊢ φ)) :=
  hilbert_iff_nd_ctx_min.trans nd_iff_lm

/-! ## Soundness and Completeness Corollary -/

/-- **LM Soundness and Completeness**: A formula is minimally valid if and only if
it has an LM proof from the empty context.

Forward direction: by `min_strong_completeness` (Kripke) and `hilbert_iff_lm`.
Backward direction: by `SeqProofMinimal.sound` applied to all minimal Kripke models. -/
theorem lm_iff_mvalid {φ : Proposition Atom} :
    MValid.{u, u} φ ↔ Nonempty (SeqProofMinimal (∅ ⊢ φ)) := by
  constructor
  · intro h_valid
    -- h_valid : MValid.{u, u} φ — forced at every world of every minimal Kripke model
    have h_entail : MSemanticEntails (∅ : Set (Proposition Atom)) φ :=
      MSemanticEntails_of_MValid h_valid _
    obtain ⟨L, hL_sub, hL_deriv⟩ := min_strong_completeness h_entail
    obtain ⟨dtree⟩ := hL_deriv
    -- L ⊆ ∅ so L = []
    have hL_nil : L = [] := by
      by_contra hne
      obtain ⟨a, ha⟩ := List.exists_mem_of_ne_nil L hne
      exact absurd (hL_sub a ha) (fun h => h)
    subst hL_nil
    rw [← hilbert_iff_lm]
    simp only [Finset.toList_empty]
    exact ⟨dtree⟩
  · intro ⟨d⟩ World _ val bot_forces v_uc bf_uc w
    exact d.sound val bot_forces v_uc bf_uc w (fun _ h => by simp at h)

end Cslib.Logic.PL
