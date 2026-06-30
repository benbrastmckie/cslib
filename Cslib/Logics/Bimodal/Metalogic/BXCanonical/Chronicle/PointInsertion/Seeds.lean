/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Bimodal.Metalogic.BXCanonical.Frame
public import Cslib.Logics.Bimodal.Metalogic.BXCanonical.Chronicle.ChronicleTypes
public import Cslib.Logics.Bimodal.Metalogic.BXCanonical.Chronicle.RRelation
public import Cslib.Logics.Bimodal.Metalogic.BXCanonical.CanonicalModel
public import Cslib.Logics.Bimodal.Theorems.TemporalDerived

/-! # Seeds — Helper Lemmas and Core Point Insertion (Seeds)

Helper F/G lemmas, Lemma 2.4/2.5/2.6, seriality, seed consistency, and R3Maximal utilities.
These form the foundational building blocks for the Burgess chronicle point-insertion machinery.

## Main Results

- `lemma24`: Until witness endpoint construction
- `lemma26`: Counterexample insertion
- `gPropagationWitness`: G-propagation insertion witness
- `G_implies_F_mcs`, `H_implies_P_mcs`: Seriality consequences at MCS level
-/

@[expose] public section

namespace Cslib.Logic.Bimodal.Metalogic.BXCanonical.Chronicle

set_option linter.unusedSimpArgs false
set_option linter.style.emptyLine false
set_option linter.style.longLine false
set_option linter.style.setOption false
set_option linter.flexible false

attribute [local instance] Classical.propDecidable

variable {Atom : Type*}

open Cslib.Logic.Bimodal

open Cslib.Logic.Bimodal.Metalogic.Core
open Cslib.Logic.Bimodal.Metalogic.Bundle
open Cslib.Logic.Bimodal.Metalogic.BXCanonical
open Cslib.Logic.Bimodal.Metalogic.BXCanonical.CanonicalModel
open Cslib.Logic.Bimodal.Theorems.Propositional
open Cslib.Logic.Bimodal.Theorems.Combinators
open Cslib.Logic.Bimodal.Theorems.TemporalDerived

/-! ## Helper: F(neg phi) from G(phi) not in A

A common pattern: if G(φ) ∉ MCS A, then F(¬φ) ∈ A.
This requires going through double-negation elimination under G,
since F(¬φ) = ¬G(¬¬φ) which is not definitionally equal to ¬G(φ).
-/

/-- If G(φ) ∉ MCS A, then F(¬φ) ∈ A. -/
theorem F_neg_of_G_not (fc : FrameClass) {A : Set (Formula Atom)}
    (h_mcs : SetMaximalConsistent fc A) (φ : Formula Atom)
    (h_Gφ_not : Formula.allFuture φ ∉ A) :
    Formula.someFuture φ.neg ∈ A := by
  -- Case split on F(¬φ) directly
  rcases SetMaximalConsistent.negation_complete h_mcs (Formula.someFuture φ.neg) with h | h
  · exact h
  · -- ¬F(¬φ) ∈ A: derive G(¬¬φ) via duality bridge
    have h_G_nnφ : Formula.allFuture φ.neg.neg ∈ A :=
      neg_someFuture_to_allFuture_neg h_mcs φ.neg h
    -- G(¬¬φ) → G(φ) via DNE under G
    have h_dne : DerivationTree fc [] (φ.neg.neg.imp φ) :=
      liftBase fc (Cslib.Logic.Bimodal.Theorems.Propositional.doubleNegation φ)
    have h_G_dne : DerivationTree fc [] (Formula.allFuture (φ.neg.neg.imp φ)) :=
      DerivationTree.temporal_necessitation _ h_dne
    have h_kd : DerivationTree fc [] ((φ.neg.neg.imp φ).allFuture.imp
        (φ.neg.neg.allFuture.imp φ.allFuture)) :=
      liftBase fc (Cslib.Logic.Bimodal.Theorems.TemporalDerived.tempKDistDerived φ.neg.neg φ)
    have h1 := theoremInMcsFc h_mcs h_G_dne
    have h2 := theoremInMcsFc h_mcs h_kd
    have h3 := SetMaximalConsistent.implication_property h_mcs h2 h1
    have h_Gφ := SetMaximalConsistent.implication_property h_mcs h3 h_G_nnφ
    exact absurd h_Gφ h_Gφ_not

/-- If H(φ) ∉ MCS A, then P(¬φ) ∈ A. Dual of `F_neg_of_G_not`. -/
theorem P_neg_of_H_not (fc : FrameClass) {A : Set (Formula Atom)}
    (h_mcs : SetMaximalConsistent fc A) (φ : Formula Atom)
    (h_Hφ_not : Formula.allPast φ ∉ A) :
    Formula.somePast φ.neg ∈ A := by
  rcases SetMaximalConsistent.negation_complete h_mcs (Formula.somePast φ.neg) with h | h
  · exact h
  · have h_H_nnφ : Formula.allPast φ.neg.neg ∈ A :=
      neg_somePast_to_allPast_neg h_mcs φ.neg h
    have h_dne : DerivationTree fc [] (φ.neg.neg.imp φ) :=
      liftBase fc (Cslib.Logic.Bimodal.Theorems.Propositional.doubleNegation φ)
    have h_H_dne : DerivationTree fc [] (Formula.allPast (φ.neg.neg.imp φ)) :=
      Cslib.Logic.Bimodal.Theorems.pastNecessitation _ h_dne
    have h_kd : DerivationTree fc [] ((φ.neg.neg.imp φ).allPast.imp
        (φ.neg.neg.allPast.imp φ.allPast)) :=
      Cslib.Logic.Bimodal.Theorems.pastKDist φ.neg.neg φ
    have h1 := theoremInMcsFc h_mcs h_H_dne
    have h2 := theoremInMcsFc h_mcs h_kd
    have h3 := SetMaximalConsistent.implication_property h_mcs h2 h1
    have h_Hφ := SetMaximalConsistent.implication_property h_mcs h3 h_H_nnφ
    exact absurd h_Hφ h_Hφ_not

/-! ## Lemma 2.4: Until Witness Endpoint Construction -/

/-- The Until witness seed: {β} ∪ gContent(A) is consistent when
U(γ,β) ∈ MCS A. -/
theorem until_witness_seed_consistent (fc : FrameClass) {A : Set (Formula Atom)}
    (h_mcs : SetMaximalConsistent fc A) (γ β : Formula Atom)
    (h_until : Formula.untl γ β ∈ A) :
    SetConsistent fc ({β} ∪ gContent A) := by
  have h_F_β : Formula.someFuture β ∈ A := by
    have h_ax : DerivationTree fc [] ((Formula.untl γ β).imp (Formula.someFuture β)) :=
      DerivationTree.axiom [] _ (Axiom.until_F γ β) trivial
    exact SetMaximalConsistent.implication_property h_mcs
      (theoremInMcsFc h_mcs h_ax) h_until
  exact forward_temporal_witness_seed_consistent A h_mcs β h_F_β

/-- **Lemma 2.4** (adapted for strict semantics): Given MCS A with U(γ, β) ∈ A
and ¬burgessR3(A, Set.univ, C) for the constructed C, there exists MCS C with
β ∈ C, gContent(A) ⊆ C, P(U(γ,β)) ∈ C, and a DCS interval set B with
BurgessR3Maximal(A, B, C).

The hypothesis `h_not_univ_gen` provides ¬burgessR3(A, Set.univ, C) for ANY MCS C
extending the seed {β} ∪ gContent(A). This is needed because C is constructed
internally and callers cannot know it in advance. -/
lemma lemma24 (fc : FrameClass) {A : Set (Formula Atom)}
    (h_mcs : SetMaximalConsistent fc A) (γ β : Formula Atom)
    (h_until : Formula.untl γ β ∈ A) :
    ∃ B C : Set (Formula Atom), SetMaximalConsistent fc C ∧
      β ∈ C ∧ gContent A ⊆ C ∧
      Formula.somePast (Formula.untl γ β) ∈ C ∧
      BurgessR3Maximal fc A B C := by
  have h_seed_cons := until_witness_seed_consistent fc h_mcs γ β h_until
  obtain ⟨C, h_sup, h_C_mcs⟩ := set_lindenbaum_fc h_seed_cons
  have h_β_C : β ∈ C := h_sup (Set.mem_union_left _ (Set.mem_singleton β))
  have h_g_sub : gContent A ⊆ C := fun χ hχ => h_sup (Set.mem_union_right _ hχ)
  have h_GP : Formula.allFuture (Formula.somePast (Formula.untl γ β)) ∈ A := by
    have h_ax : DerivationTree fc [] ((Formula.untl γ β).imp
        (Formula.allFuture (Formula.somePast (Formula.untl γ β)))) :=
      DerivationTree.axiom [] _ (Axiom.connect_future (Formula.untl γ β)) trivial
    exact SetMaximalConsistent.implication_property h_mcs
      (theoremInMcsFc h_mcs h_ax) h_until
  have h_P_until_C : Formula.somePast (Formula.untl γ β) ∈ C :=
    h_g_sub h_GP
  obtain ⟨B, h_B⟩ := burgessR3Maximal_from_g_content_sub fc h_mcs h_C_mcs h_g_sub
  exact ⟨B, C, h_C_mcs, h_β_C, h_g_sub, h_P_until_C, h_B⟩

/-- BX10 at MCS level: U(γ,β) ∈ A implies F(β) ∈ A. -/
theorem until_F_mcs (fc : FrameClass) {A : Set (Formula Atom)}
    (h_mcs : SetMaximalConsistent fc A) (γ β : Formula Atom)
    (h_until : Formula.untl γ β ∈ A) :
    Formula.someFuture β ∈ A := by
  have h_ax : DerivationTree fc [] ((Formula.untl γ β).imp (Formula.someFuture β)) :=
    DerivationTree.axiom [] _ (Axiom.until_F γ β) trivial
  exact SetMaximalConsistent.implication_property h_mcs
    (theoremInMcsFc h_mcs h_ax) h_until

/-- BX5 at MCS level: U(γ,β) ∈ A implies U(γ∧U(γ,β), β) ∈ A. -/
theorem self_accum_until_mcs (fc : FrameClass) {A : Set (Formula Atom)}
    (h_mcs : SetMaximalConsistent fc A) (γ β : Formula Atom)
    (h_until : Formula.untl γ β ∈ A) :
    Formula.untl (Formula.and γ (Formula.untl γ β)) β ∈ A := by
  have h_ax : DerivationTree fc [] ((Formula.untl γ β).imp
      (Formula.untl (Formula.and γ (Formula.untl γ β)) β)) :=
    DerivationTree.axiom [] _ (Axiom.self_accum_until γ β) trivial
  exact SetMaximalConsistent.implication_property h_mcs
    (theoremInMcsFc h_mcs h_ax) h_until

/-- BX5' at set-MCS level: snce(γ, β) ∈ A implies snce(γ ∧ snce(γ, β), β) ∈ A. -/
theorem self_accum_since_mcs (fc : FrameClass) {A : Set (Formula Atom)}
    (h_mcs : SetMaximalConsistent fc A) (γ β : Formula Atom)
    (h_since : Formula.snce γ β ∈ A) :
    Formula.snce (Formula.and γ (Formula.snce γ β)) β ∈ A := by
  have h_ax : DerivationTree fc [] ((Formula.snce γ β).imp
      (Formula.snce (Formula.and γ (Formula.snce γ β)) β)) :=
    DerivationTree.axiom [] _ (Axiom.self_accum_since γ β) trivial
  exact SetMaximalConsistent.implication_property h_mcs
    (theoremInMcsFc h_mcs h_ax) h_since

/-- BX4 at MCS level: φ ∈ A implies G(P(φ)) ∈ A. -/
theorem connect_future_mcs (fc : FrameClass) {A : Set (Formula Atom)}
    (h_mcs : SetMaximalConsistent fc A) (φ : Formula Atom)
    (h_φ : φ ∈ A) :
    Formula.allFuture (Formula.somePast φ) ∈ A := by
  have h_ax : DerivationTree fc [] (φ.imp (Formula.allFuture (Formula.somePast φ))) :=
    DerivationTree.axiom [] _ (Axiom.connect_future φ) trivial
  exact SetMaximalConsistent.implication_property h_mcs
    (theoremInMcsFc h_mcs h_ax) h_φ

/-- Conjunction introduction at MCS level. -/
theorem conj_mcs (fc : FrameClass) {A : Set (Formula Atom)}
    (h_mcs : SetMaximalConsistent fc A) (φ ψ : Formula Atom)
    (h_φ : φ ∈ A) (h_ψ : ψ ∈ A) :
    Formula.and φ ψ ∈ A := by
  rcases SetMaximalConsistent.negation_complete h_mcs (φ.imp ψ.neg) with h | h
  · have h_neg_ψ := SetMaximalConsistent.implication_property h_mcs h h_φ
    exact absurd h_ψ (SetMaximalConsistent.neg_excludes h_mcs _ h_neg_ψ)
  · exact h

/-- MCS disjunction elimination (local version): If (φ ∨ ψ) ∈ A then φ ∈ A ∨ ψ ∈ A.
Recall φ.or ψ = φ.neg.imp ψ. -/
theorem or_elim_mcs (fc : FrameClass) {A : Set (Formula Atom)}
    (h_mcs : SetMaximalConsistent fc A) {φ ψ : Formula Atom}
    (h : (φ.or ψ) ∈ A) : φ ∈ A ∨ ψ ∈ A := by
  rcases SetMaximalConsistent.negation_complete h_mcs φ with h_φ | h_neg_φ
  · exact Or.inl h_φ
  · exact Or.inr (SetMaximalConsistent.implication_property h_mcs h h_neg_φ)

/-- BX7 (linear_until) at MCS level: If U(φ,ψ) ∈ A and U(χ,θ) ∈ A,
then one of three disjuncts holds:
  D1: U(φ∧χ, ψ∧θ) ∈ A, or D2: U(φ∧χ, ψ∧χ) ∈ A, or D3: U(φ∧χ, φ∧θ) ∈ A. -/
theorem linear_until_mcs (fc : FrameClass) {A : Set (Formula Atom)}
    (h_mcs : SetMaximalConsistent fc A) (φ ψ χ θ : Formula Atom)
    (h_u1 : Formula.untl φ ψ ∈ A)
    (h_u2 : Formula.untl χ θ ∈ A) :
    Formula.untl (Formula.and φ χ) (Formula.and ψ θ) ∈ A ∨
    Formula.untl (Formula.and φ χ) (Formula.and ψ χ) ∈ A ∨
    Formula.untl (Formula.and φ χ) (Formula.and φ θ) ∈ A := by
  -- Form the conjunction: U(φ,ψ) ∧ U(χ,θ) ∈ A
  have h_conj := conj_mcs fc h_mcs _ _ h_u1 h_u2
  -- Apply BX7 axiom
  have h_bx7 := DerivationTree.axiom (fc := fc) [] _ (Axiom.linear_until φ ψ χ θ) trivial
  have h_disj := SetMaximalConsistent.implication_property h_mcs
    (theoremInMcsFc h_mcs h_bx7) h_conj
  -- h_disj : (D1 ∨ D2) ∨ D3 ∈ A
  -- Case split on the outer disjunction
  rcases or_elim_mcs fc h_mcs h_disj with h12 | h3
  · -- D1 ∨ D2 ∈ A
    rcases or_elim_mcs fc h_mcs h12 with h1 | h2
    · exact Or.inl h1
    · exact Or.inr (Or.inl h2)
  · exact Or.inr (Or.inr h3)

/-- BX7' (linear_since) at MCS level: If S(φ,ψ) ∈ A and S(χ,θ) ∈ A,
then one of three disjuncts holds:
  D1: S(φ∧χ, ψ∧θ) ∈ A, or D2: S(φ∧χ, ψ∧χ) ∈ A, or D3: S(φ∧χ, φ∧θ) ∈ A. -/
theorem linear_since_mcs (fc : FrameClass) {A : Set (Formula Atom)}
    (h_mcs : SetMaximalConsistent fc A) (φ ψ χ θ : Formula Atom)
    (h_s1 : Formula.snce φ ψ ∈ A)
    (h_s2 : Formula.snce χ θ ∈ A) :
    Formula.snce (Formula.and φ χ) (Formula.and ψ θ) ∈ A ∨
    Formula.snce (Formula.and φ χ) (Formula.and ψ χ) ∈ A ∨
    Formula.snce (Formula.and φ χ) (Formula.and φ θ) ∈ A := by
  have h_conj := conj_mcs fc h_mcs _ _ h_s1 h_s2
  have h_bx7 := DerivationTree.axiom (fc := fc) [] _ (Axiom.linear_since φ ψ χ θ) trivial
  have h_disj := SetMaximalConsistent.implication_property h_mcs
    (theoremInMcsFc h_mcs h_bx7) h_conj
  rcases or_elim_mcs fc h_mcs h_disj with h12 | h3
  · rcases or_elim_mcs fc h_mcs h12 with h1 | h2
    · exact Or.inl h1
    · exact Or.inr (Or.inl h2)
  · exact Or.inr (Or.inr h3)

/-! ## Lemma 2.5: gContent Ordering Composition -/

/-- **Lemma 2.5** (composition): gContent ordering is transitive. -/
theorem lemma_2_5b (fc : FrameClass) {A D C : Set (Formula Atom)}
    (h_mcs_A : SetMaximalConsistent fc A)
    (h_AD : gContent A ⊆ D) (h_DC : gContent D ⊆ C) :
    gContent A ⊆ C := by
  intro φ hφ
  have h_GGφ : Formula.allFuture (Formula.allFuture φ) ∈ A :=
    SetMaximalConsistent.allFuture_allFuture h_mcs_A hφ
  have h_Gφ_D : Formula.allFuture φ ∈ D := h_AD h_GGφ
  exact h_DC h_Gφ_D

/-- Dual of lemma_2_5b: hContent ordering is transitive (past direction). -/
theorem lemma_2_5b_past (fc : FrameClass) {A D C : Set (Formula Atom)}
    (h_mcs_C : SetMaximalConsistent fc C)
    (h_CD : hContent C ⊆ D) (h_DA : hContent D ⊆ A) :
    hContent C ⊆ A := by
  intro φ hφ
  have h_HHφ : Formula.allPast (Formula.allPast φ) ∈ C :=
    SetMaximalConsistent.allPast_allPast h_mcs_C hφ
  have h_Hφ_D : Formula.allPast φ ∈ D := h_CD h_HHφ
  exact h_DA h_Hφ_D

/-! ## Lemma 2.6: Counterexample Insertion (Negative Insertion) -/

/-- **Lemma 2.6** (adapted): Given MCS A and C with gContent(A) ⊆ C,
if δ ∉ C, then there exists MCS D with ¬δ ∈ D and gContent(A) ⊆ D. -/
lemma lemma26 (fc : FrameClass) {A C : Set (Formula Atom)}
    (h_mcs_A : SetMaximalConsistent fc A)
    (_h_mcs_C : SetMaximalConsistent fc C)
    (h_g_AC : gContent A ⊆ C)
    (δ : Formula Atom)
    (h_δ_not_C : δ ∉ C) :
    ∃ D : Set (Formula Atom), SetMaximalConsistent fc D ∧
      δ.neg ∈ D ∧ gContent A ⊆ D := by
  have h_Gδ_not_A : Formula.allFuture δ ∉ A := by
    intro h_Gδ; exact h_δ_not_C (h_g_AC h_Gδ)
  have h_F_neg_δ := F_neg_of_G_not fc h_mcs_A δ h_Gδ_not_A
  have h_seed_cons := forward_temporal_witness_seed_consistent A h_mcs_A δ.neg h_F_neg_δ
  obtain ⟨D, h_sup, h_D_mcs⟩ := set_lindenbaum_fc h_seed_cons
  exact ⟨D, h_D_mcs,
    h_sup (Set.mem_union_left _ (Set.mem_singleton _)),
    fun χ hχ => h_sup (Set.mem_union_right _ hχ)⟩

/-! ### Withdrawn and Re-assessed Lemmas

- `lemma_2_6_strong`: FALSE under strict semantics (gContent(D) ≤ C unprovable).
  Remains withdrawn.

- `lemma_2_7`: Previously marked FALSE under strict semantics (Phase 3, task 107),
  but that assessment was for a "D2 branch" proof approach that predated BX13
  (enrichment_until, Burgess A3a). With BX13 now available (Phase 2, task 107),
  Burgess's ORIGINAL proof of Lemma 2.7 is valid:
  1. BX5 (self_accum_until) enriches the Until guard
  2. BX7 (linear_until) provides the three-way disjunction
  3. BX13 (enrichment_until) simplifies the surviving disjunct
  4. BX1/BX2G (monotonicity) rule out two disjuncts
  None of these axioms depend on BX9 (removed) or the T-axiom.
  **Gate verdict (Phase 5, plan v27): VALID. Proceed with Strategy 1.**

- `lemma_2_8`: May also be recoverable with BX13, but Lemma 2.7 suffices
  for the C5 n>0 sub-case 3 (Burgess Lemma 2.10). Not needed if 2.7 works.
-/

/-- Conjunction membership gives left component in MCS. -/
theorem conj_left_mcs (fc : FrameClass) {A : Set (Formula Atom)}
    (h_mcs : SetMaximalConsistent fc A) (φ ψ : Formula Atom)
    (h_conj : Formula.and φ ψ ∈ A) :
    φ ∈ A := by
  have h_ax : DerivationTree fc [] ((Formula.and φ ψ).imp φ) := lceImp φ ψ
  exact SetMaximalConsistent.implication_property h_mcs
    (theoremInMcsFc h_mcs h_ax) h_conj

/-- Conjunction membership gives right component in MCS. -/
theorem conj_right_mcs (fc : FrameClass) {A : Set (Formula Atom)}
    (h_mcs : SetMaximalConsistent fc A) (φ ψ : Formula Atom)
    (h_conj : Formula.and φ ψ ∈ A) :
    ψ ∈ A := by
  have h_ax : DerivationTree fc [] ((Formula.and φ ψ).imp ψ) := rceImp φ ψ
  exact SetMaximalConsistent.implication_property h_mcs
    (theoremInMcsFc h_mcs h_ax) h_conj

/-! ## G/H Implies F/P (Seriality + BX3 + BX10/BX12) -/

/-- In an MCS, G(α) implies F(α). Uses seriality + BX3 + BX10 + BX12. -/
theorem G_implies_F_mcs (fc : FrameClass) {A : Set (Formula Atom)}
    (h_mcs : SetMaximalConsistent fc A) (α : Formula Atom)
    (h_G : Formula.allFuture α ∈ A) :
    Formula.someFuture α ∈ A := by
  set top := (Formula.bot : Formula Atom).imp (Formula.bot : Formula Atom) with top_def
  have h_weak : DerivationTree fc [] (Formula.imp α (Formula.imp top α)) :=
    DerivationTree.axiom [] _ (Axiom.imp_s α top) trivial
  have h_G_top_α : Formula.allFuture (Formula.imp top α) ∈ A := by
    have h1 := theoremInMcsFc h_mcs (DerivationTree.temporal_necessitation _ h_weak)
    have h2 := theoremInMcsFc h_mcs
      (liftBase fc (Cslib.Logic.Bimodal.Theorems.TemporalDerived.tempKDistDerived α (Formula.imp top α)))
    exact SetMaximalConsistent.implication_property h_mcs
      (SetMaximalConsistent.implication_property h_mcs h2 h1) h_G
  have h_top_in : top ∈ A :=
    theoremInMcsFc h_mcs (Cslib.Logic.Bimodal.Theorems.Combinators.identity (Formula.bot : Formula Atom))
  have h_F_top : Formula.someFuture top ∈ A :=
    SetMaximalConsistent.implication_property h_mcs
      (theoremInMcsFc h_mcs (DerivationTree.axiom [] _ Axiom.serial_future trivial)) h_top_in
  have h_TUT : Formula.untl top top ∈ A :=
    SetMaximalConsistent.implication_property h_mcs
      (theoremInMcsFc h_mcs (DerivationTree.axiom [] _ (Axiom.F_until_equiv top) trivial)) h_F_top
  have h_TUα : Formula.untl top α ∈ A := by
    have h1 := SetMaximalConsistent.implication_property h_mcs
      (theoremInMcsFc h_mcs (DerivationTree.axiom [] _ (Axiom.right_mono_until top α top) trivial))
      h_G_top_α
    exact SetMaximalConsistent.implication_property h_mcs h1 h_TUT
  exact SetMaximalConsistent.implication_property h_mcs
    (theoremInMcsFc h_mcs (DerivationTree.axiom [] _ (Axiom.until_F top α) trivial)) h_TUα

/-- In an MCS, H(α) implies P(α). Mirror of G_implies_F_mcs. -/
theorem H_implies_P_mcs (fc : FrameClass) {A : Set (Formula Atom)}
    (h_mcs : SetMaximalConsistent fc A) (α : Formula Atom)
    (h_H : Formula.allPast α ∈ A) :
    Formula.somePast α ∈ A := by
  set top := (Formula.bot : Formula Atom).imp (Formula.bot : Formula Atom) with top_def
  have h_weak : DerivationTree fc [] (Formula.imp α (Formula.imp top α)) :=
    DerivationTree.axiom [] _ (Axiom.imp_s α top) trivial
  have h_H_top_α : Formula.allPast (Formula.imp top α) ∈ A := by
    have h1 := theoremInMcsFc h_mcs (Cslib.Logic.Bimodal.Theorems.pastNecessitation _ h_weak)
    have h2 := theoremInMcsFc h_mcs (Cslib.Logic.Bimodal.Theorems.pastKDist α (Formula.imp top α))
    exact SetMaximalConsistent.implication_property h_mcs
      (SetMaximalConsistent.implication_property h_mcs h2 h1) h_H
  have h_top_in : top ∈ A :=
    theoremInMcsFc h_mcs (Cslib.Logic.Bimodal.Theorems.Combinators.identity (Formula.bot : Formula Atom))
  have h_P_top : Formula.somePast top ∈ A :=
    SetMaximalConsistent.implication_property h_mcs
      (theoremInMcsFc h_mcs (DerivationTree.axiom [] _ Axiom.serial_past trivial)) h_top_in
  have h_TST : Formula.snce top top ∈ A :=
    SetMaximalConsistent.implication_property h_mcs
      (theoremInMcsFc h_mcs (DerivationTree.axiom [] _ (Axiom.P_since_equiv top) trivial)) h_P_top
  have h_TSα : Formula.snce top α ∈ A := by
    have h1 := SetMaximalConsistent.implication_property h_mcs
      (theoremInMcsFc h_mcs (DerivationTree.axiom [] _ (Axiom.right_mono_since top α top) trivial))
      h_H_top_α
    exact SetMaximalConsistent.implication_property h_mcs h1 h_TST
  exact SetMaximalConsistent.implication_property h_mcs
    (theoremInMcsFc h_mcs (DerivationTree.axiom [] _ (Axiom.since_P top α) trivial)) h_TSα

/-- G-propagation seed consistency. -/
theorem g_propagation_seed_consistent (fc : FrameClass) {A : Set (Formula Atom)}
    (h_mcs : SetMaximalConsistent fc A) (α : Formula Atom)
    (h_G : Formula.allFuture α ∈ A) :
    SetConsistent fc (forwardTemporalWitnessSeed A α) := by
  exact forward_temporal_witness_seed_consistent A h_mcs α (G_implies_F_mcs fc h_mcs α h_G)

/-- G-propagation insertion: given G(α) ∈ f(x), produce MCS D with α ∈ D
and gContent(f(x)) ⊆ D. -/
lemma gPropagationWitness (fc : FrameClass) {A : Set (Formula Atom)}
    (h_mcs : SetMaximalConsistent fc A) (α : Formula Atom)
    (h_G : Formula.allFuture α ∈ A) :
    ∃ D : Set (Formula Atom), SetMaximalConsistent fc D ∧ α ∈ D ∧ gContent A ⊆ D := by
  obtain ⟨D, h_sup, h_D_mcs⟩ := set_lindenbaum_fc (g_propagation_seed_consistent fc h_mcs α h_G)
  exact ⟨D, h_D_mcs,
    h_sup (Set.mem_union_left _ (Set.mem_singleton _)),
    fun χ hχ => h_sup (Set.mem_union_right _ hχ)⟩

/-! ## Seed Consistency for DCS Extension -/

/-- If S is a DCS and φ ∉ S, then {φ.neg} ∪ S is consistent. -/
theorem dcs_neg_union_consistent (fc : FrameClass) {Sig : Set (Formula Atom)} (h_dcs : SetDeductivelyClosed fc Sig)
    {φ : Formula Atom} (h_not : φ ∉ Sig) :
    SetConsistent fc ({φ.neg} ∪ Sig) := by
  intro L hL ⟨d⟩
  apply h_not
  by_cases h_neg_in_L : φ.neg ∈ L
  · have d_ext : DerivationTree fc (φ.neg :: L) Formula.bot :=
      DerivationTree.weakening L (φ.neg :: L) Formula.bot d (List.subset_cons_of_subset _ (List.Subset.refl L))
    have d_imp : DerivationTree fc L φ.neg.neg :=
      deductionTheorem L φ.neg Formula.bot d_ext
    have h_dne : DerivationTree fc [] (φ.neg.neg.imp φ) :=
      Cslib.Logic.Bimodal.Theorems.Propositional.doubleNegation φ
    have d_phi : DerivationTree fc L φ :=
      DerivationTree.modus_ponens L φ.neg.neg φ
        (DerivationTree.weakening [] L (φ.neg.neg.imp φ) h_dne (List.nil_subset L)) d_imp
    set M := L.filter (fun x => !decide (x = φ.neg)) with hM_def
    have hM_sub_S : ∀ ψ ∈ M, ψ ∈ Sig := by
      intro ψ hψ; rw [hM_def] at hψ
      have h_mem := List.mem_filter.mp hψ
      have h1 : ψ ∈ L := h_mem.1
      have h2 : ψ ≠ φ.neg := by simp at h_mem; exact h_mem.2
      rcases hL ψ h1 with h_sing | h_S
      · exact absurd (Set.mem_singleton_iff.mp h_sing) h2
      · exact h_S
    have hL_sub : L ⊆ φ.neg :: M := by
      intro x hx
      by_cases heq : x = φ.neg
      · subst heq; exact .head M
      · exact .tail _ (List.mem_filter.mpr ⟨hx, by simp; exact heq⟩)
    have d_phi_w : DerivationTree fc (φ.neg :: M) φ :=
      DerivationTree.weakening L (φ.neg :: M) φ d_phi hL_sub
    have d_neg_imp : DerivationTree fc M (φ.neg.imp φ) :=
      deductionTheorem M φ.neg φ d_phi_w
    have h_peirce : DerivationTree fc [] ((φ.neg.imp φ).imp φ) := by
      have s1 : DerivationTree fc [φ.neg, φ.neg.imp φ] φ :=
        DerivationTree.modus_ponens [φ.neg, φ.neg.imp φ] φ.neg φ
          (DerivationTree.assumption _ (φ.neg.imp φ) (by simp))
          (DerivationTree.assumption _ φ.neg (by simp))
      have s2 : DerivationTree fc [φ.neg, φ.neg.imp φ] Formula.bot :=
        DerivationTree.modus_ponens [φ.neg, φ.neg.imp φ] φ Formula.bot
          (DerivationTree.assumption _ φ.neg (by simp)) s1
      have s3 := deductionTheorem [φ.neg.imp φ] φ.neg Formula.bot s2
      have s4 : DerivationTree fc [φ.neg.imp φ] φ :=
        DerivationTree.modus_ponens [φ.neg.imp φ] φ.neg.neg φ
          (DerivationTree.weakening [] [φ.neg.imp φ] (φ.neg.neg.imp φ) h_dne (List.nil_subset _)) s3
      exact deductionTheorem [] (φ.neg.imp φ) φ s4
    have d_phi_M : DerivationTree fc M φ :=
      DerivationTree.modus_ponens M (φ.neg.imp φ) φ
        (DerivationTree.weakening [] M ((φ.neg.imp φ).imp φ) h_peirce (List.nil_subset M)) d_neg_imp
    exact h_dcs.2 M φ hM_sub_S d_phi_M
  · have hL_S : ∀ ψ ∈ L, ψ ∈ Sig := by
      intro ψ hψ
      have h_mem := hL ψ hψ
      rcases h_mem with h_sing | h_S
      · have : ψ = φ.neg := Set.mem_singleton_iff.mp h_sing
        exact absurd (this ▸ hψ) h_neg_in_L
      · exact h_S
    exact absurd (h_dcs.1 L hL_S ⟨d⟩) (not_false)

/-! ## R3Maximal Properties -/

/-- R3Maximal negation completeness: δ ∉ B implies δ.neg ∈ B. -/
theorem r3Maximal_neg_of_not_mem (fc : FrameClass) {A B C : Set (Formula Atom)}
    (h_R3 : R3Maximal fc A B C) (δ : Formula Atom) (h_not : δ ∉ B) :
    δ.neg ∈ B := by
  by_contra h_neg_not
  have h_cons := dcs_neg_union_consistent fc h_R3.1 h_not
  have h_dc_dcs := deductiveClosure_is_dcs fc h_cons
  have h_B_sub : B ⊆ deductiveClosure fc ({δ.neg} ∪ B) :=
    fun φ hφ => subset_deductiveClosure fc ({δ.neg} ∪ B) (Set.mem_union_right _ hφ)
  have h_neg_in : δ.neg ∈ deductiveClosure fc ({δ.neg} ∪ B) :=
    subset_deductiveClosure fc ({δ.neg} ∪ B) (Set.mem_union_left _ (Set.mem_singleton δ.neg))
  have h_proper : B ⊂ deductiveClosure fc ({δ.neg} ∪ B) :=
    ⟨h_B_sub, fun h_eq => h_neg_not (h_eq h_neg_in)⟩
  have h_r3 : r3Relation A (deductiveClosure fc ({δ.neg} ∪ B)) C :=
    r3Relation_subset h_R3.2.1 h_B_sub
  exact h_R3.2.2 _ h_dc_dcs h_proper h_r3

/-- R3Maximal forces MCS (via monotonicity of r3Relation). -/
theorem R3Maximal_is_mcs (fc : FrameClass) {A B C : Set (Formula Atom)}
    (h_R3 : R3Maximal fc A B C) : SetMaximalConsistent fc B := by
  refine ⟨h_R3.1.1, ?_⟩
  intro φ h_not_φ h_cons_insert
  have h_cons : SetConsistent fc ({φ} ∪ B) := by rwa [Set.insert_eq] at h_cons_insert
  have h_dc_dcs := deductiveClosure_is_dcs fc h_cons
  have h_B_sub : B ⊆ deductiveClosure fc ({φ} ∪ B) :=
    fun ψ hψ => subset_deductiveClosure fc ({φ} ∪ B) (Set.mem_union_right _ hψ)
  have h_φ_in : φ ∈ deductiveClosure fc ({φ} ∪ B) :=
    subset_deductiveClosure fc ({φ} ∪ B) (Set.mem_union_left _ (Set.mem_singleton φ))
  exact h_R3.2.2 _ h_dc_dcs ⟨h_B_sub, fun h_eq => h_not_φ (h_eq h_φ_in)⟩
    (r3Relation_subset h_R3.2.1 h_B_sub)

/-- An MCS has no proper DCS extension. -/
theorem mcs_no_proper_dcs_extension (fc : FrameClass) {B D : Set (Formula Atom)}
    (h_mcs : SetMaximalConsistent fc B) (h_dcs : SetDeductivelyClosed fc D)
    (hBD : B ⊂ D) : False := by
  obtain ⟨φ, h_φ_D, h_φ_not_B⟩ := Set.not_subset.mp hBD.2
  have h_incons := h_mcs.2 φ h_φ_not_B
  apply h_incons
  intro L hL ⟨d⟩
  exact h_dcs.1 L (fun ψ hψ => (Set.insert_subset h_φ_D hBD.1) (hL ψ hψ)) ⟨d⟩


end Cslib.Logic.Bimodal.Metalogic.BXCanonical.Chronicle

end
