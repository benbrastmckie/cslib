/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Modal.Metalogic.Completeness
public import Cslib.Logics.Modal.Metalogic.Systems.D.Soundness

/-! # Completeness Theorem for Modal Logic D (KD)

This module proves completeness for modal logic D over serial Kripke frames
via the canonical model construction (completeness-via-canonicity).

## Main Results

- `d_derive_box_from_inconsistency`: Box witness consistency using axiom D + NEC
  instead of axiom T.
- `d_mcs_box_witness`: Box witness for D (K-style, without axiom T).
- `d_canonical_serial`: The canonical model for any DAxiom-containing system is serial
  (Blackburn Theorem 4.28 clause 3).
- `d_truth_lemma`: Truth lemma using D-style box witness.

The weak completeness theorem `d_completeness` is derived below as a
corollary of strong completeness via `ModalSetDerivable_empty_iff`.

## References

* Blackburn, de Rijke, Venema, "Modal Logic" (2002), Chapter 4
  - Theorem 4.28 clause 3 (KD seriality is canonical)
  - Lemma 4.21 (Truth Lemma)
  - Proposition 4.12 (Completeness criterion)
-/

@[expose] public section

namespace Cslib.Logic.Modal

open Cslib.Logic

universe u
variable {Atom : Type u}

/-! ## Box Witness Consistency for D -/

/-- From `L |- bot` where `L <= {psi | box psi in S} union {neg phi}`,
derive `False`, using axiom D instead of axiom T.

This adapts `derive_box_from_inconsistency` from MCS.lean:
- Case 1 (neg phi in L): Identical to S5 -- filter, deduction theorem, derive box phi.
- Case 2 (neg phi not in L): All elements have box versions in S. From L |- bot,
  derive box bot in S. Then axiom D gives diamond bot in S. Since top (= bot -> bot)
  is derivable, NEC gives box top in S. MP with diamond bot gives bot in S.
  Contradiction with MCS consistency. -/
theorem d_derive_box_from_inconsistency
    {Axioms : Proposition Atom → Prop}
    (h_implyK : ∀ (φ ψ : Proposition Atom), Axioms (φ.imp (ψ.imp φ)))
    (h_implyS : ∀ (φ ψ χ : Proposition Atom),
      Axioms ((φ.imp (ψ.imp χ)).imp ((φ.imp ψ).imp (φ.imp χ))))
    (h_efq : ∀ (φ : Proposition Atom), Axioms (Proposition.bot.imp φ))
    (h_peirce : ∀ (φ ψ : Proposition Atom),
      Axioms (((φ.imp ψ).imp φ).imp φ))
    (h_K : ∀ (φ ψ : Proposition Atom),
      Axioms ((Proposition.box (φ.imp ψ)).imp
        ((Proposition.box φ).imp (Proposition.box ψ))))
    (h_D : ∀ (φ : Proposition Atom),
      Axioms ((Proposition.box φ).imp
        ((Proposition.box (φ.imp .bot)).imp .bot)))
    {S : Set (Proposition Atom)} (h_mcs : SetMaximalConsistent Axioms S)
    {φ : Proposition Atom} (h_not_box : (□φ) ∉ S)
    {L : List (Proposition Atom)}
    (hL : ∀ x ∈ L, x ∈ {ψ | (□ψ) ∈ S} ∪ {(¬φ)})
    (d_bot : DerivationTree Axioms L ⊥) : False := by
  classical
  let L' := L.filter (· ≠ (¬φ))
  have h_L'_box : ∀ ψ ∈ L', (□ψ) ∈ S := by
    intro ψ hψ
    simp only [L', List.mem_filter, decide_eq_true_eq] at hψ
    rcases hL ψ hψ.1 with h | h
    · exact h
    · exact absurd h hψ.2
  by_cases h_neg_in_L : (¬φ) ∈ L
  · -- Case 1: neg phi in L -- identical to S5 version
    have h_perm : ∀ x, x ∈ L → x ∈ (¬φ) :: L' := by
      intro x hx
      by_cases hxn : x = (¬φ)
      · exact List.mem_cons.mpr (Or.inl hxn)
      · exact List.mem_cons.mpr (Or.inr (by
          simp only [L', List.mem_filter, decide_eq_true_eq]; exact ⟨hx, hxn⟩))
    have d_reord := DerivationTree.weakening L ((¬φ) :: L')
      ⊥ d_bot h_perm
    have d_dne := deductionTheorem h_implyK h_implyS L' (¬φ)
      ⊥ d_reord
    let neg_phi := (¬φ)
    have efq_ax : DerivationTree Axioms L' (Proposition.bot.imp φ) :=
      .weakening [] L' _ (.ax [] _ (h_efq φ)) (fun _ h => nomatch h)
    have ik : DerivationTree Axioms L'
        ((Proposition.bot.imp φ).imp (neg_phi.imp (Proposition.bot.imp φ))) :=
      .weakening [] L' _ (.ax [] _ (h_implyK (Proposition.bot.imp φ) neg_phi))
        (fun _ h => nomatch h)
    have step_k := DerivationTree.modus_ponens L' _ _ ik efq_ax
    have is_ax : DerivationTree Axioms L'
        ((neg_phi.imp (Proposition.bot.imp φ)).imp
         ((neg_phi.imp Proposition.bot).imp (neg_phi.imp φ))) :=
      .weakening [] L' _ (.ax [] _ (h_implyS neg_phi Proposition.bot φ))
        (fun _ h => nomatch h)
    have step_s := DerivationTree.modus_ponens L' _ _ is_ax step_k
    have step3 := DerivationTree.modus_ponens L' _ _ step_s d_dne
    have peirce_ax : DerivationTree Axioms L'
        (((φ.imp Proposition.bot).imp φ).imp φ) :=
      .weakening [] L' _ (.ax [] _ (h_peirce φ Proposition.bot))
        (fun _ h => nomatch h)
    have d_phi := DerivationTree.modus_ponens L' _ _ peirce_ax step3
    exact h_not_box (derive_box_from_box_context h_implyK h_implyS h_K h_mcs
      d_phi h_L'_box)
  · have h_all_box : ∀ x ∈ L, (□x) ∈ S := by
      intro x hx
      rcases hL x hx with h | h
      · exact h
      · exact absurd (h ▸ hx) h_neg_in_L
    have h_box_bot : (□⊥) ∈ S :=
      derive_box_from_box_context h_implyK h_implyS h_K h_mcs d_bot h_all_box
    -- Raw shape (task 441: `diamond` is native, no longer defeq to `Axioms.AxiomD`'s RHS).
    have h_diamond_bot :
        ((Proposition.box (Proposition.bot.imp Proposition.bot)).imp Proposition.bot) ∈ S :=
      mcs_mp_axiom h_implyK h_implyS h_mcs h_box_bot (h_D ⊥)
    have d_top : DerivationTree Axioms [] (Proposition.imp .bot .bot) :=
      .ax [] _ (h_efq Proposition.bot)
    have d_box_top : DerivationTree Axioms [] (Proposition.box (Proposition.imp .bot .bot)) :=
      .necessitation _ d_top
    have h_box_top : (□(⊥ → ⊥)) ∈ S :=
      modal_closed_under_derivation h_implyK h_implyS h_mcs
        (L := []) (fun _ h => nomatch h) ⟨d_box_top⟩
    have h_bot : ⊥ ∈ S :=
      modal_implication_property h_implyK h_implyS h_mcs h_diamond_bot h_box_top
    exact mcs_bot_not_mem h_mcs h_bot

/-! ## Box Witness for D -/

/-- **Box Witness for D**: If `box phi not in S` and `S` is MCS, then there exists
an MCS `T` such that `forall psi, box psi in S -> psi in T` and `phi not in T`.

This uses axiom D instead of axiom T for the consistency argument. -/
theorem d_mcs_box_witness
    {Axioms : Proposition Atom → Prop}
    (h_implyK : ∀ (φ ψ : Proposition Atom), Axioms (φ.imp (ψ.imp φ)))
    (h_implyS : ∀ (φ ψ χ : Proposition Atom),
      Axioms ((φ.imp (ψ.imp χ)).imp ((φ.imp ψ).imp (φ.imp χ))))
    (h_efq : ∀ (φ : Proposition Atom), Axioms (Proposition.bot.imp φ))
    (h_peirce : ∀ (φ ψ : Proposition Atom),
      Axioms (((φ.imp ψ).imp φ).imp φ))
    (h_K : ∀ (φ ψ : Proposition Atom),
      Axioms ((Proposition.box (φ.imp ψ)).imp
        ((Proposition.box φ).imp (Proposition.box ψ))))
    (h_D : ∀ (φ : Proposition Atom),
      Axioms ((Proposition.box φ).imp
        ((Proposition.box (φ.imp .bot)).imp .bot)))
    {S : Set (Proposition Atom)} (h_mcs : SetMaximalConsistent Axioms S)
    {φ : Proposition Atom} (h_not_box : (□φ) ∉ S) :
    ∃ T : Set (Proposition Atom), SetMaximalConsistent Axioms T ∧
      (∀ ψ, (□ψ) ∈ S → ψ ∈ T) ∧ φ ∉ T := by
  let W := {ψ : Proposition Atom | (□ψ) ∈ S} ∪ {(¬φ)}
  have hW : SetConsistent Axioms W := by
    intro L hL
    unfold Metalogic.Consistent
    intro ⟨d_bot⟩
    exact d_derive_box_from_inconsistency h_implyK h_implyS h_efq h_peirce h_K h_D
      h_mcs h_not_box hL d_bot
  obtain ⟨T, hWT, hT_mcs⟩ := modal_lindenbaum hW
  refine ⟨T, hT_mcs, ?_, ?_⟩
  · intro ψ h_box
    exact hWT (Set.mem_union_left _ h_box)
  · have h_neg : (¬φ) ∈ T :=
      hWT (Set.mem_union_right _ (Set.mem_singleton _))
    exact mcs_not_mem_of_neg h_implyK h_implyS hT_mcs h_neg

/-! ## Truth Lemma for D -/

/-- **Truth Lemma for D**: For any canonical world `S` and formula `phi`,
`Satisfies (CanonicalModel Axioms) S phi <-> phi in S.val`.

This follows Blackburn Lemma 4.21. The only difference from the S5 truth lemma
is the box case, which uses `d_mcs_box_witness` (axiom D) instead of
`mcs_box_witness` (axiom T). -/
theorem d_truth_lemma
    {Axioms : Proposition Atom → Prop}
    (h_implyK : ∀ (φ ψ : Proposition Atom), Axioms (φ.imp (ψ.imp φ)))
    (h_implyS : ∀ (φ ψ χ : Proposition Atom),
      Axioms ((φ.imp (ψ.imp χ)).imp ((φ.imp ψ).imp (φ.imp χ))))
    (h_efq : ∀ (φ : Proposition Atom), Axioms (Proposition.bot.imp φ))
    (h_peirce : ∀ (φ ψ : Proposition Atom),
      Axioms (((φ.imp ψ).imp φ).imp φ))
    (h_K : ∀ (φ ψ : Proposition Atom),
      Axioms ((Proposition.box (φ.imp ψ)).imp
        ((Proposition.box φ).imp (Proposition.box ψ))))
    (h_D : ∀ (φ : Proposition Atom),
      Axioms ((Proposition.box φ).imp
        ((Proposition.box (φ.imp .bot)).imp .bot)))
    (h_andI : ∀ (φ ψ : Proposition Atom), Axioms (Cslib.Logic.Axioms.AndI φ ψ))
    (h_andE1 : ∀ (φ ψ : Proposition Atom), Axioms (Cslib.Logic.Axioms.AndE1 φ ψ))
    (h_andE2 : ∀ (φ ψ : Proposition Atom), Axioms (Cslib.Logic.Axioms.AndE2 φ ψ))
    (h_orI1 : ∀ (φ ψ : Proposition Atom), Axioms (Cslib.Logic.Axioms.OrI1 φ ψ))
    (h_orI2 : ∀ (φ ψ : Proposition Atom), Axioms (Cslib.Logic.Axioms.OrI2 φ ψ))
    (h_orE : ∀ (φ ψ χ : Proposition Atom), Axioms (Cslib.Logic.Axioms.OrE φ ψ χ))
    (h_dualFwd : ∀ (φ : Proposition Atom), Axioms (Cslib.Logic.Axioms.AxiomDiaDualityFwd φ))
    (h_dualBack : ∀ (φ : Proposition Atom), Axioms (Cslib.Logic.Axioms.AxiomDiaDualityBack φ))
    (S : CanonicalWorld Axioms) :
    (φ : Proposition Atom) →
    (Satisfies (CanonicalModel Axioms) S φ ↔ φ ∈ S.val)
  | .atom p => by
    constructor
    · intro h; exact h
    · intro h; exact h
  | .bot => by
    constructor
    · intro h; exact absurd h id
    · intro h; exact absurd h (mcs_bot_not_mem S.property)
  | .imp φ ψ => by
    constructor
    · intro h_sat
      rcases modal_negation_complete h_implyK h_implyS S.property (φ.imp ψ)
        with h | h
      · exact h
      · exfalso
        have h_phi_S : φ ∈ S.val := by
          apply modal_closed_under_derivation h_implyK h_implyS S.property
            (L := [(φ.imp ψ).imp .bot])
            (fun x hx => by
              simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
              exact hx ▸ h)
          unfold modalDerivationSystem Deriv
          have d_bot' : DerivationTree Axioms
              [φ.imp ψ, (φ.imp ψ).imp .bot] Proposition.bot :=
            .modus_ponens _ (φ.imp ψ) .bot
              (.assumption _ _ (by simp [List.mem_cons]))
              (.assumption _ _ (by simp [List.mem_cons]))
          have d_efq' : DerivationTree Axioms
              [φ.imp ψ, (φ.imp ψ).imp .bot] φ :=
            .modus_ponens _ .bot φ
              (.weakening [] _ _ (.ax [] _ (h_efq φ)) (fun _ h => nomatch h))
              d_bot'
          have d_dt := deductionTheorem h_implyK h_implyS
            [(φ.imp ψ).imp .bot] (φ.imp ψ) φ d_efq'
          have d_peirce' : DerivationTree Axioms
              [(φ.imp ψ).imp .bot] (((φ.imp ψ).imp φ).imp φ) :=
            .weakening [] _ _ (.ax [] _ (h_peirce φ ψ)) (fun _ h => nomatch h)
          exact ⟨.modus_ponens _ _ _ d_peirce' d_dt⟩
        have h_sat_phi :=
          (d_truth_lemma h_implyK h_implyS h_efq h_peirce h_K h_D
            h_andI h_andE1 h_andE2 h_orI1 h_orI2 h_orE h_dualFwd h_dualBack S φ).mpr h_phi_S
        have h_psi_S :=
          (d_truth_lemma h_implyK h_implyS h_efq h_peirce h_K h_D
            h_andI h_andE1 h_andE2 h_orI1 h_orI2 h_orE h_dualFwd h_dualBack S ψ).mp
            (h_sat h_sat_phi)
        have h_neg_psi_S : (¬ψ) ∈ S.val := by
          apply modal_closed_under_derivation h_implyK h_implyS S.property
            (L := [(φ.imp ψ).imp .bot])
            (fun x hx => by
              simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
              exact hx ▸ h)
          unfold modalDerivationSystem Deriv
          have d_imp : DerivationTree Axioms
              [ψ, (φ.imp ψ).imp .bot] (φ.imp ψ) :=
            .modus_ponens _ ψ (φ.imp ψ)
              (.weakening [] _ _ (.ax [] _ (h_implyK ψ φ))
                (fun _ h => nomatch h))
              (.assumption _ _ (by simp [List.mem_cons]))
          have d_bot'' : DerivationTree Axioms
              [ψ, (φ.imp ψ).imp .bot] Proposition.bot :=
            .modus_ponens _ (φ.imp ψ) .bot
              (.assumption _ _ (by simp [List.mem_cons]))
              d_imp
          exact ⟨deductionTheorem h_implyK h_implyS
            [(φ.imp ψ).imp .bot] ψ .bot d_bot''⟩
        exact mcs_bot_not_mem S.property
          (modal_implication_property h_implyK h_implyS S.property
            h_neg_psi_S h_psi_S)
    · intro h_mem h_sat_phi
      exact (d_truth_lemma h_implyK h_implyS h_efq h_peirce h_K h_D
        h_andI h_andE1 h_andE2 h_orI1 h_orI2 h_orE h_dualFwd h_dualBack S ψ).mpr
        (modal_implication_property h_implyK h_implyS S.property h_mem
          ((d_truth_lemma h_implyK h_implyS h_efq h_peirce h_K h_D
            h_andI h_andE1 h_andE2 h_orI1 h_orI2 h_orE h_dualFwd h_dualBack S φ).mp
            h_sat_phi))
  | .and φ ψ => by
    constructor
    · intro h_sat
      exact (mcs_and_mem_iff h_implyK h_implyS h_andI h_andE1 h_andE2 S.property).mpr
        ⟨(d_truth_lemma h_implyK h_implyS h_efq h_peirce h_K h_D
            h_andI h_andE1 h_andE2 h_orI1 h_orI2 h_orE h_dualFwd h_dualBack S φ).mp h_sat.1,
         (d_truth_lemma h_implyK h_implyS h_efq h_peirce h_K h_D
            h_andI h_andE1 h_andE2 h_orI1 h_orI2 h_orE h_dualFwd h_dualBack S ψ).mp h_sat.2⟩
    · intro h_mem
      obtain ⟨h1, h2⟩ :=
        (mcs_and_mem_iff h_implyK h_implyS h_andI h_andE1 h_andE2 S.property).mp h_mem
      exact ⟨(d_truth_lemma h_implyK h_implyS h_efq h_peirce h_K h_D
                h_andI h_andE1 h_andE2 h_orI1 h_orI2 h_orE h_dualFwd h_dualBack S φ).mpr h1,
             (d_truth_lemma h_implyK h_implyS h_efq h_peirce h_K h_D
                h_andI h_andE1 h_andE2 h_orI1 h_orI2 h_orE h_dualFwd h_dualBack S ψ).mpr h2⟩
  | .or φ ψ => by
    constructor
    · intro h_sat
      apply (mcs_or_mem_iff h_implyK h_implyS h_orI1 h_orI2 h_orE S.property).mpr
      cases h_sat with
      | inl h1 => exact Or.inl ((d_truth_lemma h_implyK h_implyS h_efq h_peirce h_K h_D
          h_andI h_andE1 h_andE2 h_orI1 h_orI2 h_orE h_dualFwd h_dualBack S φ).mp h1)
      | inr h2 => exact Or.inr ((d_truth_lemma h_implyK h_implyS h_efq h_peirce h_K h_D
          h_andI h_andE1 h_andE2 h_orI1 h_orI2 h_orE h_dualFwd h_dualBack S ψ).mp h2)
    · intro h_mem
      rcases (mcs_or_mem_iff h_implyK h_implyS h_orI1 h_orI2 h_orE S.property).mp h_mem
        with h1 | h2
      · exact Or.inl ((d_truth_lemma h_implyK h_implyS h_efq h_peirce h_K h_D
          h_andI h_andE1 h_andE2 h_orI1 h_orI2 h_orE h_dualFwd h_dualBack S φ).mpr h1)
      · exact Or.inr ((d_truth_lemma h_implyK h_implyS h_efq h_peirce h_K h_D
          h_andI h_andE1 h_andE2 h_orI1 h_orI2 h_orE h_dualFwd h_dualBack S ψ).mpr h2)
  | .box φ => by
    constructor
    · intro h_sat
      by_contra h_not_box
      obtain ⟨T, hT_mcs, hST, h_phi_not_T⟩ :=
        d_mcs_box_witness h_implyK h_implyS h_efq h_peirce h_K h_D
          S.property h_not_box
      exact h_phi_not_T
        ((d_truth_lemma h_implyK h_implyS h_efq h_peirce h_K h_D
          h_andI h_andE1 h_andE2 h_orI1 h_orI2 h_orE h_dualFwd h_dualBack
          ⟨T, hT_mcs⟩ φ).mp (h_sat ⟨T, hT_mcs⟩ hST))
    · intro h_box T hST
      exact (d_truth_lemma h_implyK h_implyS h_efq h_peirce h_K h_D
        h_andI h_andE1 h_andE2 h_orI1 h_orI2 h_orE h_dualFwd h_dualBack T φ).mpr
        (hST φ h_box)
  | .diamond φ => by
    constructor
    · rintro ⟨T', hR, hSatT'⟩
      have h_phi_T' : φ ∈ T'.val :=
        (d_truth_lemma h_implyK h_implyS h_efq h_peirce h_K h_D
          h_andI h_andE1 h_andE2 h_orI1 h_orI2 h_orE h_dualFwd h_dualBack T' φ).mp hSatT'
      by_contra h_not_dia
      have h_box_neg : (□¬φ) ∈ S.val := by
        by_contra h_not_box_neg
        exact h_not_dia (mcs_raw_to_dia h_implyK h_implyS h_dualBack S.property
          (mcs_neg_of_not_mem h_implyK h_implyS S.property h_not_box_neg))
      exact absurd h_phi_T'
        (mcs_not_mem_of_neg h_implyK h_implyS T'.property (hR _ h_box_neg))
    · intro h_dia
      have h_box_neg_not_S : (□¬φ) ∉ S.val :=
        mcs_not_mem_of_neg h_implyK h_implyS S.property
          (mcs_dia_to_raw h_implyK h_implyS h_dualFwd S.property h_dia)
      obtain ⟨T, hT_mcs, hST, h_neg_not_T⟩ :=
        d_mcs_box_witness h_implyK h_implyS h_efq h_peirce h_K h_D
          S.property h_box_neg_not_S
      have h_phi_T : φ ∈ T :=
        (mcs_mem_iff_neg_not_mem h_implyK h_implyS hT_mcs).mpr h_neg_not_T
      exact ⟨⟨T, hT_mcs⟩, hST,
        (d_truth_lemma h_implyK h_implyS h_efq h_peirce h_K h_D
          h_andI h_andE1 h_andE2 h_orI1 h_orI2 h_orE h_dualFwd h_dualBack
          ⟨T, hT_mcs⟩ φ).mpr h_phi_T⟩

/-! ## D Frame Condition and Canonical Witness -/

/-- The D frame condition: every model whose accessibility relation is serial. -/
def dFC : ∀ {World : Type u}, Model World Atom → Prop :=
  fun m => Relation.Serial m.r

/-- The canonical D model satisfies `dFC`: its accessibility relation is serial. -/
private theorem d_canonical_FC : dFC (CanonicalModel (@DAxiom Atom)) := by
  constructor
  intro S
  exact d_canonical_serial
    (fun φ ψ => ⟨.implyK, by decide, φ, ψ, rfl⟩)
    (fun φ ψ χ => ⟨.implyS, by decide, φ, ψ, χ, rfl⟩)
    (fun φ => ⟨.efq, by decide, φ, rfl⟩)
    (fun φ ψ => ⟨.modalK, by decide, φ, ψ, rfl⟩)
    (fun φ => ⟨.modalD, by decide, φ, rfl⟩)
    S

/-- Pre-applied D truth lemma: satisfaction at world `S` iff membership in `S.val`. -/
theorem d_truth_lemma_applied (S : CanonicalWorld (@DAxiom Atom))
    (φ : Proposition Atom) :
    Satisfies (CanonicalModel (@DAxiom Atom)) S φ ↔ φ ∈ S.val :=
  d_truth_lemma
    (fun φ ψ => ⟨.implyK, by decide, φ, ψ, rfl⟩)
    (fun φ ψ χ => ⟨.implyS, by decide, φ, ψ, χ, rfl⟩)
    (fun φ => ⟨.efq, by decide, φ, rfl⟩)
    (fun φ ψ => ⟨.peirce, by decide, φ, ψ, rfl⟩)
    (fun φ ψ => ⟨.modalK, by decide, φ, ψ, rfl⟩)
    (fun φ => ⟨.modalD, by decide, φ, rfl⟩)
    (fun φ ψ => ⟨.andI, by decide, φ, ψ, rfl⟩)
    (fun φ ψ => ⟨.andE1, by decide, φ, ψ, rfl⟩)
    (fun φ ψ => ⟨.andE2, by decide, φ, ψ, rfl⟩)
    (fun φ ψ => ⟨.orI1, by decide, φ, ψ, rfl⟩)
    (fun φ ψ => ⟨.orI2, by decide, φ, ψ, rfl⟩)
    (fun φ ψ χ => ⟨.orE, by decide, φ, ψ, χ, rfl⟩)
    (fun φ => ⟨.diaDualityFwd, by decide, φ, rfl⟩)
    (fun φ => ⟨.diaDualityBack, by decide, φ, rfl⟩)
    S φ

/-- D soundness adapter matching the `strong_soundness` callback shape.
The frame condition for D is `dFC m = Relation.Serial m.r`. -/
private theorem d_sound_cb {World : Type u} (m : Model World Atom) (w : World)
    (L : List (Proposition Atom))
    (hFC : dFC m)
    (d : DerivationTree (@DAxiom Atom) L phi)
    (h_ctx : ∀ γ ∈ L, Satisfies m w γ) : Satisfies m w phi :=
  d_soundness d m hFC w h_ctx

/-! ## D Strong Soundness -/

/-- **Strong Soundness for D**: If `phi` is set-derivable from `Gamma` using `DAxiom`,
then `phi` is a semantic consequence of `Gamma` over all serial frames.

For any serial model `m` and any world `w` satisfying all of `Gamma`, `phi`
holds at `w`. -/
theorem d_strong_soundness {Gamma : Set (Proposition Atom)} {phi : Proposition Atom}
    (h : ModalSetDerivable (@DAxiom Atom) Gamma phi)
    (World : Type u) (m : Model World Atom) (w : World)
    (h_serial : Relation.Serial m.r)
    (h_sat : ∀ γ ∈ Gamma, Satisfies m w γ) : Satisfies m w phi :=
  strong_soundness (Axioms := @DAxiom Atom) (FC := dFC)
    d_sound_cb h World m w h_serial h_sat

/-! ## D Strong Completeness -/

/-- **Strong Completeness for D**: If `phi` is a semantic consequence of `Gamma`
over all serial frames, then `phi` is set-derivable from `Gamma` using `DAxiom`.

Delegates to the parametric `strong_completeness` with `d_truth_lemma_applied`
and `d_canonical_FC`. -/
theorem d_strong_completeness {Gamma : Set (Proposition Atom)} {phi : Proposition Atom}
    (h : ∀ (World : Type u) (m : Model World Atom) (w : World),
        Relation.Serial m.r →
        (∀ γ ∈ Gamma, Satisfies m w γ) →
        Satisfies m w phi) :
    ModalSetDerivable (@DAxiom Atom) Gamma phi :=
  strong_completeness (Axioms := @DAxiom Atom) (FC := dFC)
    (fun φ ψ => ⟨.implyK, by decide, φ, ψ, rfl⟩)
    (fun φ ψ χ => ⟨.implyS, by decide, φ, ψ, χ, rfl⟩)
    (fun φ => ⟨.efq, by decide, φ, rfl⟩)
    (fun φ ψ => ⟨.peirce, by decide, φ, ψ, rfl⟩)
    d_truth_lemma_applied
    d_canonical_FC
    (fun World m w hFC h_sat => h World m w hFC h_sat)

/-! ## D Biconditional Wrapper -/

/-- **Strong Soundness and Completeness for D**:
`phi` is a semantic consequence of `Gamma` over all serial frames iff `phi` is
set-derivable from `Gamma` using `DAxiom`. -/
theorem d_strong_completeness_iff {Gamma : Set (Proposition Atom)} {phi : Proposition Atom} :
    (∀ (World : Type u) (m : Model World Atom) (w : World),
        Relation.Serial m.r →
        (∀ γ ∈ Gamma, Satisfies m w γ) →
        Satisfies m w phi) ↔
    ModalSetDerivable (@DAxiom Atom) Gamma phi :=
  ⟨d_strong_completeness, fun h World m w h_serial h_sat =>
    d_strong_soundness h World m w h_serial h_sat⟩

/-! ## D Compactness -/

/-- **Compactness for D Semantics**: If `phi` is a semantic consequence of `Gamma`
over all serial frames, there exists a finite list `L ⊆ Gamma` such that
`phi` is a semantic consequence of (members of) `L` over all serial frames. -/
theorem d_compactness {Gamma : Set (Proposition Atom)} {phi : Proposition Atom}
    (h : ∀ (World : Type u) (m : Model World Atom) (w : World),
        Relation.Serial m.r →
        (∀ γ ∈ Gamma, Satisfies m w γ) →
        Satisfies m w phi) :
    ∃ L : List (Proposition Atom),
      (∀ x ∈ L, x ∈ Gamma) ∧
      ∀ (World : Type u) (m : Model World Atom) (w : World),
        Relation.Serial m.r →
        (∀ γ ∈ {ψ | ψ ∈ L}, Satisfies m w γ) →
        Satisfies m w phi := by
  obtain ⟨L, hL_sub, hL_sem⟩ :=
    compactness (Axioms := @DAxiom Atom) (FC := dFC)
      d_sound_cb
      (fun φ ψ => ⟨.implyK, by decide, φ, ψ, rfl⟩)
      (fun φ ψ χ => ⟨.implyS, by decide, φ, ψ, χ, rfl⟩)
      (fun φ => ⟨.efq, by decide, φ, rfl⟩)
      (fun φ ψ => ⟨.peirce, by decide, φ, ψ, rfl⟩)
      d_truth_lemma_applied
      d_canonical_FC
      (fun World m w hFC h_sat => h World m w hFC h_sat)
  exact ⟨L, hL_sub, fun World m w h_serial h_sat => hL_sem World m w h_serial h_sat⟩

/-! ## D Weak Completeness (Corollary) -/

/-- **Completeness Theorem for Modal Logic D** (corollary of strong completeness):

If `phi` is valid over all serial frames, then `phi` is D-derivable
from the empty context.

This is a corollary of `d_strong_completeness` instantiated at `Gamma = ∅`. -/
theorem d_completeness (φ : Proposition Atom)
    (h_valid : ∀ (World : Type u) (m : Model World Atom),
      Relation.Serial m.r →
      ∀ w, Satisfies m w φ) :
    Derivable (@DAxiom Atom) φ :=
  ModalSetDerivable_empty_iff.mp
    (d_strong_completeness (fun W m w hSer _ => h_valid W m hSer w))

end Cslib.Logic.Modal
