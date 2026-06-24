/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Modal.Metalogic.Completeness
public import Cslib.Logics.Modal.Metalogic.Systems.K.Soundness
public import Cslib.Logics.Modal.ProofSystem.Instances

/-! # Completeness Theorem for Modal Logic K

This module proves completeness for modal logic K via the canonical Kripke model
construction, following Blackburn, de Rijke, Venema "Modal Logic" (2002), Theorem 4.23.

The key challenge is the K-specific Existence Lemma (BRV Lemma 4.20): the existing
`mcs_box_witness` requires axiom T, which K does not have. We provide a K-specific
version `k_mcs_box_witness` that uses EFQ + `derive_box_from_box_context` instead.

## Main Results

- `k_derive_box_from_inconsistency`: K-specific consistency helper (no `h_T`).
- `k_mcs_box_witness`: K-specific Existence Lemma (BRV Lemma 4.20 for K).
- `k_truth_lemma`: K-specific Truth Lemma (BRV Lemma 4.21 for K).
The weak completeness theorem `k_completeness` is derived below as a
corollary of strong completeness via `ModalSetDerivable_empty_iff`.

## References

* Blackburn, de Rijke, Venema - Modal Logic (Ch. 4, Theorems 4.20-4.23)
-/

@[expose] public section

namespace Cslib.Logic.Modal

open Cslib.Logic

universe u
variable {Atom : Type u}

/-! ## K-Specific Box Witness Consistency (BRV Lemma 4.20) -/

/-- K-specific version of `derive_box_from_inconsistency` without axiom T.

When `neg phi not in L`, all elements of L have box-versions in S. From `L |- bot`,
we derive `L |- phi` via EFQ, then use `derive_box_from_box_context` to get
`box phi in S`, contradicting `h_not_box`. -/
theorem k_derive_box_from_inconsistency
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
  · -- Case: neg phi in L -- identical to existing code (does not use h_T)
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
    have efq_ax : DerivationTree Axioms L (Proposition.bot.imp φ) :=
      .weakening [] L _ (.ax [] _ (h_efq φ)) (fun _ h => nomatch h)
    have d_phi : DerivationTree Axioms L φ :=
      .modus_ponens L .bot φ efq_ax d_bot
    exact h_not_box (derive_box_from_box_context h_implyK h_implyS h_K h_mcs
      d_phi h_all_box)

/-! ## K-Specific Box Witness (BRV Lemma 4.20 for K) -/

/-- **K-Specific Box Witness** (BRV Lemma 4.20 for K):
If `box phi not in S` and `S` is MCS, then there exists an MCS `T`
such that `forall psi, box psi in S -> psi in T` and `phi not in T`.
No axiom T hypothesis needed. -/
theorem k_mcs_box_witness
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
    {S : Set (Proposition Atom)} (h_mcs : SetMaximalConsistent Axioms S)
    {φ : Proposition Atom} (h_not_box : (□φ) ∉ S) :
    ∃ T : Set (Proposition Atom), SetMaximalConsistent Axioms T ∧
      (∀ ψ, (□ψ) ∈ S → ψ ∈ T) ∧ φ ∉ T := by
  let W := {ψ : Proposition Atom | (□ψ) ∈ S} ∪ {(¬φ)}
  have hW : SetConsistent Axioms W := by
    intro L hL
    unfold Metalogic.Consistent
    intro ⟨d_bot⟩
    exact k_derive_box_from_inconsistency h_implyK h_implyS h_efq h_peirce h_K
      h_mcs h_not_box hL d_bot
  obtain ⟨T, hWT, hT_mcs⟩ := modal_lindenbaum hW
  refine ⟨T, hT_mcs, ?_, ?_⟩
  · intro ψ h_box
    exact hWT (Set.mem_union_left _ h_box)
  · have h_neg : (¬φ) ∈ T :=
      hWT (Set.mem_union_right _ (Set.mem_singleton _))
    exact mcs_not_mem_of_neg h_implyK h_implyS hT_mcs h_neg

/-! ## K-Specific Truth Lemma (BRV Lemma 4.21 for K) -/

/-- **K-Specific Truth Lemma** (BRV Lemma 4.21 for K):
For any canonical world `S` and formula `phi`,
`Satisfies (CanonicalModel Axioms) S phi <-> phi in S.val`.
Uses `k_mcs_box_witness` instead of `mcs_box_witness` (no axiom T). -/
theorem k_truth_lemma
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
          (k_truth_lemma h_implyK h_implyS h_efq h_peirce h_K S φ).mpr h_phi_S
        have h_psi_S :=
          (k_truth_lemma h_implyK h_implyS h_efq h_peirce h_K S ψ).mp
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
      exact (k_truth_lemma h_implyK h_implyS h_efq h_peirce h_K S ψ).mpr
        (modal_implication_property h_implyK h_implyS S.property h_mem
          ((k_truth_lemma h_implyK h_implyS h_efq h_peirce h_K S φ).mp
            h_sat_phi))
  | .box φ => by
    constructor
    · intro h_sat
      by_contra h_not_box
      obtain ⟨T, hT_mcs, hST, h_phi_not_T⟩ :=
        k_mcs_box_witness h_implyK h_implyS h_efq h_peirce h_K
          S.property h_not_box
      exact h_phi_not_T
        ((k_truth_lemma h_implyK h_implyS h_efq h_peirce h_K
          ⟨T, hT_mcs⟩ φ).mp (h_sat ⟨T, hT_mcs⟩ hST))
    · intro h_box T hST
      exact (k_truth_lemma h_implyK h_implyS h_efq h_peirce h_K T φ).mpr
        (hST φ h_box)

/-- Pre-applied K truth lemma: satisfaction at world `S` iff membership in `S.val`. -/
private theorem k_truth_lemma_applied (S : CanonicalWorld (@KAxiom Atom))
    (φ : Proposition Atom) :
    Satisfies (CanonicalModel (@KAxiom Atom)) S φ ↔ φ ∈ S.val :=
  k_truth_lemma
    (fun φ ψ => .implyK φ ψ)
    (fun φ ψ χ => .implyS φ ψ χ)
    (fun φ => .efq φ)
    (fun φ ψ => .peirce φ ψ)
    (fun φ ψ => .modalK φ ψ)
    S φ

/-- K soundness adapter matching the `strong_soundness` callback shape.
The frame condition for K is trivial (`fun _ => True`), so the hypothesis is discarded. -/
private theorem k_sound_cb {World : Type u} (m : Model World Atom) (w : World)
    (L : List (Proposition Atom))
    (_ : (fun (_ : Model World Atom) => True) m)
    (d : DerivationTree (@KAxiom Atom) L phi)
    (h_ctx : ∀ γ ∈ L, Satisfies m w γ) : Satisfies m w phi :=
  k_soundness d m w h_ctx

/-! ## K Strong Soundness -/

/-- **Strong Soundness for K**: If `phi` is set-derivable from `Gamma` using `KAxiom`,
then `phi` is a semantic consequence of `Gamma` over all frames.

Delegates to the parametric `strong_soundness` with `k_sound_cb`. -/
theorem k_strong_soundness {Gamma : Set (Proposition Atom)} {phi : Proposition Atom}
    (h : ModalSetDerivable (@KAxiom Atom) Gamma phi) :
    ModalSemanticEntails (fun _ => True) Gamma phi :=
  (strong_completeness_iff (Axioms := @KAxiom Atom) (FC := fun _ => True)
    k_sound_cb
    (fun φ ψ => .implyK φ ψ)
    (fun φ ψ χ => .implyS φ ψ χ)
    (fun φ => .efq φ)
    (fun φ ψ => .peirce φ ψ)
    k_truth_lemma_applied
    trivial).mpr h

/-! ## K Strong Completeness -/

/-- **Strong Completeness for K**: If `phi` is a semantic consequence of `Gamma`
over all frames, then `phi` is set-derivable from `Gamma` using `KAxiom`.

Delegates to the parametric `strong_completeness` with K-specific callbacks. -/
theorem k_strong_completeness {Gamma : Set (Proposition Atom)} {phi : Proposition Atom}
    (h : ModalSemanticEntails (fun _ => True) Gamma phi) :
    ModalSetDerivable (@KAxiom Atom) Gamma phi :=
  (strong_completeness_iff (Axioms := @KAxiom Atom) (FC := fun _ => True)
    k_sound_cb
    (fun φ ψ => .implyK φ ψ)
    (fun φ ψ χ => .implyS φ ψ χ)
    (fun φ => .efq φ)
    (fun φ ψ => .peirce φ ψ)
    k_truth_lemma_applied
    trivial).mp h

/-! ## K Biconditional Wrapper -/

/-- **Strong Soundness and Completeness for K**:
`phi` is a semantic consequence of `Gamma` over all frames iff `phi` is
set-derivable from `Gamma` using `KAxiom`.

Delegates to the parametric `strong_completeness_iff`. -/
theorem k_strong_completeness_iff {Gamma : Set (Proposition Atom)} {phi : Proposition Atom} :
    ModalSemanticEntails (fun _ => True) Gamma phi ↔
    ModalSetDerivable (@KAxiom Atom) Gamma phi :=
  strong_completeness_iff (Axioms := @KAxiom Atom) (FC := fun _ => True)
    k_sound_cb
    (fun φ ψ => .implyK φ ψ)
    (fun φ ψ χ => .implyS φ ψ χ)
    (fun φ => .efq φ)
    (fun φ ψ => .peirce φ ψ)
    k_truth_lemma_applied
    trivial

/-! ## K Compactness -/

/-- **Compactness for K Semantics**: If `phi` is a semantic consequence of `Gamma`
over all frames, there exists a finite list `L ⊆ Gamma` such that `phi` is a
semantic consequence of (members of) `L` over all frames.

Delegates to the parametric `compactness`. -/
theorem k_compactness {Gamma : Set (Proposition Atom)} {phi : Proposition Atom}
    (h : ModalSemanticEntails (fun _ => True) Gamma phi) :
    ∃ L : List (Proposition Atom),
      (∀ x ∈ L, x ∈ Gamma) ∧
      ModalSemanticEntails (fun _ => True) {ψ | ψ ∈ L} phi :=
  compactness (Axioms := @KAxiom Atom) (FC := fun _ => True)
    k_sound_cb
    (fun φ ψ => .implyK φ ψ)
    (fun φ ψ χ => .implyS φ ψ χ)
    (fun φ => .efq φ)
    (fun φ ψ => .peirce φ ψ)
    k_truth_lemma_applied
    trivial
    h

/-! ## K Weak Completeness (Corollary) -/

/-- **Completeness Theorem for Modal Logic K** (corollary of strong completeness):

If `phi` is valid over all frames (no frame conditions), then `phi`
is K-derivable from the empty context.

Delegates to the parametric `weak_completeness`. -/
theorem k_completeness (φ : Proposition Atom)
    (h_valid : ∀ (World : Type u) (m : Model World Atom),
      ∀ w, Satisfies m w φ) :
    Derivable (@KAxiom Atom) φ :=
  weak_completeness (Axioms := @KAxiom Atom) (FC := fun _ => True)
    (fun φ ψ => .implyK φ ψ)
    (fun φ ψ χ => .implyS φ ψ χ)
    (fun φ => .efq φ)
    (fun φ ψ => .peirce φ ψ)
    k_truth_lemma_applied
    trivial
    (fun W m _ w => h_valid W m w)

end Cslib.Logic.Modal
