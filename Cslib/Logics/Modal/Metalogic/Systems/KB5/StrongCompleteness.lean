/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Modal.Metalogic.StrongCompleteness
public import Cslib.Logics.Modal.Metalogic.Systems.KB5.Soundness
public import Cslib.Logics.Modal.Metalogic.Systems.KB5.Completeness

/-! # Strong Completeness for Modal Logic KB5

This module proves strong soundness and strong completeness for modal logic KB5:
semantic entailment from a set of premises `Gamma` (over all symmetric, Euclidean
frames) is equivalent to set-derivability using `KB5Axiom`.

## Main Results

- `kb5_strong_soundness`: Set-derivability from `Gamma` implies semantic entailment
  over all symmetric, Euclidean frames.
- `kb5_strong_completeness`: Semantic entailment over symmetric, Euclidean frames
  implies set-derivability from `Gamma`.
- `kb5_strong_completeness_iff`: Biconditional combining the above.
- `kb5_compactness`: Compactness for KB5 semantics.

## References

* [Blackburn, de Rijke, Venema, *Modal Logic*][Blackburn2001], Ch. 4, Thm 4.28 cl.2
* Cslib/Logics/Modal/Metalogic/Systems/KB5/Completeness.lean -- KB5 completeness (weak)
-/

@[expose] public section

namespace Cslib.Logic.Modal

open Cslib.Logic

universe u
variable {Atom : Type u}

/-! ## KB5 Strong Soundness -/

/-- **Strong Soundness for KB5**: If `phi` is set-derivable from `Gamma` using `KB5Axiom`,
then `phi` is a semantic consequence of `Gamma` over all symmetric, Euclidean frames.

For any symmetric, Euclidean model `m` and any world `w` satisfying all of `Gamma`,
`phi` holds at `w`. -/
theorem kb5_strong_soundness {Gamma : Set (Proposition Atom)} {phi : Proposition Atom}
    (h : ModalSetDerivable (@KB5Axiom Atom) Gamma phi)
    (World : Type u) (m : Model World Atom) (w : World)
    (h_symm : ∀ w₁ w₂, m.r w₁ w₂ → m.r w₂ w₁)
    (h_eucl : ∀ w₁ w₂ w₃, m.r w₁ w₂ → m.r w₁ w₃ → m.r w₂ w₃)
    (h_sat : ∀ γ ∈ Gamma, Satisfies m w γ) : Satisfies m w phi := by
  obtain ⟨L, hL_sub, hL_deriv⟩ := h
  obtain ⟨d⟩ := hL_deriv
  exact kb5_soundness d m h_symm h_eucl w (fun ψ hψ => h_sat ψ (hL_sub ψ hψ))

/-! ## KB5 Strong Completeness -/

/-- **Strong Completeness for KB5**: If `phi` is a semantic consequence of `Gamma`
over all symmetric, Euclidean frames, then `phi` is set-derivable from `Gamma`
using `KB5Axiom`.

Proof by contrapositive: if `phi` is not set-derivable, `Gamma ∪ {¬phi}` is
consistent; extend to MCS, apply `k_truth_lemma` in the canonical symmetric,
Euclidean frame, derive contradiction. -/
theorem kb5_strong_completeness {Gamma : Set (Proposition Atom)} {phi : Proposition Atom}
    (h : ∀ (World : Type u) (m : Model World Atom) (w : World),
        (∀ w₁ w₂, m.r w₁ w₂ → m.r w₂ w₁) →
        (∀ w₁ w₂ w₃, m.r w₁ w₂ → m.r w₁ w₃ → m.r w₂ w₃) →
        (∀ γ ∈ Gamma, Satisfies m w γ) →
        Satisfies m w phi) :
    ModalSetDerivable (@KB5Axiom Atom) Gamma phi := by
  by_contra h_not
  have h_cons := modal_not_SetDerivable_union_neg_consistent
    (fun φ ψ => .implyK φ ψ)
    (fun φ ψ χ => .implyS φ ψ χ)
    (fun φ => .efq φ)
    (fun φ ψ => .peirce φ ψ)
    h_not
  obtain ⟨M, hM_sup, hM_mcs⟩ := modal_lindenbaum h_cons
  let w : CanonicalWorld (@KB5Axiom Atom) := ⟨M, hM_mcs⟩
  have h_neg_phi : (¬phi) ∈ M :=
    hM_sup (Set.mem_union_right Gamma (Set.mem_singleton_iff.mpr rfl))
  have h_gamma_sub : ∀ ψ ∈ Gamma, ψ ∈ M :=
    fun ψ hψ => hM_sup (Set.mem_union_left _ hψ)
  have h_symm := @canonical_symm Atom (@KB5Axiom Atom)
    (fun φ ψ => .implyK φ ψ)
    (fun φ ψ χ => .implyS φ ψ χ)
    (fun φ ψ => .modalK φ ψ)
    (fun φ => .modalB φ)
  have h_eucl := @canonical_eucl_from_5 Atom (@KB5Axiom Atom)
    (fun φ ψ => .implyK φ ψ)
    (fun φ ψ χ => .implyS φ ψ χ)
    (fun φ ψ => .modalK φ ψ)
    (fun φ => .modalFive φ)
  have h_gamma_sat : ∀ γ ∈ Gamma, Satisfies (CanonicalModel (@KB5Axiom Atom)) w γ :=
    fun γ hγ => (k_truth_lemma
      (fun φ ψ => .implyK φ ψ)
      (fun φ ψ χ => .implyS φ ψ χ)
      (fun φ => .efq φ)
      (fun φ ψ => .peirce φ ψ)
      (fun φ ψ => .modalK φ ψ)
      w γ).mpr (h_gamma_sub γ hγ)
  have h_phi_sat := h (CanonicalWorld (@KB5Axiom Atom)) (CanonicalModel (@KB5Axiom Atom))
    w (fun S T hST => h_symm S T hST) (fun S T U hST hSU => h_eucl S T U hST hSU)
    h_gamma_sat
  have h_phi_M := (k_truth_lemma
    (fun φ ψ => .implyK φ ψ)
    (fun φ ψ χ => .implyS φ ψ χ)
    (fun φ => .efq φ)
    (fun φ ψ => .peirce φ ψ)
    (fun φ ψ => .modalK φ ψ)
    w phi).mp h_phi_sat
  exact mcs_bot_not_mem hM_mcs
    (modal_implication_property
      (fun φ ψ => .implyK φ ψ)
      (fun φ ψ χ => .implyS φ ψ χ)
      hM_mcs h_neg_phi h_phi_M)

/-! ## KB5 Biconditional Wrapper -/

/-- **Strong Soundness and Completeness for KB5**:
`phi` is a semantic consequence of `Gamma` over all symmetric, Euclidean frames
iff `phi` is set-derivable from `Gamma` using `KB5Axiom`. -/
theorem kb5_strong_completeness_iff {Gamma : Set (Proposition Atom)} {phi : Proposition Atom} :
    (∀ (World : Type u) (m : Model World Atom) (w : World),
        (∀ w₁ w₂, m.r w₁ w₂ → m.r w₂ w₁) →
        (∀ w₁ w₂ w₃, m.r w₁ w₂ → m.r w₁ w₃ → m.r w₂ w₃) →
        (∀ γ ∈ Gamma, Satisfies m w γ) →
        Satisfies m w phi) ↔
    ModalSetDerivable (@KB5Axiom Atom) Gamma phi :=
  ⟨kb5_strong_completeness, fun h World m w h_symm h_eucl h_sat =>
    kb5_strong_soundness h World m w h_symm h_eucl h_sat⟩

/-! ## KB5 Compactness -/

/-- **Compactness for KB5 Semantics**: If `phi` is a semantic consequence of `Gamma`
over all symmetric, Euclidean frames, there exists a finite list `L ⊆ Gamma` such
that `phi` is a semantic consequence of (members of) `L` over all symmetric, Euclidean
frames. -/
theorem kb5_compactness {Gamma : Set (Proposition Atom)} {phi : Proposition Atom}
    (h : ∀ (World : Type u) (m : Model World Atom) (w : World),
        (∀ w₁ w₂, m.r w₁ w₂ → m.r w₂ w₁) →
        (∀ w₁ w₂ w₃, m.r w₁ w₂ → m.r w₁ w₃ → m.r w₂ w₃) →
        (∀ γ ∈ Gamma, Satisfies m w γ) →
        Satisfies m w phi) :
    ∃ L : List (Proposition Atom),
      (∀ x ∈ L, x ∈ Gamma) ∧
      ∀ (World : Type u) (m : Model World Atom) (w : World),
        (∀ w₁ w₂, m.r w₁ w₂ → m.r w₂ w₁) →
        (∀ w₁ w₂ w₃, m.r w₁ w₂ → m.r w₁ w₃ → m.r w₂ w₃) →
        (∀ γ ∈ {ψ | ψ ∈ L}, Satisfies m w γ) →
        Satisfies m w phi := by
  obtain ⟨L, hL_sub, hL_deriv⟩ := kb5_strong_completeness h
  exact ⟨L, hL_sub, fun World m w h_symm h_eucl h_sat =>
    kb5_strong_soundness ⟨L, fun x hx => Set.mem_setOf_eq.mpr hx, hL_deriv⟩
      World m w h_symm h_eucl h_sat⟩

end Cslib.Logic.Modal
