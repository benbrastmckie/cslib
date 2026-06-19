/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Modal.Metalogic.Completeness
public import Cslib.Logics.Modal.Metalogic.Systems.K5.Soundness
public import Cslib.Logics.Modal.Metalogic.Systems.K.Completeness

/-! # Strong Completeness for Modal Logic K5

This module proves strong soundness and strong completeness for modal logic K5:
semantic entailment from a set of premises `Gamma` (over all Euclidean frames)
is equivalent to set-derivability using `K5Axiom`.

## Main Results

- `k5_strong_soundness`: Set-derivability from `Gamma` implies semantic entailment.
- `k5_strong_completeness`: Semantic entailment implies set-derivability from `Gamma`.
- `k5_strong_completeness_iff`: Biconditional combining the above.
- `k5_completeness`: Weak completeness (corollary of strong completeness).
- `k5_compactness`: Compactness for K5 semantics.

## References

* [Blackburn, de Rijke, Venema, *Modal Logic*][Blackburn2001], Ch. 4
-/

@[expose] public section

namespace Cslib.Logic.Modal

open Cslib.Logic

universe u
variable {Atom : Type u}

/-! ## K5 Strong Soundness -/

/-- **Strong Soundness for K5**: If `phi` is set-derivable from `Gamma` using `K5Axiom`,
then `phi` is a semantic consequence of `Gamma` over all Euclidean frames.

For any Euclidean model `m` and any world `w` satisfying all of `Gamma`, `phi`
holds at `w`. -/
theorem k5_strong_soundness {Gamma : Set (Proposition Atom)} {phi : Proposition Atom}
    (h : ModalSetDerivable (@K5Axiom Atom) Gamma phi)
    (World : Type u) (m : Model World Atom) (w : World)
    (h_eucl : ∀ w₁ w₂ w₃, m.r w₁ w₂ → m.r w₁ w₃ → m.r w₂ w₃)
    (h_sat : ∀ γ ∈ Gamma, Satisfies m w γ) : Satisfies m w phi := by
  obtain ⟨L, hL_sub, hL_deriv⟩ := h
  obtain ⟨d⟩ := hL_deriv
  exact k5_soundness d m h_eucl w (fun ψ hψ => h_sat ψ (hL_sub ψ hψ))

/-! ## K5 Strong Completeness -/

/-- **Strong Completeness for K5**: If `phi` is a semantic consequence of `Gamma`
over all Euclidean frames, then `phi` is set-derivable from `Gamma` using `K5Axiom`. -/
theorem k5_strong_completeness {Gamma : Set (Proposition Atom)} {phi : Proposition Atom}
    (h : ∀ (World : Type u) (m : Model World Atom) (w : World),
        (∀ w₁ w₂ w₃, m.r w₁ w₂ → m.r w₁ w₃ → m.r w₂ w₃) →
        (∀ γ ∈ Gamma, Satisfies m w γ) →
        Satisfies m w phi) :
    ModalSetDerivable (@K5Axiom Atom) Gamma phi := by
  by_contra h_not
  have h_cons := modal_not_SetDerivable_union_neg_consistent
    (fun φ ψ => .implyK φ ψ)
    (fun φ ψ χ => .implyS φ ψ χ)
    (fun φ => .efq φ)
    (fun φ ψ => .peirce φ ψ)
    h_not
  obtain ⟨M, hM_sup, hM_mcs⟩ := modal_lindenbaum h_cons
  let w : CanonicalWorld (@K5Axiom Atom) := ⟨M, hM_mcs⟩
  have h_neg_phi : (¬phi) ∈ M :=
    hM_sup (Set.mem_union_right Gamma (Set.mem_singleton_iff.mpr rfl))
  have h_gamma_sub : ∀ ψ ∈ Gamma, ψ ∈ M :=
    fun ψ hψ => hM_sup (Set.mem_union_left _ hψ)
  have h_eucl := @canonical_eucl_from_5 Atom (@K5Axiom Atom)
    (fun φ ψ => .implyK φ ψ)
    (fun φ ψ χ => .implyS φ ψ χ)
    (fun φ ψ => .modalK φ ψ)
    (fun φ => .modalFive φ)
  have h_gamma_sat : ∀ γ ∈ Gamma, Satisfies (CanonicalModel (@K5Axiom Atom)) w γ :=
    fun γ hγ => (k_truth_lemma
      (fun φ ψ => .implyK φ ψ)
      (fun φ ψ χ => .implyS φ ψ χ)
      (fun φ => .efq φ)
      (fun φ ψ => .peirce φ ψ)
      (fun φ ψ => .modalK φ ψ)
      w γ).mpr (h_gamma_sub γ hγ)
  have h_phi_sat := h (CanonicalWorld (@K5Axiom Atom)) (CanonicalModel (@K5Axiom Atom))
    w h_eucl h_gamma_sat
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

/-! ## K5 Biconditional Wrapper -/

/-- **Strong Soundness and Completeness for K5**:
`phi` is a semantic consequence of `Gamma` over all Euclidean frames iff `phi` is
set-derivable from `Gamma` using `K5Axiom`. -/
theorem k5_strong_completeness_iff {Gamma : Set (Proposition Atom)} {phi : Proposition Atom} :
    (∀ (World : Type u) (m : Model World Atom) (w : World),
        (∀ w₁ w₂ w₃, m.r w₁ w₂ → m.r w₁ w₃ → m.r w₂ w₃) →
        (∀ γ ∈ Gamma, Satisfies m w γ) →
        Satisfies m w phi) ↔
    ModalSetDerivable (@K5Axiom Atom) Gamma phi :=
  ⟨k5_strong_completeness, fun h World m w h_eucl h_sat =>
    k5_strong_soundness h World m w h_eucl h_sat⟩

/-! ## K5 Compactness -/

/-- **Compactness for K5 Semantics**: If `phi` is a semantic consequence of `Gamma`
over all Euclidean frames, there exists a finite list `L ⊆ Gamma` such that
`phi` is a semantic consequence of (members of) `L` over all Euclidean frames. -/
theorem k5_compactness {Gamma : Set (Proposition Atom)} {phi : Proposition Atom}
    (h : ∀ (World : Type u) (m : Model World Atom) (w : World),
        (∀ w₁ w₂ w₃, m.r w₁ w₂ → m.r w₁ w₃ → m.r w₂ w₃) →
        (∀ γ ∈ Gamma, Satisfies m w γ) →
        Satisfies m w phi) :
    ∃ L : List (Proposition Atom),
      (∀ x ∈ L, x ∈ Gamma) ∧
      ∀ (World : Type u) (m : Model World Atom) (w : World),
        (∀ w₁ w₂ w₃, m.r w₁ w₂ → m.r w₁ w₃ → m.r w₂ w₃) →
        (∀ γ ∈ {ψ | ψ ∈ L}, Satisfies m w γ) →
        Satisfies m w phi := by
  obtain ⟨L, hL_sub, hL_deriv⟩ := k5_strong_completeness h
  exact ⟨L, hL_sub, fun World m w h_eucl h_sat =>
    k5_strong_soundness ⟨L, fun x hx => Set.mem_setOf_eq.mpr hx, hL_deriv⟩
      World m w h_eucl h_sat⟩

/-! ## K5 Weak Completeness (Corollary) -/

/-- **Completeness Theorem for Modal Logic K5** (corollary of strong completeness):

If `phi` is valid over all Euclidean frames, then `phi` is K5-derivable
from the empty context.

This is a corollary of `k5_strong_completeness` instantiated at `Gamma = ∅`. -/
theorem k5_completeness (φ : Proposition Atom)
    (h_valid : ∀ (World : Type u) (m : Model World Atom),
      (∀ w₁ w₂ w₃, m.r w₁ w₂ → m.r w₁ w₃ → m.r w₂ w₃) →
      ∀ w, Satisfies m w φ) :
    Derivable (@K5Axiom Atom) φ :=
  ModalSetDerivable_empty_iff.mp
    (k5_strong_completeness (fun W m w hEucl _ => h_valid W m hEucl w))

end Cslib.Logic.Modal
