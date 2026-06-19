/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module


public import Cslib.Logics.Modal.Metalogic.Completeness
public import Cslib.Logics.Modal.Metalogic.StrongCompleteness
public import Cslib.Logics.Modal.Metalogic.Systems.B.Soundness
public import Cslib.Logics.Modal.Metalogic.Systems.K.Completeness
public import Cslib.Logics.Modal.ProofSystem.Instances

/-! # Strong Completeness for Modal Logic B (KB)

This module proves strong soundness and strong completeness for modal logic B:
semantic entailment from a set of premises `Gamma` (over all symmetric frames)
is equivalent to set-derivability using `BAxiom`.

## Main Results

- `b_strong_soundness`: Set-derivability from `Gamma` implies semantic entailment
  over all symmetric frames.
- `b_strong_completeness`: Semantic entailment over symmetric frames implies
  set-derivability from `Gamma`.
- `b_strong_completeness_iff`: Biconditional combining the above.
- `b_completeness`: Weak completeness (corollary of strong completeness).
- `b_compactness`: If `phi` is a B-semantic consequence of `Gamma`, there exists
  a finite list `L ⊆ Gamma` such that `phi` is a B-semantic consequence of `L`.

## References

* [Blackburn, de Rijke, Venema, *Modal Logic*][Blackburn2001], Ch. 4, Thm 4.28 cl.2
-/

@[expose] public section

namespace Cslib.Logic.Modal

open Cslib.Logic

universe u
variable {Atom : Type u}

/-! ## B Strong Soundness -/

/-- **Strong Soundness for B**: If `phi` is set-derivable from `Gamma` using `BAxiom`,
then `phi` is a semantic consequence of `Gamma` over all symmetric frames.

For any symmetric model `m` and any world `w` satisfying all of `Gamma`, `phi`
holds at `w`. -/
theorem b_strong_soundness {Gamma : Set (Proposition Atom)} {phi : Proposition Atom}
    (h : ModalSetDerivable (@BAxiom Atom) Gamma phi)
    (World : Type u) (m : Model World Atom) (w : World)
    (h_symm : ∀ w₁ w₂, m.r w₁ w₂ → m.r w₂ w₁)
    (h_sat : ∀ γ ∈ Gamma, Satisfies m w γ) : Satisfies m w phi := by
  obtain ⟨L, hL_sub, hL_deriv⟩ := h
  obtain ⟨d⟩ := hL_deriv
  exact b_soundness d m h_symm w (fun ψ hψ => h_sat ψ (hL_sub ψ hψ))

/-! ## B Strong Completeness -/

/-- **Strong Completeness for B**: If `phi` is a semantic consequence of `Gamma`
over all symmetric frames, then `phi` is set-derivable from `Gamma` using `BAxiom`.

Proof by contrapositive: if `phi` is not set-derivable, `Gamma ∪ {¬phi}` is
consistent; extend to MCS, apply `k_truth_lemma` in the canonical symmetric
frame, derive contradiction. -/
theorem b_strong_completeness {Gamma : Set (Proposition Atom)} {phi : Proposition Atom}
    (h : ∀ (World : Type u) (m : Model World Atom) (w : World),
        (∀ w₁ w₂, m.r w₁ w₂ → m.r w₂ w₁) →
        (∀ γ ∈ Gamma, Satisfies m w γ) →
        Satisfies m w phi) :
    ModalSetDerivable (@BAxiom Atom) Gamma phi := by
  by_contra h_not
  have h_cons := modal_not_SetDerivable_union_neg_consistent
    (fun φ ψ => .implyK φ ψ)
    (fun φ ψ χ => .implyS φ ψ χ)
    (fun φ => .efq φ)
    (fun φ ψ => .peirce φ ψ)
    h_not
  obtain ⟨M, hM_sup, hM_mcs⟩ := modal_lindenbaum h_cons
  let w : CanonicalWorld (@BAxiom Atom) := ⟨M, hM_mcs⟩
  have h_neg_phi : (¬phi) ∈ M :=
    hM_sup (Set.mem_union_right Gamma (Set.mem_singleton_iff.mpr rfl))
  have h_gamma_sub : ∀ ψ ∈ Gamma, ψ ∈ M :=
    fun ψ hψ => hM_sup (Set.mem_union_left _ hψ)
  have h_symm : ∀ (S T : CanonicalWorld (@BAxiom Atom)),
      (CanonicalModel (@BAxiom Atom)).r S T →
      (CanonicalModel (@BAxiom Atom)).r T S :=
    canonical_symm
      (fun φ ψ => .implyK φ ψ)
      (fun φ ψ χ => .implyS φ ψ χ)
      (fun φ ψ => .modalK φ ψ)
      (fun φ => .modalB φ)
  have h_gamma_sat : ∀ γ ∈ Gamma, Satisfies (CanonicalModel (@BAxiom Atom)) w γ :=
    fun γ hγ => (k_truth_lemma
      (fun φ ψ => .implyK φ ψ)
      (fun φ ψ χ => .implyS φ ψ χ)
      (fun φ => .efq φ)
      (fun φ ψ => .peirce φ ψ)
      (fun φ ψ => .modalK φ ψ)
      w γ).mpr (h_gamma_sub γ hγ)
  have h_phi_sat := h (CanonicalWorld (@BAxiom Atom)) (CanonicalModel (@BAxiom Atom))
    w (fun S T hST => h_symm S T hST) h_gamma_sat
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

/-! ## B Biconditional Wrapper -/

/-- **Strong Soundness and Completeness for B**:
`phi` is a semantic consequence of `Gamma` over all symmetric frames iff `phi` is
set-derivable from `Gamma` using `BAxiom`. -/
theorem b_strong_completeness_iff {Gamma : Set (Proposition Atom)} {phi : Proposition Atom} :
    (∀ (World : Type u) (m : Model World Atom) (w : World),
        (∀ w₁ w₂, m.r w₁ w₂ → m.r w₂ w₁) →
        (∀ γ ∈ Gamma, Satisfies m w γ) →
        Satisfies m w phi) ↔
    ModalSetDerivable (@BAxiom Atom) Gamma phi :=
  ⟨b_strong_completeness, fun h World m w h_symm h_sat =>
    b_strong_soundness h World m w h_symm h_sat⟩

/-! ## B Compactness -/

/-- **Compactness for B Semantics**: If `phi` is a semantic consequence of `Gamma`
over all symmetric frames, there exists a finite list `L ⊆ Gamma` such that
`phi` is a semantic consequence of (members of) `L` over all symmetric frames. -/
theorem b_compactness {Gamma : Set (Proposition Atom)} {phi : Proposition Atom}
    (h : ∀ (World : Type u) (m : Model World Atom) (w : World),
        (∀ w₁ w₂, m.r w₁ w₂ → m.r w₂ w₁) →
        (∀ γ ∈ Gamma, Satisfies m w γ) →
        Satisfies m w phi) :
    ∃ L : List (Proposition Atom),
      (∀ x ∈ L, x ∈ Gamma) ∧
      ∀ (World : Type u) (m : Model World Atom) (w : World),
        (∀ w₁ w₂, m.r w₁ w₂ → m.r w₂ w₁) →
        (∀ γ ∈ {ψ | ψ ∈ L}, Satisfies m w γ) →
        Satisfies m w phi := by
  obtain ⟨L, hL_sub, hL_deriv⟩ := b_strong_completeness h
  exact ⟨L, hL_sub, fun World m w h_symm h_sat =>
    b_strong_soundness ⟨L, fun x hx => Set.mem_setOf_eq.mpr hx, hL_deriv⟩
      World m w h_symm h_sat⟩

/-! ## B Weak Completeness (Corollary) -/

/-- **Completeness Theorem for Modal Logic B** (corollary of strong completeness):

If `phi` is valid over all symmetric frames, then `phi` is B-derivable
from the empty context.

This is a corollary of `b_strong_completeness` instantiated at `Gamma = ∅`. -/
theorem b_completeness (φ : Proposition Atom)
    (h_valid : ∀ (World : Type u) (m : Model World Atom),
      (∀ w₁ w₂, m.r w₁ w₂ → m.r w₂ w₁) → ∀ w, Satisfies m w φ) :
    Derivable (@BAxiom Atom) φ :=
  ModalSetDerivable_empty_iff.mp
    (b_strong_completeness (fun W m w hSymm _ => h_valid W m hSymm w))

end Cslib.Logic.Modal
