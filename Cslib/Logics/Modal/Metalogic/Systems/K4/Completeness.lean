/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module


public import Cslib.Logics.Modal.Metalogic.Completeness
public import Cslib.Logics.Modal.Metalogic.StrongCompleteness
public import Cslib.Logics.Modal.Metalogic.Systems.K4.Soundness
public import Cslib.Logics.Modal.Metalogic.Systems.K.Completeness
public import Cslib.Logics.Modal.ProofSystem.Instances

/-! # Strong Completeness for Modal Logic K4

This module proves strong soundness and strong completeness for modal logic K4:
semantic entailment from a set of premises `Gamma` (over all transitive frames)
is equivalent to set-derivability using `K4Axiom`.

## Main Results

- `k4_strong_soundness`: Set-derivability from `Gamma` implies semantic entailment.
- `k4_strong_completeness`: Semantic entailment implies set-derivability from `Gamma`.
- `k4_strong_completeness_iff`: Biconditional combining the above.
- `k4_completeness`: Weak completeness (corollary of strong completeness).
- `k4_compactness`: Compactness for K4 semantics.

## References

* [Blackburn, de Rijke, Venema, *Modal Logic*][Blackburn2001], Ch. 4, Thm 4.27
-/

@[expose] public section

namespace Cslib.Logic.Modal

open Cslib.Logic

universe u
variable {Atom : Type u}

/-! ## K4 Strong Soundness -/

/-- **Strong Soundness for K4**: If `phi` is set-derivable from `Gamma` using `K4Axiom`,
then `phi` is a semantic consequence of `Gamma` over all transitive frames.

For any transitive model `m` and any world `w` satisfying all of `Gamma`, `phi`
holds at `w`. -/
theorem k4_strong_soundness {Gamma : Set (Proposition Atom)} {phi : Proposition Atom}
    (h : ModalSetDerivable (@K4Axiom Atom) Gamma phi)
    (World : Type u) (m : Model World Atom) (w : World)
    (h_trans : ∀ w₁ w₂ w₃, m.r w₁ w₂ → m.r w₂ w₃ → m.r w₁ w₃)
    (h_sat : ∀ γ ∈ Gamma, Satisfies m w γ) : Satisfies m w phi := by
  obtain ⟨L, hL_sub, hL_deriv⟩ := h
  obtain ⟨d⟩ := hL_deriv
  exact k4_soundness d m h_trans w (fun ψ hψ => h_sat ψ (hL_sub ψ hψ))

/-! ## K4 Strong Completeness -/

/-- **Strong Completeness for K4**: If `phi` is a semantic consequence of `Gamma`
over all transitive frames, then `phi` is set-derivable from `Gamma` using `K4Axiom`. -/
theorem k4_strong_completeness {Gamma : Set (Proposition Atom)} {phi : Proposition Atom}
    (h : ∀ (World : Type u) (m : Model World Atom) (w : World),
        (∀ w₁ w₂ w₃, m.r w₁ w₂ → m.r w₂ w₃ → m.r w₁ w₃) →
        (∀ γ ∈ Gamma, Satisfies m w γ) →
        Satisfies m w phi) :
    ModalSetDerivable (@K4Axiom Atom) Gamma phi := by
  by_contra h_not
  have h_cons := modal_not_SetDerivable_union_neg_consistent
    (fun φ ψ => .implyK φ ψ)
    (fun φ ψ χ => .implyS φ ψ χ)
    (fun φ => .efq φ)
    (fun φ ψ => .peirce φ ψ)
    h_not
  obtain ⟨M, hM_sup, hM_mcs⟩ := modal_lindenbaum h_cons
  let w : CanonicalWorld (@K4Axiom Atom) := ⟨M, hM_mcs⟩
  have h_neg_phi : (¬phi) ∈ M :=
    hM_sup (Set.mem_union_right Gamma (Set.mem_singleton_iff.mpr rfl))
  have h_gamma_sub : ∀ ψ ∈ Gamma, ψ ∈ M :=
    fun ψ hψ => hM_sup (Set.mem_union_left _ hψ)
  have h_trans := @canonical_trans Atom (@K4Axiom Atom)
    (fun φ ψ => .implyK φ ψ)
    (fun φ ψ χ => .implyS φ ψ χ)
    (fun φ => .modalFour φ)
  have h_gamma_sat : ∀ γ ∈ Gamma, Satisfies (CanonicalModel (@K4Axiom Atom)) w γ :=
    fun γ hγ => (k_truth_lemma
      (fun φ ψ => .implyK φ ψ)
      (fun φ ψ χ => .implyS φ ψ χ)
      (fun φ => .efq φ)
      (fun φ ψ => .peirce φ ψ)
      (fun φ ψ => .modalK φ ψ)
      w γ).mpr (h_gamma_sub γ hγ)
  have h_phi_sat := h (CanonicalWorld (@K4Axiom Atom)) (CanonicalModel (@K4Axiom Atom))
    w h_trans h_gamma_sat
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

/-! ## K4 Biconditional Wrapper -/

/-- **Strong Soundness and Completeness for K4**:
`phi` is a semantic consequence of `Gamma` over all transitive frames iff `phi` is
set-derivable from `Gamma` using `K4Axiom`. -/
theorem k4_strong_completeness_iff {Gamma : Set (Proposition Atom)} {phi : Proposition Atom} :
    (∀ (World : Type u) (m : Model World Atom) (w : World),
        (∀ w₁ w₂ w₃, m.r w₁ w₂ → m.r w₂ w₃ → m.r w₁ w₃) →
        (∀ γ ∈ Gamma, Satisfies m w γ) →
        Satisfies m w phi) ↔
    ModalSetDerivable (@K4Axiom Atom) Gamma phi :=
  ⟨k4_strong_completeness, fun h World m w h_trans h_sat =>
    k4_strong_soundness h World m w h_trans h_sat⟩

/-! ## K4 Compactness -/

/-- **Compactness for K4 Semantics**: If `phi` is a semantic consequence of `Gamma`
over all transitive frames, there exists a finite list `L ⊆ Gamma` such that
`phi` is a semantic consequence of (members of) `L` over all transitive frames. -/
theorem k4_compactness {Gamma : Set (Proposition Atom)} {phi : Proposition Atom}
    (h : ∀ (World : Type u) (m : Model World Atom) (w : World),
        (∀ w₁ w₂ w₃, m.r w₁ w₂ → m.r w₂ w₃ → m.r w₁ w₃) →
        (∀ γ ∈ Gamma, Satisfies m w γ) →
        Satisfies m w phi) :
    ∃ L : List (Proposition Atom),
      (∀ x ∈ L, x ∈ Gamma) ∧
      ∀ (World : Type u) (m : Model World Atom) (w : World),
        (∀ w₁ w₂ w₃, m.r w₁ w₂ → m.r w₂ w₃ → m.r w₁ w₃) →
        (∀ γ ∈ {ψ | ψ ∈ L}, Satisfies m w γ) →
        Satisfies m w phi := by
  obtain ⟨L, hL_sub, hL_deriv⟩ := k4_strong_completeness h
  exact ⟨L, hL_sub, fun World m w h_trans h_sat =>
    k4_strong_soundness ⟨L, fun x hx => Set.mem_setOf_eq.mpr hx, hL_deriv⟩
      World m w h_trans h_sat⟩

/-! ## K4 Weak Completeness (Corollary) -/

/-- **Completeness Theorem for K4 Modal Logic** (corollary of strong completeness):

If `phi` is valid over all transitive frames, then `phi` is K4-derivable
from the empty context.

This is a corollary of `k4_strong_completeness` instantiated at `Gamma = ∅`. -/
theorem k4_completeness (φ : Proposition Atom)
    (h_valid : ∀ (World : Type u) (m : Model World Atom),
      (∀ w₁ w₂ w₃, m.r w₁ w₂ → m.r w₂ w₃ → m.r w₁ w₃) →
      ∀ w, Satisfies m w φ) :
    Derivable (@K4Axiom Atom) φ :=
  ModalSetDerivable_empty_iff.mp
    (k4_strong_completeness (fun W m w hTrans _ => h_valid W m hTrans w))

end Cslib.Logic.Modal
