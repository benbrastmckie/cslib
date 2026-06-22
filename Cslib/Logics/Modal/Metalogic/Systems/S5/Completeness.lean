/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Modal.Metalogic.Completeness
public import Cslib.Logics.Modal.Metalogic.Systems.S5.Soundness

/-! # Strong Completeness for Modal Logic S5

This module proves strong soundness and strong completeness for modal logic S5:
semantic entailment from a set of premises `Gamma` (over all reflexive, transitive,
Euclidean frames) is equivalent to set-derivability using `ModalAxiom`.

## Main Results

- `s5_strong_soundness`: Set-derivability from `Gamma` implies semantic entailment
  over all S5 frames.
- `s5_strong_completeness`: Semantic entailment over S5 frames implies
  set-derivability from `Gamma`.
- `s5_strong_completeness_iff`: Biconditional combining the above.
- `s5_completeness`: Weak completeness (corollary of strong completeness).
- `s5_compactness`: If `phi` is an S5-semantic consequence of `Gamma`, there exists
  a finite list `L ⊆ Gamma` such that `phi` is an S5-semantic consequence of `L`.

## References

* [Blackburn, de Rijke, Venema, *Modal Logic*][Blackburn2001], Ch. 4, Thm 4.28
-/

@[expose] public section

namespace Cslib.Logic.Modal

open Cslib.Logic

universe u
variable {Atom : Type u}

/-! ## S5 Strong Soundness -/

/-- **Strong Soundness for S5**: If `phi` is set-derivable from `Gamma` using `ModalAxiom`,
then `phi` is a semantic consequence of `Gamma` over all S5 frames (reflexive, transitive,
Euclidean).

For any S5 model `m` and any world `w` satisfying all of `Gamma`, `phi` holds at `w`. -/
theorem s5_strong_soundness {Gamma : Set (Proposition Atom)} {phi : Proposition Atom}
    (h : ModalSetDerivable (@ModalAxiom Atom) Gamma phi)
    (World : Type u) (m : Model World Atom) (w : World)
    (h_refl : ∀ w, m.r w w)
    (h_trans : ∀ w₁ w₂ w₃, m.r w₁ w₂ → m.r w₂ w₃ → m.r w₁ w₃)
    (h_eucl : ∀ w₁ w₂ w₃, m.r w₁ w₂ → m.r w₁ w₃ → m.r w₂ w₃)
    (h_sat : ∀ γ ∈ Gamma, Satisfies m w γ) : Satisfies m w phi := by
  obtain ⟨L, hL_sub, hL_deriv⟩ := h
  obtain ⟨d⟩ := hL_deriv
  exact s5_soundness d m h_refl h_trans h_eucl w (fun ψ hψ => h_sat ψ (hL_sub ψ hψ))

/-! ## S5 Strong Completeness -/

/-- **Strong Completeness for S5**: If `phi` is a semantic consequence of `Gamma`
over all S5 frames, then `phi` is set-derivable from `Gamma` using `ModalAxiom`.

Proof by contrapositive: if `phi` is not set-derivable, `Gamma ∪ {¬phi}` is
consistent; extend to MCS, apply `truth_lemma` in the canonical S5 frame
(reflexive via `canonical_refl`, transitive via `canonical_trans`, Euclidean via
`canonical_eucl`), derive contradiction. -/
theorem s5_strong_completeness {Gamma : Set (Proposition Atom)} {phi : Proposition Atom}
    (h : ∀ (World : Type u) (m : Model World Atom) (w : World),
        (∀ w, m.r w w) →
        (∀ w₁ w₂ w₃, m.r w₁ w₂ → m.r w₂ w₃ → m.r w₁ w₃) →
        (∀ w₁ w₂ w₃, m.r w₁ w₂ → m.r w₁ w₃ → m.r w₂ w₃) →
        (∀ γ ∈ Gamma, Satisfies m w γ) →
        Satisfies m w phi) :
    ModalSetDerivable (@ModalAxiom Atom) Gamma phi := by
  by_contra h_not
  have h_cons := modal_not_SetDerivable_union_neg_consistent
    (fun φ ψ => .implyK φ ψ)
    (fun φ ψ χ => .implyS φ ψ χ)
    (fun φ => .efq φ)
    (fun φ ψ => .peirce φ ψ)
    h_not
  obtain ⟨M, hM_sup, hM_mcs⟩ := modal_lindenbaum h_cons
  let w : CanonicalWorld (@ModalAxiom Atom) := ⟨M, hM_mcs⟩
  have h_neg_phi : (¬phi) ∈ M :=
    hM_sup (Set.mem_union_right Gamma (Set.mem_singleton_iff.mpr rfl))
  have h_gamma_sub : ∀ ψ ∈ Gamma, ψ ∈ M :=
    fun ψ hψ => hM_sup (Set.mem_union_left _ hψ)
  have h_refl : ∀ (S : CanonicalWorld (@ModalAxiom Atom)),
      (CanonicalModel (@ModalAxiom Atom)).r S S :=
    fun S => canonical_refl
      (fun φ ψ => .implyK φ ψ)
      (fun φ ψ χ => .implyS φ ψ χ)
      (fun φ => .modalT φ)
      S
  have h_trans : ∀ (S T U : CanonicalWorld (@ModalAxiom Atom)),
      (CanonicalModel (@ModalAxiom Atom)).r S T →
      (CanonicalModel (@ModalAxiom Atom)).r T U →
      (CanonicalModel (@ModalAxiom Atom)).r S U :=
    canonical_trans
      (fun φ ψ => .implyK φ ψ)
      (fun φ ψ χ => .implyS φ ψ χ)
      (fun φ => .modalFour φ)
  have h_eucl : ∀ (S T U : CanonicalWorld (@ModalAxiom Atom)),
      (CanonicalModel (@ModalAxiom Atom)).r S T →
      (CanonicalModel (@ModalAxiom Atom)).r S U →
      (CanonicalModel (@ModalAxiom Atom)).r T U :=
    canonical_eucl
      (fun φ ψ => .implyK φ ψ)
      (fun φ ψ χ => .implyS φ ψ χ)
      (fun φ => .modalFour φ)
      (fun φ => .modalB φ)
      (fun φ ψ => .modalK φ ψ)
  have h_gamma_sat : ∀ γ ∈ Gamma, Satisfies (CanonicalModel (@ModalAxiom Atom)) w γ :=
    fun γ hγ => (truth_lemma
      (fun φ ψ => .implyK φ ψ)
      (fun φ ψ χ => .implyS φ ψ χ)
      (fun φ => .efq φ)
      (fun φ ψ => .peirce φ ψ)
      (fun φ ψ => .modalK φ ψ)
      (fun φ => .modalT φ)
      w γ).mpr (h_gamma_sub γ hγ)
  have h_phi_sat := h (CanonicalWorld (@ModalAxiom Atom)) (CanonicalModel (@ModalAxiom Atom))
    w (fun S => h_refl S)
    (fun S T U hST hTU => h_trans S T U hST hTU)
    (fun S T U hST hSU => h_eucl S T U hST hSU)
    h_gamma_sat
  have h_phi_M := (truth_lemma
    (fun φ ψ => .implyK φ ψ)
    (fun φ ψ χ => .implyS φ ψ χ)
    (fun φ => .efq φ)
    (fun φ ψ => .peirce φ ψ)
    (fun φ ψ => .modalK φ ψ)
    (fun φ => .modalT φ)
    w phi).mp h_phi_sat
  exact mcs_bot_not_mem hM_mcs
    (modal_implication_property
      (fun φ ψ => .implyK φ ψ)
      (fun φ ψ χ => .implyS φ ψ χ)
      hM_mcs h_neg_phi h_phi_M)

/-! ## S5 Biconditional Wrapper -/

/-- **Strong Soundness and Completeness for S5**:
`phi` is a semantic consequence of `Gamma` over all S5 frames iff `phi` is
set-derivable from `Gamma` using `ModalAxiom`. -/
theorem s5_strong_completeness_iff {Gamma : Set (Proposition Atom)} {phi : Proposition Atom} :
    (∀ (World : Type u) (m : Model World Atom) (w : World),
        (∀ w, m.r w w) →
        (∀ w₁ w₂ w₃, m.r w₁ w₂ → m.r w₂ w₃ → m.r w₁ w₃) →
        (∀ w₁ w₂ w₃, m.r w₁ w₂ → m.r w₁ w₃ → m.r w₂ w₃) →
        (∀ γ ∈ Gamma, Satisfies m w γ) →
        Satisfies m w phi) ↔
    ModalSetDerivable (@ModalAxiom Atom) Gamma phi :=
  ⟨s5_strong_completeness, fun h World m w h_refl h_trans h_eucl h_sat =>
    s5_strong_soundness h World m w h_refl h_trans h_eucl h_sat⟩

/-! ## S5 Compactness -/

/-- **Compactness for S5 Semantics**: If `phi` is a semantic consequence of `Gamma`
over all S5 frames, there exists a finite list `L ⊆ Gamma` such that
`phi` is a semantic consequence of (members of) `L` over all S5 frames. -/
theorem s5_compactness {Gamma : Set (Proposition Atom)} {phi : Proposition Atom}
    (h : ∀ (World : Type u) (m : Model World Atom) (w : World),
        (∀ w, m.r w w) →
        (∀ w₁ w₂ w₃, m.r w₁ w₂ → m.r w₂ w₃ → m.r w₁ w₃) →
        (∀ w₁ w₂ w₃, m.r w₁ w₂ → m.r w₁ w₃ → m.r w₂ w₃) →
        (∀ γ ∈ Gamma, Satisfies m w γ) →
        Satisfies m w phi) :
    ∃ L : List (Proposition Atom),
      (∀ x ∈ L, x ∈ Gamma) ∧
      ∀ (World : Type u) (m : Model World Atom) (w : World),
        (∀ w, m.r w w) →
        (∀ w₁ w₂ w₃, m.r w₁ w₂ → m.r w₂ w₃ → m.r w₁ w₃) →
        (∀ w₁ w₂ w₃, m.r w₁ w₂ → m.r w₁ w₃ → m.r w₂ w₃) →
        (∀ γ ∈ {ψ | ψ ∈ L}, Satisfies m w γ) →
        Satisfies m w phi := by
  obtain ⟨L, hL_sub, hL_deriv⟩ := s5_strong_completeness h
  exact ⟨L, hL_sub, fun World m w h_refl h_trans h_eucl h_sat =>
    s5_strong_soundness ⟨L, fun x hx => Set.mem_setOf_eq.mpr hx, hL_deriv⟩
      World m w h_refl h_trans h_eucl h_sat⟩

/-! ## S5 Weak Completeness (Corollary) -/

/-- **Completeness Theorem for S5 Modal Logic** (corollary of strong completeness):

If `phi` is valid over all S5 frames (reflexive, transitive, Euclidean), then `phi`
is S5-derivable from the empty context.

This is a corollary of `s5_strong_completeness` instantiated at `Gamma = ∅`. -/
theorem s5_completeness (φ : Proposition Atom)
    (h_valid : ∀ (World : Type u) (m : Model World Atom),
      (∀ w, m.r w w) →
      (∀ w₁ w₂ w₃, m.r w₁ w₂ → m.r w₂ w₃ → m.r w₁ w₃) →
      (∀ w₁ w₂ w₃, m.r w₁ w₂ → m.r w₁ w₃ → m.r w₂ w₃) →
      ∀ w, Satisfies m w φ) :
    Derivable (@ModalAxiom Atom) φ :=
  ModalSetDerivable_empty_iff.mp
    (s5_strong_completeness (fun W m w hRefl hTrans hEucl _ =>
      h_valid W m hRefl hTrans hEucl w))

end Cslib.Logic.Modal
