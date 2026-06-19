/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Modal.Metalogic.StrongCompleteness
public import Cslib.Logics.Modal.Metalogic.Systems.S4.Soundness
public import Cslib.Logics.Modal.Metalogic.Systems.S4.Completeness

/-! # Strong Completeness for Modal Logic S4

This module proves strong soundness and strong completeness for modal logic S4:
semantic entailment from a set of premises `Gamma` (over all reflexive, transitive frames)
is equivalent to set-derivability using `S4Axiom`.

## Main Results

- `s4_strong_soundness`: Set-derivability from `Gamma` implies semantic entailment
  over all reflexive, transitive frames.
- `s4_strong_completeness`: Semantic entailment over reflexive, transitive frames implies
  set-derivability from `Gamma`.
- `s4_strong_completeness_iff`: Biconditional combining the above.
- `s4_completeness`: Weak completeness (corollary of strong completeness).
- `s4_compactness`: If `phi` is an S4-semantic consequence of `Gamma`, there exists
  a finite list `L ⊆ Gamma` such that `phi` is an S4-semantic consequence of `L`.

## References

* [Blackburn, de Rijke, Venema, *Modal Logic*][Blackburn2001], Ch. 4
* Cslib/Logics/Modal/Metalogic/Systems/S4/Completeness.lean -- S4 completeness (weak)
-/

@[expose] public section

namespace Cslib.Logic.Modal

open Cslib.Logic

universe u
variable {Atom : Type u}

/-! ## S4 Strong Soundness -/

/-- **Strong Soundness for S4**: If `phi` is set-derivable from `Gamma` using `S4Axiom`,
then `phi` is a semantic consequence of `Gamma` over all reflexive, transitive frames.

For any reflexive, transitive model `m` and any world `w` satisfying all of `Gamma`, `phi`
holds at `w`. -/
theorem s4_strong_soundness {Gamma : Set (Proposition Atom)} {phi : Proposition Atom}
    (h : ModalSetDerivable (@S4Axiom Atom) Gamma phi)
    (World : Type u) (m : Model World Atom) (w : World)
    (h_refl : ∀ w, m.r w w)
    (h_trans : ∀ w₁ w₂ w₃, m.r w₁ w₂ → m.r w₂ w₃ → m.r w₁ w₃)
    (h_sat : ∀ γ ∈ Gamma, Satisfies m w γ) : Satisfies m w phi := by
  obtain ⟨L, hL_sub, hL_deriv⟩ := h
  obtain ⟨d⟩ := hL_deriv
  exact s4_soundness d m h_refl h_trans w (fun ψ hψ => h_sat ψ (hL_sub ψ hψ))

/-! ## S4 Strong Completeness -/

/-- **Strong Completeness for S4**: If `phi` is a semantic consequence of `Gamma`
over all reflexive, transitive frames, then `phi` is set-derivable from `Gamma`
using `S4Axiom`.

Proof by contrapositive: if `phi` is not set-derivable, `Gamma ∪ {¬phi}` is
consistent; extend to MCS, apply `truth_lemma` in the canonical reflexive, transitive
frame, derive contradiction. -/
theorem s4_strong_completeness {Gamma : Set (Proposition Atom)} {phi : Proposition Atom}
    (h : ∀ (World : Type u) (m : Model World Atom) (w : World),
        (∀ w, m.r w w) →
        (∀ w₁ w₂ w₃, m.r w₁ w₂ → m.r w₂ w₃ → m.r w₁ w₃) →
        (∀ γ ∈ Gamma, Satisfies m w γ) →
        Satisfies m w phi) :
    ModalSetDerivable (@S4Axiom Atom) Gamma phi := by
  by_contra h_not
  have h_cons := modal_not_SetDerivable_union_neg_consistent
    (fun φ ψ => .implyK φ ψ)
    (fun φ ψ χ => .implyS φ ψ χ)
    (fun φ => .efq φ)
    (fun φ ψ => .peirce φ ψ)
    h_not
  obtain ⟨M, hM_sup, hM_mcs⟩ := modal_lindenbaum h_cons
  let w : CanonicalWorld (@S4Axiom Atom) := ⟨M, hM_mcs⟩
  have h_neg_phi : (¬phi) ∈ M :=
    hM_sup (Set.mem_union_right Gamma (Set.mem_singleton_iff.mpr rfl))
  have h_gamma_sub : ∀ ψ ∈ Gamma, ψ ∈ M :=
    fun ψ hψ => hM_sup (Set.mem_union_left _ hψ)
  have h_refl : ∀ (S : CanonicalWorld (@S4Axiom Atom)),
      (CanonicalModel (@S4Axiom Atom)).r S S :=
    fun S => canonical_refl
      (fun φ ψ => .implyK φ ψ)
      (fun φ ψ χ => .implyS φ ψ χ)
      (fun φ => .modalT φ)
      S
  have h_trans : ∀ (S T U : CanonicalWorld (@S4Axiom Atom)),
      (CanonicalModel (@S4Axiom Atom)).r S T →
      (CanonicalModel (@S4Axiom Atom)).r T U →
      (CanonicalModel (@S4Axiom Atom)).r S U :=
    canonical_trans
      (fun φ ψ => .implyK φ ψ)
      (fun φ ψ χ => .implyS φ ψ χ)
      (fun φ => .modalFour φ)
  have h_gamma_sat : ∀ γ ∈ Gamma, Satisfies (CanonicalModel (@S4Axiom Atom)) w γ :=
    fun γ hγ => (truth_lemma
      (fun φ ψ => .implyK φ ψ)
      (fun φ ψ χ => .implyS φ ψ χ)
      (fun φ => .efq φ)
      (fun φ ψ => .peirce φ ψ)
      (fun φ ψ => .modalK φ ψ)
      (fun φ => .modalT φ)
      w γ).mpr (h_gamma_sub γ hγ)
  have h_phi_sat := h (CanonicalWorld (@S4Axiom Atom)) (CanonicalModel (@S4Axiom Atom))
    w (fun S => h_refl S) (fun S T U hST hTU => h_trans S T U hST hTU) h_gamma_sat
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

/-! ## S4 Biconditional Wrapper -/

/-- **Strong Soundness and Completeness for S4**:
`phi` is a semantic consequence of `Gamma` over all reflexive, transitive frames iff `phi` is
set-derivable from `Gamma` using `S4Axiom`. -/
theorem s4_strong_completeness_iff {Gamma : Set (Proposition Atom)} {phi : Proposition Atom} :
    (∀ (World : Type u) (m : Model World Atom) (w : World),
        (∀ w, m.r w w) →
        (∀ w₁ w₂ w₃, m.r w₁ w₂ → m.r w₂ w₃ → m.r w₁ w₃) →
        (∀ γ ∈ Gamma, Satisfies m w γ) →
        Satisfies m w phi) ↔
    ModalSetDerivable (@S4Axiom Atom) Gamma phi :=
  ⟨s4_strong_completeness, fun h World m w h_refl h_trans h_sat =>
    s4_strong_soundness h World m w h_refl h_trans h_sat⟩

/-! ## S4 Compactness -/

/-- **Compactness for S4 Semantics**: If `phi` is a semantic consequence of `Gamma`
over all reflexive, transitive frames, there exists a finite list `L ⊆ Gamma` such that
`phi` is a semantic consequence of (members of) `L` over all reflexive, transitive frames. -/
theorem s4_compactness {Gamma : Set (Proposition Atom)} {phi : Proposition Atom}
    (h : ∀ (World : Type u) (m : Model World Atom) (w : World),
        (∀ w, m.r w w) →
        (∀ w₁ w₂ w₃, m.r w₁ w₂ → m.r w₂ w₃ → m.r w₁ w₃) →
        (∀ γ ∈ Gamma, Satisfies m w γ) →
        Satisfies m w phi) :
    ∃ L : List (Proposition Atom),
      (∀ x ∈ L, x ∈ Gamma) ∧
      ∀ (World : Type u) (m : Model World Atom) (w : World),
        (∀ w, m.r w w) →
        (∀ w₁ w₂ w₃, m.r w₁ w₂ → m.r w₂ w₃ → m.r w₁ w₃) →
        (∀ γ ∈ {ψ | ψ ∈ L}, Satisfies m w γ) →
        Satisfies m w phi := by
  obtain ⟨L, hL_sub, hL_deriv⟩ := s4_strong_completeness h
  exact ⟨L, hL_sub, fun World m w h_refl h_trans h_sat =>
    s4_strong_soundness ⟨L, fun x hx => Set.mem_setOf_eq.mpr hx, hL_deriv⟩
      World m w h_refl h_trans h_sat⟩

/-! ## S4 Weak Completeness (Corollary) -/

/-- **Completeness Theorem for S4 Modal Logic** (corollary of strong completeness):

If `phi` is valid over all reflexive, transitive frames, then `phi` is S4-derivable
from the empty context.

This is a corollary of `s4_strong_completeness` instantiated at `Gamma = ∅`. -/
theorem s4_completeness (φ : Proposition Atom)
    (h_valid : ∀ (World : Type u) (m : Model World Atom),
      (∀ w, m.r w w) →
      (∀ w₁ w₂ w₃, m.r w₁ w₂ → m.r w₂ w₃ → m.r w₁ w₃) →
      ∀ w, Satisfies m w φ) :
    Derivable (@S4Axiom Atom) φ :=
  ModalSetDerivable_empty_iff.mp
    (s4_strong_completeness (fun W m w hRefl hTrans _ => h_valid W m hRefl hTrans w))

end Cslib.Logic.Modal
