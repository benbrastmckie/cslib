/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Modal.Metalogic.StrongCompleteness
public import Cslib.Logics.Modal.Metalogic.Systems.D4.Soundness
public import Cslib.Logics.Modal.Metalogic.Systems.D.Completeness

/-! # Strong Completeness for Modal Logic D4

This module proves strong soundness and strong completeness for modal logic D4:
semantic entailment from a set of premises `Gamma` (over all serial, transitive frames)
is equivalent to set-derivability using `D4Axiom`.

## Main Results

- `d4_strong_soundness`: Set-derivability from `Gamma` implies semantic entailment
  over all serial, transitive frames.
- `d4_strong_completeness`: Semantic entailment over serial, transitive frames implies
  set-derivability from `Gamma`.
- `d4_strong_completeness_iff`: Biconditional combining the above.
- `d4_compactness`: If `phi` is a D4-semantic consequence of `Gamma`, there exists
  a finite list `L ⊆ Gamma` such that `phi` is a D4-semantic consequence of `L`.

## References

* [Blackburn, de Rijke, Venema, *Modal Logic*][Blackburn2001], Ch. 4
* Cslib/Logics/Modal/Metalogic/Systems/D/Completeness.lean -- D completeness
  (canonical serial, truth_lemma_d)
-/

@[expose] public section

namespace Cslib.Logic.Modal

open Cslib.Logic

universe u
variable {Atom : Type u}

/-! ## D4 Strong Soundness -/

/-- **Strong Soundness for D4**: If `phi` is set-derivable from `Gamma` using `D4Axiom`,
then `phi` is a semantic consequence of `Gamma` over all serial, transitive frames.

For any serial, transitive model `m` and any world `w` satisfying all of `Gamma`, `phi`
holds at `w`. -/
theorem d4_strong_soundness {Gamma : Set (Proposition Atom)} {phi : Proposition Atom}
    (h : ModalSetDerivable (@D4Axiom Atom) Gamma phi)
    (World : Type u) (m : Model World Atom) (w : World)
    (h_serial : Relation.Serial m.r)
    (h_trans : ∀ w₁ w₂ w₃, m.r w₁ w₂ → m.r w₂ w₃ → m.r w₁ w₃)
    (h_sat : ∀ γ ∈ Gamma, Satisfies m w γ) : Satisfies m w phi := by
  obtain ⟨L, hL_sub, hL_deriv⟩ := h
  obtain ⟨d⟩ := hL_deriv
  exact d4_soundness d m h_serial h_trans w (fun ψ hψ => h_sat ψ (hL_sub ψ hψ))

/-! ## D4 Strong Completeness -/

/-- **Strong Completeness for D4**: If `phi` is a semantic consequence of `Gamma`
over all serial, transitive frames, then `phi` is set-derivable from `Gamma`
using `D4Axiom`.

Proof by contrapositive: if `phi` is not set-derivable, `Gamma ∪ {¬phi}` is
consistent; extend to MCS, apply `truth_lemma_d` in the canonical serial, transitive
frame, derive contradiction. -/
theorem d4_strong_completeness {Gamma : Set (Proposition Atom)} {phi : Proposition Atom}
    (h : ∀ (World : Type u) (m : Model World Atom) (w : World),
        Relation.Serial m.r →
        (∀ w₁ w₂ w₃, m.r w₁ w₂ → m.r w₂ w₃ → m.r w₁ w₃) →
        (∀ γ ∈ Gamma, Satisfies m w γ) →
        Satisfies m w phi) :
    ModalSetDerivable (@D4Axiom Atom) Gamma phi := by
  by_contra h_not
  have h_cons := modal_not_SetDerivable_union_neg_consistent
    (fun φ ψ => .implyK φ ψ)
    (fun φ ψ χ => .implyS φ ψ χ)
    (fun φ => .efq φ)
    (fun φ ψ => .peirce φ ψ)
    h_not
  obtain ⟨M, hM_sup, hM_mcs⟩ := modal_lindenbaum h_cons
  let w : CanonicalWorld (@D4Axiom Atom) := ⟨M, hM_mcs⟩
  have h_neg_phi : (¬phi) ∈ M :=
    hM_sup (Set.mem_union_right Gamma (Set.mem_singleton_iff.mpr rfl))
  have h_gamma_sub : ∀ ψ ∈ Gamma, ψ ∈ M :=
    fun ψ hψ => hM_sup (Set.mem_union_left _ hψ)
  have h_serial : Relation.Serial (CanonicalModel (@D4Axiom Atom)).r := by
    constructor
    intro S
    exact canonical_serial
      (fun φ ψ => .implyK φ ψ)
      (fun φ ψ χ => .implyS φ ψ χ)
      (fun φ => .efq φ)
      (fun φ ψ => .modalK φ ψ)
      (fun φ => .modalD φ)
      S
  have h_trans : ∀ (S T U : CanonicalWorld (@D4Axiom Atom)),
      (CanonicalModel (@D4Axiom Atom)).r S T →
      (CanonicalModel (@D4Axiom Atom)).r T U →
      (CanonicalModel (@D4Axiom Atom)).r S U :=
    canonical_trans
      (fun φ ψ => .implyK φ ψ)
      (fun φ ψ χ => .implyS φ ψ χ)
      (fun φ => .modalFour φ)
  have h_gamma_sat : ∀ γ ∈ Gamma, Satisfies (CanonicalModel (@D4Axiom Atom)) w γ :=
    fun γ hγ => (truth_lemma_d
      (fun φ ψ => .implyK φ ψ)
      (fun φ ψ χ => .implyS φ ψ χ)
      (fun φ => .efq φ)
      (fun φ ψ => .peirce φ ψ)
      (fun φ ψ => .modalK φ ψ)
      (fun φ => .modalD φ)
      w γ).mpr (h_gamma_sub γ hγ)
  have h_phi_sat := h (CanonicalWorld (@D4Axiom Atom)) (CanonicalModel (@D4Axiom Atom))
    w h_serial (fun S T U hST hTU => h_trans S T U hST hTU) h_gamma_sat
  have h_phi_M := (truth_lemma_d
    (fun φ ψ => .implyK φ ψ)
    (fun φ ψ χ => .implyS φ ψ χ)
    (fun φ => .efq φ)
    (fun φ ψ => .peirce φ ψ)
    (fun φ ψ => .modalK φ ψ)
    (fun φ => .modalD φ)
    w phi).mp h_phi_sat
  exact mcs_bot_not_mem hM_mcs
    (modal_implication_property
      (fun φ ψ => .implyK φ ψ)
      (fun φ ψ χ => .implyS φ ψ χ)
      hM_mcs h_neg_phi h_phi_M)

/-! ## D4 Biconditional Wrapper -/

/-- **Strong Soundness and Completeness for D4**:
`phi` is a semantic consequence of `Gamma` over all serial, transitive frames iff `phi` is
set-derivable from `Gamma` using `D4Axiom`. -/
theorem d4_strong_completeness_iff {Gamma : Set (Proposition Atom)} {phi : Proposition Atom} :
    (∀ (World : Type u) (m : Model World Atom) (w : World),
        Relation.Serial m.r →
        (∀ w₁ w₂ w₃, m.r w₁ w₂ → m.r w₂ w₃ → m.r w₁ w₃) →
        (∀ γ ∈ Gamma, Satisfies m w γ) →
        Satisfies m w phi) ↔
    ModalSetDerivable (@D4Axiom Atom) Gamma phi :=
  ⟨d4_strong_completeness, fun h World m w h_serial h_trans h_sat =>
    d4_strong_soundness h World m w h_serial h_trans h_sat⟩

/-! ## D4 Compactness -/

/-- **Compactness for D4 Semantics**: If `phi` is a semantic consequence of `Gamma`
over all serial, transitive frames, there exists a finite list `L ⊆ Gamma` such that
`phi` is a semantic consequence of (members of) `L` over all serial, transitive frames. -/
theorem d4_compactness {Gamma : Set (Proposition Atom)} {phi : Proposition Atom}
    (h : ∀ (World : Type u) (m : Model World Atom) (w : World),
        Relation.Serial m.r →
        (∀ w₁ w₂ w₃, m.r w₁ w₂ → m.r w₂ w₃ → m.r w₁ w₃) →
        (∀ γ ∈ Gamma, Satisfies m w γ) →
        Satisfies m w phi) :
    ∃ L : List (Proposition Atom),
      (∀ x ∈ L, x ∈ Gamma) ∧
      ∀ (World : Type u) (m : Model World Atom) (w : World),
        Relation.Serial m.r →
        (∀ w₁ w₂ w₃, m.r w₁ w₂ → m.r w₂ w₃ → m.r w₁ w₃) →
        (∀ γ ∈ {ψ | ψ ∈ L}, Satisfies m w γ) →
        Satisfies m w phi := by
  obtain ⟨L, hL_sub, hL_deriv⟩ := d4_strong_completeness h
  exact ⟨L, hL_sub, fun World m w h_serial h_trans h_sat =>
    d4_strong_soundness ⟨L, fun x hx => Set.mem_setOf_eq.mpr hx, hL_deriv⟩
      World m w h_serial h_trans h_sat⟩

end Cslib.Logic.Modal
