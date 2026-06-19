/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Modal.Metalogic.StrongCompleteness
public import Cslib.Logics.Modal.Metalogic.Systems.D.Soundness
public import Cslib.Logics.Modal.Metalogic.Systems.D.Completeness

/-! # Strong Completeness for Modal Logic D (KD)

This module proves strong soundness and strong completeness for modal logic D:
semantic entailment from a set of premises `Gamma` (over all serial frames)
is equivalent to set-derivability using `DAxiom`.

## Main Results

- `d_strong_soundness`: Set-derivability from `Gamma` implies semantic entailment
  over all serial frames.
- `d_strong_completeness`: Semantic entailment over serial frames implies
  set-derivability from `Gamma`.
- `d_strong_completeness_iff`: Biconditional combining the above.
- `d_compactness`: If `phi` is a D-semantic consequence of `Gamma`, there exists
  a finite list `L ⊆ Gamma` such that `phi` is a D-semantic consequence of `L`.

## References

* [Blackburn, de Rijke, Venema, *Modal Logic*][Blackburn2001], Ch. 4
* Cslib/Logics/Modal/Metalogic/Systems/D/Completeness.lean -- D completeness (weak)
-/

@[expose] public section

namespace Cslib.Logic.Modal

open Cslib.Logic

universe u
variable {Atom : Type u}

/-! ## D Strong Soundness -/

/-- **Strong Soundness for D**: If `phi` is set-derivable from `Gamma` using `DAxiom`,
then `phi` is a semantic consequence of `Gamma` over all serial frames.

For any serial model `m` and any world `w` satisfying all of `Gamma`, `phi`
holds at `w`. -/
theorem d_strong_soundness {Gamma : Set (Proposition Atom)} {phi : Proposition Atom}
    (h : ModalSetDerivable (@DAxiom Atom) Gamma phi)
    (World : Type u) (m : Model World Atom) (w : World)
    (h_serial : Relation.Serial m.r)
    (h_sat : ∀ γ ∈ Gamma, Satisfies m w γ) : Satisfies m w phi := by
  obtain ⟨L, hL_sub, hL_deriv⟩ := h
  obtain ⟨d⟩ := hL_deriv
  exact d_soundness d m h_serial w (fun ψ hψ => h_sat ψ (hL_sub ψ hψ))

/-! ## D Strong Completeness -/

/-- **Strong Completeness for D**: If `phi` is a semantic consequence of `Gamma`
over all serial frames, then `phi` is set-derivable from `Gamma` using `DAxiom`.

Proof by contrapositive: if `phi` is not set-derivable, `Gamma ∪ {¬phi}` is
consistent; extend to MCS, apply `truth_lemma_d` in the canonical serial
frame, derive contradiction. -/
theorem d_strong_completeness {Gamma : Set (Proposition Atom)} {phi : Proposition Atom}
    (h : ∀ (World : Type u) (m : Model World Atom) (w : World),
        Relation.Serial m.r →
        (∀ γ ∈ Gamma, Satisfies m w γ) →
        Satisfies m w phi) :
    ModalSetDerivable (@DAxiom Atom) Gamma phi := by
  by_contra h_not
  have h_cons := modal_not_SetDerivable_union_neg_consistent
    (fun φ ψ => .implyK φ ψ)
    (fun φ ψ χ => .implyS φ ψ χ)
    (fun φ => .efq φ)
    (fun φ ψ => .peirce φ ψ)
    h_not
  obtain ⟨M, hM_sup, hM_mcs⟩ := modal_lindenbaum h_cons
  let w : CanonicalWorld (@DAxiom Atom) := ⟨M, hM_mcs⟩
  have h_neg_phi : (¬phi) ∈ M :=
    hM_sup (Set.mem_union_right Gamma (Set.mem_singleton_iff.mpr rfl))
  have h_gamma_sub : ∀ ψ ∈ Gamma, ψ ∈ M :=
    fun ψ hψ => hM_sup (Set.mem_union_left _ hψ)
  have h_serial : Relation.Serial (CanonicalModel (@DAxiom Atom)).r := by
    constructor
    intro S
    exact canonical_serial
      (fun φ ψ => .implyK φ ψ)
      (fun φ ψ χ => .implyS φ ψ χ)
      (fun φ => .efq φ)
      (fun φ ψ => .modalK φ ψ)
      (fun φ => .modalD φ)
      S
  have h_gamma_sat : ∀ γ ∈ Gamma, Satisfies (CanonicalModel (@DAxiom Atom)) w γ :=
    fun γ hγ => (truth_lemma_d
      (fun φ ψ => .implyK φ ψ)
      (fun φ ψ χ => .implyS φ ψ χ)
      (fun φ => .efq φ)
      (fun φ ψ => .peirce φ ψ)
      (fun φ ψ => .modalK φ ψ)
      (fun φ => .modalD φ)
      w γ).mpr (h_gamma_sub γ hγ)
  have h_phi_sat := h (CanonicalWorld (@DAxiom Atom)) (CanonicalModel (@DAxiom Atom))
    w h_serial h_gamma_sat
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
  obtain ⟨L, hL_sub, hL_deriv⟩ := d_strong_completeness h
  exact ⟨L, hL_sub, fun World m w h_serial h_sat =>
    d_strong_soundness ⟨L, fun x hx => Set.mem_setOf_eq.mpr hx, hL_deriv⟩
      World m w h_serial h_sat⟩

end Cslib.Logic.Modal
