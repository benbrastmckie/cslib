/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Modal.Metalogic.StrongCompleteness
public import Cslib.Logics.Modal.Metalogic.Systems.D5.Soundness
public import Cslib.Logics.Modal.Metalogic.Systems.D.Completeness

/-! # Strong Completeness for Modal Logic D5

This module proves strong soundness and strong completeness for modal logic D5:
semantic entailment from a set of premises `Gamma` (over all serial, Euclidean frames)
is equivalent to set-derivability using `D5Axiom`.

## Main Results

- `d5_strong_soundness`: Set-derivability from `Gamma` implies semantic entailment
  over all serial, Euclidean frames.
- `d5_strong_completeness`: Semantic entailment over serial, Euclidean frames implies
  set-derivability from `Gamma`.
- `d5_strong_completeness_iff`: Biconditional combining the above.
- `d5_completeness`: Weak completeness (corollary of strong completeness).
- `d5_compactness`: If `phi` is a D5-semantic consequence of `Gamma`, there exists
  a finite list `L ⊆ Gamma` such that `phi` is a D5-semantic consequence of `L`.

## References

* [Blackburn, de Rijke, Venema, *Modal Logic*][Blackburn2001], Ch. 4
* Cslib/Logics/Modal/Metalogic/Systems/D/Completeness.lean -- D completeness
  (canonical serial, d_truth_lemma)
-/

@[expose] public section

namespace Cslib.Logic.Modal

open Cslib.Logic

universe u
variable {Atom : Type u}

/-! ## D5 Strong Soundness -/

/-- **Strong Soundness for D5**: If `phi` is set-derivable from `Gamma` using `D5Axiom`,
then `phi` is a semantic consequence of `Gamma` over all serial, Euclidean frames.

For any serial, Euclidean model `m` and any world `w` satisfying all of `Gamma`, `phi`
holds at `w`. -/
theorem d5_strong_soundness {Gamma : Set (Proposition Atom)} {phi : Proposition Atom}
    (h : ModalSetDerivable (@D5Axiom Atom) Gamma phi)
    (World : Type u) (m : Model World Atom) (w : World)
    (h_serial : Relation.Serial m.r)
    (h_eucl : ∀ w₁ w₂ w₃, m.r w₁ w₂ → m.r w₁ w₃ → m.r w₂ w₃)
    (h_sat : ∀ γ ∈ Gamma, Satisfies m w γ) : Satisfies m w phi := by
  obtain ⟨L, hL_sub, hL_deriv⟩ := h
  obtain ⟨d⟩ := hL_deriv
  exact d5_soundness d m h_serial h_eucl w (fun ψ hψ => h_sat ψ (hL_sub ψ hψ))

/-! ## D5 Strong Completeness -/

/-- **Strong Completeness for D5**: If `phi` is a semantic consequence of `Gamma`
over all serial, Euclidean frames, then `phi` is set-derivable from `Gamma`
using `D5Axiom`.

Proof by contrapositive: if `phi` is not set-derivable, `Gamma ∪ {¬phi}` is
consistent; extend to MCS, apply `d_truth_lemma` in the canonical serial, Euclidean
frame (Euclidean via `canonical_eucl_from_5`), derive contradiction. -/
theorem d5_strong_completeness {Gamma : Set (Proposition Atom)} {phi : Proposition Atom}
    (h : ∀ (World : Type u) (m : Model World Atom) (w : World),
        Relation.Serial m.r →
        (∀ w₁ w₂ w₃, m.r w₁ w₂ → m.r w₁ w₃ → m.r w₂ w₃) →
        (∀ γ ∈ Gamma, Satisfies m w γ) →
        Satisfies m w phi) :
    ModalSetDerivable (@D5Axiom Atom) Gamma phi := by
  by_contra h_not
  have h_cons := modal_not_SetDerivable_union_neg_consistent
    (fun φ ψ => .implyK φ ψ)
    (fun φ ψ χ => .implyS φ ψ χ)
    (fun φ => .efq φ)
    (fun φ ψ => .peirce φ ψ)
    h_not
  obtain ⟨M, hM_sup, hM_mcs⟩ := modal_lindenbaum h_cons
  let w : CanonicalWorld (@D5Axiom Atom) := ⟨M, hM_mcs⟩
  have h_neg_phi : (¬phi) ∈ M :=
    hM_sup (Set.mem_union_right Gamma (Set.mem_singleton_iff.mpr rfl))
  have h_gamma_sub : ∀ ψ ∈ Gamma, ψ ∈ M :=
    fun ψ hψ => hM_sup (Set.mem_union_left _ hψ)
  have h_serial : Relation.Serial (CanonicalModel (@D5Axiom Atom)).r := by
    constructor
    intro S
    exact d_canonical_serial
      (fun φ ψ => .implyK φ ψ)
      (fun φ ψ χ => .implyS φ ψ χ)
      (fun φ => .efq φ)
      (fun φ ψ => .modalK φ ψ)
      (fun φ => .modalD φ)
      S
  have h_eucl := @canonical_eucl_from_5 Atom (@D5Axiom Atom)
    (fun φ ψ => .implyK φ ψ)
    (fun φ ψ χ => .implyS φ ψ χ)
    (fun φ ψ => .modalK φ ψ)
    (fun φ => .modalFive φ)
  have h_gamma_sat : ∀ γ ∈ Gamma, Satisfies (CanonicalModel (@D5Axiom Atom)) w γ :=
    fun γ hγ => (d_truth_lemma
      (fun φ ψ => .implyK φ ψ)
      (fun φ ψ χ => .implyS φ ψ χ)
      (fun φ => .efq φ)
      (fun φ ψ => .peirce φ ψ)
      (fun φ ψ => .modalK φ ψ)
      (fun φ => .modalD φ)
      w γ).mpr (h_gamma_sub γ hγ)
  have h_phi_sat := h (CanonicalWorld (@D5Axiom Atom)) (CanonicalModel (@D5Axiom Atom))
    w h_serial (fun S T U hST hSU => h_eucl S T U hST hSU) h_gamma_sat
  have h_phi_M := (d_truth_lemma
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

/-! ## D5 Biconditional Wrapper -/

/-- **Strong Soundness and Completeness for D5**:
`phi` is a semantic consequence of `Gamma` over all serial, Euclidean frames iff `phi` is
set-derivable from `Gamma` using `D5Axiom`. -/
theorem d5_strong_completeness_iff {Gamma : Set (Proposition Atom)} {phi : Proposition Atom} :
    (∀ (World : Type u) (m : Model World Atom) (w : World),
        Relation.Serial m.r →
        (∀ w₁ w₂ w₃, m.r w₁ w₂ → m.r w₁ w₃ → m.r w₂ w₃) →
        (∀ γ ∈ Gamma, Satisfies m w γ) →
        Satisfies m w phi) ↔
    ModalSetDerivable (@D5Axiom Atom) Gamma phi :=
  ⟨d5_strong_completeness, fun h World m w h_serial h_eucl h_sat =>
    d5_strong_soundness h World m w h_serial h_eucl h_sat⟩

/-! ## D5 Compactness -/

/-- **Compactness for D5 Semantics**: If `phi` is a semantic consequence of `Gamma`
over all serial, Euclidean frames, there exists a finite list `L ⊆ Gamma` such that
`phi` is a semantic consequence of (members of) `L` over all serial, Euclidean frames. -/
theorem d5_compactness {Gamma : Set (Proposition Atom)} {phi : Proposition Atom}
    (h : ∀ (World : Type u) (m : Model World Atom) (w : World),
        Relation.Serial m.r →
        (∀ w₁ w₂ w₃, m.r w₁ w₂ → m.r w₁ w₃ → m.r w₂ w₃) →
        (∀ γ ∈ Gamma, Satisfies m w γ) →
        Satisfies m w phi) :
    ∃ L : List (Proposition Atom),
      (∀ x ∈ L, x ∈ Gamma) ∧
      ∀ (World : Type u) (m : Model World Atom) (w : World),
        Relation.Serial m.r →
        (∀ w₁ w₂ w₃, m.r w₁ w₂ → m.r w₁ w₃ → m.r w₂ w₃) →
        (∀ γ ∈ {ψ | ψ ∈ L}, Satisfies m w γ) →
        Satisfies m w phi := by
  obtain ⟨L, hL_sub, hL_deriv⟩ := d5_strong_completeness h
  exact ⟨L, hL_sub, fun World m w h_serial h_eucl h_sat =>
    d5_strong_soundness ⟨L, fun x hx => Set.mem_setOf_eq.mpr hx, hL_deriv⟩
      World m w h_serial h_eucl h_sat⟩

/-! ## D5 Weak Completeness (Corollary) -/

/-- **Completeness Theorem for Modal Logic D5** (corollary of strong completeness):

If `phi` is valid over all serial, Euclidean frames, then `phi` is D5-derivable
from the empty context.

This is a corollary of `d5_strong_completeness` instantiated at `Gamma = ∅`. -/
theorem d5_completeness (φ : Proposition Atom)
    (h_valid : ∀ (World : Type u) (m : Model World Atom),
      Relation.Serial m.r →
      (∀ w₁ w₂ w₃, m.r w₁ w₂ → m.r w₁ w₃ → m.r w₂ w₃) →
      ∀ w, Satisfies m w φ) :
    Derivable (@D5Axiom Atom) φ :=
  ModalSetDerivable_empty_iff.mp
    (d5_strong_completeness (fun W m w hSer hEucl _ => h_valid W m hSer hEucl w))

end Cslib.Logic.Modal
