/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Modal.Metalogic.StrongCompleteness
public import Cslib.Logics.Modal.Metalogic.Systems.T.Soundness
public import Cslib.Logics.Modal.Metalogic.Systems.T.Completeness

/-! # Strong Completeness for Modal Logic T

This module proves strong soundness and strong completeness for modal logic T:
semantic entailment from a set of premises `Gamma` (over all reflexive frames)
is equivalent to set-derivability using `TAxiom`.

## Main Results

- `t_strong_soundness`: Set-derivability from `Gamma` implies semantic entailment
  over all reflexive frames.
- `t_strong_completeness`: Semantic entailment over reflexive frames implies
  set-derivability from `Gamma`.
- `t_strong_completeness_iff`: Biconditional combining the above.
- `t_completeness`: Weak completeness (corollary of strong completeness).
- `t_compactness`: If `phi` is a T-semantic consequence of `Gamma`, there exists
  a finite list `L ⊆ Gamma` such that `phi` is a T-semantic consequence of `L`.

## References

* [Blackburn, de Rijke, Venema, *Modal Logic*][Blackburn2001], Ch. 4, Thm 4.28 cl.1
* Cslib/Logics/Modal/Metalogic/Systems/T/Completeness.lean -- T completeness (weak)
-/

@[expose] public section

namespace Cslib.Logic.Modal

open Cslib.Logic

universe u
variable {Atom : Type u}

/-! ## T Strong Soundness -/

/-- **Strong Soundness for T**: If `phi` is set-derivable from `Gamma` using `TAxiom`,
then `phi` is a semantic consequence of `Gamma` over all reflexive frames.

For any reflexive model `m` and any world `w` satisfying all of `Gamma`, `phi`
holds at `w`. -/
theorem t_strong_soundness {Gamma : Set (Proposition Atom)} {phi : Proposition Atom}
    (h : ModalSetDerivable (@TAxiom Atom) Gamma phi)
    (World : Type u) (m : Model World Atom) (w : World)
    (h_refl : ∀ w, m.r w w)
    (h_sat : ∀ γ ∈ Gamma, Satisfies m w γ) : Satisfies m w phi := by
  obtain ⟨L, hL_sub, hL_deriv⟩ := h
  obtain ⟨d⟩ := hL_deriv
  exact t_soundness d m h_refl w (fun ψ hψ => h_sat ψ (hL_sub ψ hψ))

/-! ## T Strong Completeness -/

/-- **Strong Completeness for T**: If `phi` is a semantic consequence of `Gamma`
over all reflexive frames, then `phi` is set-derivable from `Gamma` using `TAxiom`.

Proof by contrapositive: if `phi` is not set-derivable, `Gamma ∪ {¬phi}` is
consistent; extend to MCS, apply `truth_lemma` in the canonical reflexive
frame, derive contradiction. -/
theorem t_strong_completeness {Gamma : Set (Proposition Atom)} {phi : Proposition Atom}
    (h : ∀ (World : Type u) (m : Model World Atom) (w : World),
        (∀ w, m.r w w) →
        (∀ γ ∈ Gamma, Satisfies m w γ) →
        Satisfies m w phi) :
    ModalSetDerivable (@TAxiom Atom) Gamma phi := by
  by_contra h_not
  have h_cons := modal_not_SetDerivable_union_neg_consistent
    (fun φ ψ => .implyK φ ψ)
    (fun φ ψ χ => .implyS φ ψ χ)
    (fun φ => .efq φ)
    (fun φ ψ => .peirce φ ψ)
    h_not
  obtain ⟨M, hM_sup, hM_mcs⟩ := modal_lindenbaum h_cons
  let w : CanonicalWorld (@TAxiom Atom) := ⟨M, hM_mcs⟩
  have h_neg_phi : (¬phi) ∈ M :=
    hM_sup (Set.mem_union_right Gamma (Set.mem_singleton_iff.mpr rfl))
  have h_gamma_sub : ∀ ψ ∈ Gamma, ψ ∈ M :=
    fun ψ hψ => hM_sup (Set.mem_union_left _ hψ)
  have h_refl : ∀ (S : CanonicalWorld (@TAxiom Atom)),
      (CanonicalModel (@TAxiom Atom)).r S S :=
    fun S => canonical_refl
      (fun φ ψ => .implyK φ ψ)
      (fun φ ψ χ => .implyS φ ψ χ)
      (fun φ => .modalT φ)
      S
  have h_gamma_sat : ∀ γ ∈ Gamma, Satisfies (CanonicalModel (@TAxiom Atom)) w γ :=
    fun γ hγ => (truth_lemma
      (fun φ ψ => .implyK φ ψ)
      (fun φ ψ χ => .implyS φ ψ χ)
      (fun φ => .efq φ)
      (fun φ ψ => .peirce φ ψ)
      (fun φ ψ => .modalK φ ψ)
      (fun φ => .modalT φ)
      w γ).mpr (h_gamma_sub γ hγ)
  have h_phi_sat := h (CanonicalWorld (@TAxiom Atom)) (CanonicalModel (@TAxiom Atom))
    w (fun S => h_refl S) h_gamma_sat
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

/-! ## T Biconditional Wrapper -/

/-- **Strong Soundness and Completeness for T**:
`phi` is a semantic consequence of `Gamma` over all reflexive frames iff `phi` is
set-derivable from `Gamma` using `TAxiom`. -/
theorem t_strong_completeness_iff {Gamma : Set (Proposition Atom)} {phi : Proposition Atom} :
    (∀ (World : Type u) (m : Model World Atom) (w : World),
        (∀ w, m.r w w) →
        (∀ γ ∈ Gamma, Satisfies m w γ) →
        Satisfies m w phi) ↔
    ModalSetDerivable (@TAxiom Atom) Gamma phi :=
  ⟨t_strong_completeness, fun h World m w h_refl h_sat =>
    t_strong_soundness h World m w h_refl h_sat⟩

/-! ## T Compactness -/

/-- **Compactness for T Semantics**: If `phi` is a semantic consequence of `Gamma`
over all reflexive frames, there exists a finite list `L ⊆ Gamma` such that
`phi` is a semantic consequence of (members of) `L` over all reflexive frames. -/
theorem t_compactness {Gamma : Set (Proposition Atom)} {phi : Proposition Atom}
    (h : ∀ (World : Type u) (m : Model World Atom) (w : World),
        (∀ w, m.r w w) →
        (∀ γ ∈ Gamma, Satisfies m w γ) →
        Satisfies m w phi) :
    ∃ L : List (Proposition Atom),
      (∀ x ∈ L, x ∈ Gamma) ∧
      ∀ (World : Type u) (m : Model World Atom) (w : World),
        (∀ w, m.r w w) →
        (∀ γ ∈ {ψ | ψ ∈ L}, Satisfies m w γ) →
        Satisfies m w phi := by
  obtain ⟨L, hL_sub, hL_deriv⟩ := t_strong_completeness h
  exact ⟨L, hL_sub, fun World m w h_refl h_sat =>
    t_strong_soundness ⟨L, fun x hx => Set.mem_setOf_eq.mpr hx, hL_deriv⟩
      World m w h_refl h_sat⟩

/-! ## T Weak Completeness (Corollary) -/

/-- **Completeness Theorem for Modal Logic T** (corollary of strong completeness):

If `phi` is valid over all reflexive frames, then `phi` is T-derivable
from the empty context.

This is a corollary of `t_strong_completeness` instantiated at `Gamma = ∅`. -/
theorem t_completeness (φ : Proposition Atom)
    (h_valid : ∀ (World : Type u) (m : Model World Atom),
      (∀ w, m.r w w) →
      ∀ w, Satisfies m w φ) :
    Derivable (@TAxiom Atom) φ :=
  ModalSetDerivable_empty_iff.mp
    (t_strong_completeness (fun W m w hRefl _ => h_valid W m hRefl w))

end Cslib.Logic.Modal
