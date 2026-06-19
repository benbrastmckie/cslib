/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Modal.Metalogic.StrongCompleteness
public import Cslib.Logics.Modal.Metalogic.Systems.K.Soundness
public import Cslib.Logics.Modal.Metalogic.Systems.K.Completeness

/-! # Strong Completeness for Modal Logic K

This module proves strong soundness and strong completeness for modal logic K:
semantic entailment from a set of premises `Gamma` (over all frames) is
equivalent to set-derivability using `KAxiom`.

## Main Results

- `k_strong_soundness`: `ModalSetDerivable KAxiom Gamma phi →
  ModalSemanticEntails (fun _ => True) Gamma phi`
- `k_strong_completeness`: `ModalSemanticEntails (fun _ => True) Gamma phi →
  ModalSetDerivable KAxiom Gamma phi`
- `k_strong_completeness_iff`: Biconditional combining the above.
- `k_completeness`: Weak completeness (corollary of strong completeness).
- `k_compactness`: If `phi` is a K-semantic consequence of `Gamma`, there exists
  a finite list `L ⊆ Gamma` such that `phi` is a K-semantic consequence of `L`.

## References

* [A. Chagrov, M. Zakharyaschev, *Modal Logic*][ChagrovZakharyaschev1997], Theorem 1.16
* Cslib/Logics/Modal/Metalogic/Systems/K/Completeness.lean -- K completeness (weak)
-/

@[expose] public section

namespace Cslib.Logic.Modal

open Cslib.Logic

universe u
variable {Atom : Type u}

/-! ## K Strong Soundness -/

/-- **Strong Soundness for K**: If `phi` is set-derivable from `Gamma` using `KAxiom`,
then `phi` is a semantic consequence of `Gamma` over all frames.

Proof: unfold `ModalSetDerivable` to get finite `L ⊆ Gamma`, apply `k_soundness`. -/
theorem k_strong_soundness {Gamma : Set (Proposition Atom)} {phi : Proposition Atom}
    (h : ModalSetDerivable (@KAxiom Atom) Gamma phi) :
    ModalSemanticEntails (fun _ => True) Gamma phi := by
  obtain ⟨L, hL_sub, hL_deriv⟩ := h
  obtain ⟨d⟩ := hL_deriv
  intro World m w _hFC h_sat
  exact k_soundness d m w (fun ψ hψ => h_sat ψ (hL_sub ψ hψ))

/-! ## K Strong Completeness -/

/-- **Strong Completeness for K**: If `phi` is a semantic consequence of `Gamma`
over all frames, then `phi` is set-derivable from `Gamma` using `KAxiom`.

Proof by contrapositive: assume `phi` not set-derivable from `Gamma`. Then by
`modal_not_SetDerivable_union_neg_consistent`, `Gamma ∪ {¬phi}` is consistent.
By `modal_lindenbaum`, extend to MCS `M ⊇ Gamma ∪ {¬phi}`. By `k_truth_lemma`,
all of `Gamma` is satisfied at `M` in the canonical model, but `phi` is not
(since `¬phi ∈ M`). This contradicts the hypothesis. -/
theorem k_strong_completeness {Gamma : Set (Proposition Atom)} {phi : Proposition Atom}
    (h : ModalSemanticEntails (fun _ => True) Gamma phi) :
    ModalSetDerivable (@KAxiom Atom) Gamma phi := by
  by_contra h_not
  have h_cons := modal_not_SetDerivable_union_neg_consistent
    (fun φ ψ => .implyK φ ψ)
    (fun φ ψ χ => .implyS φ ψ χ)
    (fun φ => .efq φ)
    (fun φ ψ => .peirce φ ψ)
    h_not
  obtain ⟨M, hM_sup, hM_mcs⟩ := modal_lindenbaum h_cons
  let w : CanonicalWorld (@KAxiom Atom) := ⟨M, hM_mcs⟩
  have h_neg_phi : (¬phi) ∈ M :=
    hM_sup (Set.mem_union_right Gamma (Set.mem_singleton_iff.mpr rfl))
  have h_gamma_sub : ∀ ψ ∈ Gamma, ψ ∈ M :=
    fun ψ hψ => hM_sup (Set.mem_union_left _ hψ)
  have h_gamma_sat : ∀ γ ∈ Gamma, Satisfies (CanonicalModel (@KAxiom Atom)) w γ :=
    fun γ hγ => (k_truth_lemma
      (fun φ ψ => .implyK φ ψ)
      (fun φ ψ χ => .implyS φ ψ χ)
      (fun φ => .efq φ)
      (fun φ ψ => .peirce φ ψ)
      (fun φ ψ => .modalK φ ψ)
      w γ).mpr (h_gamma_sub γ hγ)
  have h_phi_sat := h (CanonicalWorld (@KAxiom Atom)) (CanonicalModel (@KAxiom Atom)) w
    True.intro h_gamma_sat
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

/-! ## K Biconditional Wrapper -/

/-- **Strong Soundness and Completeness for K**:
`phi` is a semantic consequence of `Gamma` over all frames iff `phi` is
set-derivable from `Gamma` using `KAxiom`. -/
@[simp]
theorem k_strong_completeness_iff {Gamma : Set (Proposition Atom)} {phi : Proposition Atom} :
    ModalSemanticEntails (fun _ => True) Gamma phi ↔
    ModalSetDerivable (@KAxiom Atom) Gamma phi :=
  ⟨k_strong_completeness, k_strong_soundness⟩

/-! ## K Compactness -/

/-- **Compactness for K Semantics**: If `phi` is a semantic consequence of `Gamma`
over all frames, there exists a finite list `L ⊆ Gamma` such that `phi` is a
semantic consequence of (members of) `L` over all frames.

Proof: strong completeness gives a finite derivation witness; strong soundness
lifts it back to semantic entailment over just the finite list. -/
theorem k_compactness {Gamma : Set (Proposition Atom)} {phi : Proposition Atom}
    (h : ModalSemanticEntails (fun _ => True) Gamma phi) :
    ∃ L : List (Proposition Atom),
      (∀ x ∈ L, x ∈ Gamma) ∧
      ModalSemanticEntails (fun _ => True) {ψ | ψ ∈ L} phi := by
  obtain ⟨L, hL_sub, hL_deriv⟩ := k_strong_completeness h
  exact ⟨L, hL_sub,
    k_strong_soundness ⟨L, fun x hx => Set.mem_setOf_eq.mpr hx, hL_deriv⟩⟩

/-! ## K Weak Completeness (Corollary) -/

/-- **Completeness Theorem for Modal Logic K** (corollary of strong completeness):

If `phi` is valid over all frames (no frame conditions), then `phi`
is K-derivable from the empty context.

This is a corollary of `k_strong_completeness` instantiated at `Gamma = ∅`. -/
theorem k_completeness (φ : Proposition Atom)
    (h_valid : ∀ (World : Type u) (m : Model World Atom),
      ∀ w, Satisfies m w φ) :
    Derivable (@KAxiom Atom) φ :=
  ModalSetDerivable_empty_iff.mp
    (k_strong_completeness (ModalSemanticEntails_of_Valid (fun W m _ => h_valid W m) ∅))

end Cslib.Logic.Modal
