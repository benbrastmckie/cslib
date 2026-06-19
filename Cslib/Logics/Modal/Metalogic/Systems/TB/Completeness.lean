/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Modal.Metalogic.Completeness
public import Cslib.Logics.Modal.Metalogic.Systems.TB.Soundness
public import Cslib.Logics.Modal.ProofSystem.Instances

/-! # Completeness Theorem for Modal Logic TB

This module proves completeness for TB modal logic (= KTB) via the canonical Kripke
model construction: if a formula is valid on all reflexive, symmetric frames, then
it is TB-derivable.

The proof follows Blackburn, de Rijke, Venema "Modal Logic" (2002) Chapter 4:

- **Theorem 4.28, clause 1** (reflexivity is canonical): Uses axiom T (`□φ → φ`)
  via `canonical_refl` and `mcs_box_closure`.

- **Theorem 4.28, clause 2** (symmetry is canonical): Uses axiom B (`φ → □◇φ`)
  via `canonical_symm`.

## Main Results

- `tb_canonical_refl`: The canonical frame for TB is reflexive (BRV Thm 4.28 cl.1).
- `tb_canonical_symm`: The canonical frame for TB is symmetric (BRV Thm 4.28 cl.2).
- `tb_truth_lemma`: TB-specific Truth Lemma (reuses existing `truth_lemma`).

The weak completeness theorem `tb_completeness` is derived below as a
corollary of strong completeness via `ModalSetDerivable_empty_iff`.

## References

* Blackburn, de Rijke, Venema - Modal Logic (Ch. 4, Theorems 4.22, 4.28)
* Cslib/Logics/Modal/Metalogic/Completeness.lean -- parameterized canonical model
-/

@[expose] public section

namespace Cslib.Logic.Modal

open Cslib.Logic

universe u
variable {Atom : Type u}

/-! ## TB Strong Soundness -/

/-- **Strong Soundness for TB**: If `phi` is set-derivable from `Gamma` using `TBAxiom`,
then `phi` is a semantic consequence of `Gamma` over all reflexive, symmetric frames.

For any reflexive, symmetric model `m` and any world `w` satisfying all of `Gamma`, `phi`
holds at `w`. -/
theorem tb_strong_soundness {Gamma : Set (Proposition Atom)} {phi : Proposition Atom}
    (h : ModalSetDerivable (@TBAxiom Atom) Gamma phi)
    (World : Type u) (m : Model World Atom) (w : World)
    (h_refl : ∀ w, m.r w w)
    (h_symm : ∀ w₁ w₂, m.r w₁ w₂ → m.r w₂ w₁)
    (h_sat : ∀ γ ∈ Gamma, Satisfies m w γ) : Satisfies m w phi := by
  obtain ⟨L, hL_sub, hL_deriv⟩ := h
  obtain ⟨d⟩ := hL_deriv
  exact tb_soundness d m h_refl h_symm w (fun ψ hψ => h_sat ψ (hL_sub ψ hψ))

/-! ## TB Strong Completeness -/

/-- **Strong Completeness for TB**: If `phi` is a semantic consequence of `Gamma`
over all reflexive, symmetric frames, then `phi` is set-derivable from `Gamma`
using `TBAxiom`.

Proof by contrapositive: if `phi` is not set-derivable, `Gamma ∪ {¬phi}` is
consistent; extend to MCS, apply `truth_lemma` in the canonical reflexive, symmetric
frame, derive contradiction. -/
theorem tb_strong_completeness {Gamma : Set (Proposition Atom)} {phi : Proposition Atom}
    (h : ∀ (World : Type u) (m : Model World Atom) (w : World),
        (∀ w, m.r w w) →
        (∀ w₁ w₂, m.r w₁ w₂ → m.r w₂ w₁) →
        (∀ γ ∈ Gamma, Satisfies m w γ) →
        Satisfies m w phi) :
    ModalSetDerivable (@TBAxiom Atom) Gamma phi := by
  by_contra h_not
  have h_cons := modal_not_SetDerivable_union_neg_consistent
    (fun φ ψ => .implyK φ ψ)
    (fun φ ψ χ => .implyS φ ψ χ)
    (fun φ => .efq φ)
    (fun φ ψ => .peirce φ ψ)
    h_not
  obtain ⟨M, hM_sup, hM_mcs⟩ := modal_lindenbaum h_cons
  let w : CanonicalWorld (@TBAxiom Atom) := ⟨M, hM_mcs⟩
  have h_neg_phi : (¬phi) ∈ M :=
    hM_sup (Set.mem_union_right Gamma (Set.mem_singleton_iff.mpr rfl))
  have h_gamma_sub : ∀ ψ ∈ Gamma, ψ ∈ M :=
    fun ψ hψ => hM_sup (Set.mem_union_left _ hψ)
  have h_refl : ∀ (S : CanonicalWorld (@TBAxiom Atom)),
      (CanonicalModel (@TBAxiom Atom)).r S S :=
    fun S => canonical_refl
      (fun φ ψ => .implyK φ ψ)
      (fun φ ψ χ => .implyS φ ψ χ)
      (fun φ => .modalT φ)
      S
  have h_symm : ∀ (S T : CanonicalWorld (@TBAxiom Atom)),
      (CanonicalModel (@TBAxiom Atom)).r S T →
      (CanonicalModel (@TBAxiom Atom)).r T S :=
    canonical_symm
      (fun φ ψ => .implyK φ ψ)
      (fun φ ψ χ => .implyS φ ψ χ)
      (fun φ ψ => .modalK φ ψ)
      (fun φ => .modalB φ)
  have h_gamma_sat : ∀ γ ∈ Gamma, Satisfies (CanonicalModel (@TBAxiom Atom)) w γ :=
    fun γ hγ => (truth_lemma
      (fun φ ψ => .implyK φ ψ)
      (fun φ ψ χ => .implyS φ ψ χ)
      (fun φ => .efq φ)
      (fun φ ψ => .peirce φ ψ)
      (fun φ ψ => .modalK φ ψ)
      (fun φ => .modalT φ)
      w γ).mpr (h_gamma_sub γ hγ)
  have h_phi_sat := h (CanonicalWorld (@TBAxiom Atom)) (CanonicalModel (@TBAxiom Atom))
    w (fun S => h_refl S) (fun S T hST => h_symm S T hST) h_gamma_sat
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

/-! ## TB Biconditional Wrapper -/

/-- **Strong Soundness and Completeness for TB**:
`phi` is a semantic consequence of `Gamma` over all reflexive, symmetric frames iff `phi` is
set-derivable from `Gamma` using `TBAxiom`. -/
theorem tb_strong_completeness_iff {Gamma : Set (Proposition Atom)} {phi : Proposition Atom} :
    (∀ (World : Type u) (m : Model World Atom) (w : World),
        (∀ w, m.r w w) →
        (∀ w₁ w₂, m.r w₁ w₂ → m.r w₂ w₁) →
        (∀ γ ∈ Gamma, Satisfies m w γ) →
        Satisfies m w phi) ↔
    ModalSetDerivable (@TBAxiom Atom) Gamma phi :=
  ⟨tb_strong_completeness, fun h World m w h_refl h_symm h_sat =>
    tb_strong_soundness h World m w h_refl h_symm h_sat⟩

/-! ## TB Compactness -/

/-- **Compactness for TB Semantics**: If `phi` is a semantic consequence of `Gamma`
over all reflexive, symmetric frames, there exists a finite list `L ⊆ Gamma` such that
`phi` is a semantic consequence of (members of) `L` over all reflexive, symmetric frames. -/
theorem tb_compactness {Gamma : Set (Proposition Atom)} {phi : Proposition Atom}
    (h : ∀ (World : Type u) (m : Model World Atom) (w : World),
        (∀ w, m.r w w) →
        (∀ w₁ w₂, m.r w₁ w₂ → m.r w₂ w₁) →
        (∀ γ ∈ Gamma, Satisfies m w γ) →
        Satisfies m w phi) :
    ∃ L : List (Proposition Atom),
      (∀ x ∈ L, x ∈ Gamma) ∧
      ∀ (World : Type u) (m : Model World Atom) (w : World),
        (∀ w, m.r w w) →
        (∀ w₁ w₂, m.r w₁ w₂ → m.r w₂ w₁) →
        (∀ γ ∈ {ψ | ψ ∈ L}, Satisfies m w γ) →
        Satisfies m w phi := by
  obtain ⟨L, hL_sub, hL_deriv⟩ := tb_strong_completeness h
  exact ⟨L, hL_sub, fun World m w h_refl h_symm h_sat =>
    tb_strong_soundness ⟨L, fun x hx => Set.mem_setOf_eq.mpr hx, hL_deriv⟩
      World m w h_refl h_symm h_sat⟩

/-! ## TB Weak Completeness (Corollary) -/

/-- **Completeness Theorem for TB Modal Logic** (corollary of strong completeness):

If `phi` is valid over all reflexive, symmetric frames, then `phi` is TB-derivable
from the empty context.

This is a corollary of `tb_strong_completeness` instantiated at `Gamma = ∅`. -/
theorem tb_completeness (φ : Proposition Atom)
    (h_valid : ∀ (World : Type u) (m : Model World Atom),
      (∀ w, m.r w w) →
      (∀ w₁ w₂, m.r w₁ w₂ → m.r w₂ w₁) →
      ∀ w, Satisfies m w φ) :
    Derivable (@TBAxiom Atom) φ :=
  ModalSetDerivable_empty_iff.mp
    (tb_strong_completeness (fun W m w hRefl hSymm _ => h_valid W m hRefl hSymm w))

end Cslib.Logic.Modal
