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

/-! ## S5 Frame Condition and Canonical Witness -/

/-- The S5 frame condition: every model whose accessibility relation is reflexive,
transitive, and Euclidean. -/
def s5FC : ∀ {World : Type u}, Model World Atom → Prop :=
  fun m => (∀ w, m.r w w) ∧
           (∀ w₁ w₂ w₃, m.r w₁ w₂ → m.r w₂ w₃ → m.r w₁ w₃) ∧
           (∀ w₁ w₂ w₃, m.r w₁ w₂ → m.r w₁ w₃ → m.r w₂ w₃)

/-- The canonical S5 model satisfies `s5FC`: its accessibility relation is reflexive,
transitive, and Euclidean. -/
private theorem s5_canonical_FC : s5FC (CanonicalModel (@ModalAxiom Atom)) :=
  ⟨fun S => canonical_refl
      (fun φ ψ => .implyK φ ψ)
      (fun φ ψ χ => .implyS φ ψ χ)
      (fun φ => .modalT φ)
      S,
   canonical_trans
      (fun φ ψ => .implyK φ ψ)
      (fun φ ψ χ => .implyS φ ψ χ)
      (fun φ => .modalFour φ),
   canonical_eucl
      (fun φ ψ => .implyK φ ψ)
      (fun φ ψ χ => .implyS φ ψ χ)
      (fun φ => .modalFour φ)
      (fun φ => .modalB φ)
      (fun φ ψ => .modalK φ ψ)⟩

/-- Pre-applied S5 truth lemma: satisfaction at world `S` iff membership in `S.val`. -/
private theorem s5_truth_lemma_applied (S : CanonicalWorld (@ModalAxiom Atom))
    (φ : Proposition Atom) :
    Satisfies (CanonicalModel (@ModalAxiom Atom)) S φ ↔ φ ∈ S.val :=
  truth_lemma
    (fun φ ψ => .implyK φ ψ)
    (fun φ ψ χ => .implyS φ ψ χ)
    (fun φ => .efq φ)
    (fun φ ψ => .peirce φ ψ)
    (fun φ ψ => .modalK φ ψ)
    (fun φ => .modalT φ)
    (fun φ ψ => .andI φ ψ)
    (fun φ ψ => .andE1 φ ψ)
    (fun φ ψ => .andE2 φ ψ)
    (fun φ ψ => .orI1 φ ψ)
    (fun φ ψ => .orI2 φ ψ)
    (fun φ ψ χ => .orE φ ψ χ)
    (fun φ => .diaDualityFwd φ)
    (fun φ => .diaDualityBack φ)
    S φ

/-- S5 soundness adapter matching the `strong_soundness` callback shape.
The frame condition for S5 is `s5FC m = (∀ w, m.r w w) ∧ (∀ ..., trans) ∧ (∀ ..., eucl)`. -/
private theorem s5_sound_cb {World : Type u} (m : Model World Atom) (w : World)
    (L : List (Proposition Atom))
    (hFC : s5FC m)
    (d : DerivationTree (@ModalAxiom Atom) L phi)
    (h_ctx : ∀ γ ∈ L, Satisfies m w γ) : Satisfies m w phi :=
  s5_soundness d m hFC.1 hFC.2.1 hFC.2.2 w h_ctx

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
    (h_sat : ∀ γ ∈ Gamma, Satisfies m w γ) : Satisfies m w phi :=
  strong_soundness (Axioms := @ModalAxiom Atom) (FC := s5FC)
    s5_sound_cb h World m w ⟨h_refl, h_trans, h_eucl⟩ h_sat

/-! ## S5 Strong Completeness -/

/-- **Strong Completeness for S5**: If `phi` is a semantic consequence of `Gamma`
over all S5 frames, then `phi` is set-derivable from `Gamma` using `ModalAxiom`.

Delegates to the parametric `strong_completeness` with `s5_truth_lemma_applied`
and `s5_canonical_FC`. -/
theorem s5_strong_completeness {Gamma : Set (Proposition Atom)} {phi : Proposition Atom}
    (h : ∀ (World : Type u) (m : Model World Atom) (w : World),
        (∀ w, m.r w w) →
        (∀ w₁ w₂ w₃, m.r w₁ w₂ → m.r w₂ w₃ → m.r w₁ w₃) →
        (∀ w₁ w₂ w₃, m.r w₁ w₂ → m.r w₁ w₃ → m.r w₂ w₃) →
        (∀ γ ∈ Gamma, Satisfies m w γ) →
        Satisfies m w phi) :
    ModalSetDerivable (@ModalAxiom Atom) Gamma phi :=
  strong_completeness (Axioms := @ModalAxiom Atom) (FC := s5FC)
    (fun φ ψ => .implyK φ ψ)
    (fun φ ψ χ => .implyS φ ψ χ)
    (fun φ => .efq φ)
    (fun φ ψ => .peirce φ ψ)
    s5_truth_lemma_applied
    s5_canonical_FC
    (fun World m w ⟨hRefl, hTrans, hEucl⟩ h_sat => h World m w hRefl hTrans hEucl h_sat)

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
  obtain ⟨L, hL_sub, hL_sem⟩ :=
    compactness (Axioms := @ModalAxiom Atom) (FC := s5FC)
      s5_sound_cb
      (fun φ ψ => .implyK φ ψ)
      (fun φ ψ χ => .implyS φ ψ χ)
      (fun φ => .efq φ)
      (fun φ ψ => .peirce φ ψ)
      s5_truth_lemma_applied
      s5_canonical_FC
      (fun World m w ⟨hRefl, hTrans, hEucl⟩ h_sat => h World m w hRefl hTrans hEucl h_sat)
  exact ⟨L, hL_sub, fun World m w h_refl h_trans h_eucl h_sat =>
    hL_sem World m w ⟨h_refl, h_trans, h_eucl⟩ h_sat⟩

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
