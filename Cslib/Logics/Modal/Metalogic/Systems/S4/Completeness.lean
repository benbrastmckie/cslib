/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Modal.Metalogic.Completeness
public import Cslib.Logics.Modal.Metalogic.Systems.S4.Soundness
public import Cslib.Logics.Modal.ProofSystem.Instances

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
-/

@[expose] public section

namespace Cslib.Logic.Modal

open Cslib.Logic

universe u
variable {Atom : Type u}

/-! ## S4 Frame Condition and Canonical Witness -/

/-- The S4 frame condition: every model whose accessibility relation is reflexive and
transitive. -/
def s4FC : ∀ {World : Type u}, Model World Atom → Prop :=
  fun m => (∀ w, m.r w w) ∧ (∀ w₁ w₂ w₃, m.r w₁ w₂ → m.r w₂ w₃ → m.r w₁ w₃)

/-- The canonical S4 model satisfies `s4FC`: its accessibility relation is reflexive
and transitive. -/
private theorem s4_canonical_FC : s4FC (CanonicalModel (@S4Axiom Atom)) :=
  ⟨fun S => canonical_refl
      (fun φ ψ => ⟨.implyK, by decide, φ, ψ, rfl⟩)
      (fun φ ψ χ => ⟨.implyS, by decide, φ, ψ, χ, rfl⟩)
      (fun φ => ⟨.modalT, by decide, φ, rfl⟩)
      S,
   canonical_trans
      (fun φ ψ => ⟨.implyK, by decide, φ, ψ, rfl⟩)
      (fun φ ψ χ => ⟨.implyS, by decide, φ, ψ, χ, rfl⟩)
      (fun φ => ⟨.modalFour, by decide, φ, rfl⟩)⟩

/-- Pre-applied S4 truth lemma: satisfaction at world `S` iff membership in `S.val`. -/
private theorem s4_truth_lemma_applied (S : CanonicalWorld (@S4Axiom Atom))
    (φ : Proposition Atom) :
    Satisfies (CanonicalModel (@S4Axiom Atom)) S φ ↔ φ ∈ S.val :=
  canonicalTruthLemmaOfKCore (by decide) S φ

/-- S4 soundness adapter matching the `strong_soundness` callback shape.
The frame condition for S4 is `s4FC m = (∀ w, m.r w w) ∧ (∀ w₁ w₂ w₃, ...)`. -/
private theorem s4_sound_cb {World : Type u} (m : Model World Atom) (w : World)
    (L : List (Proposition Atom))
    (hFC : s4FC m)
    (d : DerivationTree (@S4Axiom Atom) L phi)
    (h_ctx : ∀ γ ∈ L, Satisfies m w γ) : Satisfies m w phi :=
  s4_soundness d m hFC.1 hFC.2 w h_ctx

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
    (h_sat : ∀ γ ∈ Gamma, Satisfies m w γ) : Satisfies m w phi :=
  strong_soundness (Axioms := @S4Axiom Atom) (FC := s4FC)
    s4_sound_cb h World m w ⟨h_refl, h_trans⟩ h_sat

/-! ## S4 Strong Completeness -/

/-- **Strong Completeness for S4**: If `phi` is a semantic consequence of `Gamma`
over all reflexive, transitive frames, then `phi` is set-derivable from `Gamma`
using `S4Axiom`.

Delegates to the parametric `strong_completeness` with `s4_truth_lemma_applied`
and `s4_canonical_FC`. -/
theorem s4_strong_completeness {Gamma : Set (Proposition Atom)} {phi : Proposition Atom}
    (h : ∀ (World : Type u) (m : Model World Atom) (w : World),
        (∀ w, m.r w w) →
        (∀ w₁ w₂ w₃, m.r w₁ w₂ → m.r w₂ w₃ → m.r w₁ w₃) →
        (∀ γ ∈ Gamma, Satisfies m w γ) →
        Satisfies m w phi) :
    ModalSetDerivable (@S4Axiom Atom) Gamma phi :=
  strong_completeness (Axioms := @S4Axiom Atom) (FC := s4FC)
    (fun φ ψ => ⟨.implyK, by decide, φ, ψ, rfl⟩)
    (fun φ ψ χ => ⟨.implyS, by decide, φ, ψ, χ, rfl⟩)
    (fun φ => ⟨.efq, by decide, φ, rfl⟩)
    (fun φ ψ => ⟨.peirce, by decide, φ, ψ, rfl⟩)
    s4_truth_lemma_applied
    s4_canonical_FC
    (fun World m w ⟨hRefl, hTrans⟩ h_sat => h World m w hRefl hTrans h_sat)

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
  obtain ⟨L, hL_sub, hL_sem⟩ :=
    compactness (Axioms := @S4Axiom Atom) (FC := s4FC)
      s4_sound_cb
      (fun φ ψ => ⟨.implyK, by decide, φ, ψ, rfl⟩)
      (fun φ ψ χ => ⟨.implyS, by decide, φ, ψ, χ, rfl⟩)
      (fun φ => ⟨.efq, by decide, φ, rfl⟩)
      (fun φ ψ => ⟨.peirce, by decide, φ, ψ, rfl⟩)
      s4_truth_lemma_applied
      s4_canonical_FC
      (fun World m w ⟨hRefl, hTrans⟩ h_sat => h World m w hRefl hTrans h_sat)
  exact ⟨L, hL_sub, fun World m w h_refl h_trans h_sat =>
    hL_sem World m w ⟨h_refl, h_trans⟩ h_sat⟩

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
