/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Modal.Metalogic.Completeness
public import Cslib.Logics.Modal.Metalogic.Systems.KB5.Soundness
public import Cslib.Logics.Modal.Metalogic.Systems.K.Completeness
public import Cslib.Logics.Modal.ProofSystem.Instances

/-! # Strong Completeness for Modal Logic KB5

This module proves strong soundness and strong completeness for modal logic KB5:
semantic entailment from a set of premises `Gamma` (over all symmetric, Euclidean
frames) is equivalent to set-derivability using `KB5Axiom`.

## Main Results

- `kb5_strong_soundness`: Set-derivability from `Gamma` implies semantic entailment
  over all symmetric, Euclidean frames.
- `kb5_strong_completeness`: Semantic entailment over symmetric, Euclidean frames
  implies set-derivability from `Gamma`.
- `kb5_strong_completeness_iff`: Biconditional combining the above.
- `kb5_completeness`: Weak completeness (corollary of strong completeness).
- `kb5_compactness`: Compactness for KB5 semantics.

## References

* [Blackburn, de Rijke, Venema, *Modal Logic*][Blackburn2001], Ch. 4, Thm 4.28 cl.2
-/

@[expose] public section

namespace Cslib.Logic.Modal

open Cslib.Logic

universe u
variable {Atom : Type u}

/-! ## KB5 Frame Condition and Canonical Witness -/

/-- The KB5 frame condition: every model whose accessibility relation is symmetric and
Euclidean. -/
def kb5FC : ∀ {World : Type u}, Model World Atom → Prop :=
  fun m => (∀ w₁ w₂, m.r w₁ w₂ → m.r w₂ w₁) ∧
           (∀ w₁ w₂ w₃, m.r w₁ w₂ → m.r w₁ w₃ → m.r w₂ w₃)

/-- The canonical KB5 model satisfies `kb5FC`: its accessibility relation is symmetric
and Euclidean (from axioms B and 5). -/
private theorem kb5_canonical_FC : kb5FC (CanonicalModel (@KB5Axiom Atom)) :=
  ⟨canonical_symm
      (fun φ ψ => ⟨.implyK, by decide, φ, ψ, rfl⟩)
      (fun φ ψ χ => ⟨.implyS, by decide, φ, ψ, χ, rfl⟩)
      (fun φ ψ => ⟨.modalK, by decide, φ, ψ, rfl⟩)
      (fun φ => ⟨.modalB, by decide, φ, rfl⟩),
   canonical_eucl_from_5
      (fun φ ψ => ⟨.implyK, by decide, φ, ψ, rfl⟩)
      (fun φ ψ χ => ⟨.implyS, by decide, φ, ψ, χ, rfl⟩)
      (fun φ ψ => ⟨.modalK, by decide, φ, ψ, rfl⟩)
      (fun φ => ⟨.modalFive, by decide, φ, rfl⟩)⟩

/-- Pre-applied KB5 truth lemma: satisfaction at world `S` iff membership in `S.val`. -/
private theorem kb5_truth_lemma_applied (S : CanonicalWorld (@KB5Axiom Atom))
    (φ : Proposition Atom) :
    Satisfies (CanonicalModel (@KB5Axiom Atom)) S φ ↔ φ ∈ S.val :=
  k_truth_lemma
    (fun φ ψ => ⟨.implyK, by decide, φ, ψ, rfl⟩)
    (fun φ ψ χ => ⟨.implyS, by decide, φ, ψ, χ, rfl⟩)
    (fun φ => ⟨.efq, by decide, φ, rfl⟩)
    (fun φ ψ => ⟨.peirce, by decide, φ, ψ, rfl⟩)
    (fun φ ψ => ⟨.modalK, by decide, φ, ψ, rfl⟩)
    (fun φ ψ => ⟨.andI, by decide, φ, ψ, rfl⟩)
    (fun φ ψ => ⟨.andE1, by decide, φ, ψ, rfl⟩)
    (fun φ ψ => ⟨.andE2, by decide, φ, ψ, rfl⟩)
    (fun φ ψ => ⟨.orI1, by decide, φ, ψ, rfl⟩)
    (fun φ ψ => ⟨.orI2, by decide, φ, ψ, rfl⟩)
    (fun φ ψ χ => ⟨.orE, by decide, φ, ψ, χ, rfl⟩)
    (fun φ => ⟨.diaDualityFwd, by decide, φ, rfl⟩)
    (fun φ => ⟨.diaDualityBack, by decide, φ, rfl⟩)
    S φ

/-- KB5 soundness adapter matching the `strong_soundness` callback shape.
The frame condition for KB5 is `kb5FC m = (symm) ∧ (eucl)`. -/
private theorem kb5_sound_cb {World : Type u} (m : Model World Atom) (w : World)
    (L : List (Proposition Atom))
    (hFC : kb5FC m)
    (d : DerivationTree (@KB5Axiom Atom) L phi)
    (h_ctx : ∀ γ ∈ L, Satisfies m w γ) : Satisfies m w phi :=
  kb5_soundness d m hFC.1 hFC.2 w h_ctx

/-! ## KB5 Strong Soundness -/

/-- **Strong Soundness for KB5**: If `phi` is set-derivable from `Gamma` using `KB5Axiom`,
then `phi` is a semantic consequence of `Gamma` over all symmetric, Euclidean frames.

For any symmetric, Euclidean model `m` and any world `w` satisfying all of `Gamma`,
`phi` holds at `w`. -/
theorem kb5_strong_soundness {Gamma : Set (Proposition Atom)} {phi : Proposition Atom}
    (h : ModalSetDerivable (@KB5Axiom Atom) Gamma phi)
    (World : Type u) (m : Model World Atom) (w : World)
    (h_symm : ∀ w₁ w₂, m.r w₁ w₂ → m.r w₂ w₁)
    (h_eucl : ∀ w₁ w₂ w₃, m.r w₁ w₂ → m.r w₁ w₃ → m.r w₂ w₃)
    (h_sat : ∀ γ ∈ Gamma, Satisfies m w γ) : Satisfies m w phi :=
  strong_soundness (Axioms := @KB5Axiom Atom) (FC := kb5FC)
    kb5_sound_cb h World m w ⟨h_symm, h_eucl⟩ h_sat

/-! ## KB5 Strong Completeness -/

/-- **Strong Completeness for KB5**: If `phi` is a semantic consequence of `Gamma`
over all symmetric, Euclidean frames, then `phi` is set-derivable from `Gamma`
using `KB5Axiom`.

Delegates to the parametric `strong_completeness` with `k_truth_lemma_applied`
and `kb5_canonical_FC`. -/
theorem kb5_strong_completeness {Gamma : Set (Proposition Atom)} {phi : Proposition Atom}
    (h : ∀ (World : Type u) (m : Model World Atom) (w : World),
        (∀ w₁ w₂, m.r w₁ w₂ → m.r w₂ w₁) →
        (∀ w₁ w₂ w₃, m.r w₁ w₂ → m.r w₁ w₃ → m.r w₂ w₃) →
        (∀ γ ∈ Gamma, Satisfies m w γ) →
        Satisfies m w phi) :
    ModalSetDerivable (@KB5Axiom Atom) Gamma phi :=
  strong_completeness (Axioms := @KB5Axiom Atom) (FC := kb5FC)
    (fun φ ψ => ⟨.implyK, by decide, φ, ψ, rfl⟩)
    (fun φ ψ χ => ⟨.implyS, by decide, φ, ψ, χ, rfl⟩)
    (fun φ => ⟨.efq, by decide, φ, rfl⟩)
    (fun φ ψ => ⟨.peirce, by decide, φ, ψ, rfl⟩)
    kb5_truth_lemma_applied
    kb5_canonical_FC
    (fun World m w ⟨hSymm, hEucl⟩ h_sat => h World m w hSymm hEucl h_sat)

/-! ## KB5 Biconditional Wrapper -/

/-- **Strong Soundness and Completeness for KB5**:
`phi` is a semantic consequence of `Gamma` over all symmetric, Euclidean frames
iff `phi` is set-derivable from `Gamma` using `KB5Axiom`. -/
theorem kb5_strong_completeness_iff {Gamma : Set (Proposition Atom)} {phi : Proposition Atom} :
    (∀ (World : Type u) (m : Model World Atom) (w : World),
        (∀ w₁ w₂, m.r w₁ w₂ → m.r w₂ w₁) →
        (∀ w₁ w₂ w₃, m.r w₁ w₂ → m.r w₁ w₃ → m.r w₂ w₃) →
        (∀ γ ∈ Gamma, Satisfies m w γ) →
        Satisfies m w phi) ↔
    ModalSetDerivable (@KB5Axiom Atom) Gamma phi :=
  ⟨kb5_strong_completeness, fun h World m w h_symm h_eucl h_sat =>
    kb5_strong_soundness h World m w h_symm h_eucl h_sat⟩

/-! ## KB5 Compactness -/

/-- **Compactness for KB5 Semantics**: If `phi` is a semantic consequence of `Gamma`
over all symmetric, Euclidean frames, there exists a finite list `L ⊆ Gamma` such
that `phi` is a semantic consequence of (members of) `L` over all symmetric, Euclidean
frames. -/
theorem kb5_compactness {Gamma : Set (Proposition Atom)} {phi : Proposition Atom}
    (h : ∀ (World : Type u) (m : Model World Atom) (w : World),
        (∀ w₁ w₂, m.r w₁ w₂ → m.r w₂ w₁) →
        (∀ w₁ w₂ w₃, m.r w₁ w₂ → m.r w₁ w₃ → m.r w₂ w₃) →
        (∀ γ ∈ Gamma, Satisfies m w γ) →
        Satisfies m w phi) :
    ∃ L : List (Proposition Atom),
      (∀ x ∈ L, x ∈ Gamma) ∧
      ∀ (World : Type u) (m : Model World Atom) (w : World),
        (∀ w₁ w₂, m.r w₁ w₂ → m.r w₂ w₁) →
        (∀ w₁ w₂ w₃, m.r w₁ w₂ → m.r w₁ w₃ → m.r w₂ w₃) →
        (∀ γ ∈ {ψ | ψ ∈ L}, Satisfies m w γ) →
        Satisfies m w phi := by
  obtain ⟨L, hL_sub, hL_sem⟩ :=
    compactness (Axioms := @KB5Axiom Atom) (FC := kb5FC)
      kb5_sound_cb
      (fun φ ψ => ⟨.implyK, by decide, φ, ψ, rfl⟩)
      (fun φ ψ χ => ⟨.implyS, by decide, φ, ψ, χ, rfl⟩)
      (fun φ => ⟨.efq, by decide, φ, rfl⟩)
      (fun φ ψ => ⟨.peirce, by decide, φ, ψ, rfl⟩)
      kb5_truth_lemma_applied
      kb5_canonical_FC
      (fun World m w ⟨hSymm, hEucl⟩ h_sat => h World m w hSymm hEucl h_sat)
  exact ⟨L, hL_sub, fun World m w h_symm h_eucl h_sat =>
    hL_sem World m w ⟨h_symm, h_eucl⟩ h_sat⟩

/-! ## KB5 Weak Completeness (Corollary) -/

/-- **Completeness Theorem for KB5 Modal Logic** (corollary of strong completeness):

If `phi` is valid over all symmetric, Euclidean frames, then `phi` is KB5-derivable
from the empty context.

This is a corollary of `kb5_strong_completeness` instantiated at `Gamma = ∅`. -/
theorem kb5_completeness (φ : Proposition Atom)
    (h_valid : ∀ (World : Type u) (m : Model World Atom),
      (∀ w₁ w₂, m.r w₁ w₂ → m.r w₂ w₁) →
      (∀ w₁ w₂ w₃, m.r w₁ w₂ → m.r w₁ w₃ → m.r w₂ w₃) →
      ∀ w, Satisfies m w φ) :
    Derivable (@KB5Axiom Atom) φ :=
  ModalSetDerivable_empty_iff.mp
    (kb5_strong_completeness (fun W m w hSymm hEucl _ => h_valid W m hSymm hEucl w))

end Cslib.Logic.Modal
