/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Modal.Metalogic.Completeness
public import Cslib.Logics.Modal.Metalogic.Systems.K4.Soundness
public import Cslib.Logics.Modal.ProofSystem.Instances

/-! # Strong Completeness for Modal Logic K4

This module proves strong soundness and strong completeness for modal logic K4:
semantic entailment from a set of premises `Gamma` (over all transitive frames)
is equivalent to set-derivability using `K4Axiom`.

## Main Results

- `k4_strong_soundness`: Set-derivability from `Gamma` implies semantic entailment.
- `k4_strong_completeness`: Semantic entailment implies set-derivability from `Gamma`.
- `k4_strong_completeness_iff`: Biconditional combining the above.
- `k4_completeness`: Weak completeness (corollary of strong completeness).
- `k4_compactness`: Compactness for K4 semantics.

## References

* [Blackburn, de Rijke, Venema, *Modal Logic*][Blackburn2001], Ch. 4, Thm 4.27
-/

@[expose] public section

namespace Cslib.Logic.Modal

open Cslib.Logic

universe u
variable {Atom : Type u}

/-! ## K4 Frame Condition and Canonical Witness -/

/-- The K4 frame condition: every model whose accessibility relation is transitive. -/
def k4FC : ∀ {World : Type u}, Model World Atom → Prop :=
  fun m => ∀ w₁ w₂ w₃, m.r w₁ w₂ → m.r w₂ w₃ → m.r w₁ w₃

/-- The canonical K4 model satisfies `k4FC`: its accessibility relation is transitive. -/
private theorem k4_canonical_FC : k4FC (CanonicalModel (@K4Axiom Atom)) :=
  canonical_trans
    (fun φ ψ => ⟨.implyK, by decide, φ, ψ, rfl⟩)
    (fun φ ψ χ => ⟨.implyS, by decide, φ, ψ, χ, rfl⟩)
    (fun φ => ⟨.modalFour, by decide, φ, rfl⟩)

/-- Pre-applied K4 truth lemma: satisfaction at world `S` iff membership in `S.val`. -/
private theorem k4_truth_lemma_applied (S : CanonicalWorld (@K4Axiom Atom))
    (φ : Proposition Atom) :
    Satisfies (CanonicalModel (@K4Axiom Atom)) S φ ↔ φ ∈ S.val :=
  canonicalTruthLemmaOfKCore (by decide) S φ

/-- `kCore ⊆ k4Tags`: feeds the `holds*` helpers so `k4_strong_completeness`/`k4_compactness`
below share this single subset fact instead of repeating 4 `by decide` witnesses. -/
private theorem coreSubset : kCore ⊆ k4Tags := by decide

/-- K4 soundness adapter matching the `strong_soundness` callback shape.
The frame condition for K4 is `k4FC m = ∀ w₁ w₂ w₃, m.r w₁ w₂ → m.r w₂ w₃ → m.r w₁ w₃`. -/
private theorem k4_sound_cb {World : Type u} (m : Model World Atom) (w : World)
    (L : List (Proposition Atom))
    (hFC : k4FC m)
    (d : DerivationTree (@K4Axiom Atom) L phi)
    (h_ctx : ∀ γ ∈ L, Satisfies m w γ) : Satisfies m w phi :=
  k4_soundness d m hFC w h_ctx

/-! ## K4 Strong Soundness -/

/-- **Strong Soundness for K4**: If `phi` is set-derivable from `Gamma` using `K4Axiom`,
then `phi` is a semantic consequence of `Gamma` over all transitive frames.

For any transitive model `m` and any world `w` satisfying all of `Gamma`, `phi`
holds at `w`. -/
theorem k4_strong_soundness {Gamma : Set (Proposition Atom)} {phi : Proposition Atom}
    (h : ModalSetDerivable (@K4Axiom Atom) Gamma phi)
    (World : Type u) (m : Model World Atom) (w : World)
    (h_trans : ∀ w₁ w₂ w₃, m.r w₁ w₂ → m.r w₂ w₃ → m.r w₁ w₃)
    (h_sat : ∀ γ ∈ Gamma, Satisfies m w γ) : Satisfies m w phi :=
  strong_soundness (Axioms := @K4Axiom Atom) (FC := k4FC)
    k4_sound_cb h World m w h_trans h_sat

/-! ## K4 Strong Completeness -/

/-- **Strong Completeness for K4**: If `phi` is a semantic consequence of `Gamma`
over all transitive frames, then `phi` is set-derivable from `Gamma` using `K4Axiom`.

Delegates to the parametric `strong_completeness` with `k4_truth_lemma_applied`
and `k4_canonical_FC`. -/
theorem k4_strong_completeness {Gamma : Set (Proposition Atom)} {phi : Proposition Atom}
    (h : ∀ (World : Type u) (m : Model World Atom) (w : World),
        (∀ w₁ w₂ w₃, m.r w₁ w₂ → m.r w₂ w₃ → m.r w₁ w₃) →
        (∀ γ ∈ Gamma, Satisfies m w γ) →
        Satisfies m w phi) :
    ModalSetDerivable (@K4Axiom Atom) Gamma phi :=
  strong_completeness (Axioms := @K4Axiom Atom) (FC := k4FC)
    (holdsImplyK coreSubset)
    (holdsImplyS coreSubset)
    (holdsEfq coreSubset)
    (holdsPeirce coreSubset)
    k4_truth_lemma_applied
    k4_canonical_FC
    (fun World m w hFC h_sat => h World m w hFC h_sat)

/-! ## K4 Biconditional Wrapper -/

/-- **Strong Soundness and Completeness for K4**:
`phi` is a semantic consequence of `Gamma` over all transitive frames iff `phi` is
set-derivable from `Gamma` using `K4Axiom`. -/
theorem k4_strong_completeness_iff {Gamma : Set (Proposition Atom)} {phi : Proposition Atom} :
    (∀ (World : Type u) (m : Model World Atom) (w : World),
        (∀ w₁ w₂ w₃, m.r w₁ w₂ → m.r w₂ w₃ → m.r w₁ w₃) →
        (∀ γ ∈ Gamma, Satisfies m w γ) →
        Satisfies m w phi) ↔
    ModalSetDerivable (@K4Axiom Atom) Gamma phi :=
  ⟨k4_strong_completeness, fun h World m w h_trans h_sat =>
    k4_strong_soundness h World m w h_trans h_sat⟩

/-! ## K4 Compactness -/

/-- **Compactness for K4 Semantics**: If `phi` is a semantic consequence of `Gamma`
over all transitive frames, there exists a finite list `L ⊆ Gamma` such that
`phi` is a semantic consequence of (members of) `L` over all transitive frames. -/
theorem k4_compactness {Gamma : Set (Proposition Atom)} {phi : Proposition Atom}
    (h : ∀ (World : Type u) (m : Model World Atom) (w : World),
        (∀ w₁ w₂ w₃, m.r w₁ w₂ → m.r w₂ w₃ → m.r w₁ w₃) →
        (∀ γ ∈ Gamma, Satisfies m w γ) →
        Satisfies m w phi) :
    ∃ L : List (Proposition Atom),
      (∀ x ∈ L, x ∈ Gamma) ∧
      ∀ (World : Type u) (m : Model World Atom) (w : World),
        (∀ w₁ w₂ w₃, m.r w₁ w₂ → m.r w₂ w₃ → m.r w₁ w₃) →
        (∀ γ ∈ {ψ | ψ ∈ L}, Satisfies m w γ) →
        Satisfies m w phi := by
  obtain ⟨L, hL_sub, hL_sem⟩ :=
    compactness (Axioms := @K4Axiom Atom) (FC := k4FC)
      k4_sound_cb
      (holdsImplyK coreSubset)
      (holdsImplyS coreSubset)
      (holdsEfq coreSubset)
      (holdsPeirce coreSubset)
      k4_truth_lemma_applied
      k4_canonical_FC
      (fun World m w hFC h_sat => h World m w hFC h_sat)
  exact ⟨L, hL_sub, fun World m w h_trans h_sat => hL_sem World m w h_trans h_sat⟩

/-! ## K4 Weak Completeness (Corollary) -/

/-- **Completeness Theorem for K4 Modal Logic** (corollary of strong completeness):

If `phi` is valid over all transitive frames, then `phi` is K4-derivable
from the empty context.

This is a corollary of `k4_strong_completeness` instantiated at `Gamma = ∅`. -/
theorem k4_completeness (φ : Proposition Atom)
    (h_valid : ∀ (World : Type u) (m : Model World Atom),
      (∀ w₁ w₂ w₃, m.r w₁ w₂ → m.r w₂ w₃ → m.r w₁ w₃) →
      ∀ w, Satisfies m w φ) :
    Derivable (@K4Axiom Atom) φ :=
  ModalSetDerivable_empty_iff.mp
    (k4_strong_completeness (fun W m w hTrans _ => h_valid W m hTrans w))

end Cslib.Logic.Modal
