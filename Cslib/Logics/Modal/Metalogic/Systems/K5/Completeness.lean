/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Modal.Metalogic.Completeness
public import Cslib.Logics.Modal.Metalogic.Systems.K5.Soundness

/-! # Strong Completeness for Modal Logic K5

This module proves strong soundness and strong completeness for modal logic K5:
semantic entailment from a set of premises `Gamma` (over all Euclidean frames)
is equivalent to set-derivability using `K5Axiom`.

## Main Results

- `k5_strong_soundness`: Set-derivability from `Gamma` implies semantic entailment.
- `k5_strong_completeness`: Semantic entailment implies set-derivability from `Gamma`.
- `k5_strong_completeness_iff`: Biconditional combining the above.
- `k5_completeness`: Weak completeness (corollary of strong completeness).
- `k5_compactness`: Compactness for K5 semantics.

## References

* [Blackburn, de Rijke, Venema, *Modal Logic*][Blackburn2001], Ch. 4
-/

@[expose] public section

namespace Cslib.Logic.Modal

open Cslib.Logic

universe u
variable {Atom : Type u}

/-! ## K5 Frame Condition and Canonical Witness -/

/-- The K5 frame condition: every model whose accessibility relation is Euclidean. -/
def k5FC : ∀ {World : Type u}, Model World Atom → Prop :=
  fun m => ∀ w₁ w₂ w₃, m.r w₁ w₂ → m.r w₁ w₃ → m.r w₂ w₃

/-- The canonical K5 model satisfies `k5FC`: its accessibility relation is Euclidean
(from axiom 5). -/
private theorem k5_canonical_FC : k5FC (CanonicalModel (@K5Axiom Atom)) :=
  canonical_eucl_from_5
    (fun φ ψ => ⟨.implyK, by decide, φ, ψ, rfl⟩)
    (fun φ ψ χ => ⟨.implyS, by decide, φ, ψ, χ, rfl⟩)
    (fun φ ψ => ⟨.modalK, by decide, φ, ψ, rfl⟩)
    (fun φ => ⟨.modalFive, by decide, φ, rfl⟩)

/-- Pre-applied K5 truth lemma: satisfaction at world `S` iff membership in `S.val`. -/
private theorem k5_truth_lemma_applied (S : CanonicalWorld (@K5Axiom Atom))
    (φ : Proposition Atom) :
    Satisfies (CanonicalModel (@K5Axiom Atom)) S φ ↔ φ ∈ S.val :=
  canonicalTruthLemmaOfKCore (by decide) S φ

/-- `kCore ⊆ k5Tags`: feeds the `holds*` helpers so `k5_strong_completeness`/`k5_compactness`
below share this single subset fact instead of repeating 4 `by decide` witnesses. -/
private theorem coreSubset : kCore ⊆ k5Tags := by decide

/-- K5 soundness adapter matching the `strong_soundness` callback shape.
The frame condition for K5 is `k5FC m = ∀ w₁ w₂ w₃, m.r w₁ w₂ → m.r w₁ w₃ → m.r w₂ w₃`. -/
private theorem k5_sound_cb {World : Type u} (m : Model World Atom) (w : World)
    (L : List (Proposition Atom))
    (hFC : k5FC m)
    (d : DerivationTree (@K5Axiom Atom) L phi)
    (h_ctx : ∀ γ ∈ L, Satisfies m w γ) : Satisfies m w phi :=
  k5_soundness d m hFC w h_ctx

/-! ## K5 Strong Soundness -/

/-- **Strong Soundness for K5**: If `phi` is set-derivable from `Gamma` using `K5Axiom`,
then `phi` is a semantic consequence of `Gamma` over all Euclidean frames.

For any Euclidean model `m` and any world `w` satisfying all of `Gamma`, `phi`
holds at `w`. -/
theorem k5_strong_soundness {Gamma : Set (Proposition Atom)} {phi : Proposition Atom}
    (h : ModalSetDerivable (@K5Axiom Atom) Gamma phi)
    (World : Type u) (m : Model World Atom) (w : World)
    (h_eucl : ∀ w₁ w₂ w₃, m.r w₁ w₂ → m.r w₁ w₃ → m.r w₂ w₃)
    (h_sat : ∀ γ ∈ Gamma, Satisfies m w γ) : Satisfies m w phi :=
  strong_soundness (Axioms := @K5Axiom Atom) (FC := k5FC)
    k5_sound_cb h World m w h_eucl h_sat

/-! ## K5 Strong Completeness -/

/-- **Strong Completeness for K5**: If `phi` is a semantic consequence of `Gamma`
over all Euclidean frames, then `phi` is set-derivable from `Gamma` using `K5Axiom`.

Delegates to the parametric `strong_completeness` with `k5_truth_lemma_applied`
and `k5_canonical_FC`. -/
theorem k5_strong_completeness {Gamma : Set (Proposition Atom)} {phi : Proposition Atom}
    (h : ∀ (World : Type u) (m : Model World Atom) (w : World),
        (∀ w₁ w₂ w₃, m.r w₁ w₂ → m.r w₁ w₃ → m.r w₂ w₃) →
        (∀ γ ∈ Gamma, Satisfies m w γ) →
        Satisfies m w phi) :
    ModalSetDerivable (@K5Axiom Atom) Gamma phi :=
  strong_completeness (Axioms := @K5Axiom Atom) (FC := k5FC)
    (holdsImplyK coreSubset)
    (holdsImplyS coreSubset)
    (holdsEfq coreSubset)
    (holdsPeirce coreSubset)
    k5_truth_lemma_applied
    k5_canonical_FC
    (fun World m w hFC h_sat => h World m w hFC h_sat)

/-! ## K5 Biconditional Wrapper -/

/-- **Strong Soundness and Completeness for K5**:
`phi` is a semantic consequence of `Gamma` over all Euclidean frames iff `phi` is
set-derivable from `Gamma` using `K5Axiom`. -/
theorem k5_strong_completeness_iff {Gamma : Set (Proposition Atom)} {phi : Proposition Atom} :
    (∀ (World : Type u) (m : Model World Atom) (w : World),
        (∀ w₁ w₂ w₃, m.r w₁ w₂ → m.r w₁ w₃ → m.r w₂ w₃) →
        (∀ γ ∈ Gamma, Satisfies m w γ) →
        Satisfies m w phi) ↔
    ModalSetDerivable (@K5Axiom Atom) Gamma phi :=
  ⟨k5_strong_completeness, fun h World m w h_eucl h_sat =>
    k5_strong_soundness h World m w h_eucl h_sat⟩

/-! ## K5 Compactness -/

/-- **Compactness for K5 Semantics**: If `phi` is a semantic consequence of `Gamma`
over all Euclidean frames, there exists a finite list `L ⊆ Gamma` such that
`phi` is a semantic consequence of (members of) `L` over all Euclidean frames. -/
theorem k5_compactness {Gamma : Set (Proposition Atom)} {phi : Proposition Atom}
    (h : ∀ (World : Type u) (m : Model World Atom) (w : World),
        (∀ w₁ w₂ w₃, m.r w₁ w₂ → m.r w₁ w₃ → m.r w₂ w₃) →
        (∀ γ ∈ Gamma, Satisfies m w γ) →
        Satisfies m w phi) :
    ∃ L : List (Proposition Atom),
      (∀ x ∈ L, x ∈ Gamma) ∧
      ∀ (World : Type u) (m : Model World Atom) (w : World),
        (∀ w₁ w₂ w₃, m.r w₁ w₂ → m.r w₁ w₃ → m.r w₂ w₃) →
        (∀ γ ∈ {ψ | ψ ∈ L}, Satisfies m w γ) →
        Satisfies m w phi := by
  obtain ⟨L, hL_sub, hL_sem⟩ :=
    compactness (Axioms := @K5Axiom Atom) (FC := k5FC)
      k5_sound_cb
      (holdsImplyK coreSubset)
      (holdsImplyS coreSubset)
      (holdsEfq coreSubset)
      (holdsPeirce coreSubset)
      k5_truth_lemma_applied
      k5_canonical_FC
      (fun World m w hFC h_sat => h World m w hFC h_sat)
  exact ⟨L, hL_sub, fun World m w h_eucl h_sat => hL_sem World m w h_eucl h_sat⟩

/-! ## K5 Weak Completeness (Corollary) -/

/-- **Completeness Theorem for Modal Logic K5** (corollary of strong completeness):

If `phi` is valid over all Euclidean frames, then `phi` is K5-derivable
from the empty context.

This is a corollary of `k5_strong_completeness` instantiated at `Gamma = ∅`. -/
theorem k5_completeness (φ : Proposition Atom)
    (h_valid : ∀ (World : Type u) (m : Model World Atom),
      (∀ w₁ w₂ w₃, m.r w₁ w₂ → m.r w₁ w₃ → m.r w₂ w₃) →
      ∀ w, Satisfies m w φ) :
    Derivable (@K5Axiom Atom) φ :=
  ModalSetDerivable_empty_iff.mp
    (k5_strong_completeness (fun W m w hEucl _ => h_valid W m hEucl w))

end Cslib.Logic.Modal
