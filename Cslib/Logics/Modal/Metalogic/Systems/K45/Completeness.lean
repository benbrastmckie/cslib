/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Modal.Metalogic.Completeness
public import Cslib.Logics.Modal.Metalogic.Systems.K45.Soundness
public import Cslib.Logics.Modal.Metalogic.Systems.K.Completeness
public import Cslib.Logics.Modal.ProofSystem.Instances

/-! # Strong Completeness for Modal Logic K45

This module proves strong soundness and strong completeness for modal logic K45:
semantic entailment from a set of premises `Gamma` (over all transitive, Euclidean
frames) is equivalent to set-derivability using `K45Axiom`.

## Main Results

- `k45_strong_soundness`: Set-derivability from `Gamma` implies semantic entailment.
- `k45_strong_completeness`: Semantic entailment implies set-derivability from `Gamma`.
- `k45_strong_completeness_iff`: Biconditional combining the above.
- `k45_completeness`: Weak completeness (corollary of strong completeness).
- `k45_compactness`: Compactness for K45 semantics.

## References

* [Blackburn, de Rijke, Venema, *Modal Logic*][Blackburn2001], Ch. 4, Thm 4.27
-/

@[expose] public section

namespace Cslib.Logic.Modal

open Cslib.Logic

universe u
variable {Atom : Type u}

/-! ## K45 Frame Condition and Canonical Witness -/

/-- The K45 frame condition: every model whose accessibility relation is transitive and
Euclidean. -/
def k45FC : ∀ {World : Type u}, Model World Atom → Prop :=
  fun m => (∀ w₁ w₂ w₃, m.r w₁ w₂ → m.r w₂ w₃ → m.r w₁ w₃) ∧
           (∀ w₁ w₂ w₃, m.r w₁ w₂ → m.r w₁ w₃ → m.r w₂ w₃)

/-- The canonical K45 model satisfies `k45FC`: its accessibility relation is transitive
and Euclidean (from axioms 4 and 5). -/
private theorem k45_canonical_FC : k45FC (CanonicalModel (@K45Axiom Atom)) :=
  ⟨canonical_trans
      (fun φ ψ => (schemaUnion_k45Tags_iff_K45Axiom).mp ⟨.implyK, by decide, φ, ψ, rfl⟩)
      (fun φ ψ χ => (schemaUnion_k45Tags_iff_K45Axiom).mp ⟨.implyS, by decide, φ, ψ, χ, rfl⟩)
      (fun φ => (schemaUnion_k45Tags_iff_K45Axiom).mp ⟨.modalFour, by decide, φ, rfl⟩),
   canonical_eucl_from_5
      (fun φ ψ => (schemaUnion_k45Tags_iff_K45Axiom).mp ⟨.implyK, by decide, φ, ψ, rfl⟩)
      (fun φ ψ χ => (schemaUnion_k45Tags_iff_K45Axiom).mp ⟨.implyS, by decide, φ, ψ, χ, rfl⟩)
      (fun φ ψ => (schemaUnion_k45Tags_iff_K45Axiom).mp ⟨.modalK, by decide, φ, ψ, rfl⟩)
      (fun φ => (schemaUnion_k45Tags_iff_K45Axiom).mp ⟨.modalFive, by decide, φ, rfl⟩)⟩

/-- Pre-applied K45 truth lemma: satisfaction at world `S` iff membership in `S.val`. -/
private theorem k45_truth_lemma_applied (S : CanonicalWorld (@K45Axiom Atom))
    (φ : Proposition Atom) :
    Satisfies (CanonicalModel (@K45Axiom Atom)) S φ ↔ φ ∈ S.val :=
  k_truth_lemma
    (fun φ ψ => (schemaUnion_k45Tags_iff_K45Axiom).mp ⟨.implyK, by decide, φ, ψ, rfl⟩)
    (fun φ ψ χ => (schemaUnion_k45Tags_iff_K45Axiom).mp ⟨.implyS, by decide, φ, ψ, χ, rfl⟩)
    (fun φ => (schemaUnion_k45Tags_iff_K45Axiom).mp ⟨.efq, by decide, φ, rfl⟩)
    (fun φ ψ => (schemaUnion_k45Tags_iff_K45Axiom).mp ⟨.peirce, by decide, φ, ψ, rfl⟩)
    (fun φ ψ => (schemaUnion_k45Tags_iff_K45Axiom).mp ⟨.modalK, by decide, φ, ψ, rfl⟩)
    (fun φ ψ => (schemaUnion_k45Tags_iff_K45Axiom).mp ⟨.andI, by decide, φ, ψ, rfl⟩)
    (fun φ ψ => (schemaUnion_k45Tags_iff_K45Axiom).mp ⟨.andE1, by decide, φ, ψ, rfl⟩)
    (fun φ ψ => (schemaUnion_k45Tags_iff_K45Axiom).mp ⟨.andE2, by decide, φ, ψ, rfl⟩)
    (fun φ ψ => (schemaUnion_k45Tags_iff_K45Axiom).mp ⟨.orI1, by decide, φ, ψ, rfl⟩)
    (fun φ ψ => (schemaUnion_k45Tags_iff_K45Axiom).mp ⟨.orI2, by decide, φ, ψ, rfl⟩)
    (fun φ ψ χ => (schemaUnion_k45Tags_iff_K45Axiom).mp ⟨.orE, by decide, φ, ψ, χ, rfl⟩)
    (fun φ => (schemaUnion_k45Tags_iff_K45Axiom).mp ⟨.diaDualityFwd, by decide, φ, rfl⟩)
    (fun φ => (schemaUnion_k45Tags_iff_K45Axiom).mp ⟨.diaDualityBack, by decide, φ, rfl⟩)
    S φ

/-- K45 soundness adapter matching the `strong_soundness` callback shape.
The frame condition for K45 is `k45FC m = (trans) ∧ (eucl)`. -/
private theorem k45_sound_cb {World : Type u} (m : Model World Atom) (w : World)
    (L : List (Proposition Atom))
    (hFC : k45FC m)
    (d : DerivationTree (@K45Axiom Atom) L phi)
    (h_ctx : ∀ γ ∈ L, Satisfies m w γ) : Satisfies m w phi :=
  k45_soundness d m hFC.1 hFC.2 w h_ctx

/-! ## K45 Strong Soundness -/

/-- **Strong Soundness for K45**: If `phi` is set-derivable from `Gamma` using `K45Axiom`,
then `phi` is a semantic consequence of `Gamma` over all transitive, Euclidean frames.

For any transitive, Euclidean model `m` and any world `w` satisfying all of `Gamma`,
`phi` holds at `w`. -/
theorem k45_strong_soundness {Gamma : Set (Proposition Atom)} {phi : Proposition Atom}
    (h : ModalSetDerivable (@K45Axiom Atom) Gamma phi)
    (World : Type u) (m : Model World Atom) (w : World)
    (h_trans : ∀ w₁ w₂ w₃, m.r w₁ w₂ → m.r w₂ w₃ → m.r w₁ w₃)
    (h_eucl : ∀ w₁ w₂ w₃, m.r w₁ w₂ → m.r w₁ w₃ → m.r w₂ w₃)
    (h_sat : ∀ γ ∈ Gamma, Satisfies m w γ) : Satisfies m w phi :=
  strong_soundness (Axioms := @K45Axiom Atom) (FC := k45FC)
    k45_sound_cb h World m w ⟨h_trans, h_eucl⟩ h_sat

/-! ## K45 Strong Completeness -/

/-- **Strong Completeness for K45**: If `phi` is a semantic consequence of `Gamma`
over all transitive, Euclidean frames, then `phi` is set-derivable from `Gamma`
using `K45Axiom`.

Delegates to the parametric `strong_completeness` with `k_truth_lemma_applied`
and `k45_canonical_FC`. -/
theorem k45_strong_completeness {Gamma : Set (Proposition Atom)} {phi : Proposition Atom}
    (h : ∀ (World : Type u) (m : Model World Atom) (w : World),
        (∀ w₁ w₂ w₃, m.r w₁ w₂ → m.r w₂ w₃ → m.r w₁ w₃) →
        (∀ w₁ w₂ w₃, m.r w₁ w₂ → m.r w₁ w₃ → m.r w₂ w₃) →
        (∀ γ ∈ Gamma, Satisfies m w γ) →
        Satisfies m w phi) :
    ModalSetDerivable (@K45Axiom Atom) Gamma phi :=
  strong_completeness (Axioms := @K45Axiom Atom) (FC := k45FC)
    (fun φ ψ => (schemaUnion_k45Tags_iff_K45Axiom).mp ⟨.implyK, by decide, φ, ψ, rfl⟩)
    (fun φ ψ χ => (schemaUnion_k45Tags_iff_K45Axiom).mp ⟨.implyS, by decide, φ, ψ, χ, rfl⟩)
    (fun φ => (schemaUnion_k45Tags_iff_K45Axiom).mp ⟨.efq, by decide, φ, rfl⟩)
    (fun φ ψ => (schemaUnion_k45Tags_iff_K45Axiom).mp ⟨.peirce, by decide, φ, ψ, rfl⟩)
    k45_truth_lemma_applied
    k45_canonical_FC
    (fun World m w ⟨hTrans, hEucl⟩ h_sat => h World m w hTrans hEucl h_sat)

/-! ## K45 Biconditional Wrapper -/

/-- **Strong Soundness and Completeness for K45**:
`phi` is a semantic consequence of `Gamma` over all transitive, Euclidean frames
iff `phi` is set-derivable from `Gamma` using `K45Axiom`. -/
theorem k45_strong_completeness_iff {Gamma : Set (Proposition Atom)} {phi : Proposition Atom} :
    (∀ (World : Type u) (m : Model World Atom) (w : World),
        (∀ w₁ w₂ w₃, m.r w₁ w₂ → m.r w₂ w₃ → m.r w₁ w₃) →
        (∀ w₁ w₂ w₃, m.r w₁ w₂ → m.r w₁ w₃ → m.r w₂ w₃) →
        (∀ γ ∈ Gamma, Satisfies m w γ) →
        Satisfies m w phi) ↔
    ModalSetDerivable (@K45Axiom Atom) Gamma phi :=
  ⟨k45_strong_completeness, fun h World m w h_trans h_eucl h_sat =>
    k45_strong_soundness h World m w h_trans h_eucl h_sat⟩

/-! ## K45 Compactness -/

/-- **Compactness for K45 Semantics**: If `phi` is a semantic consequence of `Gamma`
over all transitive, Euclidean frames, there exists a finite list `L ⊆ Gamma` such
that `phi` is a semantic consequence of (members of) `L` over all transitive,
Euclidean frames. -/
theorem k45_compactness {Gamma : Set (Proposition Atom)} {phi : Proposition Atom}
    (h : ∀ (World : Type u) (m : Model World Atom) (w : World),
        (∀ w₁ w₂ w₃, m.r w₁ w₂ → m.r w₂ w₃ → m.r w₁ w₃) →
        (∀ w₁ w₂ w₃, m.r w₁ w₂ → m.r w₁ w₃ → m.r w₂ w₃) →
        (∀ γ ∈ Gamma, Satisfies m w γ) →
        Satisfies m w phi) :
    ∃ L : List (Proposition Atom),
      (∀ x ∈ L, x ∈ Gamma) ∧
      ∀ (World : Type u) (m : Model World Atom) (w : World),
        (∀ w₁ w₂ w₃, m.r w₁ w₂ → m.r w₂ w₃ → m.r w₁ w₃) →
        (∀ w₁ w₂ w₃, m.r w₁ w₂ → m.r w₁ w₃ → m.r w₂ w₃) →
        (∀ γ ∈ {ψ | ψ ∈ L}, Satisfies m w γ) →
        Satisfies m w phi := by
  obtain ⟨L, hL_sub, hL_sem⟩ :=
    compactness (Axioms := @K45Axiom Atom) (FC := k45FC)
      k45_sound_cb
      (fun φ ψ => (schemaUnion_k45Tags_iff_K45Axiom).mp ⟨.implyK, by decide, φ, ψ, rfl⟩)
      (fun φ ψ χ => (schemaUnion_k45Tags_iff_K45Axiom).mp ⟨.implyS, by decide, φ, ψ, χ, rfl⟩)
      (fun φ => (schemaUnion_k45Tags_iff_K45Axiom).mp ⟨.efq, by decide, φ, rfl⟩)
      (fun φ ψ => (schemaUnion_k45Tags_iff_K45Axiom).mp ⟨.peirce, by decide, φ, ψ, rfl⟩)
      k45_truth_lemma_applied
      k45_canonical_FC
      (fun World m w ⟨hTrans, hEucl⟩ h_sat => h World m w hTrans hEucl h_sat)
  exact ⟨L, hL_sub, fun World m w h_trans h_eucl h_sat =>
    hL_sem World m w ⟨h_trans, h_eucl⟩ h_sat⟩

/-! ## K45 Weak Completeness (Corollary) -/

/-- **Completeness Theorem for K45 Modal Logic** (corollary of strong completeness):

If `phi` is valid over all transitive, Euclidean frames, then `phi` is K45-derivable
from the empty context.

This is a corollary of `k45_strong_completeness` instantiated at `Gamma = ∅`. -/
theorem k45_completeness (φ : Proposition Atom)
    (h_valid : ∀ (World : Type u) (m : Model World Atom),
      (∀ w₁ w₂ w₃, m.r w₁ w₂ → m.r w₂ w₃ → m.r w₁ w₃) →
      (∀ w₁ w₂ w₃, m.r w₁ w₂ → m.r w₁ w₃ → m.r w₂ w₃) →
      ∀ w, Satisfies m w φ) :
    Derivable (@K45Axiom Atom) φ :=
  ModalSetDerivable_empty_iff.mp
    (k45_strong_completeness (fun W m w hTrans hEucl _ => h_valid W m hTrans hEucl w))

end Cslib.Logic.Modal
