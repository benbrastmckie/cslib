/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Modal.Metalogic.Completeness
public import Cslib.Logics.Modal.Metalogic.Systems.B.Soundness
public import Cslib.Logics.Modal.ProofSystem.Instances

/-! # Strong Completeness for Modal Logic B (KB)

This module proves strong soundness and strong completeness for modal logic B:
semantic entailment from a set of premises `Gamma` (over all symmetric frames)
is equivalent to set-derivability using `BAxiom`.

## Main Results

- `b_strong_soundness`: Set-derivability from `Gamma` implies semantic entailment
  over all symmetric frames.
- `b_strong_completeness`: Semantic entailment over symmetric frames implies
  set-derivability from `Gamma`.
- `b_strong_completeness_iff`: Biconditional combining the above.
- `b_completeness`: Weak completeness (corollary of strong completeness).
- `b_compactness`: If `phi` is a B-semantic consequence of `Gamma`, there exists
  a finite list `L ⊆ Gamma` such that `phi` is a B-semantic consequence of `L`.

## References

* [Blackburn, de Rijke, Venema, *Modal Logic*][Blackburn2001], Ch. 4, Thm 4.28 cl.2
-/

@[expose] public section

namespace Cslib.Logic.Modal

open Cslib.Logic

universe u
variable {Atom : Type u}

/-! ## B Frame Condition and Canonical Witness -/

/-- The B frame condition: every model whose accessibility relation is symmetric. -/
def bFC : ∀ {World : Type u}, Model World Atom → Prop :=
  fun m => ∀ w₁ w₂, m.r w₁ w₂ → m.r w₂ w₁

/-- The canonical B model satisfies `bFC`: its accessibility relation is symmetric. -/
private theorem b_canonical_FC : bFC (CanonicalModel (@BAxiom Atom)) :=
  canonical_symm
    (fun φ ψ => ⟨.implyK, by decide, φ, ψ, rfl⟩)
    (fun φ ψ χ => ⟨.implyS, by decide, φ, ψ, χ, rfl⟩)
    (fun φ ψ => ⟨.modalK, by decide, φ, ψ, rfl⟩)
    (fun φ => ⟨.modalB, by decide, φ, rfl⟩)

/-- Pre-applied B truth lemma: satisfaction at world `S` iff membership in `S.val`. -/
private theorem b_truth_lemma_applied (S : CanonicalWorld (@BAxiom Atom))
    (φ : Proposition Atom) :
    Satisfies (CanonicalModel (@BAxiom Atom)) S φ ↔ φ ∈ S.val :=
  canonicalTruthLemmaOfKCore (by decide) S φ

/-- `kCore ⊆ bTags`: feeds the `holds*` helpers so `b_strong_completeness`/`b_compactness`
below share this single subset fact instead of repeating 4 `by decide` witnesses. -/
private theorem coreSubset : kCore ⊆ bTags := by decide

/-- B soundness adapter matching the `strong_soundness` callback shape.
The frame condition for B is `bFC m = ∀ w₁ w₂, m.r w₁ w₂ → m.r w₂ w₁`. -/
private theorem b_sound_cb {World : Type u} (m : Model World Atom) (w : World)
    (L : List (Proposition Atom))
    (hFC : bFC m)
    (d : DerivationTree (@BAxiom Atom) L phi)
    (h_ctx : ∀ γ ∈ L, Satisfies m w γ) : Satisfies m w phi :=
  b_soundness d m hFC w h_ctx

/-! ## B Strong Soundness -/

/-- **Strong Soundness for B**: If `phi` is set-derivable from `Gamma` using `BAxiom`,
then `phi` is a semantic consequence of `Gamma` over all symmetric frames.

For any symmetric model `m` and any world `w` satisfying all of `Gamma`, `phi`
holds at `w`. -/
theorem b_strong_soundness {Gamma : Set (Proposition Atom)} {phi : Proposition Atom}
    (h : ModalSetDerivable (@BAxiom Atom) Gamma phi)
    (World : Type u) (m : Model World Atom) (w : World)
    (h_symm : ∀ w₁ w₂, m.r w₁ w₂ → m.r w₂ w₁)
    (h_sat : ∀ γ ∈ Gamma, Satisfies m w γ) : Satisfies m w phi :=
  strong_soundness (Axioms := @BAxiom Atom) (FC := bFC)
    b_sound_cb h World m w h_symm h_sat

/-! ## B Strong Completeness -/

/-- **Strong Completeness for B**: If `phi` is a semantic consequence of `Gamma`
over all symmetric frames, then `phi` is set-derivable from `Gamma` using `BAxiom`.

Delegates to the parametric `strong_completeness` with `b_truth_lemma_applied`
and `b_canonical_FC`. -/
theorem b_strong_completeness {Gamma : Set (Proposition Atom)} {phi : Proposition Atom}
    (h : ∀ (World : Type u) (m : Model World Atom) (w : World),
        (∀ w₁ w₂, m.r w₁ w₂ → m.r w₂ w₁) →
        (∀ γ ∈ Gamma, Satisfies m w γ) →
        Satisfies m w phi) :
    ModalSetDerivable (@BAxiom Atom) Gamma phi :=
  strong_completeness (Axioms := @BAxiom Atom) (FC := bFC)
    (holdsImplyK coreSubset)
    (holdsImplyS coreSubset)
    (holdsEfq coreSubset)
    (holdsPeirce coreSubset)
    b_truth_lemma_applied
    b_canonical_FC
    (fun World m w hFC h_sat => h World m w hFC h_sat)

/-! ## B Biconditional Wrapper -/

/-- **Strong Soundness and Completeness for B**:
`phi` is a semantic consequence of `Gamma` over all symmetric frames iff `phi` is
set-derivable from `Gamma` using `BAxiom`. -/
theorem b_strong_completeness_iff {Gamma : Set (Proposition Atom)} {phi : Proposition Atom} :
    (∀ (World : Type u) (m : Model World Atom) (w : World),
        (∀ w₁ w₂, m.r w₁ w₂ → m.r w₂ w₁) →
        (∀ γ ∈ Gamma, Satisfies m w γ) →
        Satisfies m w phi) ↔
    ModalSetDerivable (@BAxiom Atom) Gamma phi :=
  ⟨b_strong_completeness, fun h World m w h_symm h_sat =>
    b_strong_soundness h World m w h_symm h_sat⟩

/-! ## B Compactness -/

/-- **Compactness for B Semantics**: If `phi` is a semantic consequence of `Gamma`
over all symmetric frames, there exists a finite list `L ⊆ Gamma` such that
`phi` is a semantic consequence of (members of) `L` over all symmetric frames. -/
theorem b_compactness {Gamma : Set (Proposition Atom)} {phi : Proposition Atom}
    (h : ∀ (World : Type u) (m : Model World Atom) (w : World),
        (∀ w₁ w₂, m.r w₁ w₂ → m.r w₂ w₁) →
        (∀ γ ∈ Gamma, Satisfies m w γ) →
        Satisfies m w phi) :
    ∃ L : List (Proposition Atom),
      (∀ x ∈ L, x ∈ Gamma) ∧
      ∀ (World : Type u) (m : Model World Atom) (w : World),
        (∀ w₁ w₂, m.r w₁ w₂ → m.r w₂ w₁) →
        (∀ γ ∈ {ψ | ψ ∈ L}, Satisfies m w γ) →
        Satisfies m w phi := by
  obtain ⟨L, hL_sub, hL_sem⟩ :=
    compactness (Axioms := @BAxiom Atom) (FC := bFC)
      b_sound_cb
      (holdsImplyK coreSubset)
      (holdsImplyS coreSubset)
      (holdsEfq coreSubset)
      (holdsPeirce coreSubset)
      b_truth_lemma_applied
      b_canonical_FC
      (fun World m w hFC h_sat => h World m w hFC h_sat)
  exact ⟨L, hL_sub, fun World m w h_symm h_sat => hL_sem World m w h_symm h_sat⟩

/-! ## B Weak Completeness (Corollary) -/

/-- **Completeness Theorem for Modal Logic B** (corollary of strong completeness):

If `phi` is valid over all symmetric frames, then `phi` is B-derivable
from the empty context.

This is a corollary of `b_strong_completeness` instantiated at `Gamma = ∅`. -/
theorem b_completeness (φ : Proposition Atom)
    (h_valid : ∀ (World : Type u) (m : Model World Atom),
      (∀ w₁ w₂, m.r w₁ w₂ → m.r w₂ w₁) → ∀ w, Satisfies m w φ) :
    Derivable (@BAxiom Atom) φ :=
  ModalSetDerivable_empty_iff.mp
    (b_strong_completeness (fun W m w hSymm _ => h_valid W m hSymm w))

end Cslib.Logic.Modal
