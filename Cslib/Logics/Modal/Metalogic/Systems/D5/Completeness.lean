/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Modal.Metalogic.Completeness
public import Cslib.Logics.Modal.Metalogic.Systems.D5.Soundness
public import Cslib.Logics.Modal.Metalogic.Systems.D.Completeness

/-! # Strong Completeness for Modal Logic D5

This module proves strong soundness and strong completeness for modal logic D5:
semantic entailment from a set of premises `Gamma` (over all serial, Euclidean frames)
is equivalent to set-derivability using `D5Axiom`.

## Main Results

- `d5_strong_soundness`: Set-derivability from `Gamma` implies semantic entailment
  over all serial, Euclidean frames.
- `d5_strong_completeness`: Semantic entailment over serial, Euclidean frames implies
  set-derivability from `Gamma`.
- `d5_strong_completeness_iff`: Biconditional combining the above.
- `d5_completeness`: Weak completeness (corollary of strong completeness).
- `d5_compactness`: If `phi` is a D5-semantic consequence of `Gamma`, there exists
  a finite list `L ⊆ Gamma` such that `phi` is a D5-semantic consequence of `L`.

## References

* [Blackburn, de Rijke, Venema, *Modal Logic*][Blackburn2001], Ch. 4
* Cslib/Logics/Modal/Metalogic/Systems/D/Completeness.lean -- D completeness
  (canonical serial, d_truth_lemma)
-/

@[expose] public section

namespace Cslib.Logic.Modal

open Cslib.Logic

universe u
variable {Atom : Type u}

/-! ## D5 Frame Condition and Canonical Witness -/

/-- The D5 frame condition: every model whose accessibility relation is serial and
Euclidean. -/
def d5FC : ∀ {World : Type u}, Model World Atom → Prop :=
  fun m => Relation.Serial m.r ∧ (∀ w₁ w₂ w₃, m.r w₁ w₂ → m.r w₁ w₃ → m.r w₂ w₃)

/-- The canonical D5 model satisfies `d5FC`: its accessibility relation is serial
and Euclidean. -/
private theorem d5_canonical_FC : d5FC (CanonicalModel (@D5Axiom Atom)) := by
  constructor
  · constructor
    intro S
    exact d_canonical_serial
      (fun φ ψ => D5Axiom.implyK φ ψ) (fun φ ψ χ => D5Axiom.implyS φ ψ χ)
      (fun φ => D5Axiom.efq φ) (fun φ ψ => D5Axiom.modalK φ ψ) (fun φ => D5Axiom.modalD φ) S
  · exact canonical_eucl_from_5
      (fun φ ψ => D5Axiom.implyK φ ψ) (fun φ ψ χ => D5Axiom.implyS φ ψ χ)
      (fun φ ψ => D5Axiom.modalK φ ψ) (fun φ => D5Axiom.modalFive φ)

/-- Pre-applied D5 truth lemma: satisfaction at world `S` iff membership in `S.val`. -/
private theorem d5_truth_lemma_applied (S : CanonicalWorld (@D5Axiom Atom))
    (φ : Proposition Atom) :
    Satisfies (CanonicalModel (@D5Axiom Atom)) S φ ↔ φ ∈ S.val :=
  d_truth_lemma
    (fun φ ψ => .implyK φ ψ) (fun φ ψ χ => .implyS φ ψ χ)
    (fun φ => .efq φ) (fun φ ψ => .peirce φ ψ)
    (fun φ ψ => .modalK φ ψ) (fun φ => .modalD φ)
    (fun φ ψ => .andI φ ψ) (fun φ ψ => .andE1 φ ψ) (fun φ ψ => .andE2 φ ψ)
    (fun φ ψ => .orI1 φ ψ) (fun φ ψ => .orI2 φ ψ) (fun φ ψ χ => .orE φ ψ χ)
    (fun φ => .diaDualityFwd φ) (fun φ => .diaDualityBack φ) S φ

/-- D5 soundness adapter matching the `strong_soundness` callback shape. -/
private theorem d5_sound_cb {World : Type u} (m : Model World Atom) (w : World)
    (L : List (Proposition Atom))
    (hFC : d5FC m)
    (d : DerivationTree (@D5Axiom Atom) L phi)
    (h_ctx : ∀ γ ∈ L, Satisfies m w γ) : Satisfies m w phi :=
  d5_soundness d m hFC.1 hFC.2 w h_ctx

/-! ## D5 Strong Soundness -/

/-- **Strong Soundness for D5**: If `phi` is set-derivable from `Gamma` using `D5Axiom`,
then `phi` is a semantic consequence of `Gamma` over all serial, Euclidean frames.

For any serial, Euclidean model `m` and any world `w` satisfying all of `Gamma`, `phi`
holds at `w`. -/
theorem d5_strong_soundness {Gamma : Set (Proposition Atom)} {phi : Proposition Atom}
    (h : ModalSetDerivable (@D5Axiom Atom) Gamma phi)
    (World : Type u) (m : Model World Atom) (w : World)
    (h_serial : Relation.Serial m.r)
    (h_eucl : ∀ w₁ w₂ w₃, m.r w₁ w₂ → m.r w₁ w₃ → m.r w₂ w₃)
    (h_sat : ∀ γ ∈ Gamma, Satisfies m w γ) : Satisfies m w phi :=
  strong_soundness (Axioms := @D5Axiom Atom) (FC := d5FC)
    d5_sound_cb h World m w ⟨h_serial, h_eucl⟩ h_sat

/-! ## D5 Strong Completeness -/

/-- **Strong Completeness for D5**: If `phi` is a semantic consequence of `Gamma`
over all serial, Euclidean frames, then `phi` is set-derivable from `Gamma`
using `D5Axiom`.

Delegates to the parametric `strong_completeness` with `d5_truth_lemma_applied`
and `d5_canonical_FC`. -/
theorem d5_strong_completeness {Gamma : Set (Proposition Atom)} {phi : Proposition Atom}
    (h : ∀ (World : Type u) (m : Model World Atom) (w : World),
        Relation.Serial m.r →
        (∀ w₁ w₂ w₃, m.r w₁ w₂ → m.r w₁ w₃ → m.r w₂ w₃) →
        (∀ γ ∈ Gamma, Satisfies m w γ) →
        Satisfies m w phi) :
    ModalSetDerivable (@D5Axiom Atom) Gamma phi :=
  strong_completeness (Axioms := @D5Axiom Atom) (FC := d5FC)
    (fun φ ψ => .implyK φ ψ) (fun φ ψ χ => .implyS φ ψ χ)
    (fun φ => .efq φ) (fun φ ψ => .peirce φ ψ)
    d5_truth_lemma_applied
    d5_canonical_FC
    (fun World m w ⟨hSer, hEucl⟩ h_sat => h World m w hSer hEucl h_sat)

/-! ## D5 Biconditional Wrapper -/

/-- **Strong Soundness and Completeness for D5**:
`phi` is a semantic consequence of `Gamma` over all serial, Euclidean frames iff `phi` is
set-derivable from `Gamma` using `D5Axiom`. -/
theorem d5_strong_completeness_iff {Gamma : Set (Proposition Atom)} {phi : Proposition Atom} :
    (∀ (World : Type u) (m : Model World Atom) (w : World),
        Relation.Serial m.r →
        (∀ w₁ w₂ w₃, m.r w₁ w₂ → m.r w₁ w₃ → m.r w₂ w₃) →
        (∀ γ ∈ Gamma, Satisfies m w γ) →
        Satisfies m w phi) ↔
    ModalSetDerivable (@D5Axiom Atom) Gamma phi :=
  ⟨d5_strong_completeness, fun h World m w h_serial h_eucl h_sat =>
    d5_strong_soundness h World m w h_serial h_eucl h_sat⟩

/-! ## D5 Compactness -/

/-- **Compactness for D5 Semantics**: If `phi` is a semantic consequence of `Gamma`
over all serial, Euclidean frames, there exists a finite list `L ⊆ Gamma` such that
`phi` is a semantic consequence of (members of) `L` over all serial, Euclidean frames. -/
theorem d5_compactness {Gamma : Set (Proposition Atom)} {phi : Proposition Atom}
    (h : ∀ (World : Type u) (m : Model World Atom) (w : World),
        Relation.Serial m.r →
        (∀ w₁ w₂ w₃, m.r w₁ w₂ → m.r w₁ w₃ → m.r w₂ w₃) →
        (∀ γ ∈ Gamma, Satisfies m w γ) →
        Satisfies m w phi) :
    ∃ L : List (Proposition Atom),
      (∀ x ∈ L, x ∈ Gamma) ∧
      ∀ (World : Type u) (m : Model World Atom) (w : World),
        Relation.Serial m.r →
        (∀ w₁ w₂ w₃, m.r w₁ w₂ → m.r w₁ w₃ → m.r w₂ w₃) →
        (∀ γ ∈ {ψ | ψ ∈ L}, Satisfies m w γ) →
        Satisfies m w phi := by
  obtain ⟨L, hL_sub, hL_sem⟩ :=
    compactness (Axioms := @D5Axiom Atom) (FC := d5FC)
      d5_sound_cb
      (fun φ ψ => .implyK φ ψ) (fun φ ψ χ => .implyS φ ψ χ)
      (fun φ => .efq φ) (fun φ ψ => .peirce φ ψ)
      d5_truth_lemma_applied
      d5_canonical_FC
      (fun World m w ⟨hSer, hEucl⟩ h_sat => h World m w hSer hEucl h_sat)
  exact ⟨L, hL_sub, fun World m w h_serial h_eucl h_sat =>
    hL_sem World m w ⟨h_serial, h_eucl⟩ h_sat⟩

/-! ## D5 Weak Completeness (Corollary) -/

/-- **Completeness Theorem for Modal Logic D5** (corollary of strong completeness):

If `phi` is valid over all serial, Euclidean frames, then `phi` is D5-derivable
from the empty context.

This is a corollary of `d5_strong_completeness` instantiated at `Gamma = ∅`. -/
theorem d5_completeness (φ : Proposition Atom)
    (h_valid : ∀ (World : Type u) (m : Model World Atom),
      Relation.Serial m.r →
      (∀ w₁ w₂ w₃, m.r w₁ w₂ → m.r w₁ w₃ → m.r w₂ w₃) →
      ∀ w, Satisfies m w φ) :
    Derivable (@D5Axiom Atom) φ :=
  ModalSetDerivable_empty_iff.mp
    (d5_strong_completeness (fun W m w hSer hEucl _ => h_valid W m hSer hEucl w))

end Cslib.Logic.Modal
