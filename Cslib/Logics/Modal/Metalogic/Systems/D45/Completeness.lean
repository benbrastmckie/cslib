/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Modal.Metalogic.Completeness
public import Cslib.Logics.Modal.Metalogic.Systems.D45.Soundness

/-! # Strong Completeness for Modal Logic D45

This module proves strong soundness and strong completeness for modal logic D45:
semantic entailment from a set of premises `Gamma` (over all serial, transitive, Euclidean
frames) is equivalent to set-derivability using `D45Axiom`.

## Main Results

- `d45_strong_soundness`: Set-derivability from `Gamma` implies semantic entailment
  over all serial, transitive, Euclidean frames.
- `d45_strong_completeness`: Semantic entailment over serial, transitive, Euclidean frames
  implies set-derivability from `Gamma`.
- `d45_strong_completeness_iff`: Biconditional combining the above.
- `d45_completeness`: Weak completeness (corollary of strong completeness).
- `d45_compactness`: If `phi` is a D45-semantic consequence of `Gamma`, there exists
  a finite list `L ⊆ Gamma` such that `phi` is a D45-semantic consequence of `L`.

## References

* [Blackburn, de Rijke, Venema, *Modal Logic*][Blackburn2001], Ch. 4
* Cslib/Logics/Modal/Metalogic/Completeness.lean -- `d_canonical_serial` (relocated)
  and the generic `truth_lemma` / `canonicalTruthLemmaOfKCore` wrapper
-/

@[expose] public section

namespace Cslib.Logic.Modal

open Cslib.Logic

universe u
variable {Atom : Type u}

/-! ## D45 Frame Condition and Canonical Witness -/

/-- The D45 frame condition: every model whose accessibility relation is serial, transitive,
and Euclidean. -/
def d45FC : ∀ {World : Type u}, Model World Atom → Prop :=
  fun m => Relation.Serial m.r ∧
           (∀ w₁ w₂ w₃, m.r w₁ w₂ → m.r w₂ w₃ → m.r w₁ w₃) ∧
           (∀ w₁ w₂ w₃, m.r w₁ w₂ → m.r w₁ w₃ → m.r w₂ w₃)

/-- The canonical D45 model satisfies `d45FC`: its accessibility relation is serial,
transitive, and Euclidean. -/
private theorem d45_canonical_FC : d45FC (CanonicalModel (@D45Axiom Atom)) := by
  refine ⟨?_, canonical_trans
      (fun φ ψ => ⟨.implyK, by decide, φ, ψ, rfl⟩)
      (fun φ ψ χ => ⟨.implyS, by decide, φ, ψ, χ, rfl⟩)
      (fun φ => ⟨.modalFour, by decide, φ, rfl⟩),
    canonical_eucl_from_5
      (fun φ ψ => ⟨.implyK, by decide, φ, ψ, rfl⟩)
      (fun φ ψ χ => ⟨.implyS, by decide, φ, ψ, χ, rfl⟩)
      (fun φ ψ => ⟨.modalK, by decide, φ, ψ, rfl⟩)
      (fun φ => ⟨.modalFive, by decide, φ, rfl⟩)⟩
  constructor
  intro S
  exact d_canonical_serial
    (fun φ ψ => ⟨.implyK, by decide, φ, ψ, rfl⟩)
    (fun φ ψ χ => ⟨.implyS, by decide, φ, ψ, χ, rfl⟩)
    (fun φ => ⟨.efq, by decide, φ, rfl⟩)
    (fun φ ψ => ⟨.modalK, by decide, φ, ψ, rfl⟩)
    (fun φ => ⟨.modalD, by decide, φ, rfl⟩) S

/-- Pre-applied D45 truth lemma: satisfaction at world `S` iff membership in `S.val`. -/
private theorem d45_truth_lemma_applied (S : CanonicalWorld (@D45Axiom Atom))
    (φ : Proposition Atom) :
    Satisfies (CanonicalModel (@D45Axiom Atom)) S φ ↔ φ ∈ S.val :=
  canonicalTruthLemmaOfKCore (by decide) S φ

/-- `kCore ⊆ d45Tags`: feeds the `holds*` helpers so `d45_strong_completeness`/
`d45_compactness` below share this single subset fact instead of repeating 4 `by decide`
witnesses. -/
private theorem coreSubset : kCore ⊆ d45Tags := by decide

/-- D45 soundness adapter matching the `strong_soundness` callback shape. -/
private theorem d45_sound_cb {World : Type u} (m : Model World Atom) (w : World)
    (L : List (Proposition Atom))
    (hFC : d45FC m)
    (d : DerivationTree (@D45Axiom Atom) L phi)
    (h_ctx : ∀ γ ∈ L, Satisfies m w γ) : Satisfies m w phi :=
  d45_soundness d m hFC.1 hFC.2.1 hFC.2.2 w h_ctx

/-! ## D45 Strong Soundness -/

/-- **Strong Soundness for D45**: If `phi` is set-derivable from `Gamma` using `D45Axiom`,
then `phi` is a semantic consequence of `Gamma` over all serial, transitive, Euclidean frames.

For any serial, transitive, Euclidean model `m` and any world `w` satisfying all of `Gamma`,
`phi` holds at `w`. -/
theorem d45_strong_soundness {Gamma : Set (Proposition Atom)} {phi : Proposition Atom}
    (h : ModalSetDerivable (@D45Axiom Atom) Gamma phi)
    (World : Type u) (m : Model World Atom) (w : World)
    (h_serial : Relation.Serial m.r)
    (h_trans : ∀ w₁ w₂ w₃, m.r w₁ w₂ → m.r w₂ w₃ → m.r w₁ w₃)
    (h_eucl : ∀ w₁ w₂ w₃, m.r w₁ w₂ → m.r w₁ w₃ → m.r w₂ w₃)
    (h_sat : ∀ γ ∈ Gamma, Satisfies m w γ) : Satisfies m w phi :=
  strong_soundness (Axioms := @D45Axiom Atom) (FC := d45FC)
    d45_sound_cb h World m w ⟨h_serial, h_trans, h_eucl⟩ h_sat

/-! ## D45 Strong Completeness -/

/-- **Strong Completeness for D45**: If `phi` is a semantic consequence of `Gamma`
over all serial, transitive, Euclidean frames, then `phi` is set-derivable from `Gamma`
using `D45Axiom`.

Delegates to the parametric `strong_completeness` with `d45_truth_lemma_applied`
and `d45_canonical_FC`. -/
theorem d45_strong_completeness {Gamma : Set (Proposition Atom)} {phi : Proposition Atom}
    (h : ∀ (World : Type u) (m : Model World Atom) (w : World),
        Relation.Serial m.r →
        (∀ w₁ w₂ w₃, m.r w₁ w₂ → m.r w₂ w₃ → m.r w₁ w₃) →
        (∀ w₁ w₂ w₃, m.r w₁ w₂ → m.r w₁ w₃ → m.r w₂ w₃) →
        (∀ γ ∈ Gamma, Satisfies m w γ) →
        Satisfies m w phi) :
    ModalSetDerivable (@D45Axiom Atom) Gamma phi :=
  strong_completeness (Axioms := @D45Axiom Atom) (FC := d45FC)
    (holdsImplyK coreSubset)
    (holdsImplyS coreSubset)
    (holdsEfq coreSubset)
    (holdsPeirce coreSubset)
    d45_truth_lemma_applied
    d45_canonical_FC
    (fun World m w ⟨hSer, hTrans, hEucl⟩ h_sat => h World m w hSer hTrans hEucl h_sat)

/-! ## D45 Biconditional Wrapper -/

/-- **Strong Soundness and Completeness for D45**:
`phi` is a semantic consequence of `Gamma` over all serial, transitive, Euclidean frames iff
`phi` is set-derivable from `Gamma` using `D45Axiom`. -/
theorem d45_strong_completeness_iff {Gamma : Set (Proposition Atom)} {phi : Proposition Atom} :
    (∀ (World : Type u) (m : Model World Atom) (w : World),
        Relation.Serial m.r →
        (∀ w₁ w₂ w₃, m.r w₁ w₂ → m.r w₂ w₃ → m.r w₁ w₃) →
        (∀ w₁ w₂ w₃, m.r w₁ w₂ → m.r w₁ w₃ → m.r w₂ w₃) →
        (∀ γ ∈ Gamma, Satisfies m w γ) →
        Satisfies m w phi) ↔
    ModalSetDerivable (@D45Axiom Atom) Gamma phi :=
  ⟨d45_strong_completeness, fun h World m w h_serial h_trans h_eucl h_sat =>
    d45_strong_soundness h World m w h_serial h_trans h_eucl h_sat⟩

/-! ## D45 Compactness -/

/-- **Compactness for D45 Semantics**: If `phi` is a semantic consequence of `Gamma`
over all serial, transitive, Euclidean frames, there exists a finite list `L ⊆ Gamma` such
that `phi` is a semantic consequence of (members of) `L` over all such frames. -/
theorem d45_compactness {Gamma : Set (Proposition Atom)} {phi : Proposition Atom}
    (h : ∀ (World : Type u) (m : Model World Atom) (w : World),
        Relation.Serial m.r →
        (∀ w₁ w₂ w₃, m.r w₁ w₂ → m.r w₂ w₃ → m.r w₁ w₃) →
        (∀ w₁ w₂ w₃, m.r w₁ w₂ → m.r w₁ w₃ → m.r w₂ w₃) →
        (∀ γ ∈ Gamma, Satisfies m w γ) →
        Satisfies m w phi) :
    ∃ L : List (Proposition Atom),
      (∀ x ∈ L, x ∈ Gamma) ∧
      ∀ (World : Type u) (m : Model World Atom) (w : World),
        Relation.Serial m.r →
        (∀ w₁ w₂ w₃, m.r w₁ w₂ → m.r w₂ w₃ → m.r w₁ w₃) →
        (∀ w₁ w₂ w₃, m.r w₁ w₂ → m.r w₁ w₃ → m.r w₂ w₃) →
        (∀ γ ∈ {ψ | ψ ∈ L}, Satisfies m w γ) →
        Satisfies m w phi := by
  obtain ⟨L, hL_sub, hL_sem⟩ :=
    compactness (Axioms := @D45Axiom Atom) (FC := d45FC)
      d45_sound_cb
      (holdsImplyK coreSubset)
      (holdsImplyS coreSubset)
      (holdsEfq coreSubset)
      (holdsPeirce coreSubset)
      d45_truth_lemma_applied
      d45_canonical_FC
      (fun World m w ⟨hSer, hTrans, hEucl⟩ h_sat => h World m w hSer hTrans hEucl h_sat)
  exact ⟨L, hL_sub, fun World m w h_serial h_trans h_eucl h_sat =>
    hL_sem World m w ⟨h_serial, h_trans, h_eucl⟩ h_sat⟩

/-! ## D45 Weak Completeness (Corollary) -/

/-- **Completeness Theorem for Modal Logic D45** (corollary of strong completeness):

If `phi` is valid over all serial, transitive, Euclidean frames, then `phi` is
D45-derivable from the empty context.

This is a corollary of `d45_strong_completeness` instantiated at `Gamma = ∅`. -/
theorem d45_completeness (φ : Proposition Atom)
    (h_valid : ∀ (World : Type u) (m : Model World Atom),
      Relation.Serial m.r →
      (∀ w₁ w₂ w₃, m.r w₁ w₂ → m.r w₂ w₃ → m.r w₁ w₃) →
      (∀ w₁ w₂ w₃, m.r w₁ w₂ → m.r w₁ w₃ → m.r w₂ w₃) →
      ∀ w, Satisfies m w φ) :
    Derivable (@D45Axiom Atom) φ :=
  ModalSetDerivable_empty_iff.mp
    (d45_strong_completeness (fun W m w hSer hTrans hEucl _ =>
      h_valid W m hSer hTrans hEucl w))

end Cslib.Logic.Modal
