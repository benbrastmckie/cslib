/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Modal.Metalogic.Completeness
public import Cslib.Logics.Modal.Metalogic.Systems.D.Soundness

/-! # Completeness Theorem for Modal Logic D (KD)

This module proves completeness for modal logic D over serial Kripke frames
via the canonical model construction (completeness-via-canonicity).

Task 539: the D-specific box-witness route (`d_derive_box_from_inconsistency`,
`d_mcs_box_witness`, `d_truth_lemma`) has been deleted -- it duplicated the generic route
now promoted to `Metalogic.Completeness.truth_lemma`, which needs only `EFQ + K` from `kCore`
and serves D (and all 14 other classical systems) directly via `canonicalTruthLemmaOfKCore`.
`d_canonical_serial` (a genuine frame property, not a truth-lemma duplicate) is likewise
relocated to `Metalogic.Completeness` so it survives this file's shrink.

## Main Results

- `d_truth_lemma_applied`: The generic `truth_lemma` pre-applied to `DAxiom` via
  `canonicalTruthLemmaOfKCore`.
- `d_canonical_FC`: The canonical D model is serial, via the relocated `d_canonical_serial`.

The weak completeness theorem `d_completeness` is derived below as a
corollary of strong completeness via `ModalSetDerivable_empty_iff`.

## References

* Blackburn, de Rijke, Venema, "Modal Logic" (2002), Chapter 4
  - Theorem 4.28 clause 3 (KD seriality is canonical)
  - Lemma 4.21 (Truth Lemma)
  - Proposition 4.12 (Completeness criterion)
-/

@[expose] public section

namespace Cslib.Logic.Modal

open Cslib.Logic

universe u
variable {Atom : Type u}

/-! ## D Frame Condition and Canonical Witness -/

/-- The D frame condition: every model whose accessibility relation is serial. -/
def dFC : ∀ {World : Type u}, Model World Atom → Prop :=
  fun m => Relation.Serial m.r

/-- The canonical D model satisfies `dFC`: its accessibility relation is serial. -/
private theorem d_canonical_FC : dFC (CanonicalModel (@DAxiom Atom)) := by
  constructor
  intro S
  exact d_canonical_serial
    (fun φ ψ => ⟨.implyK, by decide, φ, ψ, rfl⟩)
    (fun φ ψ χ => ⟨.implyS, by decide, φ, ψ, χ, rfl⟩)
    (fun φ => ⟨.efq, by decide, φ, rfl⟩)
    (fun φ ψ => ⟨.modalK, by decide, φ, ψ, rfl⟩)
    (fun φ => ⟨.modalD, by decide, φ, rfl⟩)
    S

/-- Pre-applied D truth lemma: satisfaction at world `S` iff membership in `S.val`. -/
theorem d_truth_lemma_applied (S : CanonicalWorld (@DAxiom Atom))
    (φ : Proposition Atom) :
    Satisfies (CanonicalModel (@DAxiom Atom)) S φ ↔ φ ∈ S.val :=
  canonicalTruthLemmaOfKCore (by decide) S φ

/-- `kCore ⊆ dTags`: feeds the `holds*` helpers so `d_strong_completeness`/`d_compactness`
below share this single subset fact instead of repeating 4 `by decide` witnesses (task 539). -/
private theorem coreSubset : kCore ⊆ dTags := by decide

/-- D soundness adapter matching the `strong_soundness` callback shape.
The frame condition for D is `dFC m = Relation.Serial m.r`. -/
private theorem d_sound_cb {World : Type u} (m : Model World Atom) (w : World)
    (L : List (Proposition Atom))
    (hFC : dFC m)
    (d : DerivationTree (@DAxiom Atom) L phi)
    (h_ctx : ∀ γ ∈ L, Satisfies m w γ) : Satisfies m w phi :=
  d_soundness d m hFC w h_ctx

/-! ## D Strong Soundness -/

/-- **Strong Soundness for D**: If `phi` is set-derivable from `Gamma` using `DAxiom`,
then `phi` is a semantic consequence of `Gamma` over all serial frames.

For any serial model `m` and any world `w` satisfying all of `Gamma`, `phi`
holds at `w`. -/
theorem d_strong_soundness {Gamma : Set (Proposition Atom)} {phi : Proposition Atom}
    (h : ModalSetDerivable (@DAxiom Atom) Gamma phi)
    (World : Type u) (m : Model World Atom) (w : World)
    (h_serial : Relation.Serial m.r)
    (h_sat : ∀ γ ∈ Gamma, Satisfies m w γ) : Satisfies m w phi :=
  strong_soundness (Axioms := @DAxiom Atom) (FC := dFC)
    d_sound_cb h World m w h_serial h_sat

/-! ## D Strong Completeness -/

/-- **Strong Completeness for D**: If `phi` is a semantic consequence of `Gamma`
over all serial frames, then `phi` is set-derivable from `Gamma` using `DAxiom`.

Delegates to the parametric `strong_completeness` with `d_truth_lemma_applied`
and `d_canonical_FC`. -/
theorem d_strong_completeness {Gamma : Set (Proposition Atom)} {phi : Proposition Atom}
    (h : ∀ (World : Type u) (m : Model World Atom) (w : World),
        Relation.Serial m.r →
        (∀ γ ∈ Gamma, Satisfies m w γ) →
        Satisfies m w phi) :
    ModalSetDerivable (@DAxiom Atom) Gamma phi :=
  strong_completeness (Axioms := @DAxiom Atom) (FC := dFC)
    (holdsImplyK coreSubset)
    (holdsImplyS coreSubset)
    (holdsEfq coreSubset)
    (holdsPeirce coreSubset)
    d_truth_lemma_applied
    d_canonical_FC
    (fun World m w hFC h_sat => h World m w hFC h_sat)

/-! ## D Biconditional Wrapper -/

/-- **Strong Soundness and Completeness for D**:
`phi` is a semantic consequence of `Gamma` over all serial frames iff `phi` is
set-derivable from `Gamma` using `DAxiom`. -/
theorem d_strong_completeness_iff {Gamma : Set (Proposition Atom)} {phi : Proposition Atom} :
    (∀ (World : Type u) (m : Model World Atom) (w : World),
        Relation.Serial m.r →
        (∀ γ ∈ Gamma, Satisfies m w γ) →
        Satisfies m w phi) ↔
    ModalSetDerivable (@DAxiom Atom) Gamma phi :=
  ⟨d_strong_completeness, fun h World m w h_serial h_sat =>
    d_strong_soundness h World m w h_serial h_sat⟩

/-! ## D Compactness -/

/-- **Compactness for D Semantics**: If `phi` is a semantic consequence of `Gamma`
over all serial frames, there exists a finite list `L ⊆ Gamma` such that
`phi` is a semantic consequence of (members of) `L` over all serial frames. -/
theorem d_compactness {Gamma : Set (Proposition Atom)} {phi : Proposition Atom}
    (h : ∀ (World : Type u) (m : Model World Atom) (w : World),
        Relation.Serial m.r →
        (∀ γ ∈ Gamma, Satisfies m w γ) →
        Satisfies m w phi) :
    ∃ L : List (Proposition Atom),
      (∀ x ∈ L, x ∈ Gamma) ∧
      ∀ (World : Type u) (m : Model World Atom) (w : World),
        Relation.Serial m.r →
        (∀ γ ∈ {ψ | ψ ∈ L}, Satisfies m w γ) →
        Satisfies m w phi := by
  obtain ⟨L, hL_sub, hL_sem⟩ :=
    compactness (Axioms := @DAxiom Atom) (FC := dFC)
      d_sound_cb
      (holdsImplyK coreSubset)
      (holdsImplyS coreSubset)
      (holdsEfq coreSubset)
      (holdsPeirce coreSubset)
      d_truth_lemma_applied
      d_canonical_FC
      (fun World m w hFC h_sat => h World m w hFC h_sat)
  exact ⟨L, hL_sub, fun World m w h_serial h_sat => hL_sem World m w h_serial h_sat⟩

/-! ## D Weak Completeness (Corollary) -/

/-- **Completeness Theorem for Modal Logic D** (corollary of strong completeness):

If `phi` is valid over all serial frames, then `phi` is D-derivable
from the empty context.

This is a corollary of `d_strong_completeness` instantiated at `Gamma = ∅`. -/
theorem d_completeness (φ : Proposition Atom)
    (h_valid : ∀ (World : Type u) (m : Model World Atom),
      Relation.Serial m.r →
      ∀ w, Satisfies m w φ) :
    Derivable (@DAxiom Atom) φ :=
  ModalSetDerivable_empty_iff.mp
    (d_strong_completeness (fun W m w hSer _ => h_valid W m hSer w))

end Cslib.Logic.Modal
