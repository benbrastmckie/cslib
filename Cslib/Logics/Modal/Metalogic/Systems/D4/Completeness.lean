/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Modal.Metalogic.Completeness
public import Cslib.Logics.Modal.Metalogic.Systems.D4.Soundness

/-! # Strong Completeness for Modal Logic D4

This module proves strong soundness and strong completeness for modal logic D4:
semantic entailment from a set of premises `Gamma` (over all serial, transitive frames)
is equivalent to set-derivability using `D4Axiom`.

## Main Results

- `d4_strong_soundness`: Set-derivability from `Gamma` implies semantic entailment
  over all serial, transitive frames.
- `d4_strong_completeness`: Semantic entailment over serial, transitive frames implies
  set-derivability from `Gamma`.
- `d4_strong_completeness_iff`: Biconditional combining the above.
- `d4_completeness`: Weak completeness (corollary of strong completeness).
- `d4_compactness`: If `phi` is a D4-semantic consequence of `Gamma`, there exists
  a finite list `L ⊆ Gamma` such that `phi` is a D4-semantic consequence of `L`.

## References

* [Blackburn, de Rijke, Venema, *Modal Logic*][Blackburn2001], Ch. 4
* Cslib/Logics/Modal/Metalogic/Completeness.lean -- `d_canonical_serial` (relocated, task 539)
  and the generic `truth_lemma` / `canonicalTruthLemmaOfKCore` wrapper
-/

@[expose] public section

namespace Cslib.Logic.Modal

open Cslib.Logic

universe u
variable {Atom : Type u}

/-! ## D4 Frame Condition and Canonical Witness -/

/-- The D4 frame condition: every model whose accessibility relation is serial and
transitive. -/
def d4FC : ∀ {World : Type u}, Model World Atom → Prop :=
  fun m => Relation.Serial m.r ∧ (∀ w₁ w₂ w₃, m.r w₁ w₂ → m.r w₂ w₃ → m.r w₁ w₃)

/-- The canonical D4 model satisfies `d4FC`: its accessibility relation is serial
and transitive. -/
private theorem d4_canonical_FC : d4FC (CanonicalModel (@D4Axiom Atom)) := by
  constructor
  · constructor
    intro S
    exact d_canonical_serial
      (fun φ ψ => ⟨.implyK, by decide, φ, ψ, rfl⟩)
      (fun φ ψ χ => ⟨.implyS, by decide, φ, ψ, χ, rfl⟩)
      (fun φ => ⟨.efq, by decide, φ, rfl⟩)
      (fun φ ψ => ⟨.modalK, by decide, φ, ψ, rfl⟩)
      (fun φ => ⟨.modalD, by decide, φ, rfl⟩) S
  · exact canonical_trans
      (fun φ ψ => ⟨.implyK, by decide, φ, ψ, rfl⟩)
      (fun φ ψ χ => ⟨.implyS, by decide, φ, ψ, χ, rfl⟩)
      (fun φ => ⟨.modalFour, by decide, φ, rfl⟩)

/-- Pre-applied D4 truth lemma: satisfaction at world `S` iff membership in `S.val`. -/
private theorem d4_truth_lemma_applied (S : CanonicalWorld (@D4Axiom Atom))
    (φ : Proposition Atom) :
    Satisfies (CanonicalModel (@D4Axiom Atom)) S φ ↔ φ ∈ S.val :=
  canonicalTruthLemmaOfKCore (by decide) S φ

/-- `kCore ⊆ d4Tags`: feeds the `holds*` helpers so `d4_strong_completeness`/`d4_compactness`
below share this single subset fact instead of repeating 4 `by decide` witnesses (task 539). -/
private theorem coreSubset : kCore ⊆ d4Tags := by decide

/-- D4 soundness adapter matching the `strong_soundness` callback shape. -/
private theorem d4_sound_cb {World : Type u} (m : Model World Atom) (w : World)
    (L : List (Proposition Atom))
    (hFC : d4FC m)
    (d : DerivationTree (@D4Axiom Atom) L phi)
    (h_ctx : ∀ γ ∈ L, Satisfies m w γ) : Satisfies m w phi :=
  d4_soundness d m hFC.1 hFC.2 w h_ctx

/-! ## D4 Strong Soundness -/

/-- **Strong Soundness for D4**: If `phi` is set-derivable from `Gamma` using `D4Axiom`,
then `phi` is a semantic consequence of `Gamma` over all serial, transitive frames.

For any serial, transitive model `m` and any world `w` satisfying all of `Gamma`, `phi`
holds at `w`. -/
theorem d4_strong_soundness {Gamma : Set (Proposition Atom)} {phi : Proposition Atom}
    (h : ModalSetDerivable (@D4Axiom Atom) Gamma phi)
    (World : Type u) (m : Model World Atom) (w : World)
    (h_serial : Relation.Serial m.r)
    (h_trans : ∀ w₁ w₂ w₃, m.r w₁ w₂ → m.r w₂ w₃ → m.r w₁ w₃)
    (h_sat : ∀ γ ∈ Gamma, Satisfies m w γ) : Satisfies m w phi :=
  strong_soundness (Axioms := @D4Axiom Atom) (FC := d4FC)
    d4_sound_cb h World m w ⟨h_serial, h_trans⟩ h_sat

/-! ## D4 Strong Completeness -/

/-- **Strong Completeness for D4**: If `phi` is a semantic consequence of `Gamma`
over all serial, transitive frames, then `phi` is set-derivable from `Gamma`
using `D4Axiom`.

Delegates to the parametric `strong_completeness` with `d4_truth_lemma_applied`
and `d4_canonical_FC`. -/
theorem d4_strong_completeness {Gamma : Set (Proposition Atom)} {phi : Proposition Atom}
    (h : ∀ (World : Type u) (m : Model World Atom) (w : World),
        Relation.Serial m.r →
        (∀ w₁ w₂ w₃, m.r w₁ w₂ → m.r w₂ w₃ → m.r w₁ w₃) →
        (∀ γ ∈ Gamma, Satisfies m w γ) →
        Satisfies m w phi) :
    ModalSetDerivable (@D4Axiom Atom) Gamma phi :=
  strong_completeness (Axioms := @D4Axiom Atom) (FC := d4FC)
    (holdsImplyK coreSubset)
    (holdsImplyS coreSubset)
    (holdsEfq coreSubset)
    (holdsPeirce coreSubset)
    d4_truth_lemma_applied
    d4_canonical_FC
    (fun World m w ⟨hSer, hTrans⟩ h_sat => h World m w hSer hTrans h_sat)

/-! ## D4 Biconditional Wrapper -/

/-- **Strong Soundness and Completeness for D4**:
`phi` is a semantic consequence of `Gamma` over all serial, transitive frames iff `phi` is
set-derivable from `Gamma` using `D4Axiom`. -/
theorem d4_strong_completeness_iff {Gamma : Set (Proposition Atom)} {phi : Proposition Atom} :
    (∀ (World : Type u) (m : Model World Atom) (w : World),
        Relation.Serial m.r →
        (∀ w₁ w₂ w₃, m.r w₁ w₂ → m.r w₂ w₃ → m.r w₁ w₃) →
        (∀ γ ∈ Gamma, Satisfies m w γ) →
        Satisfies m w phi) ↔
    ModalSetDerivable (@D4Axiom Atom) Gamma phi :=
  ⟨d4_strong_completeness, fun h World m w h_serial h_trans h_sat =>
    d4_strong_soundness h World m w h_serial h_trans h_sat⟩

/-! ## D4 Compactness -/

/-- **Compactness for D4 Semantics**: If `phi` is a semantic consequence of `Gamma`
over all serial, transitive frames, there exists a finite list `L ⊆ Gamma` such that
`phi` is a semantic consequence of (members of) `L` over all serial, transitive frames. -/
theorem d4_compactness {Gamma : Set (Proposition Atom)} {phi : Proposition Atom}
    (h : ∀ (World : Type u) (m : Model World Atom) (w : World),
        Relation.Serial m.r →
        (∀ w₁ w₂ w₃, m.r w₁ w₂ → m.r w₂ w₃ → m.r w₁ w₃) →
        (∀ γ ∈ Gamma, Satisfies m w γ) →
        Satisfies m w phi) :
    ∃ L : List (Proposition Atom),
      (∀ x ∈ L, x ∈ Gamma) ∧
      ∀ (World : Type u) (m : Model World Atom) (w : World),
        Relation.Serial m.r →
        (∀ w₁ w₂ w₃, m.r w₁ w₂ → m.r w₂ w₃ → m.r w₁ w₃) →
        (∀ γ ∈ {ψ | ψ ∈ L}, Satisfies m w γ) →
        Satisfies m w phi := by
  obtain ⟨L, hL_sub, hL_sem⟩ :=
    compactness (Axioms := @D4Axiom Atom) (FC := d4FC)
      d4_sound_cb
      (holdsImplyK coreSubset)
      (holdsImplyS coreSubset)
      (holdsEfq coreSubset)
      (holdsPeirce coreSubset)
      d4_truth_lemma_applied
      d4_canonical_FC
      (fun World m w ⟨hSer, hTrans⟩ h_sat => h World m w hSer hTrans h_sat)
  exact ⟨L, hL_sub, fun World m w h_serial h_trans h_sat =>
    hL_sem World m w ⟨h_serial, h_trans⟩ h_sat⟩

/-! ## D4 Weak Completeness (Corollary) -/

/-- **Completeness Theorem for Modal Logic D4** (corollary of strong completeness):

If `phi` is valid over all serial, transitive frames, then `phi` is D4-derivable
from the empty context.

This is a corollary of `d4_strong_completeness` instantiated at `Gamma = ∅`. -/
theorem d4_completeness (φ : Proposition Atom)
    (h_valid : ∀ (World : Type u) (m : Model World Atom),
      Relation.Serial m.r →
      (∀ w₁ w₂ w₃, m.r w₁ w₂ → m.r w₂ w₃ → m.r w₁ w₃) →
      ∀ w, Satisfies m w φ) :
    Derivable (@D4Axiom Atom) φ :=
  ModalSetDerivable_empty_iff.mp
    (d4_strong_completeness (fun W m w hSer hTrans _ => h_valid W m hSer hTrans w))

end Cslib.Logic.Modal
