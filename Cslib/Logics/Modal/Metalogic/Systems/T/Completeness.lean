/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Modal.Metalogic.Completeness
public import Cslib.Logics.Modal.Metalogic.Systems.T.Soundness
public import Cslib.Logics.Modal.ProofSystem.Instances
public import Cslib.Logics.Modal.ProofSystem.SchemaBridges

/-! # Completeness Theorem for Modal Logic T

This module proves completeness for modal logic T via the canonical Kripke model
construction, following Blackburn, de Rijke, Venema "Modal Logic" (2002),
Theorem 4.28, clause 1.

The key insight is that the canonical frame for T is reflexive (Thm 4.28 cl.1),
and the existing parameterized `truth_lemma` and `mcs_box_witness` work directly
for T since `TAxiom` includes axiom T.

## Main Results

- `t_strong_soundness`: If `phi` is T-derivable from `Gamma`, then `phi` is a semantic
  consequence of `Gamma` over all reflexive frames.
- `t_strong_completeness`: If `phi` is a semantic consequence of `Gamma` over all reflexive
  frames, then `phi` is T-derivable from `Gamma`.
- `t_strong_completeness_iff`: Biconditional combining soundness and completeness.
- `t_completeness`: Weak completeness (valid iff derivable).

The weak completeness theorem `t_completeness` is derived below as a
corollary of strong completeness via `ModalSetDerivable_empty_iff`.

## References

* Blackburn, de Rijke, Venema - Modal Logic (Ch. 4, Theorems 4.22, 4.28)
-/

@[expose] public section

namespace Cslib.Logic.Modal

open Cslib.Logic

universe u
variable {Atom : Type u}

/-! ## T Frame Condition and Canonical Witness -/

/-- The T frame condition: every model whose accessibility relation is reflexive. -/
def tFC : ∀ {World : Type u}, Model World Atom → Prop :=
  fun m => ∀ w, m.r w w

/-- The canonical T model satisfies `tFC`: its accessibility relation is reflexive. -/
private theorem t_canonical_FC : tFC (CanonicalModel (@TAxiom Atom)) :=
  fun S => canonical_refl
    (fun φ ψ => (schemaUnion_tTags_iff_TAxiom).mp ⟨.implyK, by decide, φ, ψ, rfl⟩)
    (fun φ ψ χ => (schemaUnion_tTags_iff_TAxiom).mp ⟨.implyS, by decide, φ, ψ, χ, rfl⟩)
    (fun φ => (schemaUnion_tTags_iff_TAxiom).mp ⟨.modalT, by decide, φ, rfl⟩)
    S

/-- Pre-applied T truth lemma: satisfaction at world `S` iff membership in `S.val`. -/
private theorem t_truth_lemma_applied (S : CanonicalWorld (@TAxiom Atom))
    (φ : Proposition Atom) :
    Satisfies (CanonicalModel (@TAxiom Atom)) S φ ↔ φ ∈ S.val :=
  truth_lemma
    (fun φ ψ => (schemaUnion_tTags_iff_TAxiom).mp ⟨.implyK, by decide, φ, ψ, rfl⟩)
    (fun φ ψ χ => (schemaUnion_tTags_iff_TAxiom).mp ⟨.implyS, by decide, φ, ψ, χ, rfl⟩)
    (fun φ => (schemaUnion_tTags_iff_TAxiom).mp ⟨.efq, by decide, φ, rfl⟩)
    (fun φ ψ => (schemaUnion_tTags_iff_TAxiom).mp ⟨.peirce, by decide, φ, ψ, rfl⟩)
    (fun φ ψ => (schemaUnion_tTags_iff_TAxiom).mp ⟨.modalK, by decide, φ, ψ, rfl⟩)
    (fun φ => (schemaUnion_tTags_iff_TAxiom).mp ⟨.modalT, by decide, φ, rfl⟩)
    (fun φ ψ => (schemaUnion_tTags_iff_TAxiom).mp ⟨.andI, by decide, φ, ψ, rfl⟩)
    (fun φ ψ => (schemaUnion_tTags_iff_TAxiom).mp ⟨.andE1, by decide, φ, ψ, rfl⟩)
    (fun φ ψ => (schemaUnion_tTags_iff_TAxiom).mp ⟨.andE2, by decide, φ, ψ, rfl⟩)
    (fun φ ψ => (schemaUnion_tTags_iff_TAxiom).mp ⟨.orI1, by decide, φ, ψ, rfl⟩)
    (fun φ ψ => (schemaUnion_tTags_iff_TAxiom).mp ⟨.orI2, by decide, φ, ψ, rfl⟩)
    (fun φ ψ χ => (schemaUnion_tTags_iff_TAxiom).mp ⟨.orE, by decide, φ, ψ, χ, rfl⟩)
    (fun φ => (schemaUnion_tTags_iff_TAxiom).mp ⟨.diaDualityFwd, by decide, φ, rfl⟩)
    (fun φ => (schemaUnion_tTags_iff_TAxiom).mp ⟨.diaDualityBack, by decide, φ, rfl⟩)
    S φ

/-- T soundness adapter matching the `strong_soundness` callback shape.
The frame condition for T is `tFC m = ∀ w, m.r w w`. -/
private theorem t_sound_cb {World : Type u} (m : Model World Atom) (w : World)
    (L : List (Proposition Atom))
    (hFC : tFC m)
    (d : DerivationTree (@TAxiom Atom) L phi)
    (h_ctx : ∀ γ ∈ L, Satisfies m w γ) : Satisfies m w phi :=
  t_soundness d m hFC w h_ctx

/-! ## T Strong Soundness -/

/-- **Strong Soundness for T**: If `phi` is set-derivable from `Gamma` using `TAxiom`,
then `phi` is a semantic consequence of `Gamma` over all reflexive frames.

For any reflexive model `m` and any world `w` satisfying all of `Gamma`, `phi`
holds at `w`. -/
theorem t_strong_soundness {Gamma : Set (Proposition Atom)} {phi : Proposition Atom}
    (h : ModalSetDerivable (@TAxiom Atom) Gamma phi)
    (World : Type u) (m : Model World Atom) (w : World)
    (h_refl : ∀ w, m.r w w)
    (h_sat : ∀ γ ∈ Gamma, Satisfies m w γ) : Satisfies m w phi :=
  strong_soundness (Axioms := @TAxiom Atom) (FC := tFC)
    t_sound_cb h World m w h_refl h_sat

/-! ## T Strong Completeness -/

/-- **Strong Completeness for T**: If `phi` is a semantic consequence of `Gamma`
over all reflexive frames, then `phi` is set-derivable from `Gamma` using `TAxiom`.

Delegates to the parametric `strong_completeness` with `t_truth_lemma_applied`
and `t_canonical_FC`. -/
theorem t_strong_completeness {Gamma : Set (Proposition Atom)} {phi : Proposition Atom}
    (h : ∀ (World : Type u) (m : Model World Atom) (w : World),
        (∀ w, m.r w w) →
        (∀ γ ∈ Gamma, Satisfies m w γ) →
        Satisfies m w phi) :
    ModalSetDerivable (@TAxiom Atom) Gamma phi :=
  strong_completeness (Axioms := @TAxiom Atom) (FC := tFC)
    (fun φ ψ => (schemaUnion_tTags_iff_TAxiom).mp ⟨.implyK, by decide, φ, ψ, rfl⟩)
    (fun φ ψ χ => (schemaUnion_tTags_iff_TAxiom).mp ⟨.implyS, by decide, φ, ψ, χ, rfl⟩)
    (fun φ => (schemaUnion_tTags_iff_TAxiom).mp ⟨.efq, by decide, φ, rfl⟩)
    (fun φ ψ => (schemaUnion_tTags_iff_TAxiom).mp ⟨.peirce, by decide, φ, ψ, rfl⟩)
    t_truth_lemma_applied
    t_canonical_FC
    (fun World m w hFC h_sat => h World m w hFC h_sat)

/-! ## T Biconditional Wrapper -/

/-- **Strong Soundness and Completeness for T**:
`phi` is a semantic consequence of `Gamma` over all reflexive frames iff `phi` is
set-derivable from `Gamma` using `TAxiom`. -/
theorem t_strong_completeness_iff {Gamma : Set (Proposition Atom)} {phi : Proposition Atom} :
    (∀ (World : Type u) (m : Model World Atom) (w : World),
        (∀ w, m.r w w) →
        (∀ γ ∈ Gamma, Satisfies m w γ) →
        Satisfies m w phi) ↔
    ModalSetDerivable (@TAxiom Atom) Gamma phi :=
  ⟨t_strong_completeness, fun h World m w h_refl h_sat =>
    t_strong_soundness h World m w h_refl h_sat⟩

/-! ## T Compactness -/

/-- **Compactness for T Semantics**: If `phi` is a semantic consequence of `Gamma`
over all reflexive frames, there exists a finite list `L ⊆ Gamma` such that
`phi` is a semantic consequence of (members of) `L` over all reflexive frames. -/
theorem t_compactness {Gamma : Set (Proposition Atom)} {phi : Proposition Atom}
    (h : ∀ (World : Type u) (m : Model World Atom) (w : World),
        (∀ w, m.r w w) →
        (∀ γ ∈ Gamma, Satisfies m w γ) →
        Satisfies m w phi) :
    ∃ L : List (Proposition Atom),
      (∀ x ∈ L, x ∈ Gamma) ∧
      ∀ (World : Type u) (m : Model World Atom) (w : World),
        (∀ w, m.r w w) →
        (∀ γ ∈ {ψ | ψ ∈ L}, Satisfies m w γ) →
        Satisfies m w phi := by
  obtain ⟨L, hL_sub, hL_sem⟩ :=
    compactness (Axioms := @TAxiom Atom) (FC := tFC)
      t_sound_cb
      (fun φ ψ => (schemaUnion_tTags_iff_TAxiom).mp ⟨.implyK, by decide, φ, ψ, rfl⟩)
      (fun φ ψ χ => (schemaUnion_tTags_iff_TAxiom).mp ⟨.implyS, by decide, φ, ψ, χ, rfl⟩)
      (fun φ => (schemaUnion_tTags_iff_TAxiom).mp ⟨.efq, by decide, φ, rfl⟩)
      (fun φ ψ => (schemaUnion_tTags_iff_TAxiom).mp ⟨.peirce, by decide, φ, ψ, rfl⟩)
      t_truth_lemma_applied
      t_canonical_FC
      (fun World m w hFC h_sat => h World m w hFC h_sat)
  exact ⟨L, hL_sub, fun World m w h_refl h_sat => hL_sem World m w h_refl h_sat⟩

/-! ## T Weak Completeness (Corollary) -/

/-- **Completeness Theorem for Modal Logic T** (corollary of strong completeness):

If `phi` is valid over all reflexive frames, then `phi` is T-derivable
from the empty context.

This is a corollary of `t_strong_completeness` instantiated at `Gamma = ∅`. -/
theorem t_completeness (φ : Proposition Atom)
    (h_valid : ∀ (World : Type u) (m : Model World Atom),
      (∀ w, m.r w w) →
      ∀ w, Satisfies m w φ) :
    Derivable (@TAxiom Atom) φ :=
  ModalSetDerivable_empty_iff.mp
    (t_strong_completeness (fun W m w hRefl _ => h_valid W m hRefl w))

end Cslib.Logic.Modal
