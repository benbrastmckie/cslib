/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Modal.Metalogic.Completeness
public import Cslib.Logics.Modal.Metalogic.Systems.TB.Soundness
public import Cslib.Logics.Modal.ProofSystem.Instances

/-! # Completeness Theorem for Modal Logic TB

This module proves completeness for TB modal logic (= KTB) via the canonical Kripke
model construction: if a formula is valid on all reflexive, symmetric frames, then
it is TB-derivable.

The proof follows Blackburn, de Rijke, Venema "Modal Logic" (2002) Chapter 4:

- **Theorem 4.28, clause 1** (reflexivity is canonical): Uses axiom T (`□φ → φ`)
  via `canonical_refl` and `mcs_box_closure`.

- **Theorem 4.28, clause 2** (symmetry is canonical): Uses axiom B (`φ → □◇φ`)
  via `canonical_symm`.

## Main Results

- `tb_strong_soundness`: If `phi` is TB-derivable from `Gamma`, then `phi` is a semantic
  consequence of `Gamma` over all reflexive, symmetric frames.
- `tb_strong_completeness`: If `phi` is a semantic consequence of `Gamma` over all reflexive,
  symmetric frames, then `phi` is TB-derivable from `Gamma`.
- `tb_strong_completeness_iff`: Biconditional combining soundness and completeness.
- `tb_completeness`: Weak completeness (valid iff derivable).

The weak completeness theorem `tb_completeness` is derived below as a
corollary of strong completeness via `ModalSetDerivable_empty_iff`.

## References

* Blackburn, de Rijke, Venema - Modal Logic (Ch. 4, Theorems 4.22, 4.28)
* Cslib/Logics/Modal/Metalogic/Completeness.lean -- parameterized canonical model
-/

@[expose] public section

namespace Cslib.Logic.Modal

open Cslib.Logic

universe u
variable {Atom : Type u}

/-! ## TB Frame Condition and Canonical Witness -/

/-- The TB frame condition: every model whose accessibility relation is reflexive and
symmetric. -/
def tbFC : ∀ {World : Type u}, Model World Atom → Prop :=
  fun m => (∀ w, m.r w w) ∧ (∀ w₁ w₂, m.r w₁ w₂ → m.r w₂ w₁)

/-- The canonical TB model satisfies `tbFC`: its accessibility relation is reflexive
and symmetric. -/
private theorem tb_canonical_FC : tbFC (CanonicalModel (@TBAxiom Atom)) :=
  ⟨fun S => canonical_refl
      (fun φ ψ => (schemaUnion_tbTags_iff_TBAxiom).mp ⟨.implyK, by decide, φ, ψ, rfl⟩)
      (fun φ ψ χ => (schemaUnion_tbTags_iff_TBAxiom).mp ⟨.implyS, by decide, φ, ψ, χ, rfl⟩)
      (fun φ => (schemaUnion_tbTags_iff_TBAxiom).mp ⟨.modalT, by decide, φ, rfl⟩)
      S,
   canonical_symm
      (fun φ ψ => (schemaUnion_tbTags_iff_TBAxiom).mp ⟨.implyK, by decide, φ, ψ, rfl⟩)
      (fun φ ψ χ => (schemaUnion_tbTags_iff_TBAxiom).mp ⟨.implyS, by decide, φ, ψ, χ, rfl⟩)
      (fun φ ψ => (schemaUnion_tbTags_iff_TBAxiom).mp ⟨.modalK, by decide, φ, ψ, rfl⟩)
      (fun φ => (schemaUnion_tbTags_iff_TBAxiom).mp ⟨.modalB, by decide, φ, rfl⟩)⟩

/-- Pre-applied TB truth lemma: satisfaction at world `S` iff membership in `S.val`. -/
private theorem tb_truth_lemma_applied (S : CanonicalWorld (@TBAxiom Atom))
    (φ : Proposition Atom) :
    Satisfies (CanonicalModel (@TBAxiom Atom)) S φ ↔ φ ∈ S.val :=
  truth_lemma
    (fun φ ψ => (schemaUnion_tbTags_iff_TBAxiom).mp ⟨.implyK, by decide, φ, ψ, rfl⟩)
    (fun φ ψ χ => (schemaUnion_tbTags_iff_TBAxiom).mp ⟨.implyS, by decide, φ, ψ, χ, rfl⟩)
    (fun φ => (schemaUnion_tbTags_iff_TBAxiom).mp ⟨.efq, by decide, φ, rfl⟩)
    (fun φ ψ => (schemaUnion_tbTags_iff_TBAxiom).mp ⟨.peirce, by decide, φ, ψ, rfl⟩)
    (fun φ ψ => (schemaUnion_tbTags_iff_TBAxiom).mp ⟨.modalK, by decide, φ, ψ, rfl⟩)
    (fun φ => (schemaUnion_tbTags_iff_TBAxiom).mp ⟨.modalT, by decide, φ, rfl⟩)
    (fun φ ψ => (schemaUnion_tbTags_iff_TBAxiom).mp ⟨.andI, by decide, φ, ψ, rfl⟩)
    (fun φ ψ => (schemaUnion_tbTags_iff_TBAxiom).mp ⟨.andE1, by decide, φ, ψ, rfl⟩)
    (fun φ ψ => (schemaUnion_tbTags_iff_TBAxiom).mp ⟨.andE2, by decide, φ, ψ, rfl⟩)
    (fun φ ψ => (schemaUnion_tbTags_iff_TBAxiom).mp ⟨.orI1, by decide, φ, ψ, rfl⟩)
    (fun φ ψ => (schemaUnion_tbTags_iff_TBAxiom).mp ⟨.orI2, by decide, φ, ψ, rfl⟩)
    (fun φ ψ χ => (schemaUnion_tbTags_iff_TBAxiom).mp ⟨.orE, by decide, φ, ψ, χ, rfl⟩)
    (fun φ => (schemaUnion_tbTags_iff_TBAxiom).mp ⟨.diaDualityFwd, by decide, φ, rfl⟩)
    (fun φ => (schemaUnion_tbTags_iff_TBAxiom).mp ⟨.diaDualityBack, by decide, φ, rfl⟩)
    S φ

/-- TB soundness adapter matching the `strong_soundness` callback shape.
The frame condition for TB is `tbFC m = (∀ w, m.r w w) ∧ (∀ w₁ w₂, m.r w₁ w₂ → m.r w₂ w₁)`. -/
private theorem tb_sound_cb {World : Type u} (m : Model World Atom) (w : World)
    (L : List (Proposition Atom))
    (hFC : tbFC m)
    (d : DerivationTree (@TBAxiom Atom) L phi)
    (h_ctx : ∀ γ ∈ L, Satisfies m w γ) : Satisfies m w phi :=
  tb_soundness d m hFC.1 hFC.2 w h_ctx

/-! ## TB Strong Soundness -/

/-- **Strong Soundness for TB**: If `phi` is set-derivable from `Gamma` using `TBAxiom`,
then `phi` is a semantic consequence of `Gamma` over all reflexive, symmetric frames.

For any reflexive, symmetric model `m` and any world `w` satisfying all of `Gamma`, `phi`
holds at `w`. -/
theorem tb_strong_soundness {Gamma : Set (Proposition Atom)} {phi : Proposition Atom}
    (h : ModalSetDerivable (@TBAxiom Atom) Gamma phi)
    (World : Type u) (m : Model World Atom) (w : World)
    (h_refl : ∀ w, m.r w w)
    (h_symm : ∀ w₁ w₂, m.r w₁ w₂ → m.r w₂ w₁)
    (h_sat : ∀ γ ∈ Gamma, Satisfies m w γ) : Satisfies m w phi :=
  strong_soundness (Axioms := @TBAxiom Atom) (FC := tbFC)
    tb_sound_cb h World m w ⟨h_refl, h_symm⟩ h_sat

/-! ## TB Strong Completeness -/

/-- **Strong Completeness for TB**: If `phi` is a semantic consequence of `Gamma`
over all reflexive, symmetric frames, then `phi` is set-derivable from `Gamma`
using `TBAxiom`.

Delegates to the parametric `strong_completeness` with `tb_truth_lemma_applied`
and `tb_canonical_FC`. -/
theorem tb_strong_completeness {Gamma : Set (Proposition Atom)} {phi : Proposition Atom}
    (h : ∀ (World : Type u) (m : Model World Atom) (w : World),
        (∀ w, m.r w w) →
        (∀ w₁ w₂, m.r w₁ w₂ → m.r w₂ w₁) →
        (∀ γ ∈ Gamma, Satisfies m w γ) →
        Satisfies m w phi) :
    ModalSetDerivable (@TBAxiom Atom) Gamma phi :=
  strong_completeness (Axioms := @TBAxiom Atom) (FC := tbFC)
    (fun φ ψ => (schemaUnion_tbTags_iff_TBAxiom).mp ⟨.implyK, by decide, φ, ψ, rfl⟩)
    (fun φ ψ χ => (schemaUnion_tbTags_iff_TBAxiom).mp ⟨.implyS, by decide, φ, ψ, χ, rfl⟩)
    (fun φ => (schemaUnion_tbTags_iff_TBAxiom).mp ⟨.efq, by decide, φ, rfl⟩)
    (fun φ ψ => (schemaUnion_tbTags_iff_TBAxiom).mp ⟨.peirce, by decide, φ, ψ, rfl⟩)
    tb_truth_lemma_applied
    tb_canonical_FC
    (fun World m w ⟨hRefl, hSymm⟩ h_sat => h World m w hRefl hSymm h_sat)

/-! ## TB Biconditional Wrapper -/

/-- **Strong Soundness and Completeness for TB**:
`phi` is a semantic consequence of `Gamma` over all reflexive, symmetric frames iff `phi` is
set-derivable from `Gamma` using `TBAxiom`. -/
theorem tb_strong_completeness_iff {Gamma : Set (Proposition Atom)} {phi : Proposition Atom} :
    (∀ (World : Type u) (m : Model World Atom) (w : World),
        (∀ w, m.r w w) →
        (∀ w₁ w₂, m.r w₁ w₂ → m.r w₂ w₁) →
        (∀ γ ∈ Gamma, Satisfies m w γ) →
        Satisfies m w phi) ↔
    ModalSetDerivable (@TBAxiom Atom) Gamma phi :=
  ⟨tb_strong_completeness, fun h World m w h_refl h_symm h_sat =>
    tb_strong_soundness h World m w h_refl h_symm h_sat⟩

/-! ## TB Compactness -/

/-- **Compactness for TB Semantics**: If `phi` is a semantic consequence of `Gamma`
over all reflexive, symmetric frames, there exists a finite list `L ⊆ Gamma` such that
`phi` is a semantic consequence of (members of) `L` over all reflexive, symmetric frames. -/
theorem tb_compactness {Gamma : Set (Proposition Atom)} {phi : Proposition Atom}
    (h : ∀ (World : Type u) (m : Model World Atom) (w : World),
        (∀ w, m.r w w) →
        (∀ w₁ w₂, m.r w₁ w₂ → m.r w₂ w₁) →
        (∀ γ ∈ Gamma, Satisfies m w γ) →
        Satisfies m w phi) :
    ∃ L : List (Proposition Atom),
      (∀ x ∈ L, x ∈ Gamma) ∧
      ∀ (World : Type u) (m : Model World Atom) (w : World),
        (∀ w, m.r w w) →
        (∀ w₁ w₂, m.r w₁ w₂ → m.r w₂ w₁) →
        (∀ γ ∈ {ψ | ψ ∈ L}, Satisfies m w γ) →
        Satisfies m w phi := by
  obtain ⟨L, hL_sub, hL_sem⟩ :=
    compactness (Axioms := @TBAxiom Atom) (FC := tbFC)
      tb_sound_cb
      (fun φ ψ => (schemaUnion_tbTags_iff_TBAxiom).mp ⟨.implyK, by decide, φ, ψ, rfl⟩)
      (fun φ ψ χ => (schemaUnion_tbTags_iff_TBAxiom).mp ⟨.implyS, by decide, φ, ψ, χ, rfl⟩)
      (fun φ => (schemaUnion_tbTags_iff_TBAxiom).mp ⟨.efq, by decide, φ, rfl⟩)
      (fun φ ψ => (schemaUnion_tbTags_iff_TBAxiom).mp ⟨.peirce, by decide, φ, ψ, rfl⟩)
      tb_truth_lemma_applied
      tb_canonical_FC
      (fun World m w ⟨hRefl, hSymm⟩ h_sat => h World m w hRefl hSymm h_sat)
  exact ⟨L, hL_sub, fun World m w h_refl h_symm h_sat =>
    hL_sem World m w ⟨h_refl, h_symm⟩ h_sat⟩

/-! ## TB Weak Completeness (Corollary) -/

/-- **Completeness Theorem for TB Modal Logic** (corollary of strong completeness):

If `phi` is valid over all reflexive, symmetric frames, then `phi` is TB-derivable
from the empty context.

This is a corollary of `tb_strong_completeness` instantiated at `Gamma = ∅`. -/
theorem tb_completeness (φ : Proposition Atom)
    (h_valid : ∀ (World : Type u) (m : Model World Atom),
      (∀ w, m.r w w) →
      (∀ w₁ w₂, m.r w₁ w₂ → m.r w₂ w₁) →
      ∀ w, Satisfies m w φ) :
    Derivable (@TBAxiom Atom) φ :=
  ModalSetDerivable_empty_iff.mp
    (tb_strong_completeness (fun W m w hRefl hSymm _ => h_valid W m hRefl hSymm w))

end Cslib.Logic.Modal
