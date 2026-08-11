/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Modal.ProofSystem.SchemaUnion
public import Cslib.Logics.Modal.Metalogic.Soundness
public import Cslib.Logics.Modal.Metalogic.FrameCorrespondence

/-! # Schema-Union Soundness: `unionSound` and the 18-Entry Validity Table

This module provides the single master soundness lemma `unionSound` for the schema-union axiom
combinator (`Cslib.Logics.Modal.ProofSystem.SchemaUnion`). It separates *which* schemata a
`Finset ModalSchemaTag` selects (syntax) from *why* each is valid (semantics): the 13
frame-unconditional tags are valid on every model, while the 5 modal-strength differentiator
tags (`modalT/D/B/Four/Five`) are valid only under a specific frame condition.

`unionSound` is the hinge between the syntactic side (the schema-tag alphabet) and the
`FrameCorrespondence` semantic side: every per-system soundness proof
(`Systems/*/Soundness.lean`) specializes this one lemma instead of re-deriving a per-system
case-split.

## Main Definitions

- `FrameValidatesTag`: the per-tag semantic validity obligation, uniform over all 18 tags —
  `True` for the 13 frame-unconditional tags, the exact frame-condition hypothesis for the 5
  differentiators.

## Main Results

- `unionSound`: `SchemaUnion S φ` is valid at `w` in `m`, given a proof that `m` discharges
  `FrameValidatesTag m t` for every `t ∈ S`.

## Design

The 13 frame-unconditional entries reuse the existing atoms in `Metalogic/Soundness.lean`
(`Satisfies.implyK_axiom`, …, `Satisfies.diamondDualityBack_axiom`) verbatim (read-only reuse). The
5 frame-conditioned entries delegate to the library lemmas in
`Metalogic/FrameCorrespondence.lean` (`Satisfies.modalT_axiom`, `modalFour_axiom`, `modalB_axiom`,
`modalD_axiom`, `modalFive_axiom`) rather than re-proving the frame arguments inline — this
composition (`FrameCorrespondence.lean`'s semantic side + `SchemaUnion.lean`'s syntactic side)
is a design invariant of the schema-union rollout.

## References

* Cslib/Logics/Modal/Metalogic/Soundness.lean -- frame-unconditional validity atoms
* Cslib/Logics/Modal/Metalogic/FrameCorrespondence.lean -- frame-condition correspondence lemmas
-/

@[expose] public section

namespace Cslib.Logic.Modal

open Cslib.Logic

variable {Atom : Type*}

/-! ## Per-Tag Frame-Validity Obligation -/

/-- The semantic validity obligation for a schema tag `t` on model `m`, uniform over all 18
tags: `True` for the 13 frame-unconditional tags, and — for the 5 modal-strength
differentiators — exactly the frame-condition hypothesis its `FrameCorrespondence` lemma takes
(`∀ w, m.r w w` for `modalT`; `Relation.Serial m.r` for `modalD`; symmetry for `modalB`;
transitivity for `modalFour`; right-Euclideanness for `modalFive`). Uniformity over all 18 tags
(rather than a conditional/unconditional split at the type level) keeps `unionSound`'s `hfc`
interface uniform: the 13 trivial obligations discharge by `trivial`. -/
def FrameValidatesTag {World : Type*} (m : Model World Atom) : ModalSchemaTag → Prop
  | .modalT => ∀ w, m.r w w
  | .modalD => Relation.Serial m.r
  | .modalB => ∀ w₁ w₂, m.r w₁ w₂ → m.r w₂ w₁
  | .modalFour => ∀ w₁ w₂ w₃, m.r w₁ w₂ → m.r w₂ w₃ → m.r w₁ w₃
  | .modalFive => ∀ w₁ w₂ w₃, m.r w₁ w₂ → m.r w₁ w₃ → m.r w₂ w₃
  | .implyK | .implyS | .efq | .peirce | .modalK
  | .andI | .andE1 | .andE2 | .orI1 | .orI2 | .orE
  | .diamondDualityFwd | .diamondDualityBack => True

/-! ## Master Soundness Combinator -/

/-- **Schema-Union Soundness**: `SchemaUnion S φ` is valid at any world `w` of a model `m`,
given a proof `hfc` that `m` discharges the per-tag frame-validity obligation
(`FrameValidatesTag m t`) for every tag `t ∈ S`. This is the SINGLE master soundness lemma:
every per-system `<sys>_axiom_sound` proof specializes it by instantiating `S` with that
system's tag set and discharging `hfc` from the system's frame-class hypotheses — no
per-system soundness case-split survives past this lemma. -/
theorem unionSound {World : Type*} (S : Finset ModalSchemaTag) (m : Model World Atom)
    (hfc : ∀ t ∈ S, FrameValidatesTag m t) {φ : Proposition Atom} (h : SchemaUnion S φ)
    (w : World) : Satisfies m w φ := by
  obtain ⟨t, ht, hφ⟩ := h
  have hval := hfc t ht
  cases t with
  | implyK =>
    obtain ⟨φ', ψ', rfl⟩ := hφ
    exact Satisfies.implyK_axiom m w φ' ψ'
  | implyS =>
    obtain ⟨φ', ψ', χ', rfl⟩ := hφ
    exact Satisfies.implyS_axiom m w φ' ψ' χ'
  | efq =>
    obtain ⟨φ', rfl⟩ := hφ
    exact Satisfies.efq_axiom m w φ'
  | peirce =>
    obtain ⟨φ', ψ', rfl⟩ := hφ
    exact Satisfies.peirce_axiom m w φ' ψ'
  | modalK =>
    obtain ⟨φ', ψ', rfl⟩ := hφ
    exact Satisfies.modalK_axiom m w φ' ψ'
  | modalT =>
    obtain ⟨φ', rfl⟩ := hφ
    exact Satisfies.modalT_axiom m hval w φ'
  | modalD =>
    obtain ⟨φ', rfl⟩ := hφ
    exact Satisfies.modalD_axiom m hval w φ'
  | modalB =>
    obtain ⟨φ', rfl⟩ := hφ
    exact Satisfies.modalB_axiom m hval w φ'
  | modalFour =>
    obtain ⟨φ', rfl⟩ := hφ
    exact Satisfies.modalFour_axiom m hval w φ'
  | modalFive =>
    obtain ⟨φ', rfl⟩ := hφ
    exact Satisfies.modalFive_axiom m hval w φ'
  | andI =>
    obtain ⟨φ', ψ', rfl⟩ := hφ
    exact Satisfies.andI_axiom m w φ' ψ'
  | andE1 =>
    obtain ⟨φ', ψ', rfl⟩ := hφ
    exact Satisfies.andE1_axiom m w φ' ψ'
  | andE2 =>
    obtain ⟨φ', ψ', rfl⟩ := hφ
    exact Satisfies.andE2_axiom m w φ' ψ'
  | orI1 =>
    obtain ⟨φ', ψ', rfl⟩ := hφ
    exact Satisfies.orI1_axiom m w φ' ψ'
  | orI2 =>
    obtain ⟨φ', ψ', rfl⟩ := hφ
    exact Satisfies.orI2_axiom m w φ' ψ'
  | orE =>
    obtain ⟨φ', ψ', χ', rfl⟩ := hφ
    exact Satisfies.orE_axiom m w φ' ψ' χ'
  | diamondDualityFwd =>
    obtain ⟨φ', rfl⟩ := hφ
    exact Satisfies.diamondDualityFwd_axiom m w φ'
  | diamondDualityBack =>
    obtain ⟨φ', rfl⟩ := hφ
    exact Satisfies.diamondDualityBack_axiom m w φ'

end Cslib.Logic.Modal
