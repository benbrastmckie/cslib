/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Modal.Metalogic.DeductionTheorem

/-! # Maximal Consistent Sets for Normal Modal Logics

This module instantiates the generic MCS framework (from `Consistency.lean`)
parameterized over an axiom predicate `Axioms : Proposition Atom -> Prop` and proves
modal-specific MCS properties needed for canonical model constructions.

## Parameterization Design

- **Generic properties** (lindenbaum, closed_under_derivation, etc.) take `{Axioms}`
  and, where needed, explicit `h_implyK`/`h_implyS` for the deduction theorem.
- **Modal-specific properties** (mcs_box_closure, mcs_box_box, etc.) take explicit
  axiom hypotheses (e.g., `h_T`, `h_4`, `h_B`, `h_K`) instead of relying on specific
  `S5Axiom` constructors.

## Backward Compatibility

All definitions are parameterized. S5-specific usage passes `S5Axiom` and the
corresponding constructor proofs.

## References

* Cslib/Foundations/Logic/Metalogic/Consistency.lean -- generic MCS framework
* BimodalLogic/Theories/Bimodal/Metalogic/Core/MCSProperties.lean -- reference pattern
-/

@[expose] public section

namespace Cslib.Logic.Modal

open Cslib.Logic

variable {Atom : Type*}

/-! ## Abbreviations for readability -/

/-- Set consistency for a parameterized modal derivation system. -/
abbrev SetConsistent (Axioms : Proposition Atom → Prop)
    (S : Set (Proposition Atom)) : Prop :=
  Metalogic.SetConsistent (modalDerivationSystem Axioms) S

/-- Set maximal consistency for a parameterized modal derivation system. -/
abbrev SetMaximalConsistent (Axioms : Proposition Atom → Prop)
    (S : Set (Proposition Atom)) : Prop :=
  Metalogic.SetMaximalConsistent (modalDerivationSystem Axioms) S

/-! ## Generic MCS Properties (instantiated) -/

/-- Lindenbaum's lemma: every consistent set extends to an MCS.

This is an intentional naming/signature adapter over the generic
`Foundations/Logic/Metalogic/Consistency.lean` `Metalogic.set_lindenbaum`, specialized to
`modalDerivationSystem Axioms`. It (and its sibling family wrappers, e.g. `prop_lindenbaum`,
`temporal_lindenbaum`, `bimodal_lindenbaum`) is retained deliberately: inlining the generic at
every call site would read worse for zero proof-debt reduction. `restricted_lindenbaum`
(`Bimodal/Metalogic/Core/RestrictedMCS.lean`) is a genuine Zorn variant over closure-restricted
supersets, not reducible to `set_lindenbaum`, and is out of scope here. -/
theorem modal_lindenbaum {Axioms : Proposition Atom → Prop}
    {S : Set (Proposition Atom)}
    (hS : SetConsistent Axioms S) :
    ∃ M : Set (Proposition Atom),
      S ⊆ M ∧ SetMaximalConsistent Axioms M :=
  Metalogic.set_lindenbaum (modalDerivationSystem Axioms) hS

/-- Derivable formulas are in MCS. -/
theorem modal_closed_under_derivation
    {Axioms : Proposition Atom → Prop}
    (h_implyK : ∀ (φ ψ : Proposition Atom), Axioms (φ.imp (ψ.imp φ)))
    (h_implyS : ∀ (φ ψ χ : Proposition Atom),
      Axioms ((φ.imp (ψ.imp χ)).imp ((φ.imp ψ).imp (φ.imp χ))))
    {S : Set (Proposition Atom)} (h_mcs : SetMaximalConsistent Axioms S)
    {L : List (Proposition Atom)} (h_sub : ∀ ψ ∈ L, ψ ∈ S)
    {φ : Proposition Atom}
    (h_deriv : (modalDerivationSystem Axioms).Deriv L φ) : φ ∈ S :=
  Metalogic.SetMaximalConsistent.closed_under_derivation
    (modalDerivationSystem Axioms)
    (hasDeductionTheorem h_implyK h_implyS)
    h_mcs h_sub h_deriv

/-- Implication property: if `phi -> psi in S` and `phi in S`, then `psi in S`. -/
theorem modal_implication_property
    {Axioms : Proposition Atom → Prop}
    (h_implyK : ∀ (φ ψ : Proposition Atom), Axioms (φ.imp (ψ.imp φ)))
    (h_implyS : ∀ (φ ψ χ : Proposition Atom),
      Axioms ((φ.imp (ψ.imp χ)).imp ((φ.imp ψ).imp (φ.imp χ))))
    {S : Set (Proposition Atom)} (h_mcs : SetMaximalConsistent Axioms S)
    {φ ψ : Proposition Atom} (h_imp : (φ → ψ) ∈ S) (h_phi : φ ∈ S) :
    ψ ∈ S :=
  Metalogic.SetMaximalConsistent.implication_property
    (modalDerivationSystem Axioms)
    (hasDeductionTheorem h_implyK h_implyS)
    h_mcs h_imp h_phi

/-- Negation completeness: for any formula `phi`, either `phi in S` or `neg phi in S`. -/
theorem modal_negation_complete
    {Axioms : Proposition Atom → Prop}
    (h_implyK : ∀ (φ ψ : Proposition Atom), Axioms (φ.imp (ψ.imp φ)))
    (h_implyS : ∀ (φ ψ χ : Proposition Atom),
      Axioms ((φ.imp (ψ.imp χ)).imp ((φ.imp ψ).imp (φ.imp χ))))
    {S : Set (Proposition Atom)} (h_mcs : SetMaximalConsistent Axioms S)
    (φ : Proposition Atom) : φ ∈ S ∨ (¬φ) ∈ S :=
  Metalogic.SetMaximalConsistent.negation_complete
    (modalDerivationSystem Axioms)
    (hasDeductionTheorem h_implyK h_implyS)
    h_mcs φ

/-! ## Modal-Specific MCS Properties -/

/-- Helper: derive a formula from membership in an MCS using an axiom and MP. -/
theorem mcs_mp_axiom
    {Axioms : Proposition Atom → Prop}
    (h_implyK : ∀ (φ ψ : Proposition Atom), Axioms (φ.imp (ψ.imp φ)))
    (h_implyS : ∀ (φ ψ χ : Proposition Atom),
      Axioms ((φ.imp (ψ.imp χ)).imp ((φ.imp ψ).imp (φ.imp χ))))
    {S : Set (Proposition Atom)} (h_mcs : SetMaximalConsistent Axioms S)
    {φ ψ : Proposition Atom} (h_mem : φ ∈ S) (h_ax : Axioms (φ → ψ)) :
    ψ ∈ S := by
  apply modal_closed_under_derivation h_implyK h_implyS h_mcs
    (L := [φ]) (fun x hx => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; exact hx ▸ h_mem)
  unfold modalDerivationSystem Deriv
  exact ⟨.modus_ponens [φ] φ ψ
    (.weakening [] [φ] (φ → ψ) (.ax [] _ h_ax) (fun _ h => nomatch h))
    (.assumption [φ] φ (List.mem_cons.mpr (Or.inl rfl)))⟩

/-- `bot not in S` for any MCS `S`. -/
theorem mcs_bot_not_mem
    {Axioms : Proposition Atom → Prop}
    {S : Set (Proposition Atom)} (h_mcs : SetMaximalConsistent Axioms S) :
    ⊥ ∉ S := by
  intro h_bot
  exact h_mcs.1 [⊥]
    (fun x hx => by simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; exact hx ▸ h_bot)
    (by simp only [modalDerivationSystem, Deriv]
        exact ⟨.assumption _ _ (List.mem_cons.mpr (Or.inl rfl))⟩)

/-- If `box phi in S` and `S` is MCS, then `phi in S` (using axiom T). -/
theorem mcs_box_closure
    {Axioms : Proposition Atom → Prop}
    (h_implyK : ∀ (φ ψ : Proposition Atom), Axioms (φ.imp (ψ.imp φ)))
    (h_implyS : ∀ (φ ψ χ : Proposition Atom),
      Axioms ((φ.imp (ψ.imp χ)).imp ((φ.imp ψ).imp (φ.imp χ))))
    (h_T : ∀ (φ : Proposition Atom),
      Axioms ((Proposition.box φ).imp φ))
    {S : Set (Proposition Atom)} (h_mcs : SetMaximalConsistent Axioms S)
    {φ : Proposition Atom} (h_box : (□φ) ∈ S) : φ ∈ S :=
  mcs_mp_axiom h_implyK h_implyS h_mcs h_box (h_T φ)

/-- If `box phi in S` and `S` is MCS, then `box box phi in S` (using axiom 4). -/
theorem mcs_box_box
    {Axioms : Proposition Atom → Prop}
    (h_implyK : ∀ (φ ψ : Proposition Atom), Axioms (φ.imp (ψ.imp φ)))
    (h_implyS : ∀ (φ ψ χ : Proposition Atom),
      Axioms ((φ.imp (ψ.imp χ)).imp ((φ.imp ψ).imp (φ.imp χ))))
    (h_4 : ∀ (φ : Proposition Atom),
      Axioms ((Proposition.box φ).imp (Proposition.box (Proposition.box φ))))
    {S : Set (Proposition Atom)} (h_mcs : SetMaximalConsistent Axioms S)
    {φ : Proposition Atom} (h_box : (□φ) ∈ S) :
    (□□φ) ∈ S :=
  mcs_mp_axiom h_implyK h_implyS h_mcs h_box (h_4 φ)

/-- If `phi in S` and `S` is MCS, then `box((box(phi -> bot)) -> bot) in S` (using axiom B,
in its canonical **raw encoded** shape `Axioms.AxiomB`).

`diamond` is a native constructor, not definitionally equal to `(box (phi -> bot)) -> bot`.
`h_B` therefore stays in raw shape (matching how every
`S5Axiom`/`{Sys}Axiom.modalB` constructor is stated, see `ProofSystem/Instances/*.lean`),
and the conclusion is the raw boxed shape rather than `(□◇φ) ∈ S`. Callers bridge to native
`◇` membership only *after* unboxing through the canonical relation, using `mcs_raw_to_dia`
(below) -- this avoids needing a separate boxed-duality axiom or necessitation-closure
argument inside this parametric MCS framework. -/
theorem mcs_box_diamond
    {Axioms : Proposition Atom → Prop}
    (h_implyK : ∀ (φ ψ : Proposition Atom), Axioms (φ.imp (ψ.imp φ)))
    (h_implyS : ∀ (φ ψ χ : Proposition Atom),
      Axioms ((φ.imp (ψ.imp χ)).imp ((φ.imp ψ).imp (φ.imp χ))))
    (h_B : ∀ (φ : Proposition Atom), Axioms (Cslib.Logic.Axioms.AxiomB φ))
    {S : Set (Proposition Atom)} (h_mcs : SetMaximalConsistent Axioms S)
    {φ : Proposition Atom} (h_phi : φ ∈ S) :
    (Proposition.box ((Proposition.box (φ.imp Proposition.bot)).imp Proposition.bot)) ∈ S :=
  mcs_mp_axiom h_implyK h_implyS h_mcs h_phi (h_B φ)

/-! ## Diamond Duality Bridges

`diamond` is a native constructor, so canonical-model reasoning about `◇φ` cannot rely on
`◇φ` unifying syntactically with the raw encoded shape `(□(φ → ⊥)) → ⊥`. These two
lemmas bridge membership in an MCS between the native and raw shapes, using the
`AxiomDiamondDualityFwd`/`AxiomDiamondDualityBack` characterization schemata. -/

/-- Bridge native `◇φ` membership to the raw encoded shape, via `AxiomDiamondDualityFwd`. -/
theorem mcs_dia_to_raw
    {Axioms : Proposition Atom → Prop}
    (h_implyK : ∀ (φ ψ : Proposition Atom), Axioms (φ.imp (ψ.imp φ)))
    (h_implyS : ∀ (φ ψ χ : Proposition Atom),
      Axioms ((φ.imp (ψ.imp χ)).imp ((φ.imp ψ).imp (φ.imp χ))))
    (h_dualFwd : ∀ (φ : Proposition Atom), Axioms (Cslib.Logic.Axioms.AxiomDiamondDualityFwd φ))
    {S : Set (Proposition Atom)} (h_mcs : SetMaximalConsistent Axioms S)
    {φ : Proposition Atom} (h_dia : (◇φ) ∈ S) :
    ((Proposition.box (φ.imp Proposition.bot)).imp Proposition.bot) ∈ S :=
  mcs_mp_axiom h_implyK h_implyS h_mcs h_dia (h_dualFwd φ)

/-- Bridge the raw encoded shape to native `◇φ` membership, via `AxiomDiamondDualityBack`. -/
theorem mcs_raw_to_dia
    {Axioms : Proposition Atom → Prop}
    (h_implyK : ∀ (φ ψ : Proposition Atom), Axioms (φ.imp (ψ.imp φ)))
    (h_implyS : ∀ (φ ψ χ : Proposition Atom),
      Axioms ((φ.imp (ψ.imp χ)).imp ((φ.imp ψ).imp (φ.imp χ))))
    (h_dualBack : ∀ (φ : Proposition Atom), Axioms (Cslib.Logic.Axioms.AxiomDiamondDualityBack φ))
    {S : Set (Proposition Atom)} (h_mcs : SetMaximalConsistent Axioms S)
    {φ : Proposition Atom}
    (h_raw : ((Proposition.box (φ.imp Proposition.bot)).imp Proposition.bot) ∈ S) :
    (◇φ) ∈ S :=
  mcs_mp_axiom h_implyK h_implyS h_mcs h_raw (h_dualBack φ)

/-- If `box(phi -> psi) in S` and `box phi in S`, then `box psi in S` (using axiom K). -/
theorem mcs_box_mp
    {Axioms : Proposition Atom → Prop}
    (h_implyK : ∀ (φ ψ : Proposition Atom), Axioms (φ.imp (ψ.imp φ)))
    (h_implyS : ∀ (φ ψ χ : Proposition Atom),
      Axioms ((φ.imp (ψ.imp χ)).imp ((φ.imp ψ).imp (φ.imp χ))))
    (h_K : ∀ (φ ψ : Proposition Atom),
      Axioms ((Proposition.box (φ.imp ψ)).imp
        ((Proposition.box φ).imp (Proposition.box ψ))))
    {S : Set (Proposition Atom)} (h_mcs : SetMaximalConsistent Axioms S)
    {φ ψ : Proposition Atom} (h_box_imp : (□(φ → ψ)) ∈ S)
    (h_box_phi : (□φ) ∈ S) : (□ψ) ∈ S := by
  have h_k := mcs_mp_axiom h_implyK h_implyS h_mcs h_box_imp (h_K φ ψ)
  exact modal_implication_property h_implyK h_implyS h_mcs h_k h_box_phi

/-! ## Not-in-MCS Lemmas -/

/-- If `phi not in S` (MCS), then `neg phi in S`. -/
theorem mcs_neg_of_not_mem
    {Axioms : Proposition Atom → Prop}
    (h_implyK : ∀ (φ ψ : Proposition Atom), Axioms (φ.imp (ψ.imp φ)))
    (h_implyS : ∀ (φ ψ χ : Proposition Atom),
      Axioms ((φ.imp (ψ.imp χ)).imp ((φ.imp ψ).imp (φ.imp χ))))
    {S : Set (Proposition Atom)} (h_mcs : SetMaximalConsistent Axioms S)
    {φ : Proposition Atom} (h_not : φ ∉ S) : (¬φ) ∈ S := by
  rcases modal_negation_complete h_implyK h_implyS h_mcs φ with h | h
  · exact absurd h h_not
  · exact h

/-- If `neg phi in S` (MCS), then `phi not in S`. -/
theorem mcs_not_mem_of_neg
    {Axioms : Proposition Atom → Prop}
    (h_implyK : ∀ (φ ψ : Proposition Atom), Axioms (φ.imp (ψ.imp φ)))
    (h_implyS : ∀ (φ ψ χ : Proposition Atom),
      Axioms ((φ.imp (ψ.imp χ)).imp ((φ.imp ψ).imp (φ.imp χ))))
    {S : Set (Proposition Atom)} (h_mcs : SetMaximalConsistent Axioms S)
    {φ : Proposition Atom} (h_neg : (¬φ) ∈ S) : φ ∉ S := by
  intro h_phi
  exact mcs_bot_not_mem h_mcs
    (modal_implication_property h_implyK h_implyS h_mcs h_neg h_phi)

/-- `phi in S <-> neg phi not in S` for MCS `S`. -/
theorem mcs_mem_iff_neg_not_mem
    {Axioms : Proposition Atom → Prop}
    (h_implyK : ∀ (φ ψ : Proposition Atom), Axioms (φ.imp (ψ.imp φ)))
    (h_implyS : ∀ (φ ψ χ : Proposition Atom),
      Axioms ((φ.imp (ψ.imp χ)).imp ((φ.imp ψ).imp (φ.imp χ))))
    {S : Set (Proposition Atom)} (h_mcs : SetMaximalConsistent Axioms S)
    {φ : Proposition Atom} : φ ∈ S ↔ (¬φ) ∉ S := by
  constructor
  · intro h hn; exact mcs_bot_not_mem h_mcs
      (modal_implication_property h_implyK h_implyS h_mcs hn h)
  · intro h; rcases modal_negation_complete h_implyK h_implyS h_mcs φ with h' | h'
    · exact h'
    · exact absurd h' h

/-! ## And/Or MCS Closure

MCS-membership closure lemmas for the native `and`/`or` constructors, needed by the
generic truth lemma's `.and`/`.or` cases (`Metalogic/Completeness.lean`). -/

/-- `(φ ∧ ψ) ∈ S ↔ φ ∈ S ∧ ψ ∈ S` for MCS `S`, via `AndI`/`AndE1`/`AndE2`. -/
theorem mcs_and_mem_iff
    {Axioms : Proposition Atom → Prop}
    (h_implyK : ∀ (φ ψ : Proposition Atom), Axioms (φ.imp (ψ.imp φ)))
    (h_implyS : ∀ (φ ψ χ : Proposition Atom),
      Axioms ((φ.imp (ψ.imp χ)).imp ((φ.imp ψ).imp (φ.imp χ))))
    (h_andI : ∀ (φ ψ : Proposition Atom), Axioms (Cslib.Logic.Axioms.AndI φ ψ))
    (h_andE1 : ∀ (φ ψ : Proposition Atom), Axioms (Cslib.Logic.Axioms.AndE1 φ ψ))
    (h_andE2 : ∀ (φ ψ : Proposition Atom), Axioms (Cslib.Logic.Axioms.AndE2 φ ψ))
    {S : Set (Proposition Atom)} (h_mcs : SetMaximalConsistent Axioms S)
    {φ ψ : Proposition Atom} :
    (φ ∧ ψ) ∈ S ↔ φ ∈ S ∧ ψ ∈ S := by
  constructor
  · intro h
    exact ⟨mcs_mp_axiom h_implyK h_implyS h_mcs h (h_andE1 φ ψ),
           mcs_mp_axiom h_implyK h_implyS h_mcs h (h_andE2 φ ψ)⟩
  · intro ⟨h1, h2⟩
    have step := mcs_mp_axiom h_implyK h_implyS h_mcs h1 (h_andI φ ψ)
    exact modal_implication_property h_implyK h_implyS h_mcs step h2

/-- `(φ ∨ ψ) ∈ S ↔ φ ∈ S ∨ ψ ∈ S` for MCS `S`, via `OrI1`/`OrI2`/`OrE`. -/
theorem mcs_or_mem_iff
    {Axioms : Proposition Atom → Prop}
    (h_implyK : ∀ (φ ψ : Proposition Atom), Axioms (φ.imp (ψ.imp φ)))
    (h_implyS : ∀ (φ ψ χ : Proposition Atom),
      Axioms ((φ.imp (ψ.imp χ)).imp ((φ.imp ψ).imp (φ.imp χ))))
    (h_orI1 : ∀ (φ ψ : Proposition Atom), Axioms (Cslib.Logic.Axioms.OrI1 φ ψ))
    (h_orI2 : ∀ (φ ψ : Proposition Atom), Axioms (Cslib.Logic.Axioms.OrI2 φ ψ))
    (h_orE : ∀ (φ ψ χ : Proposition Atom), Axioms (Cslib.Logic.Axioms.OrE φ ψ χ))
    {S : Set (Proposition Atom)} (h_mcs : SetMaximalConsistent Axioms S)
    {φ ψ : Proposition Atom} :
    (φ ∨ ψ) ∈ S ↔ φ ∈ S ∨ ψ ∈ S := by
  constructor
  · intro h
    by_contra hc
    push Not at hc
    obtain ⟨h1, h2⟩ := hc
    have hn1 : (¬φ) ∈ S := mcs_neg_of_not_mem h_implyK h_implyS h_mcs h1
    have hn2 : (¬ψ) ∈ S := mcs_neg_of_not_mem h_implyK h_implyS h_mcs h2
    have step1 := mcs_mp_axiom h_implyK h_implyS h_mcs hn1 (h_orE φ ψ Proposition.bot)
    have step2 := modal_implication_property h_implyK h_implyS h_mcs step1 hn2
    exact mcs_bot_not_mem h_mcs (modal_implication_property h_implyK h_implyS h_mcs step2 h)
  · intro h
    cases h with
    | inl h1 => exact mcs_mp_axiom h_implyK h_implyS h_mcs h1 (h_orI1 φ ψ)
    | inr h2 => exact mcs_mp_axiom h_implyK h_implyS h_mcs h2 (h_orI2 φ ψ)

/-! ## Derivation Helpers for Box Witness -/

/-- Iterated deduction theorem: from `L |- phi`, derive `[] |- chain L phi` where
`chain` builds a right-nested implication. -/
noncomputable def iteratedDeduction
    {Axioms : Proposition Atom → Prop}
    (h_implyK : ∀ (φ ψ : Proposition Atom), Axioms (φ.imp (ψ.imp φ)))
    (h_implyS : ∀ (φ ψ χ : Proposition Atom),
      Axioms ((φ.imp (ψ.imp χ)).imp ((φ.imp ψ).imp (φ.imp χ))))
    (h_K : ∀ (φ ψ : Proposition Atom),
      Axioms ((Proposition.box (φ.imp ψ)).imp
        ((Proposition.box φ).imp (Proposition.box ψ)))) :
    (L : List (Proposition Atom)) → (φ : Proposition Atom) →
    DerivationTree Axioms L φ → (ψ : Proposition Atom) ×'
      DerivationTree Axioms [] ψ ×'
      (∀ (S : Set (Proposition Atom)),
        SetMaximalConsistent Axioms S →
        (□ψ) ∈ S →
        (∀ x ∈ L, (□x) ∈ S) →
        (□φ) ∈ S)
  | [], φ, d => ⟨φ, d, fun _S _h_mcs h_box _ => h_box⟩
  | A :: L', φ, d => by
    have dt := deductionTheorem h_implyK h_implyS L' A φ d
    have ⟨ψ, d_empty, h_prop⟩ :=
      iteratedDeduction h_implyK h_implyS h_K L' (A → φ) dt
    exact ⟨ψ, d_empty, fun S h_mcs h_box_psi h_all_box => by
      have h_box_imp := h_prop S h_mcs h_box_psi
        (fun x hx => h_all_box x (List.mem_cons.mpr (Or.inr hx)))
      have h_box_a := h_all_box A (List.mem_cons.mpr (Or.inl rfl))
      exact mcs_box_mp h_implyK h_implyS h_K h_mcs h_box_imp h_box_a⟩

/-- From `L |- phi` where all elements of `L` have box-versions in MCS `S`,
derive `box phi in S`. -/
theorem derive_box_from_box_context
    {Axioms : Proposition Atom → Prop}
    (h_implyK : ∀ (φ ψ : Proposition Atom), Axioms (φ.imp (ψ.imp φ)))
    (h_implyS : ∀ (φ ψ χ : Proposition Atom),
      Axioms ((φ.imp (ψ.imp χ)).imp ((φ.imp ψ).imp (φ.imp χ))))
    (h_K : ∀ (φ ψ : Proposition Atom),
      Axioms ((Proposition.box (φ.imp ψ)).imp
        ((Proposition.box φ).imp (Proposition.box ψ))))
    {S : Set (Proposition Atom)} (h_mcs : SetMaximalConsistent Axioms S)
    {L : List (Proposition Atom)} {φ : Proposition Atom}
    (d : DerivationTree Axioms L φ)
    (h_all_box : ∀ ψ ∈ L, (□ψ) ∈ S) :
    (□φ) ∈ S := by
  have ⟨ψ, d_empty, h_prop⟩ :=
    iteratedDeduction h_implyK h_implyS h_K L φ d
  have d_box := DerivationTree.necessitation ψ d_empty
  have h_box_psi : (□ψ) ∈ S :=
    modal_closed_under_derivation h_implyK h_implyS h_mcs
      (L := []) (fun _ h => nomatch h) ⟨d_box⟩
  exact h_prop S h_mcs h_box_psi h_all_box

end Cslib.Logic.Modal
