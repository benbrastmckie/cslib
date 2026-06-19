/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Modal.Metalogic.Completeness

/-! # Shared Definitions for Modal Strong Completeness

This module provides shared infrastructure for proving strong completeness
(semantic entailment from a set of premises implies set-derivability) for
all 15 systems in the modal cube.

## Main Definitions

- `ModalSetDerivable Axioms Gamma phi`: `phi` is set-derivable from `Gamma`
  using the modal derivation system for `Axioms`.
- `ModalSemanticEntails FC Gamma phi`: `phi` is a semantic consequence of
  `Gamma` over all frames satisfying the frame class predicate `FC`.

## Supporting Lemmas

- `ModalSetDerivable_of_mem`: Membership implies set-derivability.
- `ModalSetDerivable_weakening`: Set-derivability is monotone in the premise set.
- `ModalSetDerivable_of_Derivable`: Theorems are set-derivable from any set.
- `ModalSetDerivable_empty_iff`: Set-derivability from `∅` is the same as
  derivability.
- `ModalSemanticEntails_of_Valid`: Validity implies semantic entailment.
- `modal_dne_from_neg_neg`: DNE helper: derives `phi` from `ctx ⊢ (¬phi) → ⊥`.
- `modal_not_SetDerivable_union_neg_consistent`: If `phi` is not set-derivable
  from `Gamma`, then `Gamma ∪ {¬phi}` is consistent.

## References

* [A. Chagrov, M. Zakharyaschev, *Modal Logic*][ChagrovZakharyaschev1997], Theorem 1.16
* Cslib/Logics/Propositional/Metalogic/StrongCompleteness.lean -- propositional template
-/

@[expose] public section

namespace Cslib.Logic.Modal

open Cslib.Logic
open Cslib.Logic.Helpers

universe u
variable {Atom : Type u}

attribute [local instance] Classical.propDecidable

/-! ## Set-Based Derivability -/

/-- `phi` is set-derivable from `Gamma` if there exists a finite list `L ⊆ Gamma`
such that `L ⊢ phi` in the modal derivation system for `Axioms`.

This is the "finitary" version of derivability: derivations use only finitely
many assumptions even when `Gamma` is infinite. -/
def ModalSetDerivable (Axioms : Proposition Atom → Prop)
    (Gamma : Set (Proposition Atom)) (phi : Proposition Atom) : Prop :=
  ∃ L : List (Proposition Atom),
    (∀ x ∈ L, x ∈ Gamma) ∧ (modalDerivationSystem Axioms).Deriv L phi

/-! ## Basic ModalSetDerivable Lemmas -/

/-- Any member of `Gamma` is set-derivable from `Gamma`. -/
theorem ModalSetDerivable_of_mem {Axioms : Proposition Atom → Prop}
    {Gamma : Set (Proposition Atom)} {phi : Proposition Atom}
    (h : phi ∈ Gamma) : ModalSetDerivable Axioms Gamma phi :=
  ⟨[phi],
   fun x hx => by simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; exact hx ▸ h,
   (modalDerivationSystem Axioms).assumption (List.mem_cons.mpr (Or.inl rfl))⟩

/-- Set-derivability is monotone: if `Gamma ⊆ Delta` and `phi` is set-derivable
from `Gamma`, then `phi` is set-derivable from `Delta`. -/
theorem ModalSetDerivable_weakening {Axioms : Proposition Atom → Prop}
    {Gamma Delta : Set (Proposition Atom)} (h_sub : Gamma ⊆ Delta)
    {phi : Proposition Atom} (h : ModalSetDerivable Axioms Gamma phi) :
    ModalSetDerivable Axioms Delta phi := by
  obtain ⟨L, hL_sub, hL_deriv⟩ := h
  exact ⟨L, fun x hx => h_sub (hL_sub x hx), hL_deriv⟩

/-- Any theorem (derivable from the empty context) is set-derivable from any set. -/
theorem ModalSetDerivable_of_Derivable {Axioms : Proposition Atom → Prop}
    {phi : Proposition Atom} (h : Derivable Axioms phi)
    (Gamma : Set (Proposition Atom)) : ModalSetDerivable Axioms Gamma phi :=
  ⟨[], fun _ hx => by simp only [List.mem_nil_iff] at hx, by
    obtain ⟨d⟩ := h
    exact ⟨d⟩⟩

/-- Set-derivability from the empty set is equivalent to ordinary derivability. -/
theorem ModalSetDerivable_empty_iff {Axioms : Proposition Atom → Prop}
    {phi : Proposition Atom} :
    ModalSetDerivable Axioms ∅ phi ↔ Derivable Axioms phi := by
  constructor
  · intro ⟨L, hL_sub, hL_deriv⟩
    have hL_nil : L = [] := by
      by_contra h
      obtain ⟨a, ha⟩ := List.exists_mem_of_ne_nil L h
      exact absurd (hL_sub a ha) (fun h => h)
    rw [hL_nil] at hL_deriv
    exact hL_deriv
  · intro h
    exact ModalSetDerivable_of_Derivable h ∅

/-! ## Modal Semantic Entailment -/

/-- `phi` is a semantic consequence of `Gamma` over the frame class `FC`:
every world of every model satisfying `FC` and all formulas in `Gamma` also
satisfies `phi`.

The frame class predicate `FC` takes a model and returns a `Prop`, allowing
it to express arbitrary frame conditions (reflexivity, transitivity, etc.). -/
def ModalSemanticEntails
    (FC : ∀ {World : Type u}, Model World Atom → Prop)
    (Gamma : Set (Proposition Atom)) (phi : Proposition Atom) : Prop :=
  ∀ (World : Type u) (m : Model World Atom) (w : World),
    FC m →
    (∀ γ ∈ Gamma, Satisfies m w γ) →
    Satisfies m w phi

/-- Formulas valid over all `FC`-frames are semantic consequences of any set. -/
theorem ModalSemanticEntails_of_Valid
    {FC : ∀ {World : Type u}, Model World Atom → Prop}
    {phi : Proposition Atom}
    (h : ∀ (World : Type u) (m : Model World Atom), FC m →
      ∀ w, Satisfies m w phi)
    (Gamma : Set (Proposition Atom)) :
    ModalSemanticEntails FC Gamma phi :=
  fun World m w hFC _ => h World m hFC w

/-! ## DNE Helper -/

/-- Given a derivation `ctx ⊢ (¬phi) → ⊥`, produce `ctx ⊢ phi`
via EFQ + implyS composition + Peirce's law. -/
private noncomputable def modal_dne_from_neg_neg
    {Axioms : Proposition Atom → Prop}
    (h_implyK : ∀ (φ ψ : Proposition Atom), Axioms (φ.imp (ψ.imp φ)))
    (h_implyS : ∀ (φ ψ χ : Proposition Atom),
      Axioms ((φ.imp (ψ.imp χ)).imp ((φ.imp ψ).imp (φ.imp χ))))
    (h_efq : ∀ (φ : Proposition Atom), Axioms (Proposition.bot.imp φ))
    (h_peirce : ∀ (φ ψ : Proposition Atom),
      Axioms (((φ.imp ψ).imp φ).imp φ))
    {phi : Proposition Atom}
    {ctx : List (Proposition Atom)}
    (d_neg_neg : DerivationTree Axioms ctx ((¬phi).imp Proposition.bot)) :
    DerivationTree Axioms ctx phi :=
  let d_efq : DerivationTree Axioms ctx (Proposition.bot.imp phi) :=
    .weakening [] ctx _ (.ax [] _ (h_efq phi)) (fun _ h => nomatch h)
  let d_k : DerivationTree Axioms ctx
      ((Proposition.bot.imp phi).imp ((¬phi).imp (Proposition.bot.imp phi))) :=
    .weakening [] ctx _ (.ax [] _ (h_implyK (Proposition.bot.imp phi) (¬phi)))
      (fun _ h => nomatch h)
  let d_step2 := DerivationTree.modus_ponens ctx _ _ d_k d_efq
  let d_s2 : DerivationTree Axioms ctx
      (((¬phi).imp (Proposition.bot.imp phi)).imp
        (((¬phi).imp Proposition.bot).imp ((¬phi).imp phi))) :=
    .weakening [] ctx _ (.ax [] _ (h_implyS (¬phi) Proposition.bot phi))
      (fun _ h => nomatch h)
  let d_step3 := DerivationTree.modus_ponens ctx _ _ d_s2 d_step2
  let d_neg_to_phi : DerivationTree Axioms ctx ((¬phi).imp phi) :=
    DerivationTree.modus_ponens ctx _ _ d_step3 d_neg_neg
  let d_peirce : DerivationTree Axioms ctx (((¬phi).imp phi).imp phi) :=
    .weakening [] ctx _ (.ax [] _ (h_peirce phi Proposition.bot)) (fun _ h => nomatch h)
  DerivationTree.modus_ponens ctx _ _ d_peirce d_neg_to_phi

/-! ## Key Consistency Lemma -/

/-- If `phi` is not set-derivable from `Gamma`, then `Gamma ∪ {¬phi}` is
`SetConsistent Axioms`.

Proof: by contradiction. If some finite `L ⊆ Gamma ∪ {¬phi}` derives `⊥`,
use `deductionWithMem` to eliminate `¬phi` from `L` and get `L' ⊆ Gamma` with
`L' ⊢ (¬phi) → ⊥`. Then EFQ + Peirce gives `L' ⊢ phi`, contradicting
`¬ ModalSetDerivable Axioms Gamma phi`. -/
theorem modal_not_SetDerivable_union_neg_consistent
    {Axioms : Proposition Atom → Prop}
    (h_implyK : ∀ (φ ψ : Proposition Atom), Axioms (φ.imp (ψ.imp φ)))
    (h_implyS : ∀ (φ ψ χ : Proposition Atom),
      Axioms ((φ.imp (ψ.imp χ)).imp ((φ.imp ψ).imp (φ.imp χ))))
    (h_efq : ∀ (φ : Proposition Atom), Axioms (Proposition.bot.imp φ))
    (h_peirce : ∀ (φ ψ : Proposition Atom),
      Axioms (((φ.imp ψ).imp φ).imp φ))
    {Gamma : Set (Proposition Atom)} {phi : Proposition Atom}
    (h_not : ¬ ModalSetDerivable Axioms Gamma phi) :
    SetConsistent Axioms (Gamma ∪ {(¬phi)}) := by
  intro L hL
  unfold Metalogic.Consistent
  intro ⟨d_bot⟩
  by_cases h_neg_in_L : (¬phi) ∈ L
  · have d_neg_neg := deductionWithMem
        h_implyK h_implyS L (¬phi) Proposition.bot d_bot h_neg_in_L
    have h_rem_sub : ∀ x ∈ removeAll L (¬phi), x ∈ Gamma := by
      intro x hx
      simp only [removeAll, ne_eq, decide_not, List.mem_filter,
        Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not] at hx
      obtain ⟨hx_in, hx_ne⟩ := hx
      rcases hL x hx_in with h | h
      · exact h
      · exact absurd (Set.mem_singleton_iff.mp h) hx_ne
    let ctx := removeAll L (¬phi)
    exact h_not ⟨ctx, h_rem_sub,
      ⟨modal_dne_from_neg_neg h_implyK h_implyS h_efq h_peirce d_neg_neg⟩⟩
  · have hL_Gamma : ∀ x ∈ L, x ∈ Gamma := by
      intro x hx
      rcases hL x hx with h | h
      · exact h
      · exact absurd (Set.mem_singleton_iff.mp h ▸ hx) h_neg_in_L
    have d_ext : DerivationTree Axioms ((¬phi) :: L) Proposition.bot :=
      .weakening L ((¬phi) :: L) _ d_bot
        (fun x hx => List.mem_cons.mpr (Or.inr hx))
    have d_dt := deductionTheorem h_implyK h_implyS L (¬phi)
        Proposition.bot d_ext
    exact h_not ⟨L, hL_Gamma,
      ⟨modal_dne_from_neg_neg h_implyK h_implyS h_efq h_peirce d_dt⟩⟩

end Cslib.Logic.Modal
