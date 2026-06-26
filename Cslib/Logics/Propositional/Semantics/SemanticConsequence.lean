/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Propositional.Semantics.Bool
public import Cslib.Logics.Propositional.Semantics.Kripke
public import Cslib.Logics.Propositional.ProofSystem.Derivation
public import Cslib.Logics.Propositional.Metalogic.DeductionTheorem
public import Cslib.Logics.Propositional.NaturalDeduction.Equivalence

/-! # Set-Based Derivability and Semantic Consequence

This module defines set-based syntactic derivability and semantic consequence
for classical, intuitionistic, and minimal propositional logic. These are the
foundations needed for strong completeness theorems.

## Main Definitions

- `SetDerivable Axioms Γ φ`: `φ` is derivable from a finite subset of `Γ`.
- `SemanticEntails Γ φ`: Classical semantic consequence (bivalent).
- `ISemanticEntails Γ φ`: Intuitionistic Kripke semantic consequence.
- `MSemanticEntails Γ φ`: Minimal Kripke semantic consequence.

## Basic Lemmas

- `SetDerivable_of_mem`: Any member of `Γ` is set-derivable from `Γ`.
- `SetDerivable_weakening`: Set-derivability is monotone in the premise set.
- `SetDerivable_of_Derivable`: Theorems are set-derivable from any set.
- `SetDerivable_empty_iff`: Set-derivability from `∅` is the same as derivability.
- `SetDerivable_mp`: Modus ponens is closed under set-derivability.
- `setDeriv_deduction`: Deduction theorem at the `SetDerivable` level.
- `setDeriv_cut`: Cut rule at the `SetDerivable` level.

## References

* [A. Chagrov, M. Zakharyaschev, *Modal Logic*][ChagrovZakharyaschev1997], Theorem 1.16
* [A. Chagrov, M. Zakharyaschev, *Modal Logic*][ChagrovZakharyaschev1997], Theorem 2.43
-/

@[expose] public section

namespace Cslib.Logic.PL

open Cslib.Logic

universe u

variable {Atom : Type u}

attribute [local instance] Classical.propDecidable

/-! ## Set-Based Derivability -/

/-- `φ` is set-derivable from `Γ` if there exists a finite list `L ⊆ Γ`
such that `L ⊢ φ` in the given proof system.

This is the "finitary" or "compact" version of derivability: derivations
only use finitely many assumptions, even when `Γ` is infinite. -/
def SetDerivable (Axioms : PL.Proposition Atom → Prop)
    (Γ : Set (PL.Proposition Atom)) (φ : PL.Proposition Atom) : Prop :=
  ∃ L : List (PL.Proposition Atom),
    (∀ x ∈ L, x ∈ Γ) ∧ (propDerivationSystem Axioms).Deriv L φ

/-! ## Basic SetDerivable Lemmas -/

/-- Any member of `Γ` is set-derivable from `Γ`. -/
theorem SetDerivable_of_mem {Axioms : PL.Proposition Atom → Prop}
    {Γ : Set (PL.Proposition Atom)} {φ : PL.Proposition Atom}
    (h : φ ∈ Γ) : SetDerivable Axioms Γ φ :=
  ⟨[φ],
   fun x hx => by simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; exact hx ▸ h,
   (propDerivationSystem Axioms).assumption (List.mem_cons.mpr (Or.inl rfl))⟩

/-- Set-derivability is monotone: if `Γ ⊆ Δ` and `φ` is set-derivable from `Γ`,
then `φ` is set-derivable from `Δ`. -/
theorem SetDerivable_weakening {Axioms : PL.Proposition Atom → Prop}
    {Γ Δ : Set (PL.Proposition Atom)} (h_sub : Γ ⊆ Δ)
    {φ : PL.Proposition Atom} (h : SetDerivable Axioms Γ φ) :
    SetDerivable Axioms Δ φ := by
  obtain ⟨L, hL_sub, hL_deriv⟩ := h
  exact ⟨L, fun x hx => h_sub (hL_sub x hx), hL_deriv⟩

/-- Any theorem (derivable from the empty context) is set-derivable from any set. -/
theorem SetDerivable_of_Derivable {Axioms : PL.Proposition Atom → Prop}
    {φ : PL.Proposition Atom} (h : Derivable Axioms φ)
    (Γ : Set (PL.Proposition Atom)) : SetDerivable Axioms Γ φ :=
  ⟨[], fun _ hx => by simp only [List.mem_nil_iff] at hx, by
    obtain ⟨d⟩ := h
    exact ⟨d⟩⟩

/-- Set-derivability from the empty set is equivalent to ordinary derivability. -/
theorem SetDerivable_empty_iff {Axioms : PL.Proposition Atom → Prop}
    {φ : PL.Proposition Atom} :
    SetDerivable Axioms ∅ φ ↔ Derivable Axioms φ := by
  constructor
  · intro ⟨L, hL_sub, hL_deriv⟩
    have hL_nil : L = [] := by
      by_contra h
      obtain ⟨a, ha⟩ := List.exists_mem_of_ne_nil L h
      exact absurd (hL_sub a ha) (fun h => h)
    rw [hL_nil] at hL_deriv
    exact hL_deriv
  · intro h
    exact SetDerivable_of_Derivable h ∅

/-- Modus ponens is closed under set-derivability: if `Γ ⊢_S φ → ψ` and `Γ ⊢_S φ`,
then `Γ ⊢_S ψ`. -/
theorem SetDerivable_mp {Axioms : PL.Proposition Atom → Prop}
    {Γ : Set (PL.Proposition Atom)} {φ ψ : PL.Proposition Atom}
    (h_imp : SetDerivable Axioms Γ (φ.imp ψ))
    (h_phi : SetDerivable Axioms Γ φ) :
    SetDerivable Axioms Γ ψ := by
  obtain ⟨L₁, hL₁_sub, hL₁_deriv⟩ := h_imp
  obtain ⟨L₂, hL₂_sub, hL₂_deriv⟩ := h_phi
  exact ⟨L₁ ++ L₂,
    fun x hx => by
      rw [List.mem_append] at hx
      exact hx.elim (hL₁_sub x) (hL₂_sub x),
    (propDerivationSystem Axioms).mp
      ((propDerivationSystem Axioms).weakening hL₁_deriv
        (fun x hx => List.mem_append.mpr (Or.inl hx)))
      ((propDerivationSystem Axioms).weakening hL₂_deriv
        (fun x hx => List.mem_append.mpr (Or.inr hx)))⟩

/-! ## SetDerivable Deduction Theorem -/

/-- **Set-Deduction Theorem**: if `B` is set-derivable from `insert A Γ`, then
`A → B` is set-derivable from `Γ`.

This mirrors `min_deriv_imp_of_union` (MinLindenbaum.lean) but is generic over
any `[MinimalAxioms Axioms]`. The proof extracts the finite witness list `L ⊆ insert A Γ`,
applies the standard deduction theorem (`deductionTheorem`/`deductionWithMem`) to eliminate
occurrences of `A` from `L`, and establishes that the resulting list lies in `Γ`.

See [A. Chagrov, M. Zakharyaschev, *Modal Logic*][ChagrovZakharyaschev1997], Theorem 1.16. -/
theorem setDeriv_deduction {Axioms : PL.Proposition Atom → Prop}
    [inst : MinimalAxioms Axioms]
    {Γ : Set (PL.Proposition Atom)} {A B : PL.Proposition Atom}
    (h : SetDerivable Axioms (insert A Γ) B) :
    SetDerivable Axioms Γ (A.imp B) := by
  obtain ⟨L, hL_sub, hL_deriv⟩ := h
  obtain ⟨d⟩ := hL_deriv
  -- Weaken d : DerivationTree Axioms L B to A :: L, then apply the deduction theorem
  have d_ext : DerivationTree Axioms (A :: L) B :=
    DerivationTree.weakening L (A :: L) B d
      (fun x hx => List.mem_cons.mpr (Or.inr hx))
  have d_dt : DerivationTree Axioms L (A.imp B) :=
    deductionTheorem inst.h_K inst.h_S L A B d_ext
  -- hL_sub says each element of L is in insert A Γ = {A} ∪ Γ
  -- (Set.mem_insert_iff: x ∈ insert A Γ ↔ x = A ∨ x ∈ Γ)
  by_cases hAL : A ∈ L
  · -- A appears in L: use deductionWithMem to eliminate all occurrences of A
    open Cslib.Logic.Helpers in
    have d_mem : DerivationTree Axioms (removeAll L A) (A.imp (A.imp B)) :=
      deductionWithMem inst.h_K inst.h_S L A (A.imp B) d_dt hAL
    -- removeAll L A ⊆ Γ (since every element of L that is not A belongs to Γ)
    open Cslib.Logic.Helpers in
    have h_rem_sub : ∀ x ∈ removeAll L A, x ∈ Γ := by
      intro x hx
      simp only [removeAll, ne_eq, decide_not, List.mem_filter, Bool.not_eq_eq_eq_not,
        Bool.not_true, decide_eq_false_iff_not] at hx
      obtain ⟨hx_in, hx_ne⟩ := hx
      rcases Set.mem_insert_iff.mp (hL_sub x hx_in) with rfl | hmem
      · exact absurd rfl hx_ne
      · exact hmem
    -- Collapse A → (A → B) to A → B via S-combinator + identity
    open Cslib.Logic.Helpers in
    let ctx := removeAll L A
    -- S-axiom instance: (A → (A → B)) → ((A → A) → (A → B))
    open Cslib.Logic.Helpers in
    have d_is : DerivationTree Axioms ctx
        ((A.imp (A.imp B)).imp ((A.imp A).imp (A.imp B))) :=
      DerivationTree.weakening [] ctx _ (.ax [] _ (inst.h_S A A B)) (fun _ h => nomatch h)
    -- Apply to d_mem: ctx ⊢ (A → A) → (A → B)
    open Cslib.Logic.Helpers in
    have d_step1 : DerivationTree Axioms ctx ((A.imp A).imp (A.imp B)) :=
      DerivationTree.modus_ponens ctx _ _ d_is d_mem
    -- Build A → A from K and S: ⊢ A → A
    have d_k1 : DerivationTree Axioms [] (A.imp ((A.imp A).imp A)) :=
      .ax [] _ (inst.h_K A (A.imp A))
    have d_s1 : DerivationTree Axioms []
        ((A.imp ((A.imp A).imp A)).imp ((A.imp (A.imp A)).imp (A.imp A))) :=
      .ax [] _ (inst.h_S A (A.imp A) A)
    have d_mp1 : DerivationTree Axioms [] ((A.imp (A.imp A)).imp (A.imp A)) :=
      DerivationTree.modus_ponens [] _ _ d_s1 d_k1
    have d_k2 : DerivationTree Axioms [] (A.imp (A.imp A)) :=
      .ax [] _ (inst.h_K A A)
    have d_id : DerivationTree Axioms [] (A.imp A) :=
      DerivationTree.modus_ponens [] _ _ d_mp1 d_k2
    open Cslib.Logic.Helpers in
    have d_id_w : DerivationTree Axioms ctx (A.imp A) :=
      DerivationTree.weakening [] ctx _ d_id (fun _ h => nomatch h)
    -- Apply S-result to identity: ctx ⊢ A → B
    open Cslib.Logic.Helpers in
    have d_final : DerivationTree Axioms ctx (A.imp B) :=
      DerivationTree.modus_ponens ctx _ _ d_step1 d_id_w
    exact ⟨ctx, h_rem_sub, ⟨d_final⟩⟩
  · -- A ∉ L: every element of L already belongs to Γ
    have hL_sub' : ∀ x ∈ L, x ∈ Γ := by
      intro x hx
      rcases Set.mem_insert_iff.mp (hL_sub x hx) with rfl | hmem
      · exact absurd hx hAL
      · exact hmem
    exact ⟨L, hL_sub', ⟨d_dt⟩⟩

/-- **Set-Cut Rule**: if `B` is set-derivable from `insert A Γ` and `A` is itself
set-derivable from `Γ`, then `B` is set-derivable from `Γ`.

This is an immediate corollary of `setDeriv_deduction` and `SetDerivable_mp`. -/
theorem setDeriv_cut {Axioms : PL.Proposition Atom → Prop}
    [MinimalAxioms Axioms]
    {Γ : Set (PL.Proposition Atom)} {A B : PL.Proposition Atom}
    (hAB : SetDerivable Axioms (insert A Γ) B)
    (hA : SetDerivable Axioms Γ A) :
    SetDerivable Axioms Γ B :=
  SetDerivable_mp (setDeriv_deduction hAB) hA

/-! ## Classical Semantic Consequence -/

/-- Classical (bivalent) semantic consequence: `φ` is a semantic consequence of `Γ`
if every valuation satisfying all formulas in `Γ` also satisfies `φ`.

**Convention note**: The premise `∀ ψ ∈ Γ, Evaluate v ψ` uses Prop-valued forcing rather than
the algebraic `SatisfiesTheory (Evaluate v) Γ` form (which would require `Evaluate v ψ = ⊤`,
i.e. `= True` in `Prop`). These are propositionally but not definitionally equal (propext is
needed), so the algebraic `⊨` notation from `Defs.lean` cannot be applied here defeq-safely.
Full unification of the Prop-forcing and algebraic-`= ⊤` conventions is a deferred roadmap item. -/
def SemanticEntails (Γ : Set (PL.Proposition Atom))
    (φ : PL.Proposition Atom) : Prop :=
  ∀ (v : Valuation Atom),
    (∀ ψ ∈ Γ, Evaluate v ψ) → Evaluate v φ

/-! ## Intuitionistic Kripke Semantic Consequence -/

/-- Intuitionistic Kripke semantic consequence: `φ` is an intuitionistic consequence
of `Γ` if for every intuitionistic Kripke model (with `bot_forces = fun _ => False`)
and every world where all formulas in `Γ` are forced, `φ` is also forced.

**Convention note**: The premise `∀ ψ ∈ Γ, IForces val ... w ψ` uses Prop-valued Kripke
forcing rather than the algebraic `SatisfiesTheory` form. These inhabit different semantic
layers (`IForces` is a world-indexed relation, not an `= ⊤` equation), so the algebraic
`⊨` notation from `Defs.lean` does not apply here. Full unification is a deferred roadmap item. -/
def ISemanticEntails (Γ : Set (PL.Proposition Atom))
    (φ : PL.Proposition Atom) : Prop :=
  ∀ (World : Type u) [Preorder World] (val : World → Atom → Prop),
    (∀ {w w' : World} (p : Atom), w ≤ w' → val w p → val w' p) →
    ∀ (w : World),
      (∀ ψ ∈ Γ, IForces val (fun _ => False) w ψ) →
      IForces val (fun _ => False) w φ

/-! ## Minimal Kripke Semantic Consequence -/

/-- Minimal Kripke semantic consequence: `φ` is a minimal consequence of `Γ`
if for every minimal Kripke model (with arbitrary upward-closed `bot_forces`)
and every world where all formulas in `Γ` are forced, `φ` is also forced.

**Convention note**: As with `ISemanticEntails`, the premise uses Prop-valued Kripke
forcing (`IForces val bot_forces w ψ`) rather than the algebraic `SatisfiesTheory` form.
These inhabit different semantic layers and the algebraic `⊨` notation from `Defs.lean`
does not apply here defeq-safely. Full unification is a deferred roadmap item. -/
def MSemanticEntails (Γ : Set (PL.Proposition Atom))
    (φ : PL.Proposition Atom) : Prop :=
  ∀ (World : Type u) [Preorder World] (val : World → Atom → Prop)
    (bot_forces : World → Prop),
    (∀ {w w' : World} (p : Atom), w ≤ w' → val w p → val w' p) →
    (∀ {w w' : World}, w ≤ w' → bot_forces w → bot_forces w') →
    ∀ (w : World),
      (∀ ψ ∈ Γ, IForces val bot_forces w ψ) →
      IForces val bot_forces w φ

/-! ## Entailment from Validity -/

/-- Classical tautologies are classical semantic consequences of any set. -/
theorem SemanticEntails_of_Tautology {φ : PL.Proposition Atom}
    (h : Tautology φ) (Γ : Set (PL.Proposition Atom)) :
    SemanticEntails Γ φ :=
  fun v _ => h v

/-- Intuitionistic valid formulas are intuitionistic semantic consequences of any set. -/
theorem ISemanticEntails_of_IValid {φ : PL.Proposition Atom}
    (h : IValid.{u, u} φ) (Γ : Set (PL.Proposition Atom)) :
    ISemanticEntails Γ φ :=
  fun World _ val v_uc w _ => h World val v_uc w

/-- Minimally valid formulas are minimal semantic consequences of any set. -/
theorem MSemanticEntails_of_MValid {φ : PL.Proposition Atom}
    (h : MValid.{u, u} φ) (Γ : Set (PL.Proposition Atom)) :
    MSemanticEntails Γ φ :=
  fun World _ val bot_forces v_uc bf_uc w _ => h World val bot_forces v_uc bf_uc w

end Cslib.Logic.PL
