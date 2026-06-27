/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Foundations.Order.BrouwerianSemilattice
public import Cslib.Logics.Propositional.Semantics.Algebra
public import Cslib.Logics.Propositional.NaturalDeduction.HilbertDerivedRules
public import Cslib.Logics.Propositional.NaturalDeduction.Equivalence
public import Mathlib.Order.Heyting.Regular

/-! # Hilbert Lindenbaum Quotient Algebra

This module constructs the **Hilbert Lindenbaum quotient algebra**: the quotient of
`Proposition Atom` by Hilbert derivational equivalence, using `Deriv Axioms` directly
rather than the natural-deduction `DerivableIn`.

## Main Definitions

- `HilbertEquiv Axioms A B`: `Deriv Axioms [A] B ∧ Deriv Axioms [B] A`.
- `hilbertPropositionSetoid Axioms`: the induced `Setoid (Proposition Atom)`.
- `HilbertLindenbaumAlgebra Axioms`: the quotient type.
- `hilbertLindenbaumMk Axioms A`: the quotient map.
- `GeneralizedHeytingAlgebra` instance for any `[MinimalAxioms Axioms]`.
- `HeytingAlgebra` instance when `Axioms` includes EFQ.
- `BooleanAlgebra` instance when `Axioms` includes EFQ and Peirce.

## Main Results

- `hilbertLindenbaumMk_le_mk`: `[A] ≤ [B] ↔ Deriv Axioms [A] B`.
- `hilbertLindenbaumMk_sup`: `[A ∨ B] = [A] ⊔ [B]`.
- `hilbertLindenbaumMk_inf`: `[A ∧ B] = [A] ⊓ [B]`.
- `hilbertLindenbaumMk_himp`: `[A → B] = [A] ⇨ [B]`.

## References

* [A. Rasiowa, *An Algebraic Approach to Non-Classical Logics*][Rasiowa1974]
-/

@[expose] public section

noncomputable section

namespace Cslib.Logic.PL

open Proposition

variable {Atom : Type*}

/-! ## Hilbert Equivalence Relation -/

/-- Two propositions are Hilbert-equivalent if each is derivable from the other in a
singleton context. This is the quotient relation for the Hilbert Lindenbaum algebra. -/
def HilbertEquiv (Axioms : Proposition Atom → Prop) (A B : Proposition Atom) : Prop :=
  Deriv Axioms [A] B ∧ Deriv Axioms [B] A

/-! ## Equivalence Relation Lemmas -/

/-- Helper: cut a derivation `[A] ⊢ B` against `[B] ⊢ C` to obtain `[A] ⊢ C`,
collapsing `[A] ++ [] = [A]` after applying `hilbertCutDeriv`. Requires K and S axioms. -/
theorem hilbertCutSingletonDeriv
    {Axioms : Proposition Atom → Prop}
    (h_K : ∀ (φ ψ : Proposition Atom), Axioms (φ.imp (ψ.imp φ)))
    (h_S : ∀ (φ ψ χ : Proposition Atom),
      Axioms ((φ.imp (ψ.imp χ)).imp ((φ.imp ψ).imp (φ.imp χ))))
    {A B C : Proposition Atom}
    (hAB : Deriv Axioms [A] B)
    (hBC : Deriv Axioms [B] C) :
    Deriv Axioms [A] C := by
  have hcut := hilbertCutDeriv h_K h_S hAB hBC
  simp only [List.append_nil] at hcut
  exact hcut

/-- Helper: weaken a derivation from a singleton list `[X]` to a list `X :: rest`. -/
theorem hilbertWeakenSingleton
    {Axioms : Proposition Atom → Prop}
    {X : Proposition Atom}
    {rest : List (Proposition Atom)}
    {φ : Proposition Atom}
    (h : Deriv Axioms [X] φ) :
    Deriv Axioms (X :: rest) φ :=
  hilbertWeakeningDeriv h (fun x hx => by
    simp only [List.mem_singleton] at hx; subst hx; exact List.mem_cons_self)

/-- Helper: cut a derivation `Γ ⊢ B` against `[B] ⊢ C` to obtain `Γ ⊢ C`.
Handles the general case where `Γ` is any list (not necessarily a singleton).
Uses `Γ ++ [] = Γ` after applying `hilbertCutDeriv`. Requires K and S axioms. -/
theorem hilbertCutListDeriv
    {Axioms : Proposition Atom → Prop}
    (h_K : ∀ (φ ψ : Proposition Atom), Axioms (φ.imp (ψ.imp φ)))
    (h_S : ∀ (φ ψ χ : Proposition Atom),
      Axioms ((φ.imp (ψ.imp χ)).imp ((φ.imp ψ).imp (φ.imp χ))))
    {Γ : List (Proposition Atom)}
    {B C : Proposition Atom}
    (hAB : Deriv Axioms Γ B)
    (hBC : Deriv Axioms [B] C) :
    Deriv Axioms Γ C := by
  have hcut := hilbertCutDeriv h_K h_S hAB hBC
  simp only [List.append_nil] at hcut
  exact hcut

/-- `HilbertEquiv` is reflexive: `A ≡ A` via the assumption rule. -/
theorem hilbertEquiv_refl (Axioms : Proposition Atom → Prop) (A : Proposition Atom) :
    HilbertEquiv Axioms A A :=
  ⟨assumption_deriv List.mem_cons_self,
   assumption_deriv List.mem_cons_self⟩

/-- `HilbertEquiv` is symmetric by swapping the two directions. -/
theorem hilbertEquiv_symm
    {Axioms : Proposition Atom → Prop} {A B : Proposition Atom}
    (h : HilbertEquiv Axioms A B) :
    HilbertEquiv Axioms B A :=
  ⟨h.2, h.1⟩

/-- `HilbertEquiv` is transitive via the cut rule. Requires K and S axioms. -/
theorem hilbertEquiv_trans
    {Axioms : Proposition Atom → Prop}
    (h_K : ∀ (φ ψ : Proposition Atom), Axioms (φ.imp (ψ.imp φ)))
    (h_S : ∀ (φ ψ χ : Proposition Atom),
      Axioms ((φ.imp (ψ.imp χ)).imp ((φ.imp ψ).imp (φ.imp χ))))
    {A B C : Proposition Atom}
    (hAB : HilbertEquiv Axioms A B) (hBC : HilbertEquiv Axioms B C) :
    HilbertEquiv Axioms A C :=
  ⟨hilbertCutSingletonDeriv h_K h_S hAB.1 hBC.1,
   hilbertCutSingletonDeriv h_K h_S hBC.2 hAB.2⟩

/-! ## Setoid, Quotient Type, and Quotient Map -/

/-- The Hilbert-equivalence setoid on `Proposition Atom`.
Requires `ConjImpAxioms` for K and S (needed by transitivity). -/
def hilbertPropositionSetoid
    {Axioms : Proposition Atom → Prop}
    [inst : ConjImpAxioms Axioms] :
    Setoid (Proposition Atom) where
  r := HilbertEquiv Axioms
  iseqv := {
    refl := hilbertEquiv_refl Axioms
    symm := hilbertEquiv_symm
    trans := fun hab hbc => hilbertEquiv_trans inst.h_K inst.h_S hab hbc
  }

/-- The Hilbert Lindenbaum algebra: quotient of `Proposition Atom` by Hilbert equivalence.
Parameterized over an axiom predicate with a `ConjImpAxioms` instance. The `ConjImpAxioms`
typeclass (K, S, andI, andE1, andE2) is sufficient for the meet-fragment and BSL structure;
`MinimalAxioms` additionally provides or-axioms enabling the GHA instance. -/
def HilbertLindenbaumAlgebra
    (Axioms : Proposition Atom → Prop)
    [ConjImpAxioms Axioms] : Type _ :=
  Quotient (@hilbertPropositionSetoid _ Axioms _)

/-- The quotient map: sends `A` to its Hilbert equivalence class `[A]`. -/
def hilbertLindenbaumMk
    {Axioms : Proposition Atom → Prop}
    [ConjImpAxioms Axioms]
    (A : Proposition Atom) :
    HilbertLindenbaumAlgebra Axioms :=
  Quotient.mk hilbertPropositionSetoid A

/-! ## Order on the Quotient -/

/-- `[A] ≤ [B]` iff `Deriv Axioms [A] B`. Well-defined by Hilbert equivalence. -/
def hilbertLindenbaumLe
    {Axioms : Proposition Atom → Prop}
    [inst : ConjImpAxioms Axioms]
    (x y : HilbertLindenbaumAlgebra Axioms) : Prop :=
  Quotient.liftOn₂ x y
    (fun A B => Deriv Axioms [A] B)
    (fun _ _ _ _ hA hB => propext ⟨
      fun h =>
        hilbertCutSingletonDeriv inst.h_K inst.h_S
          (hilbertCutSingletonDeriv inst.h_K inst.h_S hA.2 h)
          hB.1,
      fun h =>
        hilbertCutSingletonDeriv inst.h_K inst.h_S
          (hilbertCutSingletonDeriv inst.h_K inst.h_S hA.1 h)
          hB.2⟩)

/-- The order on `HilbertLindenbaumAlgebra` reduces to derivability on representatives. -/
@[simp]
theorem hilbertLindenbaumLe_mk
    {Axioms : Proposition Atom → Prop}
    [ConjImpAxioms Axioms]
    (A B : Proposition Atom) :
    hilbertLindenbaumLe (hilbertLindenbaumMk (Axioms := Axioms) A)
      (hilbertLindenbaumMk B) ↔
    Deriv Axioms [A] B :=
  Iff.rfl

/-! ## Congruence Lemmas for Quotient Operations -/

/-- Or-congruence: if `A ≡ A'` and `B ≡ B'` then `A ∨ B ≡ A' ∨ B'`. -/
theorem hilbertEquivOrCongr
    {Axioms : Proposition Atom → Prop}
    [inst : MinimalAxioms Axioms]
    {A A' B B' : Proposition Atom}
    (hA : HilbertEquiv Axioms A A')
    (hB : HilbertEquiv Axioms B B') :
    HilbertEquiv Axioms (A.or B) (A'.or B') := by
  constructor
  · -- [A ∨ B] ⊢ A' ∨ B': case split on A ∨ B
    apply hilbertOrEDeriv inst.h_K inst.h_S inst.h_orE
    · exact assumption_deriv List.mem_cons_self
    · -- goal: Deriv [A, A ∨ B] (A' ∨ B')
      apply hilbertOrI1Deriv inst.h_orI1
      -- need Deriv [A, A ∨ B] A', weaken hA.1 : Deriv [A] A'
      exact hilbertWeakenSingleton hA.1
    · -- goal: Deriv [B, A ∨ B] (A' ∨ B')
      apply hilbertOrI2Deriv inst.h_orI2
      exact hilbertWeakenSingleton hB.1
  · apply hilbertOrEDeriv inst.h_K inst.h_S inst.h_orE
    · exact assumption_deriv List.mem_cons_self
    · apply hilbertOrI1Deriv inst.h_orI1
      exact hilbertWeakenSingleton hA.2
    · apply hilbertOrI2Deriv inst.h_orI2
      exact hilbertWeakenSingleton hB.2

/-- And-congruence: if `A ≡ A'` and `B ≡ B'` then `A ∧ B ≡ A' ∧ B'`. -/
theorem hilbertEquivAndCongr
    {Axioms : Proposition Atom → Prop}
    [inst : ConjImpAxioms Axioms]
    {A A' B B' : Proposition Atom}
    (hA : HilbertEquiv Axioms A A')
    (hB : HilbertEquiv Axioms B B') :
    HilbertEquiv Axioms (A.and B) (A'.and B') := by
  constructor
  · -- [A ∧ B] ⊢ A' ∧ B'
    have hAssume := assumption_deriv (Axioms := Axioms) (Γ := [A.and B]) List.mem_cons_self
    have hA_part := hilbertAndE1Deriv inst.h_andE1 hAssume
    have hB_part := hilbertAndE2Deriv inst.h_andE2 hAssume
    exact hilbertAndIDeriv inst.h_andI
      (hilbertCutSingletonDeriv inst.h_K inst.h_S hA_part hA.1)
      (hilbertCutSingletonDeriv inst.h_K inst.h_S hB_part hB.1)
  · -- [A' ∧ B'] ⊢ A ∧ B
    have hAssume := assumption_deriv (Axioms := Axioms) (Γ := [A'.and B']) List.mem_cons_self
    have hA'_part := hilbertAndE1Deriv inst.h_andE1 hAssume
    have hB'_part := hilbertAndE2Deriv inst.h_andE2 hAssume
    exact hilbertAndIDeriv inst.h_andI
      (hilbertCutSingletonDeriv inst.h_K inst.h_S hA'_part hA.2)
      (hilbertCutSingletonDeriv inst.h_K inst.h_S hB'_part hB.2)

/-- Imp-congruence: if `A ≡ A'` and `B ≡ B'` then `A → B ≡ A' → B'`. -/
theorem hilbertEquivImpCongr
    {Axioms : Proposition Atom → Prop}
    [inst : ConjImpAxioms Axioms]
    {A A' B B' : Proposition Atom}
    (hA : HilbertEquiv Axioms A A')
    (hB : HilbertEquiv Axioms B B') :
    HilbertEquiv Axioms (A.imp B) (A'.imp B') := by
  constructor
  · -- [A → B] ⊢ A' → B'
    apply hilbertImpIDeriv inst.h_K inst.h_S
    -- context: A' :: [A → B] = [A', A → B]
    -- need [A', A → B] ⊢ B'
    have hAimp : Deriv Axioms [A', A.imp B] (A.imp B) :=
      assumption_deriv (by simp)
    -- weaken hA.2 : Deriv [A'] A to Deriv [A', A → B] A
    have hA_part : Deriv Axioms [A', A.imp B] A :=
      hilbertWeakenSingleton hA.2
    -- apply impE to get B, then cut with hB.1
    have hB_part := hilbertImpEDeriv hAimp hA_part
    exact hilbertCutListDeriv inst.h_K inst.h_S hB_part hB.1
  · -- [A' → B'] ⊢ A → B
    apply hilbertImpIDeriv inst.h_K inst.h_S
    have hA'imp : Deriv Axioms [A, A'.imp B'] (A'.imp B') :=
      assumption_deriv (by simp)
    have hA'_part : Deriv Axioms [A, A'.imp B'] A' :=
      hilbertWeakenSingleton hA.1
    have hB'_part := hilbertImpEDeriv hA'imp hA'_part
    exact hilbertCutListDeriv inst.h_K inst.h_S hB'_part hB.2

/-! ## Operations on the Quotient -/

/-- Join: `[A] ⊔ [B] = [A ∨ B]`. -/
def hilbertLindenbaumSup
    {Axioms : Proposition Atom → Prop}
    [inst : MinimalAxioms Axioms]
    (x y : HilbertLindenbaumAlgebra Axioms) :
    HilbertLindenbaumAlgebra Axioms :=
  Quotient.lift₂
    (fun A B => hilbertLindenbaumMk (A.or B))
    (fun _ _ _ _ hA hB => Quotient.sound (hilbertEquivOrCongr hA hB))
    x y

/-- Meet: `[A] ⊓ [B] = [A ∧ B]`. -/
def hilbertLindenbaumInf
    {Axioms : Proposition Atom → Prop}
    [inst : ConjImpAxioms Axioms]
    (x y : HilbertLindenbaumAlgebra Axioms) :
    HilbertLindenbaumAlgebra Axioms :=
  Quotient.lift₂
    (fun A B => hilbertLindenbaumMk (A.and B))
    (fun _ _ _ _ hA hB => Quotient.sound (hilbertEquivAndCongr hA hB))
    x y

/-- Heyting implication: `[A] ⇨ [B] = [A → B]`. -/
def hilbertLindenbaumHimp
    {Axioms : Proposition Atom → Prop}
    [inst : ConjImpAxioms Axioms]
    (x y : HilbertLindenbaumAlgebra Axioms) :
    HilbertLindenbaumAlgebra Axioms :=
  Quotient.lift₂
    (fun A B => hilbertLindenbaumMk (A.imp B))
    (fun _ _ _ _ hA hB => Quotient.sound (hilbertEquivImpCongr hA hB))
    x y

/-- `[A ∨ B] = [A] ⊔ [B]`. -/
@[simp]
theorem hilbertLindenbaumSup_mk
    {Axioms : Proposition Atom → Prop}
    [MinimalAxioms Axioms]
    (A B : Proposition Atom) :
    hilbertLindenbaumSup (hilbertLindenbaumMk (Axioms := Axioms) A)
      (hilbertLindenbaumMk B) =
    hilbertLindenbaumMk (A.or B) := rfl

/-- `[A ∧ B] = [A] ⊓ [B]`. -/
@[simp]
theorem hilbertLindenbaumInf_mk
    {Axioms : Proposition Atom → Prop}
    [ConjImpAxioms Axioms]
    (A B : Proposition Atom) :
    hilbertLindenbaumInf (hilbertLindenbaumMk (Axioms := Axioms) A)
      (hilbertLindenbaumMk B) =
    hilbertLindenbaumMk (A.and B) := rfl

/-- `[A → B] = [A] ⇨ [B]`. -/
@[simp]
theorem hilbertLindenbaumHimp_mk
    {Axioms : Proposition Atom → Prop}
    [ConjImpAxioms Axioms]
    (A B : Proposition Atom) :
    hilbertLindenbaumHimp (hilbertLindenbaumMk (Axioms := Axioms) A)
      (hilbertLindenbaumMk B) =
    hilbertLindenbaumMk (A.imp B) := rfl

/-! ## GHA Axiom Lemmas -/

/-- Reflexivity: `[A] ≤ [A]` via the assumption rule. -/
theorem hilbertLindenbaumLe_refl
    {Axioms : Proposition Atom → Prop}
    [ConjImpAxioms Axioms]
    (x : HilbertLindenbaumAlgebra Axioms) :
    hilbertLindenbaumLe x x := by
  obtain ⟨A, rfl⟩ := Quotient.exists_rep x
  exact assumption_deriv List.mem_cons_self

/-- Transitivity via cut. -/
theorem hilbertLindenbaumLe_trans
    {Axioms : Proposition Atom → Prop}
    [inst : ConjImpAxioms Axioms]
    (x y z : HilbertLindenbaumAlgebra Axioms)
    (hxy : hilbertLindenbaumLe x y) (hyz : hilbertLindenbaumLe y z) :
    hilbertLindenbaumLe x z := by
  obtain ⟨A, rfl⟩ := Quotient.exists_rep x
  obtain ⟨B, rfl⟩ := Quotient.exists_rep y
  obtain ⟨C, rfl⟩ := Quotient.exists_rep z
  exact hilbertCutSingletonDeriv inst.h_K inst.h_S hxy hyz

/-- Antisymmetry via `Quotient.sound`. -/
theorem hilbertLindenbaumLe_antisymm
    {Axioms : Proposition Atom → Prop}
    [ConjImpAxioms Axioms]
    (x y : HilbertLindenbaumAlgebra Axioms)
    (hxy : hilbertLindenbaumLe x y) (hyx : hilbertLindenbaumLe y x) :
    x = y := by
  obtain ⟨A, rfl⟩ := Quotient.exists_rep x
  obtain ⟨B, rfl⟩ := Quotient.exists_rep y
  exact Quotient.sound ⟨hxy, hyx⟩

/-- `[A] ≤ [A ∨ B]` via orI1. -/
theorem hilbertLindenbaumLe_sup_left
    {Axioms : Proposition Atom → Prop}
    [inst : MinimalAxioms Axioms]
    (x y : HilbertLindenbaumAlgebra Axioms) :
    hilbertLindenbaumLe x (hilbertLindenbaumSup x y) := by
  obtain ⟨A, rfl⟩ := Quotient.exists_rep x
  obtain ⟨B, rfl⟩ := Quotient.exists_rep y
  exact hilbertOrI1Deriv inst.h_orI1 (assumption_deriv List.mem_cons_self)

/-- `[B] ≤ [A ∨ B]` via orI2. -/
theorem hilbertLindenbaumLe_sup_right
    {Axioms : Proposition Atom → Prop}
    [inst : MinimalAxioms Axioms]
    (x y : HilbertLindenbaumAlgebra Axioms) :
    hilbertLindenbaumLe y (hilbertLindenbaumSup x y) := by
  obtain ⟨A, rfl⟩ := Quotient.exists_rep x
  obtain ⟨B, rfl⟩ := Quotient.exists_rep y
  exact hilbertOrI2Deriv inst.h_orI2 (assumption_deriv List.mem_cons_self)

/-- `sup_le`: from `[A] ≤ [C]` and `[B] ≤ [C]` derive `[A ∨ B] ≤ [C]` via orE. -/
theorem hilbertLindenbaumSup_le
    {Axioms : Proposition Atom → Prop}
    [inst : MinimalAxioms Axioms]
    (x y z : HilbertLindenbaumAlgebra Axioms)
    (hxz : hilbertLindenbaumLe x z) (hyz : hilbertLindenbaumLe y z) :
    hilbertLindenbaumLe (hilbertLindenbaumSup x y) z := by
  obtain ⟨A, rfl⟩ := Quotient.exists_rep x
  obtain ⟨B, rfl⟩ := Quotient.exists_rep y
  obtain ⟨C, rfl⟩ := Quotient.exists_rep z
  apply hilbertOrEDeriv inst.h_K inst.h_S inst.h_orE
  · exact assumption_deriv List.mem_cons_self
  · exact hilbertWeakenSingleton hxz
  · exact hilbertWeakenSingleton hyz

/-- `[A ∧ B] ≤ [A]` via andE1. -/
theorem hilbertLindenbaumInf_le_left
    {Axioms : Proposition Atom → Prop}
    [inst : ConjImpAxioms Axioms]
    (x y : HilbertLindenbaumAlgebra Axioms) :
    hilbertLindenbaumLe (hilbertLindenbaumInf x y) x := by
  obtain ⟨A, rfl⟩ := Quotient.exists_rep x
  obtain ⟨B, rfl⟩ := Quotient.exists_rep y
  exact hilbertAndE1Deriv inst.h_andE1 (assumption_deriv List.mem_cons_self)

/-- `[A ∧ B] ≤ [B]` via andE2. -/
theorem hilbertLindenbaumInf_le_right
    {Axioms : Proposition Atom → Prop}
    [inst : ConjImpAxioms Axioms]
    (x y : HilbertLindenbaumAlgebra Axioms) :
    hilbertLindenbaumLe (hilbertLindenbaumInf x y) y := by
  obtain ⟨A, rfl⟩ := Quotient.exists_rep x
  obtain ⟨B, rfl⟩ := Quotient.exists_rep y
  exact hilbertAndE2Deriv inst.h_andE2 (assumption_deriv List.mem_cons_self)

/-- `le_inf`: from `[A] ≤ [B]` and `[A] ≤ [C]` derive `[A] ≤ [B ∧ C]` via andI. -/
theorem hilbertLindenbaumLe_inf
    {Axioms : Proposition Atom → Prop}
    [inst : ConjImpAxioms Axioms]
    (x y z : HilbertLindenbaumAlgebra Axioms)
    (hxy : hilbertLindenbaumLe x y) (hxz : hilbertLindenbaumLe x z) :
    hilbertLindenbaumLe x (hilbertLindenbaumInf y z) := by
  obtain ⟨A, rfl⟩ := Quotient.exists_rep x
  obtain ⟨B, rfl⟩ := Quotient.exists_rep y
  obtain ⟨C, rfl⟩ := Quotient.exists_rep z
  exact hilbertAndIDeriv inst.h_andI hxy hxz

/-- The hardest lemma: Heyting deduction theorem.
`[A] ≤ [B → C]` iff `[A ∧ B] ≤ [C]`. -/
theorem hilbertLindenbaumLe_himp_iff
    {Axioms : Proposition Atom → Prop}
    [inst : ConjImpAxioms Axioms]
    (x y z : HilbertLindenbaumAlgebra Axioms) :
    hilbertLindenbaumLe x (hilbertLindenbaumHimp y z) ↔
    hilbertLindenbaumLe (hilbertLindenbaumInf x y) z := by
  obtain ⟨A, rfl⟩ := Quotient.exists_rep x
  obtain ⟨B, rfl⟩ := Quotient.exists_rep y
  obtain ⟨C, rfl⟩ := Quotient.exists_rep z
  constructor
  · -- Forward: [A] ⊢ B → C  →  [A ∧ B] ⊢ C
    intro hAimp
    have hAnd := assumption_deriv (Axioms := Axioms) (Γ := [A.and B]) List.mem_cons_self
    have hA := hilbertAndE1Deriv inst.h_andE1 hAnd
    have hB := hilbertAndE2Deriv inst.h_andE2 hAnd
    -- [A ∧ B] ⊢ B → C: cut [A ∧ B] ⊢ A with [A] ⊢ B → C
    have hImp := hilbertCutSingletonDeriv inst.h_K inst.h_S hA hAimp
    exact hilbertImpEDeriv hImp hB
  · -- Backward: [A ∧ B] ⊢ C  →  [A] ⊢ B → C
    intro hAndC
    -- Use impI: from [B, A] ⊢ C, derive [A] ⊢ B → C
    apply hilbertImpIDeriv inst.h_K inst.h_S
    -- context: B :: [A] = [B, A]
    have hA : Deriv Axioms [B, A] A := assumption_deriv (by simp)
    have hB : Deriv Axioms [B, A] B := assumption_deriv (by simp)
    have hAndAB := hilbertAndIDeriv inst.h_andI hA hB
    exact hilbertCutListDeriv inst.h_K inst.h_S hAndAB hAndC

/-- `[A] ≤ ⊤` where top is `[⊥ → ⊥]`. -/
theorem hilbertLindenbaumLe_top
    {Axioms : Proposition Atom → Prop}
    [inst : ConjImpAxioms Axioms]
    (x : HilbertLindenbaumAlgebra Axioms) :
    hilbertLindenbaumLe x (hilbertLindenbaumMk (bot.imp bot)) := by
  obtain ⟨A, rfl⟩ := Quotient.exists_rep x
  apply hilbertImpIDeriv inst.h_K inst.h_S
  exact assumption_deriv List.mem_cons_self

/-! ## BSL Instance -/

/-- The Hilbert Lindenbaum algebra is a `BrouwerianSemilattice` for any `[ConjImpAxioms]`.

This is the key instance enabling the fragment axiom families (`ConjImpAxiom`, `ConjImpBotAxiom`,
`ConjImpBotMinAxiom`) to use the Lindenbaum algebra machinery without requiring or-axioms. The
`BrouwerianSemilattice` structure uses only the meet-fragment lemmas generalized to
`[ConjImpAxioms]`. -/
instance hilbertLindenbaumBSL
    {Axioms : Proposition Atom → Prop}
    [inst : ConjImpAxioms Axioms] :
    BrouwerianSemilattice (HilbertLindenbaumAlgebra Axioms) where
  le := hilbertLindenbaumLe
  top := hilbertLindenbaumMk (Axioms := Axioms) (bot.imp bot)
  inf := hilbertLindenbaumInf
  himp := hilbertLindenbaumHimp
  le_refl := hilbertLindenbaumLe_refl
  le_trans := fun x y z => hilbertLindenbaumLe_trans x y z
  le_antisymm := fun x y => hilbertLindenbaumLe_antisymm x y
  inf_le_left := hilbertLindenbaumInf_le_left
  inf_le_right := hilbertLindenbaumInf_le_right
  le_inf := fun x y z => hilbertLindenbaumLe_inf x y z
  le_himp_iff := fun x y z => hilbertLindenbaumLe_himp_iff x y z
  le_top := hilbertLindenbaumLe_top

/-! ## GHA Instance -/

/-- The Hilbert Lindenbaum algebra is a `GeneralizedHeytingAlgebra`.

This is the central result of the module. All sub-instances (PartialOrder, Lattice,
DistribLattice) are derived automatically from `le_himp_iff`. -/
instance hilbertLindenbaumGHA
    {Axioms : Proposition Atom → Prop}
    [inst : MinimalAxioms Axioms] :
    GeneralizedHeytingAlgebra (HilbertLindenbaumAlgebra Axioms) where
  le := hilbertLindenbaumLe
  top := hilbertLindenbaumMk (Axioms := Axioms) (bot.imp bot)
  sup := hilbertLindenbaumSup
  inf := hilbertLindenbaumInf
  himp := hilbertLindenbaumHimp
  le_refl := hilbertLindenbaumLe_refl
  le_trans := fun x y z => hilbertLindenbaumLe_trans x y z
  le_antisymm := fun x y => hilbertLindenbaumLe_antisymm x y
  le_sup_left := hilbertLindenbaumLe_sup_left
  le_sup_right := hilbertLindenbaumLe_sup_right
  sup_le := fun x y z => hilbertLindenbaumSup_le x y z
  inf_le_left := hilbertLindenbaumInf_le_left
  inf_le_right := hilbertLindenbaumInf_le_right
  le_inf := fun x y z => hilbertLindenbaumLe_inf x y z
  le_himp_iff := fun x y z => hilbertLindenbaumLe_himp_iff x y z
  le_top := hilbertLindenbaumLe_top

/-! ## API Simp Lemmas -/

/-- `[A] ≤ [B] ↔ Deriv Axioms [A] B`. -/
@[simp]
theorem hilbertLindenbaumMk_le_mk
    {Axioms : Proposition Atom → Prop}
    [ConjImpAxioms Axioms]
    (A B : Proposition Atom) :
    hilbertLindenbaumMk (Axioms := Axioms) A ≤ hilbertLindenbaumMk B ↔
    Deriv Axioms [A] B :=
  hilbertLindenbaumLe_mk A B

/-- `[A ∨ B] = [A] ⊔ [B]`. -/
@[simp]
theorem hilbertLindenbaumMk_sup
    {Axioms : Proposition Atom → Prop}
    [MinimalAxioms Axioms]
    (A B : Proposition Atom) :
    hilbertLindenbaumMk (Axioms := Axioms) (A.or B) =
    hilbertLindenbaumMk A ⊔ hilbertLindenbaumMk B :=
  (hilbertLindenbaumSup_mk A B).symm

/-- `[A ∧ B] = [A] ⊓ [B]`. -/
@[simp]
theorem hilbertLindenbaumMk_inf
    {Axioms : Proposition Atom → Prop}
    [ConjImpAxioms Axioms]
    (A B : Proposition Atom) :
    hilbertLindenbaumMk (Axioms := Axioms) (A.and B) =
    hilbertLindenbaumMk A ⊓ hilbertLindenbaumMk B :=
  (hilbertLindenbaumInf_mk A B).symm

/-- `[A → B] = [A] ⇨ [B]`. -/
@[simp]
theorem hilbertLindenbaumMk_himp
    {Axioms : Proposition Atom → Prop}
    [ConjImpAxioms Axioms]
    (A B : Proposition Atom) :
    hilbertLindenbaumMk (Axioms := Axioms) (A.imp B) =
    hilbertLindenbaumMk A ⇨ hilbertLindenbaumMk B :=
  (hilbertLindenbaumHimp_mk A B).symm

/-- Top in the Hilbert Lindenbaum algebra is `[⊥ → ⊥]`. -/
theorem hilbertLindenbaumTop
    {Axioms : Proposition Atom → Prop}
    [ConjImpAxioms Axioms] :
    (⊤ : HilbertLindenbaumAlgebra Axioms) =
    hilbertLindenbaumMk (bot.imp bot) := rfl

/-! ## Top Characterization -/

/-- `[A] = ⊤` in the Hilbert Lindenbaum algebra iff `A` is Hilbert-derivable from the
empty context, i.e., `Derivable Axioms A`. -/
theorem hilbertLindenbaumMk_eq_top_iff
    {Axioms : Proposition Atom → Prop} [inst : ConjImpAxioms Axioms]
    {A : Proposition Atom} :
    hilbertLindenbaumMk (Axioms := Axioms) A = ⊤ ↔ Derivable Axioms A := by
  rw [hilbertLindenbaumTop]
  constructor
  · -- Forward: [A] = [⊥ → ⊥] → Derivable A
    -- Quotient equality gives HilbertEquiv A (bot.imp bot)
    intro h
    have heq : @hilbertPropositionSetoid _ Axioms _ |>.r A (bot.imp bot) :=
      Quotient.exact h
    -- heq : HilbertEquiv Axioms A (bot.imp bot), i.e., Deriv [A] (bot → bot) ∧ Deriv [bot → bot] A
    -- From heq.2 : Deriv [bot → bot] A, and Deriv [] (bot → bot), cut gives Deriv [] A
    have hBotBot : Derivable Axioms (bot.imp bot) := by
      -- Prove [] ⊢ ⊥ → ⊥ using impI: Deriv [bot] bot via assumption
      apply hilbertImpIDeriv inst.h_K inst.h_S
      exact assumption_deriv List.mem_cons_self
    -- Cut hBotBot (Deriv [] (bot → bot)) with heq.2 (Deriv [bot → bot] A)
    exact hilbertCutListDeriv inst.h_K inst.h_S hBotBot heq.2
  · -- Backward: Derivable A → [A] = [⊥ → ⊥]
    -- Use Quotient.sound with HilbertEquiv A (bot.imp bot)
    intro hA
    apply Quotient.sound
    constructor
    · -- Deriv [A] (bot → bot): use impI on Deriv [bot, A] bot (assumption)
      apply hilbertImpIDeriv inst.h_K inst.h_S
      exact assumption_deriv (by simp)
    · -- Deriv [bot → bot] A: weaken Deriv [] A to Deriv [bot.imp bot] A
      exact weakening_deriv hA (fun _ h => nomatch h)

/-! ## Canonical Valuation and Truth Lemma -/

/-- The canonical variable assignment into the Hilbert Lindenbaum algebra:
sends each atom `x` to its equivalence class `[x]`. -/
def canonicalV (Axioms : Proposition Atom → Prop) [ConjImpAxioms Axioms] :
    Atom → HilbertLindenbaumAlgebra Axioms :=
  fun x => hilbertLindenbaumMk (.atom x)

/-- The canonical bottom value in the Hilbert Lindenbaum algebra: the class `[⊥]`. -/
def canonicalBotVal (Axioms : Proposition Atom → Prop) [ConjImpAxioms Axioms] :
    HilbertLindenbaumAlgebra Axioms :=
  hilbertLindenbaumMk .bot

/-- **Truth Lemma**: evaluating any proposition under the canonical valuation and
bottom value gives exactly its equivalence class.

`AlgEvaluate (canonicalV Axioms) (canonicalBotVal Axioms) A = [A]`

This is proved by structural induction on `A`, using the simp lemmas
`hilbertLindenbaumMk_himp`, `hilbertLindenbaumMk_inf`, `hilbertLindenbaumMk_sup`. -/
theorem canonicalV_spec
    (Axioms : Proposition Atom → Prop) [MinimalAxioms Axioms]
    (A : Proposition Atom) :
    AlgEvaluate (canonicalV Axioms) (canonicalBotVal Axioms) A =
    hilbertLindenbaumMk (Axioms := Axioms) A := by
  induction A with
  | atom x => rfl
  | bot => rfl
  | imp a b iha ihb =>
    simp only [AlgEvaluate, iha, ihb, hilbertLindenbaumMk_himp]
  | and a b iha ihb =>
    simp only [AlgEvaluate, iha, ihb, hilbertLindenbaumMk_inf]
  | or a b iha ihb =>
    simp only [AlgEvaluate, iha, ihb, hilbertLindenbaumMk_sup]

/-- Any axiom `φ` evaluates to `⊤` under the canonical valuation.
This is used in the completeness proof to instantiate the Hilbert Lindenbaum algebra. -/
theorem canonicalV_axiom_top
    (Axioms : Proposition Atom → Prop) [inst : MinimalAxioms Axioms]
    (φ : Proposition Atom) (h : Axioms φ) :
    AlgEvaluate (canonicalV Axioms) (canonicalBotVal Axioms) φ = ⊤ := by
  rw [canonicalV_spec]
  rw [hilbertLindenbaumMk_eq_top_iff]
  exact ⟨.ax [] φ h⟩

/-- The canonical Lindenbaum valuation models the axiom theory `AxiomTheory Axioms`.
That is, every axiom evaluates to `⊤` under the canonical valuation and bottom value.
This is a one-liner reusing `canonicalV_axiom_top`, used in the theory-parametric
completeness theorem `hilbert_alg_complete_theory`. -/
lemma canonicalV_algTValid
    (Axioms : Proposition Atom → Prop) [MinimalAxioms Axioms] :
    canonicalV Axioms ⊨[canonicalBotVal Axioms] AxiomTheory Axioms := by
  intro B hB; exact canonicalV_axiom_top Axioms B (by simpa [AxiomTheory] using hB)

/-! ## Heyting Algebra (EFQ) -/

/-- `⊥ ≤ [A]` when `Axioms` includes EFQ. -/
theorem hilbertLindenbaumBot_le
    {Axioms : Proposition Atom → Prop}
    [MinimalAxioms Axioms]
    (h_EFQ : ∀ (φ : Proposition Atom), Axioms (bot.imp φ))
    (x : HilbertLindenbaumAlgebra Axioms) :
    hilbertLindenbaumLe (hilbertLindenbaumMk bot) x := by
  obtain ⟨A, rfl⟩ := Quotient.exists_rep x
  exact hilbertBotEDeriv h_EFQ (assumption_deriv List.mem_cons_self)

/-- The Hilbert Lindenbaum algebra is a `HeytingAlgebra` when EFQ is available. -/
@[reducible]
def hilbertLindenbaumHeytingAlgebra
    {Axioms : Proposition Atom → Prop}
    [MinimalAxioms Axioms]
    (h_EFQ : ∀ (φ : Proposition Atom), Axioms (bot.imp φ)) :
    HeytingAlgebra (HilbertLindenbaumAlgebra Axioms) :=
  { hilbertLindenbaumGHA with
    bot := hilbertLindenbaumMk bot
    bot_le := fun x => hilbertLindenbaumBot_le h_EFQ x
    compl := fun x => x ⇨ hilbertLindenbaumMk bot
    himp_bot := fun _ => rfl }

/-- `HeytingAlgebra` instance for `HilbertLindenbaumAlgebra IntPropAxiom`. -/
instance hilbertLindenbaumIntHA :
    HeytingAlgebra (HilbertLindenbaumAlgebra (@IntPropAxiom Atom)) :=
  hilbertLindenbaumHeytingAlgebra (fun φ => .efq φ)

/-- `HeytingAlgebra` instance for `HilbertLindenbaumAlgebra PropositionalAxiom`. -/
instance hilbertLindenbaumClHA :
    HeytingAlgebra (HilbertLindenbaumAlgebra (@PropositionalAxiom Atom)) :=
  hilbertLindenbaumHeytingAlgebra (fun φ => .efq φ)

/-! ## Boolean Algebra (EFQ + Peirce) -/

/-- In a classical Hilbert Lindenbaum algebra, excluded middle holds: `[A] ⊔ ([A] ⇨ ⊥) = ⊤`. -/
lemma hilbertLindenbaumEM
    {Axioms : Proposition Atom → Prop}
    [inst : MinimalAxioms Axioms]
    (h_EFQ : ∀ (φ : Proposition Atom), Axioms (bot.imp φ))
    (h_Peirce : ∀ (φ ψ : Proposition Atom), Axioms (((φ.imp ψ).imp φ).imp φ))
    (A : Proposition Atom) :
    hilbertLindenbaumMk (Axioms := Axioms) A ⊔
    (hilbertLindenbaumMk A ⇨ hilbertLindenbaumMk bot) = ⊤ := by
  apply le_antisymm le_top
  simp only [← hilbertLindenbaumMk_sup, ← hilbertLindenbaumMk_himp,
    hilbertLindenbaumTop, hilbertLindenbaumMk_le_mk]
  let G₀ : List (Proposition Atom) := [bot.imp bot]
  let negEM : Proposition Atom := (A.or (A.imp bot)).imp bot
  let G₁ : List (Proposition Atom) := negEM :: G₀
  have h_negA : Deriv Axioms G₁ (A.imp bot) := by
    apply hilbertImpIDeriv inst.h_K inst.h_S
    have hNegEM : Deriv Axioms (A :: G₁) negEM :=
      assumption_deriv (by simp [G₁])
    have hA : Deriv Axioms (A :: G₁) A :=
      assumption_deriv List.mem_cons_self
    exact hilbertImpEDeriv hNegEM (hilbertOrI1Deriv inst.h_orI1 hA)
  have h_bot : Deriv Axioms G₁ bot := by
    have hNegEM : Deriv Axioms G₁ negEM :=
      assumption_deriv List.mem_cons_self
    exact hilbertImpEDeriv hNegEM (hilbertOrI2Deriv inst.h_orI2 h_negA)
  have h_dblNeg : Deriv Axioms G₀ (negEM.imp bot) :=
    hilbertImpIDeriv inst.h_K inst.h_S h_bot
  exact hilbertDneDeriv inst.h_K inst.h_S h_EFQ h_Peirce h_dblNeg

/-- Construct a `BooleanAlgebra` from EFQ + Peirce using excluded middle. -/
@[reducible]
def hilbertLindenbaumBooleanAlgebra
    {Axioms : Proposition Atom → Prop}
    [inst : MinimalAxioms Axioms]
    (h_EFQ : ∀ (φ : Proposition Atom), Axioms (bot.imp φ))
    (h_Peirce : ∀ (φ ψ : Proposition Atom), Axioms (((φ.imp ψ).imp φ).imp φ)) :
    BooleanAlgebra (HilbertLindenbaumAlgebra Axioms) :=
  letI hHA := hilbertLindenbaumHeytingAlgebra h_EFQ
  BooleanAlgebra.ofRegular (fun x => by
    obtain ⟨A, rfl⟩ := @Quotient.exists_rep _ (@hilbertPropositionSetoid _ Axioms _) x
    change Heyting.IsRegular (hilbertLindenbaumMk (Axioms := Axioms) A ⊔
      (hilbertLindenbaumMk A)ᶜ)
    have hEM := hilbertLindenbaumEM h_EFQ h_Peirce A
    have hcompl : (hilbertLindenbaumMk (Axioms := Axioms) A)ᶜ =
        hilbertLindenbaumMk A ⇨ hilbertLindenbaumMk bot := rfl
    rw [hcompl, hEM]
    exact Heyting.isRegular_top)

/-- `BooleanAlgebra` instance for `HilbertLindenbaumAlgebra PropositionalAxiom`. -/
instance hilbertLindenbaumClBA :
    BooleanAlgebra (HilbertLindenbaumAlgebra (@PropositionalAxiom Atom)) :=
  hilbertLindenbaumBooleanAlgebra (fun φ => .efq φ) (fun φ ψ => .peirce φ ψ)

end Cslib.Logic.PL

end

end
