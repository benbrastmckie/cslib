/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

import Cslib.Init

public import Cslib.Logics.Propositional.Semantics.Algebra.HilbertLindenbaum
public import Cslib.Logics.Propositional.Semantics.SemanticConsequence

/-! # Γ-Relativized Hilbert Lindenbaum Quotient Algebra

This module constructs a **Γ-relativized Hilbert Lindenbaum quotient algebra**: the quotient
of `Proposition Atom` by the equivalence relation `A ≈ B := SetDerivable Axioms Γ (A.imp B) ∧
SetDerivable Axioms Γ (B.imp A)`. In this algebra, every formula `ψ ∈ Γ` evaluates to `⊤`, which
is the key property needed for the strong (context-parametric) completeness theorem.

This is **Route A2** from the strong completeness proof strategy: a fresh relativized copy of
the Lindenbaum construction, chosen to keep the original 341 proof files untouched.

## Main Definitions

- `RelEquiv Axioms Γ A B`: The relativized equivalence relation.
- `relSetoid Axioms Γ`: The induced `Setoid (Proposition Atom)`.
- `RelLindenbaumAlgebra Axioms Γ`: The quotient type.
- `relMk Axioms Γ A`: The quotient map.
- `GeneralizedHeytingAlgebra (RelLindenbaumAlgebra Axioms Γ)` instance for `[MinimalAxioms Axioms]`.

## Main Results

- `relMk_eq_top_iff`: `relMk Axioms Γ A = ⊤ ↔ SetDerivable Axioms Γ A`.
- `relCanonicalV_spec`: Truth lemma for the relativized canonical valuation.
- `relCanonicalV_algTValid`: The canonical valuation models the axiom theory.
- `relCanonicalV_satisfiesΓ`: The canonical valuation satisfies every formula in `Γ`.

## Universe Note

`{Atom : Type u}` and the algebra are pinned to the same universe level `u` to avoid
universe-metavariable mismatches, matching the pattern of `HilbertLindenbaum.lean`.

## References

* [A. Rasiowa, *An Algebraic Approach to Non-Classical Logics*][Rasiowa1974]
-/

@[expose] public section

noncomputable section

namespace Cslib.Logic.PL

open Proposition

universe u

variable {Atom : Type u}

attribute [local instance] Classical.propDecidable

/-! ## Relativized Equivalence Relation -/

/-- Two propositions `A` and `B` are Γ-relativized Hilbert-equivalent if each implication
is set-derivable from `Γ`. This is the quotient relation for the relativized Lindenbaum algebra.

Unlike the standard `HilbertEquiv` (which uses `Deriv Axioms [A] B`), this relation uses
`SetDerivable Axioms Γ` with an explicit context `Γ`, so every `ψ ∈ Γ` will evaluate to `⊤`
in the resulting quotient. -/
def RelEquiv (Axioms : Proposition Atom → Prop) (Γ : Set (Proposition Atom))
    (A B : Proposition Atom) : Prop :=
  SetDerivable Axioms Γ (A.imp B) ∧ SetDerivable Axioms Γ (B.imp A)

/-! ## Equivalence Relation Lemmas -/

/-- `RelEquiv` is reflexive: `A ≈ A` via `SetDerivable_of_Derivable` and the identity
implication `⊢ A → A`. -/
theorem relEquiv_refl
    {Axioms : Proposition Atom → Prop}
    [inst : MinimalAxioms Axioms]
    (Γ : Set (Proposition Atom)) (A : Proposition Atom) :
    RelEquiv Axioms Γ A A := by
  -- ⊢ A → A: provable by impI (K and S suffice)
  have hAA : Derivable Axioms (A.imp A) :=
    hilbertImpIDeriv inst.h_K inst.h_S (assumption_deriv List.mem_cons_self)
  exact ⟨SetDerivable_of_Derivable hAA Γ, SetDerivable_of_Derivable hAA Γ⟩

/-- `RelEquiv` is symmetric by swapping the two directions. -/
theorem relEquiv_symm
    {Axioms : Proposition Atom → Prop}
    {Γ : Set (Proposition Atom)} {A B : Proposition Atom}
    (h : RelEquiv Axioms Γ A B) :
    RelEquiv Axioms Γ B A :=
  ⟨h.2, h.1⟩

/-- `RelEquiv` is transitive via `setDeriv_cut` and `SetDerivable_mp`. -/
theorem relEquiv_trans
    {Axioms : Proposition Atom → Prop}
    [inst : MinimalAxioms Axioms]
    {Γ : Set (Proposition Atom)} {A B C : Proposition Atom}
    (hAB : RelEquiv Axioms Γ A B) (hBC : RelEquiv Axioms Γ B C) :
    RelEquiv Axioms Γ A C := by
  constructor
  · -- SetDerivable Axioms Γ (A → C): from (A → B) and (B → C)
    -- Chain: Γ ⊢ A → B and Γ ⊢ B → C. Need Γ ⊢ A → C.
    -- Use: insert A Γ ⊢ B (via setDeriv_deduction.mpr of A → B),
    -- then SetDerivable_mp with B → C.
    apply setDeriv_deduction
    -- Goal: SetDerivable Axioms (insert A Γ) C
    have hAB_w : SetDerivable Axioms (insert A Γ) (A.imp B) :=
      SetDerivable_weakening (Set.subset_insert _ _) hAB.1
    have hBC_w : SetDerivable Axioms (insert A Γ) (B.imp C) :=
      SetDerivable_weakening (Set.subset_insert _ _) hBC.1
    have hA : SetDerivable Axioms (insert A Γ) A :=
      SetDerivable_of_mem (Set.mem_insert A Γ)
    exact SetDerivable_mp hBC_w (SetDerivable_mp hAB_w hA)
  · -- SetDerivable Axioms Γ (C → A): symmetric, swap hAB and hBC
    apply setDeriv_deduction
    have hCB_w : SetDerivable Axioms (insert C Γ) (C.imp B) :=
      SetDerivable_weakening (Set.subset_insert _ _) hBC.2
    have hBA_w : SetDerivable Axioms (insert C Γ) (B.imp A) :=
      SetDerivable_weakening (Set.subset_insert _ _) hAB.2
    have hC : SetDerivable Axioms (insert C Γ) C :=
      SetDerivable_of_mem (Set.mem_insert C Γ)
    exact SetDerivable_mp hBA_w (SetDerivable_mp hCB_w hC)

/-! ## Setoid, Quotient Type, and Quotient Map -/

/-- The Γ-relativized Hilbert-equivalence setoid on `Proposition Atom`.
Requires `MinimalAxioms` for K and S (needed by transitivity and reflexivity). -/
def relSetoid
    {Axioms : Proposition Atom → Prop}
    [inst : MinimalAxioms Axioms]
    (Γ : Set (Proposition Atom)) :
    Setoid (Proposition Atom) where
  r := RelEquiv Axioms Γ
  iseqv := {
    refl := relEquiv_refl Γ
    symm := relEquiv_symm
    trans := fun hab hbc => relEquiv_trans hab hbc
  }

/-- The Γ-relativized Lindenbaum algebra: quotient of `Proposition Atom` by
Γ-relativized Hilbert equivalence. In this algebra, every `ψ ∈ Γ` evaluates to `⊤`. -/
def RelLindenbaumAlgebra
    (Axioms : Proposition Atom → Prop)
    [MinimalAxioms Axioms]
    (Γ : Set (Proposition Atom)) : Type u :=
  Quotient (@relSetoid _ Axioms _ Γ)

/-- The quotient map: sends `A` to its Γ-relativized equivalence class `[A]_Γ`. -/
def relMk
    {Axioms : Proposition Atom → Prop}
    [MinimalAxioms Axioms]
    (Γ : Set (Proposition Atom))
    (A : Proposition Atom) :
    RelLindenbaumAlgebra Axioms Γ :=
  Quotient.mk (relSetoid Γ) A

/-! ## Order on the Relativized Quotient -/

/-- `[A]_Γ ≤ [B]_Γ` iff `SetDerivable Axioms Γ (A.imp B)`.
Well-defined by `RelEquiv` congruence. -/
def relLindenbaumLe
    {Axioms : Proposition Atom → Prop}
    [inst : MinimalAxioms Axioms]
    {Γ : Set (Proposition Atom)}
    (x y : RelLindenbaumAlgebra Axioms Γ) : Prop :=
  Quotient.liftOn₂ x y
    (fun A B => SetDerivable Axioms Γ (A.imp B))
    (fun _ _ _ _ hA hB => propext ⟨
      fun h =>
        -- Given [A → B], [A ≈ A'], [B ≈ B'], derive [A' → B']
        -- Γ ⊢ A' → A (from hA.2), Γ ⊢ A → B (hypothesis), Γ ⊢ B → B' (from hB.1)
        -- Chain: Γ ⊢ A' → B' via setDeriv_deduction + SetDerivable_mp
        setDeriv_deduction (SetDerivable_mp
          (SetDerivable_weakening (Set.subset_insert _ _) hB.1)
          (SetDerivable_mp
            (SetDerivable_weakening (Set.subset_insert _ _) h)
            (SetDerivable_mp
              (SetDerivable_weakening (Set.subset_insert _ _) hA.2)
              (SetDerivable_of_mem (Set.mem_insert _ _))))),
      fun h =>
        setDeriv_deduction (SetDerivable_mp
          (SetDerivable_weakening (Set.subset_insert _ _) hB.2)
          (SetDerivable_mp
            (SetDerivable_weakening (Set.subset_insert _ _) h)
            (SetDerivable_mp
              (SetDerivable_weakening (Set.subset_insert _ _) hA.1)
              (SetDerivable_of_mem (Set.mem_insert _ _)))))⟩)

/-- The order on `RelLindenbaumAlgebra` reduces to set-derivability on representatives. -/
@[simp]
theorem relLindenbaumLe_mk
    {Axioms : Proposition Atom → Prop}
    [MinimalAxioms Axioms]
    {Γ : Set (Proposition Atom)}
    (A B : Proposition Atom) :
    relLindenbaumLe (relMk Γ (Axioms := Axioms) A) (relMk Γ B) ↔
    SetDerivable Axioms Γ (A.imp B) :=
  Iff.rfl

/-! ## Congruence Lemmas for Quotient Operations -/

/-- Or-congruence: if `A ≈ A'` and `B ≈ B'` under `Γ` then `A ∨ B ≈ A' ∨ B'` under `Γ`. -/
theorem relEquivOrCongr
    {Axioms : Proposition Atom → Prop}
    [inst : MinimalAxioms Axioms]
    {Γ : Set (Proposition Atom)}
    {A A' B B' : Proposition Atom}
    (hA : RelEquiv Axioms Γ A A')
    (hB : RelEquiv Axioms Γ B B') :
    RelEquiv Axioms Γ (A.or B) (A'.or B') := by
  constructor
  · -- SetDerivable Axioms Γ ((A ∨ B) → (A' ∨ B'))
    apply setDeriv_deduction
    -- insert (A ∨ B) Γ ⊢ A' ∨ B'
    -- Use orE: Γ, A ∨ B ⊢ A' ∨ B' from case A and case B
    have hAB_mem : SetDerivable Axioms (insert (A.or B) Γ) (A.or B) :=
      SetDerivable_of_mem (Set.mem_insert _ _)
    -- Case A: insert (A ∨ B) Γ ⊢ A → A' ∨ B'
    have h_caseA : SetDerivable Axioms (insert (A.or B) Γ) (A.imp (A'.or B')) := by
      apply setDeriv_deduction
      -- insert A (insert (A ∨ B) Γ) ⊢ A' ∨ B'
      have hAA' : SetDerivable Axioms (insert A (insert (A.or B) Γ)) (A.imp A') :=
        SetDerivable_weakening ((Set.subset_insert _ _).trans (Set.subset_insert _ _)) hA.1
      have hA_mem : SetDerivable Axioms (insert A (insert (A.or B) Γ)) A :=
        SetDerivable_of_mem (Set.mem_insert _ _)
      have hA' : SetDerivable Axioms (insert A (insert (A.or B) Γ)) A' :=
        SetDerivable_mp hAA' hA_mem
      -- orI1: A' → A' ∨ B'
      have hOrI1 : Derivable Axioms (A'.imp (A'.or B')) := ⟨.ax [] _ (inst.h_orI1 A' B')⟩
      exact SetDerivable_mp (SetDerivable_of_Derivable hOrI1 _) hA'
    -- Case B: insert (A ∨ B) Γ ⊢ B → A' ∨ B'
    have h_caseB : SetDerivable Axioms (insert (A.or B) Γ) (B.imp (A'.or B')) := by
      apply setDeriv_deduction
      have hBB' : SetDerivable Axioms (insert B (insert (A.or B) Γ)) (B.imp B') :=
        SetDerivable_weakening ((Set.subset_insert _ _).trans (Set.subset_insert _ _)) hB.1
      have hB_mem : SetDerivable Axioms (insert B (insert (A.or B) Γ)) B :=
        SetDerivable_of_mem (Set.mem_insert _ _)
      have hB' : SetDerivable Axioms (insert B (insert (A.or B) Γ)) B' :=
        SetDerivable_mp hBB' hB_mem
      have hOrI2 : Derivable Axioms (B'.imp (A'.or B')) := ⟨.ax [] _ (inst.h_orI2 A' B')⟩
      exact SetDerivable_mp (SetDerivable_of_Derivable hOrI2 _) hB'
    -- orE: (A → A'∨B') → (B → A'∨B') → (A∨B → A'∨B') is an axiom
    have hOrE : Derivable Axioms
        ((A.imp (A'.or B')).imp ((B.imp (A'.or B')).imp ((A.or B).imp (A'.or B')))) :=
      ⟨.ax [] _ (inst.h_orE A B (A'.or B'))⟩
    -- Build the implication (A ∨ B) → (A' ∨ B')
    have hImpl : SetDerivable Axioms (insert (A.or B) Γ) ((A.or B).imp (A'.or B')) :=
      SetDerivable_mp (SetDerivable_mp (SetDerivable_of_Derivable hOrE _) h_caseA) h_caseB
    -- Apply to hAB_mem
    exact SetDerivable_mp hImpl hAB_mem
  · -- SetDerivable Axioms Γ ((A' ∨ B') → (A ∨ B)) (symmetric)
    apply setDeriv_deduction
    have hAB_mem' : SetDerivable Axioms (insert (A'.or B') Γ) (A'.or B') :=
      SetDerivable_of_mem (Set.mem_insert _ _)
    have h_caseA' : SetDerivable Axioms (insert (A'.or B') Γ) (A'.imp (A.or B)) := by
      apply setDeriv_deduction
      have hA'A : SetDerivable Axioms (insert A' (insert (A'.or B') Γ)) (A'.imp A) :=
        SetDerivable_weakening ((Set.subset_insert _ _).trans (Set.subset_insert _ _)) hA.2
      have hA'_mem : SetDerivable Axioms (insert A' (insert (A'.or B') Γ)) A' :=
        SetDerivable_of_mem (Set.mem_insert _ _)
      have hA : SetDerivable Axioms (insert A' (insert (A'.or B') Γ)) A :=
        SetDerivable_mp hA'A hA'_mem
      have hOrI1 : Derivable Axioms (A.imp (A.or B)) := ⟨.ax [] _ (inst.h_orI1 A B)⟩
      exact SetDerivable_mp (SetDerivable_of_Derivable hOrI1 _) hA
    have h_caseB' : SetDerivable Axioms (insert (A'.or B') Γ) (B'.imp (A.or B)) := by
      apply setDeriv_deduction
      have hB'B : SetDerivable Axioms (insert B' (insert (A'.or B') Γ)) (B'.imp B) :=
        SetDerivable_weakening ((Set.subset_insert _ _).trans (Set.subset_insert _ _)) hB.2
      have hB'_mem : SetDerivable Axioms (insert B' (insert (A'.or B') Γ)) B' :=
        SetDerivable_of_mem (Set.mem_insert _ _)
      have hB : SetDerivable Axioms (insert B' (insert (A'.or B') Γ)) B :=
        SetDerivable_mp hB'B hB'_mem
      have hOrI2 : Derivable Axioms (B.imp (A.or B)) := ⟨.ax [] _ (inst.h_orI2 A B)⟩
      exact SetDerivable_mp (SetDerivable_of_Derivable hOrI2 _) hB
    have hOrE' : Derivable Axioms
        ((A'.imp (A.or B)).imp ((B'.imp (A.or B)).imp ((A'.or B').imp (A.or B)))) :=
      ⟨.ax [] _ (inst.h_orE A' B' (A.or B))⟩
    have hImpl' : SetDerivable Axioms (insert (A'.or B') Γ) ((A'.or B').imp (A.or B)) :=
      SetDerivable_mp (SetDerivable_mp (SetDerivable_of_Derivable hOrE' _) h_caseA') h_caseB'
    exact SetDerivable_mp hImpl' hAB_mem'

/-- And-congruence: if `A ≈ A'` and `B ≈ B'` under `Γ` then `A ∧ B ≈ A' ∧ B'` under `Γ`. -/
theorem relEquivAndCongr
    {Axioms : Proposition Atom → Prop}
    [inst : MinimalAxioms Axioms]
    {Γ : Set (Proposition Atom)}
    {A A' B B' : Proposition Atom}
    (hA : RelEquiv Axioms Γ A A')
    (hB : RelEquiv Axioms Γ B B') :
    RelEquiv Axioms Γ (A.and B) (A'.and B') := by
  constructor
  · -- SetDerivable Axioms Γ ((A ∧ B) → (A' ∧ B'))
    apply setDeriv_deduction
    have hAB_mem : SetDerivable Axioms (insert (A.and B) Γ) (A.and B) :=
      SetDerivable_of_mem (Set.mem_insert _ _)
    have hAndE1 : Derivable Axioms ((A.and B).imp A) := ⟨.ax [] _ (inst.h_andE1 A B)⟩
    have hAndE2 : Derivable Axioms ((A.and B).imp B) := ⟨.ax [] _ (inst.h_andE2 A B)⟩
    have hAndI : Derivable Axioms (A'.imp (B'.imp (A'.and B'))) := ⟨.ax [] _ (inst.h_andI A' B')⟩
    have hA_part : SetDerivable Axioms (insert (A.and B) Γ) A :=
      SetDerivable_mp (SetDerivable_of_Derivable hAndE1 _) hAB_mem
    have hB_part : SetDerivable Axioms (insert (A.and B) Γ) B :=
      SetDerivable_mp (SetDerivable_of_Derivable hAndE2 _) hAB_mem
    have hA' : SetDerivable Axioms (insert (A.and B) Γ) A' :=
      SetDerivable_mp (SetDerivable_weakening (Set.subset_insert _ _) hA.1) hA_part
    have hB' : SetDerivable Axioms (insert (A.and B) Γ) B' :=
      SetDerivable_mp (SetDerivable_weakening (Set.subset_insert _ _) hB.1) hB_part
    exact SetDerivable_mp (SetDerivable_mp (SetDerivable_of_Derivable hAndI _) hA') hB'
  · -- SetDerivable Axioms Γ ((A' ∧ B') → (A ∧ B)) (symmetric)
    apply setDeriv_deduction
    have hAB_mem : SetDerivable Axioms (insert (A'.and B') Γ) (A'.and B') :=
      SetDerivable_of_mem (Set.mem_insert _ _)
    have hAndE1 : Derivable Axioms ((A'.and B').imp A') := ⟨.ax [] _ (inst.h_andE1 A' B')⟩
    have hAndE2 : Derivable Axioms ((A'.and B').imp B') := ⟨.ax [] _ (inst.h_andE2 A' B')⟩
    have hAndI : Derivable Axioms (A.imp (B.imp (A.and B))) := ⟨.ax [] _ (inst.h_andI A B)⟩
    have hA'_part : SetDerivable Axioms (insert (A'.and B') Γ) A' :=
      SetDerivable_mp (SetDerivable_of_Derivable hAndE1 _) hAB_mem
    have hB'_part : SetDerivable Axioms (insert (A'.and B') Γ) B' :=
      SetDerivable_mp (SetDerivable_of_Derivable hAndE2 _) hAB_mem
    have hA : SetDerivable Axioms (insert (A'.and B') Γ) A :=
      SetDerivable_mp (SetDerivable_weakening (Set.subset_insert _ _) hA.2) hA'_part
    have hB : SetDerivable Axioms (insert (A'.and B') Γ) B :=
      SetDerivable_mp (SetDerivable_weakening (Set.subset_insert _ _) hB.2) hB'_part
    exact SetDerivable_mp (SetDerivable_mp (SetDerivable_of_Derivable hAndI _) hA) hB

/-- Imp-congruence: if `A ≈ A'` and `B ≈ B'` under `Γ` then `A → B ≈ A' → B'` under `Γ`. -/
theorem relEquivImpCongr
    {Axioms : Proposition Atom → Prop}
    [inst : MinimalAxioms Axioms]
    {Γ : Set (Proposition Atom)}
    {A A' B B' : Proposition Atom}
    (hA : RelEquiv Axioms Γ A A')
    (hB : RelEquiv Axioms Γ B B') :
    RelEquiv Axioms Γ (A.imp B) (A'.imp B') := by
  constructor
  · -- SetDerivable Axioms Γ ((A → B) → (A' → B'))
    apply setDeriv_deduction
    apply setDeriv_deduction
    -- insert A' (insert (A → B) Γ) ⊢ B'
    have hAimp : SetDerivable Axioms (insert A' (insert (A.imp B) Γ)) (A.imp B) :=
      SetDerivable_of_mem (Set.mem_insert_of_mem _ (Set.mem_insert _ _))
    have hA'A : SetDerivable Axioms (insert A' (insert (A.imp B) Γ)) (A'.imp A) :=
      SetDerivable_weakening ((Set.subset_insert _ _).trans (Set.subset_insert _ _)) hA.2
    have hA'_mem : SetDerivable Axioms (insert A' (insert (A.imp B) Γ)) A' :=
      SetDerivable_of_mem (Set.mem_insert _ _)
    have hA_val : SetDerivable Axioms (insert A' (insert (A.imp B) Γ)) A :=
      SetDerivable_mp hA'A hA'_mem
    have hB_val : SetDerivable Axioms (insert A' (insert (A.imp B) Γ)) B :=
      SetDerivable_mp hAimp hA_val
    exact SetDerivable_mp
      (SetDerivable_weakening ((Set.subset_insert _ _).trans (Set.subset_insert _ _)) hB.1)
      hB_val
  · -- SetDerivable Axioms Γ ((A' → B') → (A → B)) (symmetric)
    apply setDeriv_deduction
    apply setDeriv_deduction
    have hA'imp : SetDerivable Axioms (insert A (insert (A'.imp B') Γ)) (A'.imp B') :=
      SetDerivable_of_mem (Set.mem_insert_of_mem _ (Set.mem_insert _ _))
    have hAA' : SetDerivable Axioms (insert A (insert (A'.imp B') Γ)) (A.imp A') :=
      SetDerivable_weakening ((Set.subset_insert _ _).trans (Set.subset_insert _ _)) hA.1
    have hA_mem : SetDerivable Axioms (insert A (insert (A'.imp B') Γ)) A :=
      SetDerivable_of_mem (Set.mem_insert _ _)
    have hA'_val : SetDerivable Axioms (insert A (insert (A'.imp B') Γ)) A' :=
      SetDerivable_mp hAA' hA_mem
    have hB'_val : SetDerivable Axioms (insert A (insert (A'.imp B') Γ)) B' :=
      SetDerivable_mp hA'imp hA'_val
    exact SetDerivable_mp
      (SetDerivable_weakening ((Set.subset_insert _ _).trans (Set.subset_insert _ _)) hB.2)
      hB'_val

/-! ## Operations on the Relativized Quotient -/

/-- Relativized join: `[A]_Γ ⊔ [B]_Γ = [A ∨ B]_Γ`. -/
def relLindenbaumSup
    {Axioms : Proposition Atom → Prop}
    [inst : MinimalAxioms Axioms]
    {Γ : Set (Proposition Atom)}
    (x y : RelLindenbaumAlgebra Axioms Γ) :
    RelLindenbaumAlgebra Axioms Γ :=
  Quotient.lift₂
    (fun A B => relMk Γ (A.or B))
    (fun _ _ _ _ hA hB => Quotient.sound (relEquivOrCongr hA hB))
    x y

/-- Relativized meet: `[A]_Γ ⊓ [B]_Γ = [A ∧ B]_Γ`. -/
def relLindenbaumInf
    {Axioms : Proposition Atom → Prop}
    [inst : MinimalAxioms Axioms]
    {Γ : Set (Proposition Atom)}
    (x y : RelLindenbaumAlgebra Axioms Γ) :
    RelLindenbaumAlgebra Axioms Γ :=
  Quotient.lift₂
    (fun A B => relMk Γ (A.and B))
    (fun _ _ _ _ hA hB => Quotient.sound (relEquivAndCongr hA hB))
    x y

/-- Relativized Heyting implication: `[A]_Γ ⇨ [B]_Γ = [A → B]_Γ`. -/
def relLindenbaumHimp
    {Axioms : Proposition Atom → Prop}
    [inst : MinimalAxioms Axioms]
    {Γ : Set (Proposition Atom)}
    (x y : RelLindenbaumAlgebra Axioms Γ) :
    RelLindenbaumAlgebra Axioms Γ :=
  Quotient.lift₂
    (fun A B => relMk Γ (A.imp B))
    (fun _ _ _ _ hA hB => Quotient.sound (relEquivImpCongr hA hB))
    x y

/-- `[A ∨ B]_Γ = [A]_Γ ⊔ [B]_Γ`. -/
@[simp]
theorem relLindenbaumSup_mk
    {Axioms : Proposition Atom → Prop}
    [MinimalAxioms Axioms]
    {Γ : Set (Proposition Atom)}
    (A B : Proposition Atom) :
    relLindenbaumSup (relMk Γ (Axioms := Axioms) A) (relMk Γ B) =
    relMk Γ (A.or B) := rfl

/-- `[A ∧ B]_Γ = [A]_Γ ⊓ [B]_Γ`. -/
@[simp]
theorem relLindenbaumInf_mk
    {Axioms : Proposition Atom → Prop}
    [MinimalAxioms Axioms]
    {Γ : Set (Proposition Atom)}
    (A B : Proposition Atom) :
    relLindenbaumInf (relMk Γ (Axioms := Axioms) A) (relMk Γ B) =
    relMk Γ (A.and B) := rfl

/-- `[A → B]_Γ = [A]_Γ ⇨ [B]_Γ`. -/
@[simp]
theorem relLindenbaumHimp_mk
    {Axioms : Proposition Atom → Prop}
    [MinimalAxioms Axioms]
    {Γ : Set (Proposition Atom)}
    (A B : Proposition Atom) :
    relLindenbaumHimp (relMk Γ (Axioms := Axioms) A) (relMk Γ B) =
    relMk Γ (A.imp B) := rfl

/-! ## GHA Axiom Lemmas -/

/-- Reflexivity: `[A]_Γ ≤ [A]_Γ` via the identity implication `Γ ⊢ A → A`. -/
theorem relLindenbaumLe_refl
    {Axioms : Proposition Atom → Prop}
    [inst : MinimalAxioms Axioms]
    {Γ : Set (Proposition Atom)}
    (x : RelLindenbaumAlgebra Axioms Γ) :
    relLindenbaumLe x x := by
  obtain ⟨A, rfl⟩ := Quotient.exists_rep x
  exact SetDerivable_of_Derivable
    (hilbertImpIDeriv inst.h_K inst.h_S (assumption_deriv List.mem_cons_self)) Γ

/-- Transitivity via chain of implications. -/
theorem relLindenbaumLe_trans
    {Axioms : Proposition Atom → Prop}
    [inst : MinimalAxioms Axioms]
    {Γ : Set (Proposition Atom)}
    (x y z : RelLindenbaumAlgebra Axioms Γ)
    (hxy : relLindenbaumLe x y) (hyz : relLindenbaumLe y z) :
    relLindenbaumLe x z := by
  obtain ⟨A, rfl⟩ := Quotient.exists_rep x
  obtain ⟨B, rfl⟩ := Quotient.exists_rep y
  obtain ⟨C, rfl⟩ := Quotient.exists_rep z
  -- hxy : SetDerivable Axioms Γ (A → B), hyz : SetDerivable Axioms Γ (B → C)
  -- Need: SetDerivable Axioms Γ (A → C)
  apply setDeriv_deduction
  have hxy_w : SetDerivable Axioms (insert A Γ) (A.imp B) :=
    SetDerivable_weakening (Set.subset_insert _ _) hxy
  have hyz_w : SetDerivable Axioms (insert A Γ) (B.imp C) :=
    SetDerivable_weakening (Set.subset_insert _ _) hyz
  have hA : SetDerivable Axioms (insert A Γ) A :=
    SetDerivable_of_mem (Set.mem_insert A Γ)
  exact SetDerivable_mp hyz_w (SetDerivable_mp hxy_w hA)

/-- Antisymmetry via `Quotient.sound`. -/
theorem relLindenbaumLe_antisymm
    {Axioms : Proposition Atom → Prop}
    [MinimalAxioms Axioms]
    {Γ : Set (Proposition Atom)}
    (x y : RelLindenbaumAlgebra Axioms Γ)
    (hxy : relLindenbaumLe x y) (hyx : relLindenbaumLe y x) :
    x = y := by
  obtain ⟨A, rfl⟩ := Quotient.exists_rep x
  obtain ⟨B, rfl⟩ := Quotient.exists_rep y
  exact Quotient.sound ⟨hxy, hyx⟩

/-- `[A]_Γ ≤ [A ∨ B]_Γ` via `orI1`. -/
theorem relLindenbaumLe_sup_left
    {Axioms : Proposition Atom → Prop}
    [inst : MinimalAxioms Axioms]
    {Γ : Set (Proposition Atom)}
    (x y : RelLindenbaumAlgebra Axioms Γ) :
    relLindenbaumLe x (relLindenbaumSup x y) := by
  obtain ⟨A, rfl⟩ := Quotient.exists_rep x
  obtain ⟨B, rfl⟩ := Quotient.exists_rep y
  exact SetDerivable_of_Derivable ⟨.ax [] _ (inst.h_orI1 A B)⟩ Γ

/-- `[B]_Γ ≤ [A ∨ B]_Γ` via `orI2`. -/
theorem relLindenbaumLe_sup_right
    {Axioms : Proposition Atom → Prop}
    [inst : MinimalAxioms Axioms]
    {Γ : Set (Proposition Atom)}
    (x y : RelLindenbaumAlgebra Axioms Γ) :
    relLindenbaumLe y (relLindenbaumSup x y) := by
  obtain ⟨A, rfl⟩ := Quotient.exists_rep x
  obtain ⟨B, rfl⟩ := Quotient.exists_rep y
  exact SetDerivable_of_Derivable ⟨.ax [] _ (inst.h_orI2 A B)⟩ Γ

/-- `sup_le`: from `[A]_Γ ≤ [C]_Γ` and `[B]_Γ ≤ [C]_Γ` derive `[A ∨ B]_Γ ≤ [C]_Γ`. -/
theorem relLindenbaumSup_le
    {Axioms : Proposition Atom → Prop}
    [inst : MinimalAxioms Axioms]
    {Γ : Set (Proposition Atom)}
    (x y z : RelLindenbaumAlgebra Axioms Γ)
    (hxz : relLindenbaumLe x z) (hyz : relLindenbaumLe y z) :
    relLindenbaumLe (relLindenbaumSup x y) z := by
  obtain ⟨A, rfl⟩ := Quotient.exists_rep x
  obtain ⟨B, rfl⟩ := Quotient.exists_rep y
  obtain ⟨C, rfl⟩ := Quotient.exists_rep z
  -- hxz : SetDerivable Axioms Γ (A → C), hyz : SetDerivable Axioms Γ (B → C)
  -- Need: SetDerivable Axioms Γ ((A ∨ B) → C)
  exact SetDerivable_mp (SetDerivable_mp
    (SetDerivable_of_Derivable ⟨.ax [] _ (inst.h_orE A B C)⟩ Γ)
    hxz) hyz

/-- `[A ∧ B]_Γ ≤ [A]_Γ` via `andE1`. -/
theorem relLindenbaumInf_le_left
    {Axioms : Proposition Atom → Prop}
    [inst : MinimalAxioms Axioms]
    {Γ : Set (Proposition Atom)}
    (x y : RelLindenbaumAlgebra Axioms Γ) :
    relLindenbaumLe (relLindenbaumInf x y) x := by
  obtain ⟨A, rfl⟩ := Quotient.exists_rep x
  obtain ⟨B, rfl⟩ := Quotient.exists_rep y
  exact SetDerivable_of_Derivable ⟨.ax [] _ (inst.h_andE1 A B)⟩ Γ

/-- `[A ∧ B]_Γ ≤ [B]_Γ` via `andE2`. -/
theorem relLindenbaumInf_le_right
    {Axioms : Proposition Atom → Prop}
    [inst : MinimalAxioms Axioms]
    {Γ : Set (Proposition Atom)}
    (x y : RelLindenbaumAlgebra Axioms Γ) :
    relLindenbaumLe (relLindenbaumInf x y) y := by
  obtain ⟨A, rfl⟩ := Quotient.exists_rep x
  obtain ⟨B, rfl⟩ := Quotient.exists_rep y
  exact SetDerivable_of_Derivable ⟨.ax [] _ (inst.h_andE2 A B)⟩ Γ

/-- `le_inf`: from `[A]_Γ ≤ [B]_Γ` and `[A]_Γ ≤ [C]_Γ` derive `[A]_Γ ≤ [B ∧ C]_Γ`. -/
theorem relLindenbaumLe_inf
    {Axioms : Proposition Atom → Prop}
    [inst : MinimalAxioms Axioms]
    {Γ : Set (Proposition Atom)}
    (x y z : RelLindenbaumAlgebra Axioms Γ)
    (hxy : relLindenbaumLe x y) (hxz : relLindenbaumLe x z) :
    relLindenbaumLe x (relLindenbaumInf y z) := by
  obtain ⟨A, rfl⟩ := Quotient.exists_rep x
  obtain ⟨B, rfl⟩ := Quotient.exists_rep y
  obtain ⟨C, rfl⟩ := Quotient.exists_rep z
  -- hxy : SetDerivable Axioms Γ (A → B), hxz : SetDerivable Axioms Γ (A → C)
  -- Need: SetDerivable Axioms Γ (A → (B ∧ C))
  -- Use: (A → B) → ((A → C) → (A → B ∧ C)) derivable from andI K S
  apply setDeriv_deduction
  -- insert A Γ ⊢ B ∧ C
  have hA : SetDerivable Axioms (insert A Γ) A :=
    SetDerivable_of_mem (Set.mem_insert A Γ)
  have hB : SetDerivable Axioms (insert A Γ) B :=
    SetDerivable_mp (SetDerivable_weakening (Set.subset_insert _ _) hxy) hA
  have hC : SetDerivable Axioms (insert A Γ) C :=
    SetDerivable_mp (SetDerivable_weakening (Set.subset_insert _ _) hxz) hA
  exact SetDerivable_mp (SetDerivable_mp
    (SetDerivable_of_Derivable ⟨.ax [] _ (inst.h_andI B C)⟩ _) hB) hC

/-- The Heyting deduction theorem for the relativized order:
`[A]_Γ ≤ [B → C]_Γ ↔ [A ∧ B]_Γ ≤ [C]_Γ`. -/
theorem relLindenbaumLe_himp_iff
    {Axioms : Proposition Atom → Prop}
    [inst : MinimalAxioms Axioms]
    {Γ : Set (Proposition Atom)}
    (x y z : RelLindenbaumAlgebra Axioms Γ) :
    relLindenbaumLe x (relLindenbaumHimp y z) ↔
    relLindenbaumLe (relLindenbaumInf x y) z := by
  obtain ⟨A, rfl⟩ := Quotient.exists_rep x
  obtain ⟨B, rfl⟩ := Quotient.exists_rep y
  obtain ⟨C, rfl⟩ := Quotient.exists_rep z
  -- lhs: SetDerivable Axioms Γ (A → (B → C))
  -- rhs: SetDerivable Axioms Γ ((A ∧ B) → C)
  constructor
  · -- Forward: Γ ⊢ A → (B → C) implies Γ ⊢ (A ∧ B) → C
    intro h
    apply setDeriv_deduction
    -- insert (A ∧ B) Γ ⊢ C
    have hAB : SetDerivable Axioms (insert (A.and B) Γ) (A.and B) :=
      SetDerivable_of_mem (Set.mem_insert _ _)
    have hA : SetDerivable Axioms (insert (A.and B) Γ) A :=
      SetDerivable_mp (SetDerivable_of_Derivable ⟨.ax [] _ (inst.h_andE1 A B)⟩ _) hAB
    have hB : SetDerivable Axioms (insert (A.and B) Γ) B :=
      SetDerivable_mp (SetDerivable_of_Derivable ⟨.ax [] _ (inst.h_andE2 A B)⟩ _) hAB
    -- Γ ⊢ A → (B → C) weakened
    have h_w : SetDerivable Axioms (insert (A.and B) Γ) (A.imp (B.imp C)) :=
      SetDerivable_weakening (Set.subset_insert _ _) h
    -- MP: insert (A ∧ B) Γ ⊢ B → C
    have hBC : SetDerivable Axioms (insert (A.and B) Γ) (B.imp C) :=
      SetDerivable_mp h_w hA
    exact SetDerivable_mp hBC hB
  · -- Backward: Γ ⊢ (A ∧ B) → C implies Γ ⊢ A → (B → C)
    intro h
    apply setDeriv_deduction
    apply setDeriv_deduction
    -- insert B (insert A Γ) ⊢ C
    have hA : SetDerivable Axioms (insert B (insert A Γ)) A :=
      SetDerivable_of_mem (Set.mem_insert_of_mem _ (Set.mem_insert A Γ))
    have hB : SetDerivable Axioms (insert B (insert A Γ)) B :=
      SetDerivable_of_mem (Set.mem_insert B _)
    have hAB : SetDerivable Axioms (insert B (insert A Γ)) (A.and B) :=
      SetDerivable_mp (SetDerivable_mp
        (SetDerivable_of_Derivable ⟨.ax [] _ (inst.h_andI A B)⟩ _) hA) hB
    have h_w : SetDerivable Axioms (insert B (insert A Γ)) ((A.and B).imp C) :=
      SetDerivable_weakening ((Set.subset_insert _ _).trans (Set.subset_insert _ _)) h
    exact SetDerivable_mp h_w hAB

/-- `[A]_Γ ≤ ⊤` where top is `[⊥ → ⊥]_Γ`. -/
theorem relLindenbaumLe_top
    {Axioms : Proposition Atom → Prop}
    [inst : MinimalAxioms Axioms]
    {Γ : Set (Proposition Atom)}
    (x : RelLindenbaumAlgebra Axioms Γ) :
    relLindenbaumLe x (relMk Γ (Axioms := Axioms) (bot.imp bot)) := by
  obtain ⟨A, rfl⟩ := Quotient.exists_rep x
  -- Need: SetDerivable Axioms Γ (A → (⊥ → ⊥))
  -- ⊢ ⊥ → ⊥ is a theorem (impI), so K gives ⊢ X → (⊥ → ⊥) for any X
  have hBotBot : Derivable Axioms (bot.imp bot) :=
    hilbertImpIDeriv inst.h_K inst.h_S (assumption_deriv List.mem_cons_self)
  -- ⊢ A → (⊥ → ⊥) via K: hBotBot gives ⊢ ⊥→⊥, then K gives ⊢ A→(⊥→⊥)
  have h : Derivable Axioms (A.imp (bot.imp bot)) := by
    apply hilbertImpIDeriv inst.h_K inst.h_S
    exact weakening_deriv hBotBot (fun _ h => nomatch h)
  exact SetDerivable_of_Derivable h Γ

/-! ## GHA Instance -/

/-- The Γ-relativized Lindenbaum algebra is a `GeneralizedHeytingAlgebra`.

This is the central result of the module. All sub-instances (PartialOrder, Lattice,
DistribLattice) are derived automatically from `le_himp_iff`. -/
instance relLindenbaumGHA
    {Axioms : Proposition Atom → Prop}
    [inst : MinimalAxioms Axioms]
    {Γ : Set (Proposition Atom)} :
    GeneralizedHeytingAlgebra (RelLindenbaumAlgebra Axioms Γ) where
  le := relLindenbaumLe
  top := relMk Γ (Axioms := Axioms) (bot.imp bot)
  sup := relLindenbaumSup
  inf := relLindenbaumInf
  himp := relLindenbaumHimp
  le_refl := relLindenbaumLe_refl
  le_trans := fun x y z => relLindenbaumLe_trans x y z
  le_antisymm := fun x y => relLindenbaumLe_antisymm x y
  le_sup_left := relLindenbaumLe_sup_left
  le_sup_right := relLindenbaumLe_sup_right
  sup_le := fun x y z => relLindenbaumSup_le x y z
  inf_le_left := relLindenbaumInf_le_left
  inf_le_right := relLindenbaumInf_le_right
  le_inf := fun x y z => relLindenbaumLe_inf x y z
  le_himp_iff := fun x y z => relLindenbaumLe_himp_iff x y z
  le_top := relLindenbaumLe_top

/-! ## API Simp Lemmas -/

/-- `[A]_Γ ≤ [B]_Γ ↔ SetDerivable Axioms Γ (A → B)`. -/
@[simp]
theorem relMk_le_mk
    {Axioms : Proposition Atom → Prop}
    [MinimalAxioms Axioms]
    {Γ : Set (Proposition Atom)}
    (A B : Proposition Atom) :
    relMk Γ (Axioms := Axioms) A ≤ relMk Γ B ↔
    SetDerivable Axioms Γ (A.imp B) :=
  relLindenbaumLe_mk A B

/-- `[A ∨ B]_Γ = [A]_Γ ⊔ [B]_Γ`. -/
@[simp]
theorem relMk_sup
    {Axioms : Proposition Atom → Prop}
    [MinimalAxioms Axioms]
    {Γ : Set (Proposition Atom)}
    (A B : Proposition Atom) :
    relMk Γ (Axioms := Axioms) (A.or B) =
    relMk Γ A ⊔ relMk Γ B :=
  (relLindenbaumSup_mk A B).symm

/-- `[A ∧ B]_Γ = [A]_Γ ⊓ [B]_Γ`. -/
@[simp]
theorem relMk_inf
    {Axioms : Proposition Atom → Prop}
    [MinimalAxioms Axioms]
    {Γ : Set (Proposition Atom)}
    (A B : Proposition Atom) :
    relMk Γ (Axioms := Axioms) (A.and B) =
    relMk Γ A ⊓ relMk Γ B :=
  (relLindenbaumInf_mk A B).symm

/-- `[A → B]_Γ = [A]_Γ ⇨ [B]_Γ`. -/
@[simp]
theorem relMk_himp
    {Axioms : Proposition Atom → Prop}
    [MinimalAxioms Axioms]
    {Γ : Set (Proposition Atom)}
    (A B : Proposition Atom) :
    relMk Γ (Axioms := Axioms) (A.imp B) =
    relMk Γ A ⇨ relMk Γ B :=
  (relLindenbaumHimp_mk A B).symm

/-- Top in the relativized Lindenbaum algebra is `[⊥ → ⊥]_Γ`. -/
theorem relLindenbaumTop
    {Axioms : Proposition Atom → Prop}
    [MinimalAxioms Axioms]
    {Γ : Set (Proposition Atom)} :
    (⊤ : RelLindenbaumAlgebra Axioms Γ) =
    relMk Γ (bot.imp bot) := rfl

/-! ## Top Characterization -/

/-- `[A]_Γ = ⊤` in the relativized Lindenbaum algebra iff `A` is set-derivable from `Γ`.

This is the key top-characterization theorem: in the relativized algebra,
`⊤ = [⊥ → ⊥]_Γ`, and `[A]_Γ = [⊥ → ⊥]_Γ` iff `SetDerivable Axioms Γ A`. -/
theorem relMk_eq_top_iff
    {Axioms : Proposition Atom → Prop}
    [inst : MinimalAxioms Axioms]
    {Γ : Set (Proposition Atom)}
    {A : Proposition Atom} :
    relMk Γ (Axioms := Axioms) A = ⊤ ↔ SetDerivable Axioms Γ A := by
  -- ⊤ = relMk Γ (bot.imp bot) (by definition of the GHA instance)
  change relMk Γ A = relMk Γ (bot.imp bot) ↔ SetDerivable Axioms Γ A
  constructor
  · -- Forward: [A]_Γ = [⊥ → ⊥]_Γ → SetDerivable Axioms Γ A
    intro h
    have heq : RelEquiv Axioms Γ A (bot.imp bot) := Quotient.exact h
    -- heq.2 : SetDerivable Axioms Γ ((⊥ → ⊥) → A)
    -- hBotBot : SetDerivable Axioms Γ (⊥ → ⊥)
    have hBotBot : SetDerivable Axioms Γ (bot.imp bot) :=
      SetDerivable_of_Derivable
        (hilbertImpIDeriv inst.h_K inst.h_S (assumption_deriv List.mem_cons_self)) Γ
    exact SetDerivable_mp heq.2 hBotBot
  · -- Backward: SetDerivable Axioms Γ A → [A]_Γ = [⊥ → ⊥]_Γ
    intro hA
    apply Quotient.sound
    constructor
    · -- SetDerivable Axioms Γ (A → (⊥ → ⊥))
      have hBotBot : Derivable Axioms (bot.imp bot) :=
        hilbertImpIDeriv inst.h_K inst.h_S (assumption_deriv List.mem_cons_self)
      have h : Derivable Axioms (A.imp (bot.imp bot)) := by
        apply hilbertImpIDeriv inst.h_K inst.h_S
        exact weakening_deriv hBotBot (fun _ h => nomatch h)
      exact SetDerivable_of_Derivable h Γ
    · -- SetDerivable Axioms Γ ((⊥ → ⊥) → A)
      -- We have Γ ⊢ A; the tautology (⊥ → ⊥) → A follows from K: A → ((⊥ → ⊥) → A)
      apply setDeriv_deduction
      exact SetDerivable_weakening (Set.subset_insert _ _) hA

/-! ## Canonical Valuation and Truth Lemma -/

/-- The relativized canonical variable assignment: sends each atom `x` to its class `[x]_Γ`. -/
def relCanonicalV
    {Axioms : Proposition Atom → Prop}
    [MinimalAxioms Axioms]
    (Γ : Set (Proposition Atom)) :
    Atom → RelLindenbaumAlgebra Axioms Γ :=
  fun x => relMk Γ (.atom x)

/-- The relativized canonical bottom value: the class `[⊥]_Γ`. -/
def relCanonicalBotVal
    {Axioms : Proposition Atom → Prop}
    [MinimalAxioms Axioms]
    (Γ : Set (Proposition Atom)) :
    RelLindenbaumAlgebra Axioms Γ :=
  relMk Γ .bot

/-- **Relativized Truth Lemma**: evaluating any proposition under the relativized canonical
valuation and bottom value gives exactly its equivalence class.

`AlgEvaluate (relCanonicalV Γ) (relCanonicalBotVal Γ) A = [A]_Γ` -/
theorem relCanonicalV_spec
    {Axioms : Proposition Atom → Prop}
    [MinimalAxioms Axioms]
    (Γ : Set (Proposition Atom))
    (A : Proposition Atom) :
    AlgEvaluate (relCanonicalV Γ) (relCanonicalBotVal Γ) A =
    relMk Γ (Axioms := Axioms) A := by
  induction A with
  | atom x => rfl
  | bot => rfl
  | imp a b iha ihb =>
    simp only [AlgEvaluate, iha, ihb]
    exact (relMk_himp a b).symm
  | and a b iha ihb =>
    simp only [AlgEvaluate, iha, ihb]
    exact (relMk_inf a b).symm
  | or a b iha ihb =>
    simp only [AlgEvaluate, iha, ihb]
    exact (relMk_sup a b).symm

/-- The relativized canonical valuation models the axiom theory `AxiomTheory Axioms`.
Every axiom evaluates to `⊤` since axioms are derivable from `[]` and hence set-derivable
from any `Γ` via `SetDerivable_of_Derivable`. -/
lemma relCanonicalV_algTValid
    {Axioms : Proposition Atom → Prop}
    [MinimalAxioms Axioms]
    (Γ : Set (Proposition Atom)) :
    relCanonicalV Γ ⊨[relCanonicalBotVal Γ (Axioms := Axioms)] AxiomTheory Axioms := by
  intro B hB
  rw [relCanonicalV_spec]
  rw [relMk_eq_top_iff]
  exact SetDerivable_of_Derivable ⟨.ax [] B (by simpa [AxiomTheory] using hB)⟩ Γ

/-- The relativized canonical valuation satisfies all formulas in `Γ`.

For any `ψ ∈ Γ`, `AlgEvaluate (relCanonicalV Γ) (relCanonicalBotVal Γ) ψ = ⊤`.
This is the key property distinguishing the relativized algebra from the standard one:
`SetDerivable_of_mem` gives `SetDerivable Axioms Γ ψ` directly, and `relMk_eq_top_iff`
converts this to the `= ⊤` statement. -/
lemma relCanonicalV_satisfiesΓ
    {Axioms : Proposition Atom → Prop}
    [MinimalAxioms Axioms]
    {Γ : Set (Proposition Atom)} :
    SatisfiesTheory
      (AlgEvaluate (relCanonicalV Γ) (relCanonicalBotVal Γ (Axioms := Axioms))) Γ := by
  intro ψ hψ
  rw [relCanonicalV_spec]
  rw [relMk_eq_top_iff]
  exact SetDerivable_of_mem hψ

end Cslib.Logic.PL

end

end
