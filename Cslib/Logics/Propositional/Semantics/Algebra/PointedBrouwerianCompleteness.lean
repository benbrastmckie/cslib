/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

import Cslib.Init

public import Cslib.Logics.Propositional.Semantics.Algebra.PointedBrouwerian
public import Cslib.Logics.Propositional.ProofSystem.FragmentAxioms
public import Cslib.Logics.Propositional.Semantics.Algebra.HilbertLindenbaum

/-! # Pointed Brouwerian Algebraic Soundness and Completeness for IPL⟨∧,→,⊥,⊤⟩

This module proves soundness and completeness of the conjunctive-implicational-bot fragment
IPL⟨∧,→,⊥,⊤⟩ with respect to pointed Brouwerian semilattices (`BrouwerianSemilattice +
OrderBot`).

**Soundness** (`conjImpBot_pointedBrouwerian_soundness_derivable`): Every
`ConjImpBotAxiom`-derivable formula evaluates to `⊤` in every pointed Brouwerian semilattice
under every variable assignment.

**Completeness** (`conjImpBot_pointedBrouwerian_complete`): Restricted to `IsOrFree` formulas,
if a formula evaluates to `⊤` in every pointed Brouwerian semilattice then it is
`ConjImpBotAxiom`-derivable. The restriction to `IsOrFree` is necessary because
`PointedBrouwerianEvaluate` maps `or` to `⊤`, making disjunction vacuously valid, while
`ConjImpBotAxiom` has no disjunction axioms.

## Proof Strategy

**Soundness** follows by case analysis on `ConjImpBotAxiom` constructors. The efq case
(`⊥ → φ`) uses `bot_le` and `BrouwerianSemilattice.himp_eq_top_iff`.

**Completeness** uses the **Pointed Brouwerian Lindenbaum algebra**: the quotient of
`Proposition Atom` by `ConjImpBotAxiom`-derivational equivalence. The construction mirrors
`BrouwerianCompleteness.lean` but the Lindenbaum algebra additionally carries an `OrderBot`
instance, where `⊥ = [⊥]` and `bot_le` holds by the efq axiom.

The truth lemma extends from `IsOrBotFree` to `IsOrFree` because
`PointedBrouwerianEvaluate v bot = ⊥ = [⊥]` — bot is now correctly handled.

## Main Definitions

- `ConjImpBotEquiv`: derivational equivalence for `ConjImpBotAxiom`
- `PointedBrouwerianLindenbaumAlgebra`: quotient `Proposition Atom / ConjImpBotEquiv`
- `pointedBrouwerianLindenbaumMk`: the quotient map
- `pointedBrouwerianCanonicalV`: canonical variable assignment `x ↦ [atom x]`

## Main Results

- `conjImpBot_pointedBrouwerian_soundness_derivable`: soundness
- `pointedBrouwerianLindenbaumMk_eq_top_iff`: `[A] = ⊤ ↔ Derivable ConjImpBotAxiom A`
- `pointedBrouwerianCanonicalV_spec`: truth lemma for `IsOrFree` formulas
- `conjImpBot_pointedBrouwerian_complete`: completeness for `IsOrFree` formulas
- `conjImpBot_pointedBrouwerian_iff`: biconditional for `IsOrFree` formulas

## References

* [W. Nemitz, *Implicative semi-lattices*][Nemitz1965]
* [P. Köhler, *Brouwerian semilattices*][Kohler1981]
* [A. Rasiowa, *An Algebraic Approach to Non-Classical Logics*][Rasiowa1974]
-/

@[expose] public section

noncomputable section

namespace Cslib.Logic.PL

open Proposition

variable {Atom : Type*}

/-! ## Pointed Brouwerian Soundness -/

/-- Every axiom of the conjunctive-implicational-bot fragment is valid in every pointed
Brouwerian semilattice: each `ConjImpBotAxiom` constructor evaluates to `⊤`. -/
theorem conjImpBot_pointedBrouwerian_axiom_sound {Atom : Type*} {φ : PL.Proposition Atom}
    (h_ax : ConjImpBotAxiom φ) : PointedBrouwerianValid φ := by
  intro H _ _ v
  cases h_ax with
  | implyK φ ψ =>
    simp only [PointedBrouwerianEvaluate_imp]
    rw [BrouwerianSemilattice.himp_eq_top_iff, BrouwerianSemilattice.le_himp_iff]
    exact inf_le_left
  | implyS φ ψ χ =>
    simp only [PointedBrouwerianEvaluate_imp]
    rw [BrouwerianSemilattice.himp_eq_top_iff, BrouwerianSemilattice.le_himp_iff,
        BrouwerianSemilattice.le_himp_iff]
    have hb : (PointedBrouwerianEvaluate v φ ⇨ PointedBrouwerianEvaluate v ψ ⇨
                PointedBrouwerianEvaluate v χ) ⊓
              (PointedBrouwerianEvaluate v φ ⇨ PointedBrouwerianEvaluate v ψ) ⊓
              PointedBrouwerianEvaluate v φ ≤ PointedBrouwerianEvaluate v ψ :=
      (inf_le_inf_right _ inf_le_right).trans BrouwerianSemilattice.himp_inf_le
    have hbc : (PointedBrouwerianEvaluate v φ ⇨ PointedBrouwerianEvaluate v ψ ⇨
                 PointedBrouwerianEvaluate v χ) ⊓
               (PointedBrouwerianEvaluate v φ ⇨ PointedBrouwerianEvaluate v ψ) ⊓
               PointedBrouwerianEvaluate v φ ≤
               PointedBrouwerianEvaluate v ψ ⇨ PointedBrouwerianEvaluate v χ :=
      (inf_le_inf_right _ inf_le_left).trans BrouwerianSemilattice.himp_inf_le
    exact (le_inf hbc hb).trans BrouwerianSemilattice.himp_inf_le
  | andI φ ψ =>
    simp only [PointedBrouwerianEvaluate_imp, PointedBrouwerianEvaluate_and]
    rw [BrouwerianSemilattice.himp_eq_top_iff, BrouwerianSemilattice.le_himp_iff]
  | andE1 φ ψ =>
    simp only [PointedBrouwerianEvaluate_imp, PointedBrouwerianEvaluate_and]
    rw [BrouwerianSemilattice.himp_eq_top_iff]
    exact inf_le_left
  | andE2 φ ψ =>
    simp only [PointedBrouwerianEvaluate_imp, PointedBrouwerianEvaluate_and]
    rw [BrouwerianSemilattice.himp_eq_top_iff]
    exact inf_le_right
  | efq φ =>
    -- efq: ⊥ → φ; need ⊥ ⇨ φ_h = ⊤
    simp only [PointedBrouwerianEvaluate_imp, PointedBrouwerianEvaluate_bot]
    rw [BrouwerianSemilattice.himp_eq_top_iff]
    exact bot_le

/-- Soundness at the derivation tree level for `ConjImpBotAxiom`. -/
theorem conjImpBot_pointedBrouwerian_soundness
    {Atom : Type*}
    {Γ : List (PL.Proposition Atom)} {φ : PL.Proposition Atom}
    (d : DerivationTree ConjImpBotAxiom Γ φ)
    {H : Type*} [BrouwerianSemilattice H] [OrderBot H]
    (v : Atom → H)
    (h_ctx : ∀ ψ, ψ ∈ Γ → PointedBrouwerianEvaluate v ψ = ⊤) :
    PointedBrouwerianEvaluate v φ = ⊤ := by
  match d with
  | .ax _ ψ h_ax => exact conjImpBot_pointedBrouwerian_axiom_sound h_ax H v
  | .assumption _ ψ h_mem => exact h_ctx ψ h_mem
  | .modus_ponens _ ψ χ d₁ d₂ =>
    have h1 := conjImpBot_pointedBrouwerian_soundness d₁ v h_ctx
    have h2 := conjImpBot_pointedBrouwerian_soundness d₂ v h_ctx
    simp only [PointedBrouwerianEvaluate_imp] at h1
    rw [BrouwerianSemilattice.himp_eq_top_iff] at h1
    rw [h2, top_le_iff] at h1
    exact h1
  | .weakening _ _ ψ d' h_sub =>
    exact conjImpBot_pointedBrouwerian_soundness d' v
      (fun x hx => h_ctx x (h_sub x hx))

/-- **Pointed Brouwerian Soundness for IPL⟨∧,→,⊥,⊤⟩**: Every `ConjImpBotAxiom`-derivable
formula is pointed Brouwerian-valid. -/
theorem conjImpBot_pointedBrouwerian_soundness_derivable {Atom : Type*} {φ : PL.Proposition Atom}
    (h : Derivable ConjImpBotAxiom φ) : PointedBrouwerianValid φ := by
  intro H _ _ v
  obtain ⟨d⟩ := h
  exact conjImpBot_pointedBrouwerian_soundness d v (fun _ h => nomatch h)

/-! ## Pointed Brouwerian Lindenbaum Construction -/

/-- Two propositions are `ConjImpBotAxiom`-equivalent if each is derivable from the other
in a singleton context. This defines the quotient relation for the Pointed Brouwerian
Lindenbaum algebra. -/
def ConjImpBotEquiv (A B : PL.Proposition Atom) : Prop :=
  Deriv ConjImpBotAxiom [A] B ∧ Deriv ConjImpBotAxiom [B] A

/-! ## Equivalence Relation Lemmas -/

/-- `ConjImpBotEquiv` is reflexive via the assumption rule. -/
theorem conjImpBotEquiv_refl (A : PL.Proposition Atom) : ConjImpBotEquiv A A :=
  ⟨assumption_deriv List.mem_cons_self,
   assumption_deriv List.mem_cons_self⟩

/-- `ConjImpBotEquiv` is symmetric by swapping. -/
theorem conjImpBotEquiv_symm {A B : PL.Proposition Atom}
    (h : ConjImpBotEquiv A B) : ConjImpBotEquiv B A :=
  ⟨h.2, h.1⟩

/-- `ConjImpBotEquiv` is transitive via the cut rule. -/
theorem conjImpBotEquiv_trans {A B C : PL.Proposition Atom}
    (hAB : ConjImpBotEquiv A B) (hBC : ConjImpBotEquiv B C) : ConjImpBotEquiv A C :=
  ⟨hilbertCutSingletonDeriv ConjImpBotAxiom.mem_implyK ConjImpBotAxiom.mem_implyS hAB.1 hBC.1,
   hilbertCutSingletonDeriv ConjImpBotAxiom.mem_implyK ConjImpBotAxiom.mem_implyS hBC.2 hAB.2⟩

/-! ## Setoid, Quotient Type, and Quotient Map -/

/-- The `ConjImpBotAxiom`-equivalence setoid on `Proposition Atom`. -/
def conjImpBotPropositionSetoid : Setoid (PL.Proposition Atom) where
  r := ConjImpBotEquiv
  iseqv := {
    refl := conjImpBotEquiv_refl
    symm := conjImpBotEquiv_symm
    trans := conjImpBotEquiv_trans
  }

/-- The **Pointed Brouwerian Lindenbaum algebra**: the quotient of `Proposition Atom` by
`ConjImpBotAxiom`-derivational equivalence. This is the universal pointed Brouwerian
semilattice for the conjunctive-implicational-bot fragment. -/
def PointedBrouwerianLindenbaumAlgebra (Atom : Type*) : Type _ :=
  Quotient (@conjImpBotPropositionSetoid Atom)

/-- The quotient map: sends `A` to its equivalence class `[A]` in the Pointed Brouwerian
Lindenbaum algebra. -/
def pointedBrouwerianLindenbaumMk (A : PL.Proposition Atom) :
    PointedBrouwerianLindenbaumAlgebra Atom :=
  Quotient.mk conjImpBotPropositionSetoid A

/-! ## Order on the Quotient -/

/-- `[A] ≤ [B]` iff `Deriv ConjImpBotAxiom [A] B`. Well-defined by congruence. -/
def pointedBrouwerianLindenbaumLe
    (x y : PointedBrouwerianLindenbaumAlgebra Atom) : Prop :=
  Quotient.liftOn₂ x y
    (fun A B => Deriv ConjImpBotAxiom [A] B)
    (fun _ _ _ _ hA hB => propext ⟨
      fun h =>
        hilbertCutSingletonDeriv ConjImpBotAxiom.mem_implyK ConjImpBotAxiom.mem_implyS
          (hilbertCutSingletonDeriv ConjImpBotAxiom.mem_implyK ConjImpBotAxiom.mem_implyS hA.2 h)
          hB.1,
      fun h =>
        hilbertCutSingletonDeriv ConjImpBotAxiom.mem_implyK ConjImpBotAxiom.mem_implyS
          (hilbertCutSingletonDeriv ConjImpBotAxiom.mem_implyK ConjImpBotAxiom.mem_implyS hA.1 h)
          hB.2⟩)

/-- The order reduces to derivability on representatives. -/
@[simp]
theorem pointedBrouwerianLindenbaumLe_mk (A B : PL.Proposition Atom) :
    pointedBrouwerianLindenbaumLe (pointedBrouwerianLindenbaumMk A)
      (pointedBrouwerianLindenbaumMk B) ↔
    Deriv ConjImpBotAxiom [A] B :=
  Iff.rfl

/-! ## Congruence Lemmas for Quotient Operations -/

/-- And-congruence: if `A ≈ A'` and `B ≈ B'` then `A ∧ B ≈ A' ∧ B'`. -/
theorem conjImpBotEquivAndCongr {A A' B B' : PL.Proposition Atom}
    (hA : ConjImpBotEquiv A A') (hB : ConjImpBotEquiv B B') :
    ConjImpBotEquiv (A.and B) (A'.and B') := by
  constructor
  · have hAssume := assumption_deriv (Axioms := ConjImpBotAxiom) (Γ := [A.and B])
      List.mem_cons_self
    have hA_part := hilbertAndE1Deriv (fun φ ψ => .andE1 φ ψ) hAssume
    have hB_part := hilbertAndE2Deriv (fun φ ψ => .andE2 φ ψ) hAssume
    exact hilbertAndIDeriv (fun φ ψ => .andI φ ψ)
      (hilbertCutSingletonDeriv ConjImpBotAxiom.mem_implyK ConjImpBotAxiom.mem_implyS
        hA_part hA.1)
      (hilbertCutSingletonDeriv ConjImpBotAxiom.mem_implyK ConjImpBotAxiom.mem_implyS
        hB_part hB.1)
  · have hAssume := assumption_deriv (Axioms := ConjImpBotAxiom) (Γ := [A'.and B'])
      List.mem_cons_self
    have hA'_part := hilbertAndE1Deriv (fun φ ψ => .andE1 φ ψ) hAssume
    have hB'_part := hilbertAndE2Deriv (fun φ ψ => .andE2 φ ψ) hAssume
    exact hilbertAndIDeriv (fun φ ψ => .andI φ ψ)
      (hilbertCutSingletonDeriv ConjImpBotAxiom.mem_implyK ConjImpBotAxiom.mem_implyS
        hA'_part hA.2)
      (hilbertCutSingletonDeriv ConjImpBotAxiom.mem_implyK ConjImpBotAxiom.mem_implyS
        hB'_part hB.2)

/-- Imp-congruence: if `A ≈ A'` and `B ≈ B'` then `A → B ≈ A' → B'`. -/
theorem conjImpBotEquivImpCongr {A A' B B' : PL.Proposition Atom}
    (hA : ConjImpBotEquiv A A') (hB : ConjImpBotEquiv B B') :
    ConjImpBotEquiv (A.imp B) (A'.imp B') := by
  constructor
  · apply hilbertImpIDeriv ConjImpBotAxiom.mem_implyK ConjImpBotAxiom.mem_implyS
    have hAimp : Deriv ConjImpBotAxiom [A', A.imp B] (A.imp B) :=
      assumption_deriv (by simp)
    have hA_part : Deriv ConjImpBotAxiom [A', A.imp B] A :=
      hilbertWeakenSingleton hA.2
    have hB_part := hilbertImpEDeriv hAimp hA_part
    exact hilbertCutListDeriv ConjImpBotAxiom.mem_implyK ConjImpBotAxiom.mem_implyS
      hB_part hB.1
  · apply hilbertImpIDeriv ConjImpBotAxiom.mem_implyK ConjImpBotAxiom.mem_implyS
    have hA'imp : Deriv ConjImpBotAxiom [A, A'.imp B'] (A'.imp B') :=
      assumption_deriv (by simp)
    have hA'_part : Deriv ConjImpBotAxiom [A, A'.imp B'] A' :=
      hilbertWeakenSingleton hA.1
    have hB'_part := hilbertImpEDeriv hA'imp hA'_part
    exact hilbertCutListDeriv ConjImpBotAxiom.mem_implyK ConjImpBotAxiom.mem_implyS
      hB'_part hB.2

/-! ## Operations on the Quotient -/

/-- Meet: `[A] ⊓ [B] = [A ∧ B]`. -/
def pointedBrouwerianLindenbaumInf
    (x y : PointedBrouwerianLindenbaumAlgebra Atom) :
    PointedBrouwerianLindenbaumAlgebra Atom :=
  Quotient.lift₂
    (fun A B => pointedBrouwerianLindenbaumMk (A.and B))
    (fun _ _ _ _ hA hB => Quotient.sound (conjImpBotEquivAndCongr hA hB))
    x y

/-- Heyting implication: `[A] ⇨ [B] = [A → B]`. -/
def pointedBrouwerianLindenbaumHimp
    (x y : PointedBrouwerianLindenbaumAlgebra Atom) :
    PointedBrouwerianLindenbaumAlgebra Atom :=
  Quotient.lift₂
    (fun A B => pointedBrouwerianLindenbaumMk (A.imp B))
    (fun _ _ _ _ hA hB => Quotient.sound (conjImpBotEquivImpCongr hA hB))
    x y

/-- `[A ∧ B] = [A] ⊓ [B]`. -/
@[simp]
theorem pointedBrouwerianLindenbaumInf_mk (A B : PL.Proposition Atom) :
    pointedBrouwerianLindenbaumInf (pointedBrouwerianLindenbaumMk A)
      (pointedBrouwerianLindenbaumMk B) =
    pointedBrouwerianLindenbaumMk (A.and B) := rfl

/-- `[A → B] = [A] ⇨ [B]`. -/
@[simp]
theorem pointedBrouwerianLindenbaumHimp_mk (A B : PL.Proposition Atom) :
    pointedBrouwerianLindenbaumHimp (pointedBrouwerianLindenbaumMk A)
      (pointedBrouwerianLindenbaumMk B) =
    pointedBrouwerianLindenbaumMk (A.imp B) := rfl

/-! ## BrouwerianSemilattice Axiom Lemmas -/

/-- Reflexivity: `[A] ≤ [A]` via the assumption rule. -/
theorem pointedBrouwerianLindenbaumLe_refl
    (x : PointedBrouwerianLindenbaumAlgebra Atom) :
    pointedBrouwerianLindenbaumLe x x := by
  obtain ⟨A, rfl⟩ := Quotient.exists_rep x
  exact assumption_deriv List.mem_cons_self

/-- Transitivity via cut. -/
theorem pointedBrouwerianLindenbaumLe_trans
    (x y z : PointedBrouwerianLindenbaumAlgebra Atom)
    (hxy : pointedBrouwerianLindenbaumLe x y) (hyz : pointedBrouwerianLindenbaumLe y z) :
    pointedBrouwerianLindenbaumLe x z := by
  obtain ⟨A, rfl⟩ := Quotient.exists_rep x
  obtain ⟨B, rfl⟩ := Quotient.exists_rep y
  obtain ⟨C, rfl⟩ := Quotient.exists_rep z
  exact hilbertCutSingletonDeriv ConjImpBotAxiom.mem_implyK ConjImpBotAxiom.mem_implyS hxy hyz

/-- Antisymmetry via `Quotient.sound`. -/
theorem pointedBrouwerianLindenbaumLe_antisymm
    (x y : PointedBrouwerianLindenbaumAlgebra Atom)
    (hxy : pointedBrouwerianLindenbaumLe x y) (hyx : pointedBrouwerianLindenbaumLe y x) :
    x = y := by
  obtain ⟨A, rfl⟩ := Quotient.exists_rep x
  obtain ⟨B, rfl⟩ := Quotient.exists_rep y
  exact Quotient.sound ⟨hxy, hyx⟩

/-- `[A ∧ B] ≤ [A]` via andE1. -/
theorem pointedBrouwerianLindenbaumInf_le_left
    (x y : PointedBrouwerianLindenbaumAlgebra Atom) :
    pointedBrouwerianLindenbaumLe (pointedBrouwerianLindenbaumInf x y) x := by
  obtain ⟨A, rfl⟩ := Quotient.exists_rep x
  obtain ⟨B, rfl⟩ := Quotient.exists_rep y
  exact hilbertAndE1Deriv (fun φ ψ => .andE1 φ ψ) (assumption_deriv List.mem_cons_self)

/-- `[A ∧ B] ≤ [B]` via andE2. -/
theorem pointedBrouwerianLindenbaumInf_le_right
    (x y : PointedBrouwerianLindenbaumAlgebra Atom) :
    pointedBrouwerianLindenbaumLe (pointedBrouwerianLindenbaumInf x y) y := by
  obtain ⟨A, rfl⟩ := Quotient.exists_rep x
  obtain ⟨B, rfl⟩ := Quotient.exists_rep y
  exact hilbertAndE2Deriv (fun φ ψ => .andE2 φ ψ) (assumption_deriv List.mem_cons_self)

/-- `le_inf`: from `[A] ≤ [B]` and `[A] ≤ [C]` derive `[A] ≤ [B ∧ C]` via andI. -/
theorem pointedBrouwerianLindenbaumLe_inf
    (x y z : PointedBrouwerianLindenbaumAlgebra Atom)
    (hxy : pointedBrouwerianLindenbaumLe x y) (hxz : pointedBrouwerianLindenbaumLe x z) :
    pointedBrouwerianLindenbaumLe x (pointedBrouwerianLindenbaumInf y z) := by
  obtain ⟨A, rfl⟩ := Quotient.exists_rep x
  obtain ⟨B, rfl⟩ := Quotient.exists_rep y
  obtain ⟨C, rfl⟩ := Quotient.exists_rep z
  exact hilbertAndIDeriv (fun φ ψ => .andI φ ψ) hxy hxz

/-- `le_top`: `[A] ≤ ⊤` where top is `[⊥ → ⊥]`. -/
theorem pointedBrouwerianLindenbaumLe_top
    (x : PointedBrouwerianLindenbaumAlgebra Atom) :
    pointedBrouwerianLindenbaumLe x (pointedBrouwerianLindenbaumMk (bot.imp bot)) := by
  obtain ⟨A, rfl⟩ := Quotient.exists_rep x
  apply hilbertImpIDeriv ConjImpBotAxiom.mem_implyK ConjImpBotAxiom.mem_implyS
  exact assumption_deriv List.mem_cons_self

/-- The hardest lemma: Brouwerian deduction theorem.
`[A] ≤ [B → C]` iff `[A ∧ B] ≤ [C]`. -/
theorem pointedBrouwerianLindenbaumLe_himp_iff
    (x y z : PointedBrouwerianLindenbaumAlgebra Atom) :
    pointedBrouwerianLindenbaumLe x (pointedBrouwerianLindenbaumHimp y z) ↔
    pointedBrouwerianLindenbaumLe (pointedBrouwerianLindenbaumInf x y) z := by
  obtain ⟨A, rfl⟩ := Quotient.exists_rep x
  obtain ⟨B, rfl⟩ := Quotient.exists_rep y
  obtain ⟨C, rfl⟩ := Quotient.exists_rep z
  constructor
  · intro hAimp
    have hAnd := assumption_deriv (Axioms := ConjImpBotAxiom) (Γ := [A.and B]) List.mem_cons_self
    have hA := hilbertAndE1Deriv (fun φ ψ => .andE1 φ ψ) hAnd
    have hB := hilbertAndE2Deriv (fun φ ψ => .andE2 φ ψ) hAnd
    have hImp := hilbertCutSingletonDeriv ConjImpBotAxiom.mem_implyK ConjImpBotAxiom.mem_implyS
      hA hAimp
    exact hilbertImpEDeriv hImp hB
  · intro hAndC
    apply hilbertImpIDeriv ConjImpBotAxiom.mem_implyK ConjImpBotAxiom.mem_implyS
    have hA : Deriv ConjImpBotAxiom [B, A] A := assumption_deriv (by simp)
    have hB : Deriv ConjImpBotAxiom [B, A] B := assumption_deriv (by simp)
    have hAndAB := hilbertAndIDeriv (fun φ ψ => .andI φ ψ) hA hB
    exact hilbertCutListDeriv ConjImpBotAxiom.mem_implyK ConjImpBotAxiom.mem_implyS hAndAB hAndC

/-! ## BrouwerianSemilattice Instance -/

/-- The Pointed Brouwerian Lindenbaum algebra is a `BrouwerianSemilattice`.

All sub-instances (PartialOrder, SemilatticeInf, OrderTop) are derived from `le_himp_iff`. -/
instance pointedBrouwerianLindenbaumBSL :
    BrouwerianSemilattice (PointedBrouwerianLindenbaumAlgebra Atom) where
  le := pointedBrouwerianLindenbaumLe
  top := pointedBrouwerianLindenbaumMk (bot.imp bot)
  inf := pointedBrouwerianLindenbaumInf
  himp := pointedBrouwerianLindenbaumHimp
  le_refl := pointedBrouwerianLindenbaumLe_refl
  le_trans := fun x y z => pointedBrouwerianLindenbaumLe_trans x y z
  le_antisymm := fun x y => pointedBrouwerianLindenbaumLe_antisymm x y
  inf_le_left := pointedBrouwerianLindenbaumInf_le_left
  inf_le_right := pointedBrouwerianLindenbaumInf_le_right
  le_inf := fun x y z => pointedBrouwerianLindenbaumLe_inf x y z
  le_top := pointedBrouwerianLindenbaumLe_top
  le_himp_iff := fun x y z => pointedBrouwerianLindenbaumLe_himp_iff x y z

/-! ## OrderBot Instance via EFQ -/

/-- `[⊥] ≤ [A]` for any `A`, via the efq axiom: `⊥ → A` is derivable, so from `[⊥]` we
derive `A` by modus ponens. -/
theorem pointedBrouwerianLindenbaumBot_le
    (x : PointedBrouwerianLindenbaumAlgebra Atom) :
    pointedBrouwerianLindenbaumLe (pointedBrouwerianLindenbaumMk Proposition.bot) x := by
  obtain ⟨A, rfl⟩ := Quotient.exists_rep x
  -- Need: Deriv ConjImpBotAxiom [⊥] A
  -- Use efq axiom: ⊥ → A, then modus ponens with assumption ⊥
  exact hilbertImpEDeriv
    ⟨.ax [Proposition.bot] _ (ConjImpBotAxiom.efq A)⟩
    (assumption_deriv List.mem_cons_self)

/-- The Pointed Brouwerian Lindenbaum algebra has `OrderBot` with `⊥ = [⊥]`.
The `bot_le` proof follows from the efq axiom. -/
instance pointedBrouwerianLindenbaumOrderBot :
    OrderBot (PointedBrouwerianLindenbaumAlgebra Atom) where
  bot := pointedBrouwerianLindenbaumMk Proposition.bot
  bot_le := pointedBrouwerianLindenbaumBot_le

/-! ## API Simp Lemmas -/

/-- `[A] ≤ [B] ↔ Deriv ConjImpBotAxiom [A] B`. -/
@[simp]
theorem pointedBrouwerianLindenbaumMk_le_mk (A B : PL.Proposition Atom) :
    pointedBrouwerianLindenbaumMk A ≤ pointedBrouwerianLindenbaumMk B ↔
    Deriv ConjImpBotAxiom [A] B :=
  pointedBrouwerianLindenbaumLe_mk A B

/-- `[A ∧ B] = [A] ⊓ [B]`. -/
@[simp]
theorem pointedBrouwerianLindenbaumMk_inf (A B : PL.Proposition Atom) :
    pointedBrouwerianLindenbaumMk (A.and B) =
    pointedBrouwerianLindenbaumMk A ⊓ pointedBrouwerianLindenbaumMk B :=
  (pointedBrouwerianLindenbaumInf_mk A B).symm

/-- `[A → B] = [A] ⇨ [B]`. -/
@[simp]
theorem pointedBrouwerianLindenbaumMk_himp (A B : PL.Proposition Atom) :
    pointedBrouwerianLindenbaumMk (A.imp B) =
    pointedBrouwerianLindenbaumMk A ⇨ pointedBrouwerianLindenbaumMk B :=
  (pointedBrouwerianLindenbaumHimp_mk A B).symm

/-- `[⊥] = ⊥` in the Pointed Brouwerian Lindenbaum algebra. -/
@[simp]
theorem pointedBrouwerianLindenbaumMk_bot :
    pointedBrouwerianLindenbaumMk (Proposition.bot (Atom := Atom)) = ⊥ := rfl

/-- Top in the Pointed Brouwerian Lindenbaum algebra is `[⊥ → ⊥]`. -/
theorem pointedBrouwerianLindenbaumTop :
    (⊤ : PointedBrouwerianLindenbaumAlgebra Atom) =
    pointedBrouwerianLindenbaumMk (bot.imp bot) := rfl

/-! ## Top Characterization -/

/-- `[A] = ⊤` in the Pointed Brouwerian Lindenbaum algebra iff `A` is `ConjImpBotAxiom`-derivable
from the empty context. -/
theorem pointedBrouwerianLindenbaumMk_eq_top_iff {A : PL.Proposition Atom} :
    pointedBrouwerianLindenbaumMk A = ⊤ ↔ Derivable ConjImpBotAxiom A := by
  rw [pointedBrouwerianLindenbaumTop]
  constructor
  · intro h
    have heq : ConjImpBotEquiv A (bot.imp bot) :=
      Quotient.exact h
    have hBotBot : Derivable (@ConjImpBotAxiom Atom) ((bot : PL.Proposition Atom).imp bot) := by
      apply hilbertImpIDeriv ConjImpBotAxiom.mem_implyK ConjImpBotAxiom.mem_implyS
      exact assumption_deriv List.mem_cons_self
    exact hilbertCutListDeriv ConjImpBotAxiom.mem_implyK ConjImpBotAxiom.mem_implyS
      hBotBot heq.2
  · intro hA
    apply Quotient.sound
    constructor
    · apply hilbertImpIDeriv ConjImpBotAxiom.mem_implyK ConjImpBotAxiom.mem_implyS
      exact assumption_deriv (by simp)
    · exact weakening_deriv hA (fun _ h => nomatch h)

/-! ## Canonical Valuation and Truth Lemma -/

/-- The canonical variable assignment into the Pointed Brouwerian Lindenbaum algebra:
sends each atom `x` to its equivalence class `[x]`. -/
def pointedBrouwerianCanonicalV :
    Atom → PointedBrouwerianLindenbaumAlgebra Atom :=
  fun x => pointedBrouwerianLindenbaumMk (.atom x)

/-- **Truth Lemma** (restricted to `IsOrFree`): evaluating an or-free proposition under
the canonical valuation gives exactly its equivalence class.

`PointedBrouwerianEvaluate pointedBrouwerianCanonicalV A = [A]` for `IsOrFree` formulas.

The restriction to `IsOrFree` is necessary because `PointedBrouwerianEvaluate` maps `or`
to `⊤`, but `[or a b]` is not generally the top element.

The key improvement over the Brouwerian truth lemma is that the `bot` case now works:
`PointedBrouwerianEvaluate canonicalV bot = ⊥ = [⊥]`. -/
theorem pointedBrouwerianCanonicalV_spec (A : PL.Proposition Atom)
    (hA : A.IsOrFree = true) :
    PointedBrouwerianEvaluate pointedBrouwerianCanonicalV A =
    pointedBrouwerianLindenbaumMk A := by
  induction A with
  | atom x => rfl
  | bot =>
    -- PointedBrouwerianEvaluate v bot = ⊥ = [⊥]
    simp [PointedBrouwerianEvaluate_bot, pointedBrouwerianLindenbaumMk_bot]
  | imp a b iha ihb =>
    simp only [Proposition.IsOrFree, Bool.and_eq_true] at hA
    simp only [PointedBrouwerianEvaluate_imp, iha hA.1, ihb hA.2,
               pointedBrouwerianLindenbaumMk_himp]
  | and a b iha ihb =>
    simp only [Proposition.IsOrFree, Bool.and_eq_true] at hA
    simp only [PointedBrouwerianEvaluate_and, iha hA.1, ihb hA.2,
               pointedBrouwerianLindenbaumMk_inf]
  | or _ _ _ _ => simp [Proposition.IsOrFree] at hA

/-! ## Completeness Theorem -/

/-- **Pointed Brouwerian Completeness for IPL⟨∧,→,⊥,⊤⟩** (restricted to `IsOrFree` formulas):
if an or-free formula is valid in every pointed Brouwerian semilattice, then it is
`ConjImpBotAxiom`-derivable.

The restriction to `IsOrFree` is necessary: `a ∨ b` is vacuously pointed Brouwerian-valid
(since `PointedBrouwerianEvaluate v (or a b) = ⊤` by definition) but `ConjImpBotAxiom`
has no disjunction axioms. -/
theorem conjImpBot_pointedBrouwerian_complete {Atom : Type u} {φ : PL.Proposition Atom}
    (hfrag : φ.IsOrFree = true)
    (h : PointedBrouwerianValid.{u, u} φ) :
    Derivable ConjImpBotAxiom φ := by
  -- Instantiate PointedBrouwerianValid at the Pointed Brouwerian Lindenbaum algebra
  have hLind : PointedBrouwerianEvaluate pointedBrouwerianCanonicalV φ = ⊤ :=
    h (PointedBrouwerianLindenbaumAlgebra Atom) pointedBrouwerianCanonicalV
  -- Apply the truth lemma (valid since φ is IsOrFree)
  rw [pointedBrouwerianCanonicalV_spec φ hfrag] at hLind
  -- Extract derivability via mk_eq_top_iff
  exact pointedBrouwerianLindenbaumMk_eq_top_iff.mp hLind

/-- **Pointed Brouwerian Biconditional for IPL⟨∧,→,⊥,⊤⟩**: For or-free formulas,
derivability and pointed Brouwerian validity coincide. -/
theorem conjImpBot_pointedBrouwerian_iff {Atom : Type u} {φ : PL.Proposition Atom}
    (hfrag : φ.IsOrFree = true) :
    Derivable ConjImpBotAxiom φ ↔ PointedBrouwerianValid.{u, u} φ :=
  ⟨conjImpBot_pointedBrouwerian_soundness_derivable,
   conjImpBot_pointedBrouwerian_complete hfrag⟩

end Cslib.Logic.PL

end

end
