/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

import Cslib.Init

public import Cslib.Logics.Propositional.Semantics.Algebra.BrouwerianBot
public import Cslib.Logics.Propositional.Semantics.Algebra.HilbertCompleteness
public import Cslib.Logics.Propositional.Semantics.Algebra.PointedBrouwerianCompleteness
public import Cslib.Logics.Propositional.ProofSystem.FragmentAxioms

/-! # Arbitrary-Point Brouwerian Algebraic Soundness and Completeness for MPL⟨∧,→,⊥,⊤⟩

This module proves soundness and completeness of the conjunctive-implicational-bot fragment
MPL⟨∧,→,⊥,⊤⟩ with respect to Brouwerian semilattices with an **arbitrary distinguished
element** (`BrouwerianSemilattice` + free `bot_val : H`, no `OrderBot`).

The key distinction from `PointedBrouwerianCompleteness.lean` is that `ConjImpBotMinAxiom`
has **no ex falso** (`efq`) axiom. Therefore `⊥` is a free constant — no axiom governs it
— and its semantic image is a universally-quantified free element `bot_val : H` rather than
the algebraic `OrderBot` least element.

**Soundness** (`conjImpBotMin_brouwerianBot_soundness_derivable`): Every
`ConjImpBotMinAxiom`-derivable formula evaluates to `⊤` in every Brouwerian semilattice
under every variable assignment and every choice of `bot_val`.

**Completeness** (`conjImpBotMin_brouwerianBot_complete`): Restricted to `IsOrFree` formulas,
if a formula evaluates to `⊤` in every Brouwerian semilattice with every `bot_val`, then it
is `ConjImpBotMinAxiom`-derivable.

## Proof Strategy

**Soundness** follows by case analysis on `ConjImpBotMinAxiom` constructors. There are five
cases (no efq case since `⊥` is free): `implyK`, `implyS`, `andI`, `andE1`, `andE2`.

**Completeness** uses the **ConjImpBotMin Brouwerian Lindenbaum algebra**: the quotient of
`Proposition Atom` by `ConjImpBotMinAxiom`-derivational equivalence. This construction
mirrors `PointedBrouwerianCompleteness.lean` but **omits** the `OrderBot` instance (since
there is no efq axiom to prove `bot_le`). The element `[⊥]` serves as the canonical `bot_val`.

The truth lemma uses `BrouwerianBotEvaluate` with `bot_val = [⊥]`; the `bot` case works
because `BrouwerianBotEvaluate canonicalV [⊥] .bot = [⊥] = mk Proposition.bot`.

## Main Definitions

- `BrouwerianBotEvaluate`: free-bot Brouwerian evaluator (`bot ↦ bot_val`, `or ↦ ⊤`).
- `BrouwerianBotValid`: validity in all Brouwerian semilattices under all `bot_val`.
- `ConjImpBotMinEquiv`: derivational equivalence for `ConjImpBotMinAxiom`.
- `ConjImpBotMinLindenbaumAlgebra`: quotient `Proposition Atom / ConjImpBotMinEquiv`.
- `conjImpBotMinLindenbaumMk`: the quotient map.
- `conjImpBotMinCanonicalV`: canonical variable assignment `x ↦ [atom x]`.

## Main Results

- `conjImpBotMin_brouwerianBot_soundness_derivable`: soundness.
- `conjImpBotMinLindenbaumMk_eq_top_iff`: `[A] = ⊤ ↔ Derivable ConjImpBotMinAxiom A`.
- `conjImpBotMinCanonicalV_spec`: truth lemma for `IsOrFree` formulas.
- `conjImpBotMin_brouwerianBot_complete`: completeness for `IsOrFree` formulas.
- `conjImpBotMin_brouwerianBot_iff`: biconditional for `IsOrFree` formulas.

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

/-! ## ConjImpBotMin Brouwerian Soundness -/

/-- Every axiom of the conjunctive-implicational-bot-min fragment is valid in every Brouwerian
semilattice with any choice of `bot_val`: each `ConjImpBotMinAxiom` constructor evaluates to
`⊤`. There is no efq case since `ConjImpBotMinAxiom` has no ex falso. -/
theorem conjImpBotMin_brouwerianBot_axiom_sound {Atom : Type*} {φ : PL.Proposition Atom}
    (h_ax : ConjImpBotMinAxiom φ) : BrouwerianBotValid φ := by
  intro H _ v bot_val
  cases h_ax with
  | implyK φ ψ =>
    simp only [BrouwerianBotEvaluate_imp]
    rw [BrouwerianSemilattice.himp_eq_top_iff, BrouwerianSemilattice.le_himp_iff]
    exact inf_le_left
  | implyS φ ψ χ =>
    simp only [BrouwerianBotEvaluate_imp]
    rw [BrouwerianSemilattice.himp_eq_top_iff, BrouwerianSemilattice.le_himp_iff,
        BrouwerianSemilattice.le_himp_iff]
    have hb : (BrouwerianBotEvaluate v bot_val φ ⇨ BrouwerianBotEvaluate v bot_val ψ ⇨
                BrouwerianBotEvaluate v bot_val χ) ⊓
              (BrouwerianBotEvaluate v bot_val φ ⇨ BrouwerianBotEvaluate v bot_val ψ) ⊓
              BrouwerianBotEvaluate v bot_val φ ≤ BrouwerianBotEvaluate v bot_val ψ :=
      (inf_le_inf_right _ inf_le_right).trans BrouwerianSemilattice.himp_inf_le
    have hbc : (BrouwerianBotEvaluate v bot_val φ ⇨ BrouwerianBotEvaluate v bot_val ψ ⇨
                 BrouwerianBotEvaluate v bot_val χ) ⊓
               (BrouwerianBotEvaluate v bot_val φ ⇨ BrouwerianBotEvaluate v bot_val ψ) ⊓
               BrouwerianBotEvaluate v bot_val φ ≤
               BrouwerianBotEvaluate v bot_val ψ ⇨ BrouwerianBotEvaluate v bot_val χ :=
      (inf_le_inf_right _ inf_le_left).trans BrouwerianSemilattice.himp_inf_le
    exact (le_inf hbc hb).trans BrouwerianSemilattice.himp_inf_le
  | andI φ ψ =>
    simp only [BrouwerianBotEvaluate_imp, BrouwerianBotEvaluate_and]
    rw [BrouwerianSemilattice.himp_eq_top_iff, BrouwerianSemilattice.le_himp_iff]
  | andE1 φ ψ =>
    simp only [BrouwerianBotEvaluate_imp, BrouwerianBotEvaluate_and]
    rw [BrouwerianSemilattice.himp_eq_top_iff]
    exact inf_le_left
  | andE2 φ ψ =>
    simp only [BrouwerianBotEvaluate_imp, BrouwerianBotEvaluate_and]
    rw [BrouwerianSemilattice.himp_eq_top_iff]
    exact inf_le_right

/-- Soundness at the derivation tree level for `ConjImpBotMinAxiom`. -/
theorem conjImpBotMin_brouwerianBot_soundness
    {Atom : Type*}
    {Γ : List (PL.Proposition Atom)} {φ : PL.Proposition Atom}
    (d : DerivationTree ConjImpBotMinAxiom Γ φ)
    {H : Type*} [BrouwerianSemilattice H]
    (v : Atom → H) (bot_val : H)
    (h_ctx : ∀ ψ, ψ ∈ Γ → BrouwerianBotEvaluate v bot_val ψ = ⊤) :
    BrouwerianBotEvaluate v bot_val φ = ⊤ := by
  match d with
  | .ax _ ψ h_ax => exact conjImpBotMin_brouwerianBot_axiom_sound h_ax H v bot_val
  | .assumption _ ψ h_mem => exact h_ctx ψ h_mem
  | .modus_ponens _ ψ χ d₁ d₂ =>
    have h1 := conjImpBotMin_brouwerianBot_soundness d₁ v bot_val h_ctx
    have h2 := conjImpBotMin_brouwerianBot_soundness d₂ v bot_val h_ctx
    simp only [BrouwerianBotEvaluate_imp] at h1
    rw [BrouwerianSemilattice.himp_eq_top_iff] at h1
    rw [h2, top_le_iff] at h1
    exact h1
  | .weakening _ _ ψ d' h_sub =>
    exact conjImpBotMin_brouwerianBot_soundness d' v bot_val
      (fun x hx => h_ctx x (h_sub x hx))

/-- **Free-Bot Brouwerian Soundness for MPL⟨∧,→,⊥,⊤⟩**: Every `ConjImpBotMinAxiom`-derivable
formula is valid in every Brouwerian semilattice with any choice of `bot_val`. -/
theorem conjImpBotMin_brouwerianBot_soundness_derivable {Atom : Type*}
    {φ : PL.Proposition Atom}
    (h : Derivable ConjImpBotMinAxiom φ) : BrouwerianBotValid φ := by
  intro H _ v bot_val
  obtain ⟨d⟩ := h
  exact conjImpBotMin_brouwerianBot_soundness d v bot_val (fun _ h => nomatch h)

/-! ## ConjImpBotMin Brouwerian Lindenbaum Construction -/

/-- Two propositions are `ConjImpBotMinAxiom`-equivalent if each is derivable from the other
in a singleton context. This defines the quotient relation for the free-bot Brouwerian
Lindenbaum algebra. -/
def ConjImpBotMinEquiv (A B : PL.Proposition Atom) : Prop :=
  Deriv ConjImpBotMinAxiom [A] B ∧ Deriv ConjImpBotMinAxiom [B] A

/-! ## Equivalence Relation Lemmas -/

/-- `ConjImpBotMinEquiv` is reflexive via the assumption rule. -/
theorem conjImpBotMinEquiv_refl (A : PL.Proposition Atom) : ConjImpBotMinEquiv A A :=
  ⟨assumption_deriv List.mem_cons_self,
   assumption_deriv List.mem_cons_self⟩

/-- `ConjImpBotMinEquiv` is symmetric by swapping. -/
theorem conjImpBotMinEquiv_symm {A B : PL.Proposition Atom}
    (h : ConjImpBotMinEquiv A B) : ConjImpBotMinEquiv B A :=
  ⟨h.2, h.1⟩

/-- `ConjImpBotMinEquiv` is transitive via the cut rule. -/
theorem conjImpBotMinEquiv_trans {A B C : PL.Proposition Atom}
    (hAB : ConjImpBotMinEquiv A B) (hBC : ConjImpBotMinEquiv B C) : ConjImpBotMinEquiv A C :=
  ⟨hilbertCutSingletonDeriv ConjImpBotMinAxiom.mem_implyK ConjImpBotMinAxiom.mem_implyS hAB.1 hBC.1,
   hilbertCutSingletonDeriv ConjImpBotMinAxiom.mem_implyK ConjImpBotMinAxiom.mem_implyS hBC.2 hAB.2⟩

/-! ## Setoid, Quotient Type, and Quotient Map -/

/-- The `ConjImpBotMinAxiom`-equivalence setoid on `Proposition Atom`. -/
def conjImpBotMinPropositionSetoid : Setoid (PL.Proposition Atom) where
  r := ConjImpBotMinEquiv
  iseqv := {
    refl := conjImpBotMinEquiv_refl
    symm := conjImpBotMinEquiv_symm
    trans := conjImpBotMinEquiv_trans
  }

/-- The **free-bot Brouwerian Lindenbaum algebra**: the quotient of `Proposition Atom` by
`ConjImpBotMinAxiom`-derivational equivalence. This is the universal Brouwerian semilattice
(with free `bot_val = [⊥]`) for the conjunctive-implicational-bot-min fragment.

Unlike `PointedBrouwerianLindenbaumAlgebra`, this quotient carries no `OrderBot` instance,
since `ConjImpBotMinAxiom` has no ex falso axiom. -/
def ConjImpBotMinLindenbaumAlgebra (Atom : Type*) : Type _ :=
  Quotient (@conjImpBotMinPropositionSetoid Atom)

/-- The quotient map: sends `A` to its equivalence class `[A]` in the free-bot Brouwerian
Lindenbaum algebra. -/
def conjImpBotMinLindenbaumMk (A : PL.Proposition Atom) :
    ConjImpBotMinLindenbaumAlgebra Atom :=
  Quotient.mk conjImpBotMinPropositionSetoid A

/-! ## Order on the Quotient -/

/-- `[A] ≤ [B]` iff `Deriv ConjImpBotMinAxiom [A] B`. Well-defined by congruence. -/
def conjImpBotMinLindenbaumLe
    (x y : ConjImpBotMinLindenbaumAlgebra Atom) : Prop :=
  Quotient.liftOn₂ x y
    (fun A B => Deriv ConjImpBotMinAxiom [A] B)
    (fun _ _ _ _ hA hB => propext ⟨
      fun h =>
        hilbertCutSingletonDeriv ConjImpBotMinAxiom.mem_implyK ConjImpBotMinAxiom.mem_implyS
          (hilbertCutSingletonDeriv ConjImpBotMinAxiom.mem_implyK
            ConjImpBotMinAxiom.mem_implyS hA.2 h)
          hB.1,
      fun h =>
        hilbertCutSingletonDeriv ConjImpBotMinAxiom.mem_implyK ConjImpBotMinAxiom.mem_implyS
          (hilbertCutSingletonDeriv ConjImpBotMinAxiom.mem_implyK
            ConjImpBotMinAxiom.mem_implyS hA.1 h)
          hB.2⟩)

/-- The order reduces to derivability on representatives. -/
@[simp]
theorem conjImpBotMinLindenbaumLe_mk (A B : PL.Proposition Atom) :
    conjImpBotMinLindenbaumLe (conjImpBotMinLindenbaumMk A)
      (conjImpBotMinLindenbaumMk B) ↔
    Deriv ConjImpBotMinAxiom [A] B :=
  Iff.rfl

/-! ## Congruence Lemmas for Quotient Operations -/

/-- And-congruence: if `A ≈ A'` and `B ≈ B'` then `A ∧ B ≈ A' ∧ B'`. -/
theorem conjImpBotMinEquivAndCongr {A A' B B' : PL.Proposition Atom}
    (hA : ConjImpBotMinEquiv A A') (hB : ConjImpBotMinEquiv B B') :
    ConjImpBotMinEquiv (A.and B) (A'.and B') := by
  constructor
  · have hAssume := assumption_deriv (Axioms := ConjImpBotMinAxiom) (Γ := [A.and B])
      List.mem_cons_self
    have hA_part := hilbertAndE1Deriv (fun φ ψ => .andE1 φ ψ) hAssume
    have hB_part := hilbertAndE2Deriv (fun φ ψ => .andE2 φ ψ) hAssume
    exact hilbertAndIDeriv (fun φ ψ => .andI φ ψ)
      (hilbertCutSingletonDeriv ConjImpBotMinAxiom.mem_implyK ConjImpBotMinAxiom.mem_implyS
        hA_part hA.1)
      (hilbertCutSingletonDeriv ConjImpBotMinAxiom.mem_implyK ConjImpBotMinAxiom.mem_implyS
        hB_part hB.1)
  · have hAssume := assumption_deriv (Axioms := ConjImpBotMinAxiom) (Γ := [A'.and B'])
      List.mem_cons_self
    have hA'_part := hilbertAndE1Deriv (fun φ ψ => .andE1 φ ψ) hAssume
    have hB'_part := hilbertAndE2Deriv (fun φ ψ => .andE2 φ ψ) hAssume
    exact hilbertAndIDeriv (fun φ ψ => .andI φ ψ)
      (hilbertCutSingletonDeriv ConjImpBotMinAxiom.mem_implyK ConjImpBotMinAxiom.mem_implyS
        hA'_part hA.2)
      (hilbertCutSingletonDeriv ConjImpBotMinAxiom.mem_implyK ConjImpBotMinAxiom.mem_implyS
        hB'_part hB.2)

/-- Imp-congruence: if `A ≈ A'` and `B ≈ B'` then `A → B ≈ A' → B'`. -/
theorem conjImpBotMinEquivImpCongr {A A' B B' : PL.Proposition Atom}
    (hA : ConjImpBotMinEquiv A A') (hB : ConjImpBotMinEquiv B B') :
    ConjImpBotMinEquiv (A.imp B) (A'.imp B') := by
  constructor
  · apply hilbertImpIDeriv ConjImpBotMinAxiom.mem_implyK ConjImpBotMinAxiom.mem_implyS
    have hAimp : Deriv ConjImpBotMinAxiom [A', A.imp B] (A.imp B) :=
      assumption_deriv (by simp)
    have hA_part : Deriv ConjImpBotMinAxiom [A', A.imp B] A :=
      hilbertWeakenSingleton hA.2
    have hB_part := hilbertImpEDeriv hAimp hA_part
    exact hilbertCutListDeriv ConjImpBotMinAxiom.mem_implyK ConjImpBotMinAxiom.mem_implyS
      hB_part hB.1
  · apply hilbertImpIDeriv ConjImpBotMinAxiom.mem_implyK ConjImpBotMinAxiom.mem_implyS
    have hA'imp : Deriv ConjImpBotMinAxiom [A, A'.imp B'] (A'.imp B') :=
      assumption_deriv (by simp)
    have hA'_part : Deriv ConjImpBotMinAxiom [A, A'.imp B'] A' :=
      hilbertWeakenSingleton hA.1
    have hB'_part := hilbertImpEDeriv hA'imp hA'_part
    exact hilbertCutListDeriv ConjImpBotMinAxiom.mem_implyK ConjImpBotMinAxiom.mem_implyS
      hB'_part hB.2

/-! ## Operations on the Quotient -/

/-- Meet: `[A] ⊓ [B] = [A ∧ B]`. -/
def conjImpBotMinLindenbaumInf
    (x y : ConjImpBotMinLindenbaumAlgebra Atom) :
    ConjImpBotMinLindenbaumAlgebra Atom :=
  Quotient.lift₂
    (fun A B => conjImpBotMinLindenbaumMk (A.and B))
    (fun _ _ _ _ hA hB => Quotient.sound (conjImpBotMinEquivAndCongr hA hB))
    x y

/-- Heyting implication: `[A] ⇨ [B] = [A → B]`. -/
def conjImpBotMinLindenbaumHimp
    (x y : ConjImpBotMinLindenbaumAlgebra Atom) :
    ConjImpBotMinLindenbaumAlgebra Atom :=
  Quotient.lift₂
    (fun A B => conjImpBotMinLindenbaumMk (A.imp B))
    (fun _ _ _ _ hA hB => Quotient.sound (conjImpBotMinEquivImpCongr hA hB))
    x y

/-- `[A ∧ B] = [A] ⊓ [B]`. -/
@[simp]
theorem conjImpBotMinLindenbaumInf_mk (A B : PL.Proposition Atom) :
    conjImpBotMinLindenbaumInf (conjImpBotMinLindenbaumMk A)
      (conjImpBotMinLindenbaumMk B) =
    conjImpBotMinLindenbaumMk (A.and B) := rfl

/-- `[A → B] = [A] ⇨ [B]`. -/
@[simp]
theorem conjImpBotMinLindenbaumHimp_mk (A B : PL.Proposition Atom) :
    conjImpBotMinLindenbaumHimp (conjImpBotMinLindenbaumMk A)
      (conjImpBotMinLindenbaumMk B) =
    conjImpBotMinLindenbaumMk (A.imp B) := rfl

/-! ## BrouwerianSemilattice Axiom Lemmas -/

/-- Reflexivity: `[A] ≤ [A]` via the assumption rule. -/
theorem conjImpBotMinLindenbaumLe_refl
    (x : ConjImpBotMinLindenbaumAlgebra Atom) :
    conjImpBotMinLindenbaumLe x x := by
  obtain ⟨A, rfl⟩ := Quotient.exists_rep x
  exact assumption_deriv List.mem_cons_self

/-- Transitivity via cut. -/
theorem conjImpBotMinLindenbaumLe_trans
    (x y z : ConjImpBotMinLindenbaumAlgebra Atom)
    (hxy : conjImpBotMinLindenbaumLe x y) (hyz : conjImpBotMinLindenbaumLe y z) :
    conjImpBotMinLindenbaumLe x z := by
  obtain ⟨A, rfl⟩ := Quotient.exists_rep x
  obtain ⟨B, rfl⟩ := Quotient.exists_rep y
  obtain ⟨C, rfl⟩ := Quotient.exists_rep z
  exact hilbertCutSingletonDeriv ConjImpBotMinAxiom.mem_implyK ConjImpBotMinAxiom.mem_implyS hxy hyz

/-- Antisymmetry via `Quotient.sound`. -/
theorem conjImpBotMinLindenbaumLe_antisymm
    (x y : ConjImpBotMinLindenbaumAlgebra Atom)
    (hxy : conjImpBotMinLindenbaumLe x y) (hyx : conjImpBotMinLindenbaumLe y x) :
    x = y := by
  obtain ⟨A, rfl⟩ := Quotient.exists_rep x
  obtain ⟨B, rfl⟩ := Quotient.exists_rep y
  exact Quotient.sound ⟨hxy, hyx⟩

/-- `[A ∧ B] ≤ [A]` via andE1. -/
theorem conjImpBotMinLindenbaumInf_le_left
    (x y : ConjImpBotMinLindenbaumAlgebra Atom) :
    conjImpBotMinLindenbaumLe (conjImpBotMinLindenbaumInf x y) x := by
  obtain ⟨A, rfl⟩ := Quotient.exists_rep x
  obtain ⟨B, rfl⟩ := Quotient.exists_rep y
  exact hilbertAndE1Deriv (fun φ ψ => .andE1 φ ψ) (assumption_deriv List.mem_cons_self)

/-- `[A ∧ B] ≤ [B]` via andE2. -/
theorem conjImpBotMinLindenbaumInf_le_right
    (x y : ConjImpBotMinLindenbaumAlgebra Atom) :
    conjImpBotMinLindenbaumLe (conjImpBotMinLindenbaumInf x y) y := by
  obtain ⟨A, rfl⟩ := Quotient.exists_rep x
  obtain ⟨B, rfl⟩ := Quotient.exists_rep y
  exact hilbertAndE2Deriv (fun φ ψ => .andE2 φ ψ) (assumption_deriv List.mem_cons_self)

/-- `le_inf`: from `[A] ≤ [B]` and `[A] ≤ [C]` derive `[A] ≤ [B ∧ C]` via andI. -/
theorem conjImpBotMinLindenbaumLe_inf
    (x y z : ConjImpBotMinLindenbaumAlgebra Atom)
    (hxy : conjImpBotMinLindenbaumLe x y) (hxz : conjImpBotMinLindenbaumLe x z) :
    conjImpBotMinLindenbaumLe x (conjImpBotMinLindenbaumInf y z) := by
  obtain ⟨A, rfl⟩ := Quotient.exists_rep x
  obtain ⟨B, rfl⟩ := Quotient.exists_rep y
  obtain ⟨C, rfl⟩ := Quotient.exists_rep z
  exact hilbertAndIDeriv (fun φ ψ => .andI φ ψ) hxy hxz

/-- `le_top`: `[A] ≤ ⊤` where top is `[⊥ → ⊥]`. -/
theorem conjImpBotMinLindenbaumLe_top
    (x : ConjImpBotMinLindenbaumAlgebra Atom) :
    conjImpBotMinLindenbaumLe x (conjImpBotMinLindenbaumMk (bot.imp bot)) := by
  obtain ⟨A, rfl⟩ := Quotient.exists_rep x
  apply hilbertImpIDeriv ConjImpBotMinAxiom.mem_implyK ConjImpBotMinAxiom.mem_implyS
  exact assumption_deriv List.mem_cons_self

/-- The hardest lemma: Brouwerian deduction theorem.
`[A] ≤ [B → C]` iff `[A ∧ B] ≤ [C]`. -/
theorem conjImpBotMinLindenbaumLe_himp_iff
    (x y z : ConjImpBotMinLindenbaumAlgebra Atom) :
    conjImpBotMinLindenbaumLe x (conjImpBotMinLindenbaumHimp y z) ↔
    conjImpBotMinLindenbaumLe (conjImpBotMinLindenbaumInf x y) z := by
  obtain ⟨A, rfl⟩ := Quotient.exists_rep x
  obtain ⟨B, rfl⟩ := Quotient.exists_rep y
  obtain ⟨C, rfl⟩ := Quotient.exists_rep z
  constructor
  · intro hAimp
    have hAnd := assumption_deriv (Axioms := ConjImpBotMinAxiom) (Γ := [A.and B]) List.mem_cons_self
    have hA := hilbertAndE1Deriv (fun φ ψ => .andE1 φ ψ) hAnd
    have hB := hilbertAndE2Deriv (fun φ ψ => .andE2 φ ψ) hAnd
    have hImp := hilbertCutSingletonDeriv ConjImpBotMinAxiom.mem_implyK
      ConjImpBotMinAxiom.mem_implyS hA hAimp
    exact hilbertImpEDeriv hImp hB
  · intro hAndC
    apply hilbertImpIDeriv ConjImpBotMinAxiom.mem_implyK ConjImpBotMinAxiom.mem_implyS
    have hA : Deriv ConjImpBotMinAxiom [B, A] A := assumption_deriv (by simp)
    have hB : Deriv ConjImpBotMinAxiom [B, A] B := assumption_deriv (by simp)
    have hAndAB := hilbertAndIDeriv (fun φ ψ => .andI φ ψ) hA hB
    exact hilbertCutListDeriv ConjImpBotMinAxiom.mem_implyK ConjImpBotMinAxiom.mem_implyS
      hAndAB hAndC

/-! ## BrouwerianSemilattice Instance -/

namespace ConjImpBotMinLindenbaumAlgebra

/-- The free-bot Brouwerian Lindenbaum algebra is a `BrouwerianSemilattice`.

Unlike `PointedBrouwerianLindenbaumAlgebra`, there is no `OrderBot` instance here because
`ConjImpBotMinAxiom` has no ex falso axiom. All sub-instances (PartialOrder, SemilatticeInf,
OrderTop) are derived from `le_himp_iff`. -/
instance brouwerianSemilattice :
    BrouwerianSemilattice (ConjImpBotMinLindenbaumAlgebra Atom) where
  le := conjImpBotMinLindenbaumLe
  top := conjImpBotMinLindenbaumMk (bot.imp bot)
  inf := conjImpBotMinLindenbaumInf
  himp := conjImpBotMinLindenbaumHimp
  le_refl := conjImpBotMinLindenbaumLe_refl
  le_trans := fun x y z => conjImpBotMinLindenbaumLe_trans x y z
  le_antisymm := fun x y => conjImpBotMinLindenbaumLe_antisymm x y
  inf_le_left := conjImpBotMinLindenbaumInf_le_left
  inf_le_right := conjImpBotMinLindenbaumInf_le_right
  le_inf := fun x y z => conjImpBotMinLindenbaumLe_inf x y z
  le_top := conjImpBotMinLindenbaumLe_top
  le_himp_iff := fun x y z => conjImpBotMinLindenbaumLe_himp_iff x y z

end ConjImpBotMinLindenbaumAlgebra

/-! ## API Simp Lemmas -/

/-- `[A] ≤ [B] ↔ Deriv ConjImpBotMinAxiom [A] B`. -/
@[simp]
theorem conjImpBotMinLindenbaumMk_le_mk (A B : PL.Proposition Atom) :
    conjImpBotMinLindenbaumMk A ≤ conjImpBotMinLindenbaumMk B ↔
    Deriv ConjImpBotMinAxiom [A] B :=
  conjImpBotMinLindenbaumLe_mk A B

/-- `[A ∧ B] = [A] ⊓ [B]`. -/
@[simp]
theorem conjImpBotMinLindenbaumMk_inf (A B : PL.Proposition Atom) :
    conjImpBotMinLindenbaumMk (A.and B) =
    conjImpBotMinLindenbaumMk A ⊓ conjImpBotMinLindenbaumMk B :=
  (conjImpBotMinLindenbaumInf_mk A B).symm

/-- `[A → B] = [A] ⇨ [B]`. -/
@[simp]
theorem conjImpBotMinLindenbaumMk_himp (A B : PL.Proposition Atom) :
    conjImpBotMinLindenbaumMk (A.imp B) =
    conjImpBotMinLindenbaumMk A ⇨ conjImpBotMinLindenbaumMk B :=
  (conjImpBotMinLindenbaumHimp_mk A B).symm

/-- Top in the free-bot Brouwerian Lindenbaum algebra is `[⊥ → ⊥]`. -/
theorem conjImpBotMinLindenbaumTop :
    (⊤ : ConjImpBotMinLindenbaumAlgebra Atom) =
    conjImpBotMinLindenbaumMk (bot.imp bot) := rfl

/-! ## Top Characterization -/

/-- `[A] = ⊤` in the free-bot Brouwerian Lindenbaum algebra iff `A` is
`ConjImpBotMinAxiom`-derivable from the empty context. -/
theorem conjImpBotMinLindenbaumMk_eq_top_iff {A : PL.Proposition Atom} :
    conjImpBotMinLindenbaumMk A = ⊤ ↔ Derivable ConjImpBotMinAxiom A := by
  rw [conjImpBotMinLindenbaumTop]
  constructor
  · intro h
    have heq : ConjImpBotMinEquiv A (bot.imp bot) :=
      Quotient.exact h
    have hBotBot : Derivable (@ConjImpBotMinAxiom Atom) ((bot : PL.Proposition Atom).imp bot) := by
      apply hilbertImpIDeriv ConjImpBotMinAxiom.mem_implyK ConjImpBotMinAxiom.mem_implyS
      exact assumption_deriv List.mem_cons_self
    exact hilbertCutListDeriv ConjImpBotMinAxiom.mem_implyK ConjImpBotMinAxiom.mem_implyS
      hBotBot heq.2
  · intro hA
    apply Quotient.sound
    constructor
    · apply hilbertImpIDeriv ConjImpBotMinAxiom.mem_implyK ConjImpBotMinAxiom.mem_implyS
      exact assumption_deriv (by simp)
    · exact weakening_deriv hA (fun _ h => nomatch h)

/-! ## Canonical Valuation and Truth Lemma -/

/-- The canonical variable assignment into the free-bot Brouwerian Lindenbaum algebra:
sends each atom `x` to its equivalence class `[x]`. -/
def conjImpBotMinCanonicalV :
    Atom → ConjImpBotMinLindenbaumAlgebra Atom :=
  fun x => conjImpBotMinLindenbaumMk (.atom x)

/-- **Truth Lemma** (restricted to `IsOrFree`): evaluating an or-free proposition under
the canonical valuation with `bot_val = [⊥]` gives exactly its equivalence class.

`BrouwerianBotEvaluate conjImpBotMinCanonicalV [⊥] A = [A]` for `IsOrFree` formulas.

The `bot` case works because `BrouwerianBotEvaluate canonicalV [⊥] .bot = [⊥] = [⊥]`
— by definition of `BrouwerianBotEvaluate`, the `bot` case returns `bot_val = [⊥]`
which is exactly `conjImpBotMinLindenbaumMk Proposition.bot`. -/
theorem conjImpBotMinCanonicalV_spec (A : PL.Proposition Atom)
    (hA : A.IsOrFree = true) :
    BrouwerianBotEvaluate conjImpBotMinCanonicalV
      (conjImpBotMinLindenbaumMk Proposition.bot) A =
    conjImpBotMinLindenbaumMk A := by
  induction A with
  | atom x => rfl
  | bot => rfl
  | imp a b iha ihb =>
    simp only [Proposition.IsOrFree, Bool.and_eq_true] at hA
    simp only [BrouwerianBotEvaluate_imp, iha hA.1, ihb hA.2,
               conjImpBotMinLindenbaumMk_himp]
  | and a b iha ihb =>
    simp only [Proposition.IsOrFree, Bool.and_eq_true] at hA
    simp only [BrouwerianBotEvaluate_and, iha hA.1, ihb hA.2,
               conjImpBotMinLindenbaumMk_inf]
  | or _ _ _ _ => simp [Proposition.IsOrFree] at hA

/-! ## Completeness Theorem -/

/-- **Free-Bot Brouwerian Completeness for MPL⟨∧,→,⊥,⊤⟩** (restricted to `IsOrFree` formulas):
if an or-free formula is valid in every Brouwerian semilattice with every choice of `bot_val`,
then it is `ConjImpBotMinAxiom`-derivable.

The restriction to `IsOrFree` is necessary: `a ∨ b` is vacuously valid (since
`BrouwerianBotEvaluate v bot_val (or a b) = ⊤` by definition) but `ConjImpBotMinAxiom`
has no disjunction axioms. -/
theorem conjImpBotMin_brouwerianBot_complete {Atom : Type u} {φ : PL.Proposition Atom}
    (hfrag : φ.IsOrFree = true)
    (h : BrouwerianBotValid.{u, u} φ) :
    Derivable ConjImpBotMinAxiom φ := by
  -- Instantiate BrouwerianBotValid at the free-bot Lindenbaum algebra with bot_val = [⊥]
  have hLind : BrouwerianBotEvaluate conjImpBotMinCanonicalV
      (conjImpBotMinLindenbaumMk Proposition.bot) φ = ⊤ :=
    h (ConjImpBotMinLindenbaumAlgebra Atom) conjImpBotMinCanonicalV
      (conjImpBotMinLindenbaumMk Proposition.bot)
  -- Apply the truth lemma (valid since φ is IsOrFree)
  rw [conjImpBotMinCanonicalV_spec φ hfrag] at hLind
  -- Extract derivability via mk_eq_top_iff
  exact conjImpBotMinLindenbaumMk_eq_top_iff.mp hLind

/-- **Free-Bot Brouwerian Biconditional for MPL⟨∧,→,⊥,⊤⟩**: For or-free formulas,
derivability and free-bot Brouwerian validity coincide. -/
theorem conjImpBotMin_brouwerianBot_iff {Atom : Type u} {φ : PL.Proposition Atom}
    (hfrag : φ.IsOrFree = true) :
    Derivable ConjImpBotMinAxiom φ ↔ BrouwerianBotValid.{u, u} φ :=
  ⟨conjImpBotMin_brouwerianBot_soundness_derivable,
   conjImpBotMin_brouwerianBot_complete hfrag⟩

end Cslib.Logic.PL

end

end
