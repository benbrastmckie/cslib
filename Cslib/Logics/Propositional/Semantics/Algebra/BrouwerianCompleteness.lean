/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Propositional.Semantics.Algebra.Brouwerian
public import Cslib.Logics.Propositional.ProofSystem.FragmentAxioms
public import Cslib.Logics.Propositional.Semantics.Algebra.HilbertLindenbaum

/-! # Brouwerian Algebraic Soundness and Completeness for IPL⟨∧,→,⊤⟩

This module proves soundness and completeness of the conjunctive-implicational fragment
IPL⟨∧,→,⊤⟩ with respect to Brouwerian semilattices.

**Soundness** (`conjImp_brouwerian_soundness_derivable`): Every `ConjImpAxiom`-derivable
formula evaluates to `⊤` in every Brouwerian semilattice under every variable assignment.

**Completeness** (`conjImp_brouwerian_complete`): Restricted to `IsOrBotFree` formulas, if
a formula evaluates to `⊤` in every Brouwerian semilattice then it is `ConjImpAxiom`-derivable.
The restriction is necessary because `BrouwerianEvaluate` maps `bot` and `or` to `⊤`, making
those connectives vacuously valid, while `ConjImpAxiom` has no EFQ or disjunction axioms.

## Proof Strategy

**Soundness** follows by case analysis on `ConjImpAxiom` constructors using
`BrouwerianSemilattice` lemmas (`le_himp_iff`, `himp_eq_top_iff`, `inf_le_left`, etc.),
then by induction on the derivation tree.

**Completeness** uses the **Brouwerian Lindenbaum algebra**: the quotient of `Proposition Atom`
by `ConjImpAxiom`-derivational equivalence. The construction follows `HilbertLindenbaum.lean`
with the key simplification that no join (sup) operation is needed.

## Main Definitions

- `ConjImpEquiv`: the derivational equivalence relation `A ≈ B iff [A] ⊢ B ∧ [B] ⊢ A`
- `BrouwerianLindenbaumAlgebra`: the quotient type `Quotient conjImpPropositionSetoid`
- `brouwerianLindenbaumMk`: the quotient map
- `brouwerianCanonicalV`: the canonical variable assignment `x ↦ [atom x]`

## Main Results

- `conjImp_brouwerian_soundness_derivable`: `Derivable ConjImpAxiom φ → BrouwerianValid φ`
- `brouwerianLindenbaumMk_eq_top_iff`: `[A] = ⊤ ↔ Derivable ConjImpAxiom A`
- `brouwerianCanonicalV_spec`: truth lemma for `IsOrBotFree` formulas
- `conjImp_brouwerian_complete`: `IsOrBotFree φ → BrouwerianValid φ → Derivable ConjImpAxiom φ`
- `conjImp_brouwerian_iff`: `IsOrBotFree φ → (Derivable ConjImpAxiom φ ↔ BrouwerianValid φ)`

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

/-! ## Brouwerian Soundness -/

/-- Every axiom of the conjunctive-implicational fragment is valid in every Brouwerian
semilattice: each `ConjImpAxiom` constructor evaluates to `⊤` under any assignment. -/
theorem conjImp_brouwerian_axiom_sound {φ : PL.Proposition Atom}
    (h_ax : ConjImpAxiom φ) : BrouwerianValid φ := by
  intro H _ v
  cases h_ax with
  | implyK φ ψ =>
    -- implyK: φ → (ψ → φ); need φ_h ⇨ (ψ_h ⇨ φ_h) = ⊤
    simp only [BrouwerianEvaluate]
    rw [BrouwerianSemilattice.himp_eq_top_iff, BrouwerianSemilattice.le_himp_iff]
    exact inf_le_left
  | implyS φ ψ χ =>
    -- implyS: (φ → (ψ → χ)) → ((φ → ψ) → (φ → χ))
    simp only [BrouwerianEvaluate]
    rw [BrouwerianSemilattice.himp_eq_top_iff, BrouwerianSemilattice.le_himp_iff,
        BrouwerianSemilattice.le_himp_iff]
    -- Goal: ((a ⇨ b ⇨ c) ⊓ (a ⇨ b)) ⊓ a ≤ c
    have hb : (BrouwerianEvaluate v φ ⇨ BrouwerianEvaluate v ψ ⇨ BrouwerianEvaluate v χ) ⊓
              (BrouwerianEvaluate v φ ⇨ BrouwerianEvaluate v ψ) ⊓
              BrouwerianEvaluate v φ ≤ BrouwerianEvaluate v ψ :=
      (inf_le_inf_right _ inf_le_right).trans BrouwerianSemilattice.himp_inf_le
    have hbc : (BrouwerianEvaluate v φ ⇨ BrouwerianEvaluate v ψ ⇨ BrouwerianEvaluate v χ) ⊓
               (BrouwerianEvaluate v φ ⇨ BrouwerianEvaluate v ψ) ⊓
               BrouwerianEvaluate v φ ≤
               BrouwerianEvaluate v ψ ⇨ BrouwerianEvaluate v χ :=
      (inf_le_inf_right _ inf_le_left).trans BrouwerianSemilattice.himp_inf_le
    exact (le_inf hbc hb).trans BrouwerianSemilattice.himp_inf_le
  | andI φ ψ =>
    -- andI: φ → (ψ → φ ∧ ψ); need φ_h ⇨ (ψ_h ⇨ φ_h ⊓ ψ_h) = ⊤
    -- himp_eq_top_iff: φ_h ≤ ψ_h ⇨ φ_h ⊓ ψ_h
    -- le_himp_iff: φ_h ⊓ ψ_h ≤ φ_h ⊓ ψ_h, which closes by rfl
    simp only [BrouwerianEvaluate]
    rw [BrouwerianSemilattice.himp_eq_top_iff, BrouwerianSemilattice.le_himp_iff]
  | andE1 φ ψ =>
    -- andE1: (φ ∧ ψ) → φ; need φ_h ⊓ ψ_h ⇨ φ_h = ⊤
    simp only [BrouwerianEvaluate]
    rw [BrouwerianSemilattice.himp_eq_top_iff]
    exact inf_le_left
  | andE2 φ ψ =>
    -- andE2: (φ ∧ ψ) → ψ; need φ_h ⊓ ψ_h ⇨ ψ_h = ⊤
    simp only [BrouwerianEvaluate]
    rw [BrouwerianSemilattice.himp_eq_top_iff]
    exact inf_le_right

/-- Soundness at the derivation tree level: if `Γ ⊢ φ` via `ConjImpAxiom` and every formula
in `Γ` evaluates to `⊤`, then `φ` evaluates to `⊤` in every Brouwerian semilattice. -/
theorem conjImp_brouwerian_soundness
    {Γ : List (PL.Proposition Atom)} {φ : PL.Proposition Atom}
    (d : DerivationTree ConjImpAxiom Γ φ)
    {H : Type*} [BrouwerianSemilattice H]
    (v : Atom → H)
    (h_ctx : ∀ ψ, ψ ∈ Γ → BrouwerianEvaluate v ψ = ⊤) :
    BrouwerianEvaluate v φ = ⊤ := by
  match d with
  | .ax _ ψ h_ax => exact conjImp_brouwerian_axiom_sound h_ax H v
  | .assumption _ ψ h_mem => exact h_ctx ψ h_mem
  | .modus_ponens _ ψ χ d₁ d₂ =>
    have h1 := conjImp_brouwerian_soundness d₁ v h_ctx
    have h2 := conjImp_brouwerian_soundness d₂ v h_ctx
    simp only [BrouwerianEvaluate] at h1
    rw [BrouwerianSemilattice.himp_eq_top_iff] at h1
    rw [h2, top_le_iff] at h1
    exact h1
  | .weakening _ _ ψ d' h_sub =>
    exact conjImp_brouwerian_soundness d' v
      (fun x hx => h_ctx x (h_sub x hx))

/-- **Brouwerian Soundness for IPL⟨∧,→,⊤⟩**: Every `ConjImpAxiom`-derivable formula is
Brouwerian-valid. -/
theorem conjImp_brouwerian_soundness_derivable {φ : PL.Proposition Atom}
    (h : Derivable ConjImpAxiom φ) : BrouwerianValid φ := by
  intro H _ v
  obtain ⟨d⟩ := h
  exact conjImp_brouwerian_soundness d v (fun _ h => nomatch h)

/-! ## Brouwerian Lindenbaum Construction -/

/-- Two propositions are `ConjImpAxiom`-equivalent if each is derivable from the other
in a singleton context. This defines the quotient relation for the Brouwerian Lindenbaum
algebra. -/
def ConjImpEquiv (A B : PL.Proposition Atom) : Prop :=
  Deriv ConjImpAxiom [A] B ∧ Deriv ConjImpAxiom [B] A

/-! ## Equivalence Relation Lemmas -/

/-- `ConjImpEquiv` is reflexive via the assumption rule. -/
theorem conjImpEquiv_refl (A : PL.Proposition Atom) : ConjImpEquiv A A :=
  ⟨assumption_deriv List.mem_cons_self,
   assumption_deriv List.mem_cons_self⟩

/-- `ConjImpEquiv` is symmetric by swapping. -/
theorem conjImpEquiv_symm {A B : PL.Proposition Atom}
    (h : ConjImpEquiv A B) : ConjImpEquiv B A :=
  ⟨h.2, h.1⟩

/-- `ConjImpEquiv` is transitive via the cut rule. -/
theorem conjImpEquiv_trans {A B C : PL.Proposition Atom}
    (hAB : ConjImpEquiv A B) (hBC : ConjImpEquiv B C) : ConjImpEquiv A C :=
  ⟨hilbertCutSingletonDeriv ConjImpAxiom.mem_implyK ConjImpAxiom.mem_implyS hAB.1 hBC.1,
   hilbertCutSingletonDeriv ConjImpAxiom.mem_implyK ConjImpAxiom.mem_implyS hBC.2 hAB.2⟩

/-! ## Setoid, Quotient Type, and Quotient Map -/

/-- The `ConjImpAxiom`-equivalence setoid on `Proposition Atom`. -/
def conjImpPropositionSetoid : Setoid (PL.Proposition Atom) where
  r := ConjImpEquiv
  iseqv := {
    refl := conjImpEquiv_refl
    symm := conjImpEquiv_symm
    trans := conjImpEquiv_trans
  }

/-- The **Brouwerian Lindenbaum algebra**: the quotient of `Proposition Atom` by
`ConjImpAxiom`-derivational equivalence. This is the universal Brouwerian semilattice
for the conjunctive-implicational fragment. -/
def BrouwerianLindenbaumAlgebra (Atom : Type*) : Type _ :=
  Quotient (@conjImpPropositionSetoid Atom)

/-- The quotient map: sends `A` to its equivalence class `[A]` in the Brouwerian
Lindenbaum algebra. -/
def brouwerianLindenbaumMk (A : PL.Proposition Atom) :
    BrouwerianLindenbaumAlgebra Atom :=
  Quotient.mk conjImpPropositionSetoid A

/-! ## Order on the Quotient -/

/-- `[A] ≤ [B]` iff `Deriv ConjImpAxiom [A] B`. Well-defined by congruence. -/
def brouwerianLindenbaumLe
    (x y : BrouwerianLindenbaumAlgebra Atom) : Prop :=
  Quotient.liftOn₂ x y
    (fun A B => Deriv ConjImpAxiom [A] B)
    (fun _ _ _ _ hA hB => propext ⟨
      fun h =>
        hilbertCutSingletonDeriv ConjImpAxiom.mem_implyK ConjImpAxiom.mem_implyS
          (hilbertCutSingletonDeriv ConjImpAxiom.mem_implyK ConjImpAxiom.mem_implyS hA.2 h)
          hB.1,
      fun h =>
        hilbertCutSingletonDeriv ConjImpAxiom.mem_implyK ConjImpAxiom.mem_implyS
          (hilbertCutSingletonDeriv ConjImpAxiom.mem_implyK ConjImpAxiom.mem_implyS hA.1 h)
          hB.2⟩)

/-- The order on the Brouwerian Lindenbaum algebra reduces to derivability on representatives. -/
@[simp]
theorem brouwerianLindenbaumLe_mk (A B : PL.Proposition Atom) :
    brouwerianLindenbaumLe (brouwerianLindenbaumMk A) (brouwerianLindenbaumMk B) ↔
    Deriv ConjImpAxiom [A] B :=
  Iff.rfl

/-! ## Congruence Lemmas for Quotient Operations -/

/-- And-congruence: if `A ≈ A'` and `B ≈ B'` then `A ∧ B ≈ A' ∧ B'`. -/
theorem conjImpEquivAndCongr {A A' B B' : PL.Proposition Atom}
    (hA : ConjImpEquiv A A') (hB : ConjImpEquiv B B') :
    ConjImpEquiv (A.and B) (A'.and B') := by
  constructor
  · -- [A ∧ B] ⊢ A' ∧ B'
    have hAssume := assumption_deriv (Axioms := ConjImpAxiom) (Γ := [A.and B])
      List.mem_cons_self
    have hA_part := hilbertAndE1Deriv (fun φ ψ => .andE1 φ ψ) hAssume
    have hB_part := hilbertAndE2Deriv (fun φ ψ => .andE2 φ ψ) hAssume
    exact hilbertAndIDeriv (fun φ ψ => .andI φ ψ)
      (hilbertCutSingletonDeriv ConjImpAxiom.mem_implyK ConjImpAxiom.mem_implyS hA_part hA.1)
      (hilbertCutSingletonDeriv ConjImpAxiom.mem_implyK ConjImpAxiom.mem_implyS hB_part hB.1)
  · -- [A' ∧ B'] ⊢ A ∧ B
    have hAssume := assumption_deriv (Axioms := ConjImpAxiom) (Γ := [A'.and B'])
      List.mem_cons_self
    have hA'_part := hilbertAndE1Deriv (fun φ ψ => .andE1 φ ψ) hAssume
    have hB'_part := hilbertAndE2Deriv (fun φ ψ => .andE2 φ ψ) hAssume
    exact hilbertAndIDeriv (fun φ ψ => .andI φ ψ)
      (hilbertCutSingletonDeriv ConjImpAxiom.mem_implyK ConjImpAxiom.mem_implyS hA'_part hA.2)
      (hilbertCutSingletonDeriv ConjImpAxiom.mem_implyK ConjImpAxiom.mem_implyS hB'_part hB.2)

/-- Imp-congruence: if `A ≈ A'` and `B ≈ B'` then `A → B ≈ A' → B'`. -/
theorem conjImpEquivImpCongr {A A' B B' : PL.Proposition Atom}
    (hA : ConjImpEquiv A A') (hB : ConjImpEquiv B B') :
    ConjImpEquiv (A.imp B) (A'.imp B') := by
  constructor
  · -- [A → B] ⊢ A' → B'
    apply hilbertImpIDeriv ConjImpAxiom.mem_implyK ConjImpAxiom.mem_implyS
    -- context: A' :: [A → B], need [A', A → B] ⊢ B'
    have hAimp : Deriv ConjImpAxiom [A', A.imp B] (A.imp B) :=
      assumption_deriv (by simp)
    have hA_part : Deriv ConjImpAxiom [A', A.imp B] A :=
      hilbertWeakenSingleton hA.2
    have hB_part := hilbertImpEDeriv hAimp hA_part
    exact hilbertCutListDeriv ConjImpAxiom.mem_implyK ConjImpAxiom.mem_implyS hB_part hB.1
  · -- [A' → B'] ⊢ A → B
    apply hilbertImpIDeriv ConjImpAxiom.mem_implyK ConjImpAxiom.mem_implyS
    have hA'imp : Deriv ConjImpAxiom [A, A'.imp B'] (A'.imp B') :=
      assumption_deriv (by simp)
    have hA'_part : Deriv ConjImpAxiom [A, A'.imp B'] A' :=
      hilbertWeakenSingleton hA.1
    have hB'_part := hilbertImpEDeriv hA'imp hA'_part
    exact hilbertCutListDeriv ConjImpAxiom.mem_implyK ConjImpAxiom.mem_implyS hB'_part hB.2

/-! ## Operations on the Quotient -/

/-- Meet: `[A] ⊓ [B] = [A ∧ B]`. -/
def brouwerianLindenbaumInf
    (x y : BrouwerianLindenbaumAlgebra Atom) :
    BrouwerianLindenbaumAlgebra Atom :=
  Quotient.lift₂
    (fun A B => brouwerianLindenbaumMk (A.and B))
    (fun _ _ _ _ hA hB => Quotient.sound (conjImpEquivAndCongr hA hB))
    x y

/-- Heyting implication: `[A] ⇨ [B] = [A → B]`. -/
def brouwerianLindenbaumHimp
    (x y : BrouwerianLindenbaumAlgebra Atom) :
    BrouwerianLindenbaumAlgebra Atom :=
  Quotient.lift₂
    (fun A B => brouwerianLindenbaumMk (A.imp B))
    (fun _ _ _ _ hA hB => Quotient.sound (conjImpEquivImpCongr hA hB))
    x y

/-- `[A ∧ B] = [A] ⊓ [B]`. -/
@[simp]
theorem brouwerianLindenbaumInf_mk (A B : PL.Proposition Atom) :
    brouwerianLindenbaumInf (brouwerianLindenbaumMk A) (brouwerianLindenbaumMk B) =
    brouwerianLindenbaumMk (A.and B) := rfl

/-- `[A → B] = [A] ⇨ [B]`. -/
@[simp]
theorem brouwerianLindenbaumHimp_mk (A B : PL.Proposition Atom) :
    brouwerianLindenbaumHimp (brouwerianLindenbaumMk A) (brouwerianLindenbaumMk B) =
    brouwerianLindenbaumMk (A.imp B) := rfl

/-! ## BrouwerianSemilattice Axiom Lemmas -/

/-- Reflexivity: `[A] ≤ [A]` via the assumption rule. -/
theorem brouwerianLindenbaumLe_refl
    (x : BrouwerianLindenbaumAlgebra Atom) :
    brouwerianLindenbaumLe x x := by
  obtain ⟨A, rfl⟩ := Quotient.exists_rep x
  exact assumption_deriv List.mem_cons_self

/-- Transitivity via cut. -/
theorem brouwerianLindenbaumLe_trans
    (x y z : BrouwerianLindenbaumAlgebra Atom)
    (hxy : brouwerianLindenbaumLe x y) (hyz : brouwerianLindenbaumLe y z) :
    brouwerianLindenbaumLe x z := by
  obtain ⟨A, rfl⟩ := Quotient.exists_rep x
  obtain ⟨B, rfl⟩ := Quotient.exists_rep y
  obtain ⟨C, rfl⟩ := Quotient.exists_rep z
  exact hilbertCutSingletonDeriv ConjImpAxiom.mem_implyK ConjImpAxiom.mem_implyS hxy hyz

/-- Antisymmetry via `Quotient.sound`. -/
theorem brouwerianLindenbaumLe_antisymm
    (x y : BrouwerianLindenbaumAlgebra Atom)
    (hxy : brouwerianLindenbaumLe x y) (hyx : brouwerianLindenbaumLe y x) :
    x = y := by
  obtain ⟨A, rfl⟩ := Quotient.exists_rep x
  obtain ⟨B, rfl⟩ := Quotient.exists_rep y
  exact Quotient.sound ⟨hxy, hyx⟩

/-- `[A ∧ B] ≤ [A]` via andE1. -/
theorem brouwerianLindenbaumInf_le_left
    (x y : BrouwerianLindenbaumAlgebra Atom) :
    brouwerianLindenbaumLe (brouwerianLindenbaumInf x y) x := by
  obtain ⟨A, rfl⟩ := Quotient.exists_rep x
  obtain ⟨B, rfl⟩ := Quotient.exists_rep y
  exact hilbertAndE1Deriv (fun φ ψ => .andE1 φ ψ) (assumption_deriv List.mem_cons_self)

/-- `[A ∧ B] ≤ [B]` via andE2. -/
theorem brouwerianLindenbaumInf_le_right
    (x y : BrouwerianLindenbaumAlgebra Atom) :
    brouwerianLindenbaumLe (brouwerianLindenbaumInf x y) y := by
  obtain ⟨A, rfl⟩ := Quotient.exists_rep x
  obtain ⟨B, rfl⟩ := Quotient.exists_rep y
  exact hilbertAndE2Deriv (fun φ ψ => .andE2 φ ψ) (assumption_deriv List.mem_cons_self)

/-- `le_inf`: from `[A] ≤ [B]` and `[A] ≤ [C]` derive `[A] ≤ [B ∧ C]` via andI. -/
theorem brouwerianLindenbaumLe_inf
    (x y z : BrouwerianLindenbaumAlgebra Atom)
    (hxy : brouwerianLindenbaumLe x y) (hxz : brouwerianLindenbaumLe x z) :
    brouwerianLindenbaumLe x (brouwerianLindenbaumInf y z) := by
  obtain ⟨A, rfl⟩ := Quotient.exists_rep x
  obtain ⟨B, rfl⟩ := Quotient.exists_rep y
  obtain ⟨C, rfl⟩ := Quotient.exists_rep z
  exact hilbertAndIDeriv (fun φ ψ => .andI φ ψ) hxy hxz

/-- `le_top`: `[A] ≤ ⊤` where top is `[⊥ → ⊥]`. -/
theorem brouwerianLindenbaumLe_top
    (x : BrouwerianLindenbaumAlgebra Atom) :
    brouwerianLindenbaumLe x (brouwerianLindenbaumMk (bot.imp bot)) := by
  obtain ⟨A, rfl⟩ := Quotient.exists_rep x
  apply hilbertImpIDeriv ConjImpAxiom.mem_implyK ConjImpAxiom.mem_implyS
  exact assumption_deriv List.mem_cons_self

/-- The hardest lemma: Brouwerian deduction theorem.
`[A] ≤ [B → C]` iff `[A ∧ B] ≤ [C]`. -/
theorem brouwerianLindenbaumLe_himp_iff
    (x y z : BrouwerianLindenbaumAlgebra Atom) :
    brouwerianLindenbaumLe x (brouwerianLindenbaumHimp y z) ↔
    brouwerianLindenbaumLe (brouwerianLindenbaumInf x y) z := by
  obtain ⟨A, rfl⟩ := Quotient.exists_rep x
  obtain ⟨B, rfl⟩ := Quotient.exists_rep y
  obtain ⟨C, rfl⟩ := Quotient.exists_rep z
  constructor
  · -- Forward: [A] ⊢ B → C  →  [A ∧ B] ⊢ C
    intro hAimp
    have hAnd := assumption_deriv (Axioms := ConjImpAxiom) (Γ := [A.and B]) List.mem_cons_self
    have hA := hilbertAndE1Deriv (fun φ ψ => .andE1 φ ψ) hAnd
    have hB := hilbertAndE2Deriv (fun φ ψ => .andE2 φ ψ) hAnd
    -- [A ∧ B] ⊢ B → C: cut [A ∧ B] ⊢ A with [A] ⊢ B → C
    have hImp := hilbertCutSingletonDeriv ConjImpAxiom.mem_implyK ConjImpAxiom.mem_implyS
      hA hAimp
    exact hilbertImpEDeriv hImp hB
  · -- Backward: [A ∧ B] ⊢ C  →  [A] ⊢ B → C
    intro hAndC
    apply hilbertImpIDeriv ConjImpAxiom.mem_implyK ConjImpAxiom.mem_implyS
    -- context: B :: [A] = [B, A], need [B, A] ⊢ C
    have hA : Deriv ConjImpAxiom [B, A] A := assumption_deriv (by simp)
    have hB : Deriv ConjImpAxiom [B, A] B := assumption_deriv (by simp)
    have hAndAB := hilbertAndIDeriv (fun φ ψ => .andI φ ψ) hA hB
    exact hilbertCutListDeriv ConjImpAxiom.mem_implyK ConjImpAxiom.mem_implyS hAndAB hAndC

/-! ## BrouwerianSemilattice Instance -/

/-- The Brouwerian Lindenbaum algebra is a `BrouwerianSemilattice`.

This is the central algebraic result. All sub-instances (PartialOrder, SemilatticeInf,
OrderTop) are derived from `le_himp_iff`. -/
instance brouwerianLindenbaumBSL :
    BrouwerianSemilattice (BrouwerianLindenbaumAlgebra Atom) where
  le := brouwerianLindenbaumLe
  top := brouwerianLindenbaumMk (bot.imp bot)
  inf := brouwerianLindenbaumInf
  himp := brouwerianLindenbaumHimp
  le_refl := brouwerianLindenbaumLe_refl
  le_trans := fun x y z => brouwerianLindenbaumLe_trans x y z
  le_antisymm := fun x y => brouwerianLindenbaumLe_antisymm x y
  inf_le_left := brouwerianLindenbaumInf_le_left
  inf_le_right := brouwerianLindenbaumInf_le_right
  le_inf := fun x y z => brouwerianLindenbaumLe_inf x y z
  le_top := brouwerianLindenbaumLe_top
  le_himp_iff := fun x y z => brouwerianLindenbaumLe_himp_iff x y z

/-! ## API Simp Lemmas -/

/-- `[A] ≤ [B] ↔ Deriv ConjImpAxiom [A] B`. -/
@[simp]
theorem brouwerianLindenbaumMk_le_mk (A B : PL.Proposition Atom) :
    brouwerianLindenbaumMk A ≤ brouwerianLindenbaumMk B ↔
    Deriv ConjImpAxiom [A] B :=
  brouwerianLindenbaumLe_mk A B

/-- `[A ∧ B] = [A] ⊓ [B]`. -/
@[simp]
theorem brouwerianLindenbaumMk_inf (A B : PL.Proposition Atom) :
    brouwerianLindenbaumMk (A.and B) =
    brouwerianLindenbaumMk A ⊓ brouwerianLindenbaumMk B :=
  (brouwerianLindenbaumInf_mk A B).symm

/-- `[A → B] = [A] ⇨ [B]`. -/
@[simp]
theorem brouwerianLindenbaumMk_himp (A B : PL.Proposition Atom) :
    brouwerianLindenbaumMk (A.imp B) =
    brouwerianLindenbaumMk A ⇨ brouwerianLindenbaumMk B :=
  (brouwerianLindenbaumHimp_mk A B).symm

/-- Top in the Brouwerian Lindenbaum algebra is `[⊥ → ⊥]`. -/
theorem brouwerianLindenbaumTop :
    (⊤ : BrouwerianLindenbaumAlgebra Atom) =
    brouwerianLindenbaumMk (bot.imp bot) := rfl

/-! ## Top Characterization -/

/-- `[A] = ⊤` in the Brouwerian Lindenbaum algebra iff `A` is `ConjImpAxiom`-derivable
from the empty context. -/
theorem brouwerianLindenbaumMk_eq_top_iff {A : PL.Proposition Atom} :
    brouwerianLindenbaumMk A = ⊤ ↔ Derivable ConjImpAxiom A := by
  rw [brouwerianLindenbaumTop]
  constructor
  · -- Forward: [A] = [⊥ → ⊥] → Derivable ConjImpAxiom A
    intro h
    have heq : ConjImpEquiv A (bot.imp bot) :=
      Quotient.exact h
    -- heq : ConjImpEquiv A (bot.imp bot), i.e., [A] ⊢ (bot → bot) ∧ [bot → bot] ⊢ A
    -- From heq.2 and Derivable (bot → bot), cut gives Derivable ConjImpAxiom A
    have hBotBot : Derivable (@ConjImpAxiom Atom) ((bot : PL.Proposition Atom).imp bot) := by
      apply hilbertImpIDeriv ConjImpAxiom.mem_implyK ConjImpAxiom.mem_implyS
      exact assumption_deriv List.mem_cons_self
    exact hilbertCutListDeriv ConjImpAxiom.mem_implyK ConjImpAxiom.mem_implyS hBotBot heq.2
  · -- Backward: Derivable ConjImpAxiom A → [A] = [⊥ → ⊥]
    intro hA
    apply Quotient.sound
    constructor
    · -- [A] ⊢ ⊥ → ⊥: use impI on [bot, A] ⊢ bot (assumption)
      apply hilbertImpIDeriv ConjImpAxiom.mem_implyK ConjImpAxiom.mem_implyS
      exact assumption_deriv (by simp)
    · -- [⊥ → ⊥] ⊢ A: weaken Derivable A to [⊥ → ⊥] ⊢ A
      exact weakening_deriv hA (fun _ h => nomatch h)

/-! ## Canonical Valuation and Truth Lemma -/

/-- The canonical variable assignment into the Brouwerian Lindenbaum algebra:
sends each atom `x` to its equivalence class `[x]`. -/
def brouwerianCanonicalV :
    Atom → BrouwerianLindenbaumAlgebra Atom :=
  fun x => brouwerianLindenbaumMk (.atom x)

/-- **Truth Lemma** (restricted to `IsOrBotFree`): evaluating an or-bot-free proposition under
the canonical valuation gives exactly its equivalence class.

`BrouwerianEvaluate brouwerianCanonicalV A = [A]` for `IsOrBotFree` formulas.

The restriction is necessary because `BrouwerianEvaluate` maps `bot` and `or` to `⊤`,
but `[bot]` and `[or a b]` are not the top element in the Lindenbaum algebra (since
`ConjImpAxiom` has no EFQ axiom). -/
theorem brouwerianCanonicalV_spec (A : PL.Proposition Atom)
    (hA : A.IsOrBotFree = true) :
    BrouwerianEvaluate brouwerianCanonicalV A =
    brouwerianLindenbaumMk A := by
  induction A with
  | atom x => rfl
  | bot => simp [Proposition.IsOrBotFree] at hA
  | imp a b iha ihb =>
    simp only [Proposition.IsOrBotFree, Bool.and_eq_true] at hA
    simp only [BrouwerianEvaluate, iha hA.1, ihb hA.2, brouwerianLindenbaumMk_himp]
  | and a b iha ihb =>
    simp only [Proposition.IsOrBotFree, Bool.and_eq_true] at hA
    simp only [BrouwerianEvaluate, iha hA.1, ihb hA.2, brouwerianLindenbaumMk_inf]
  | or _ _ _ _ => simp [Proposition.IsOrBotFree] at hA

/-! ## Completeness Theorem -/

/-- **Brouwerian Completeness for IPL⟨∧,→,⊤⟩** (restricted to `IsOrBotFree` formulas):
if an or-bot-free formula is valid in every Brouwerian semilattice, then it is
`ConjImpAxiom`-derivable.

The restriction to `IsOrBotFree` is necessary: `bot` is vacuously Brouwerian-valid
(since `BrouwerianEvaluate v bot = ⊤` by definition) but not derivable in `ConjImpAxiom`
(no EFQ axiom is available). -/
theorem conjImp_brouwerian_complete {Atom : Type u} {φ : PL.Proposition Atom}
    (hfrag : φ.IsOrBotFree = true)
    (h : BrouwerianValid.{u, u} φ) :
    Derivable ConjImpAxiom φ := by
  -- Instantiate BrouwerianValid at the Brouwerian Lindenbaum algebra
  have hLind : BrouwerianEvaluate brouwerianCanonicalV φ = ⊤ :=
    h (BrouwerianLindenbaumAlgebra Atom) brouwerianCanonicalV
  -- Apply the truth lemma (valid since φ is IsOrBotFree)
  rw [brouwerianCanonicalV_spec φ hfrag] at hLind
  -- Extract derivability via mk_eq_top_iff
  exact brouwerianLindenbaumMk_eq_top_iff.mp hLind

/-- **Brouwerian Biconditional for IPL⟨∧,→,⊤⟩**: For or-bot-free formulas, derivability and
Brouwerian validity coincide. -/
theorem conjImp_brouwerian_iff {Atom : Type u} {φ : PL.Proposition Atom}
    (hfrag : φ.IsOrBotFree = true) :
    Derivable ConjImpAxiom φ ↔ BrouwerianValid.{u, u} φ :=
  ⟨conjImp_brouwerian_soundness_derivable,
   conjImp_brouwerian_complete hfrag⟩

end Cslib.Logic.PL

end

end
