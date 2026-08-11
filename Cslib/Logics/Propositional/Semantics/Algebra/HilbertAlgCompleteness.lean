/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Propositional.Semantics.Algebra.Hilbert
public import Cslib.Logics.Propositional.ProofSystem.FragmentAxioms
public import Cslib.Logics.Propositional.Semantics.Algebra.HilbertLindenbaum

/-! # Hilbert Algebraic Soundness and Completeness for IPL⟨→,⊤⟩

This module proves soundness and completeness of the implicational fragment IPL⟨→,⊤⟩
with respect to Hilbert algebras.

**Soundness** (`imp_hilbert_soundness_derivable`): Every `ImpAxiom`-derivable formula
evaluates to `⊤` in every Hilbert algebra under every variable assignment.

**Completeness** (`imp_hilbert_completeness`): Restricted to `IsImpTopOnly` formulas, if a
formula evaluates to `⊤` in every Hilbert algebra then it is `ImpAxiom`-derivable. The
restriction is necessary because `HilbertEvaluate` maps `bot`, `and`, and `or` to `⊤`,
making those connectives vacuously valid, while `ImpAxiom` has no EFQ or conjunction
axioms.

## Proof Strategy

**Soundness** follows by case analysis on `ImpAxiom` constructors using
`HilbertAlgebra.himp_K` and `HilbertAlgebra.himp_S` (for the two constructors), then
induction on the derivation tree.

**Completeness** uses the **Hilbert Lindenbaum algebra**: the quotient of `Proposition
Atom` by `ImpAxiom`-derivational equivalence. This is strictly simpler than the
Brouwerian Lindenbaum algebra: no inf operation, no adjunction, just K and S axioms.

## Main Definitions

- `ImpEquiv`: the derivational equivalence relation `A ≈ B iff [A] ⊢ B ∧ [B] ⊢ A`
- `ImpLindenbaumAlgebra`: the quotient type `Quotient impPropositionSetoid`
- `impLindenbaumMk`: the quotient map
- `impCanonicalV`: the canonical variable assignment `x ↦ [atom x]`

## Main Results

- `imp_hilbert_soundness_derivable`: `Derivable ImpAxiom φ → HilbertValid φ`
- `impLindenbaumMk_eq_top_iff`: `[A] = ⊤ ↔ Derivable ImpAxiom A`
- `impCanonicalV_spec`: truth lemma for `IsImpTopOnly` formulas
- `imp_hilbert_completeness`: `IsImpTopOnly φ → HilbertValid φ → Derivable ImpAxiom φ`
- `imp_hilbert_iff`: `IsImpTopOnly φ → (Derivable ImpAxiom φ ↔ HilbertValid φ)`

## References

* [A. Rasiowa, *An Algebraic Approach to Non-Classical Logics*][Rasiowa1974]
-/

@[expose] public section

noncomputable section

namespace Cslib.Logic.PL

open Proposition

variable {Atom : Type*}

/-! ## Hilbert Soundness -/

/-- Every axiom of the implicational fragment is valid in every Hilbert algebra:
each `ImpAxiom` constructor evaluates to `⊤` under any assignment. -/
theorem imp_hilbert_axiom_sound {φ : PL.Proposition Atom}
    (h_ax : ImpAxiom φ) : HilbertValid φ := by
  intro H _ v
  cases h_ax with
  | implyK φ ψ =>
    -- implyK: φ → (ψ → φ); need ev(φ) ⇨ (ev(ψ) ⇨ ev(φ)) = ⊤
    simp only [HilbertEvaluate]
    exact HilbertAlgebra.himp_K (HilbertEvaluate v φ) (HilbertEvaluate v ψ)
  | implyS φ ψ χ =>
    -- implyS: (φ → (ψ → χ)) → ((φ → ψ) → (φ → χ))
    simp only [HilbertEvaluate]
    exact HilbertAlgebra.himp_S
      (HilbertEvaluate v φ) (HilbertEvaluate v ψ) (HilbertEvaluate v χ)

/-- Soundness at the derivation tree level: if `Γ ⊢ φ` via `ImpAxiom` and every formula
in `Γ` evaluates to `⊤`, then `φ` evaluates to `⊤` in every Hilbert algebra. -/
theorem imp_hilbert_soundness
    {Γ : List (PL.Proposition Atom)} {φ : PL.Proposition Atom}
    (d : DerivationTree ImpAxiom Γ φ)
    {H : Type*} [HilbertAlgebra H]
    (v : Atom → H)
    (h_ctx : ∀ ψ, ψ ∈ Γ → HilbertEvaluate v ψ = ⊤) :
    HilbertEvaluate v φ = ⊤ := by
  match d with
  | .ax _ ψ h_ax => exact imp_hilbert_axiom_sound h_ax H v
  | .assumption _ ψ h_mem => exact h_ctx ψ h_mem
  | .modusPonens _ ψ χ d₁ d₂ =>
    have h1 := imp_hilbert_soundness d₁ v h_ctx
    have h2 := imp_hilbert_soundness d₂ v h_ctx
    simp only [← Proposition.imp_def, HilbertEvaluate] at h1
    exact HilbertAlgebra.himp_mp h1 h2
  | .weakening _ _ ψ d' h_sub =>
    exact imp_hilbert_soundness d' v
      (fun x hx => h_ctx x (h_sub x hx))

/-- **Hilbert Soundness for IPL⟨→,⊤⟩**: Every `ImpAxiom`-derivable formula is
Hilbert-valid. -/
theorem imp_hilbert_soundness_derivable {φ : PL.Proposition Atom}
    (h : Derivable ImpAxiom φ) : HilbertValid φ := by
  intro H _ v
  obtain ⟨d⟩ := h
  exact imp_hilbert_soundness d v (fun _ h => nomatch h)

/-! ## Hilbert Lindenbaum Construction -/

/-- Two propositions are `ImpAxiom`-equivalent if each is derivable from the other
in a singleton context. This defines the quotient relation for the Hilbert Lindenbaum
algebra for the implicational fragment. -/
def ImpEquiv (A B : PL.Proposition Atom) : Prop :=
  Deriv ImpAxiom [A] B ∧ Deriv ImpAxiom [B] A

/-! ## Equivalence Relation Lemmas -/

/-- `ImpEquiv` is reflexive via the assumption rule. -/
theorem impEquiv_refl (A : PL.Proposition Atom) : ImpEquiv A A :=
  ⟨assumption_deriv List.mem_cons_self,
   assumption_deriv List.mem_cons_self⟩

/-- `ImpEquiv` is symmetric by swapping. -/
theorem impEquiv_symm {A B : PL.Proposition Atom}
    (h : ImpEquiv A B) : ImpEquiv B A :=
  ⟨h.2, h.1⟩

/-- `ImpEquiv` is transitive via the cut rule. -/
theorem impEquiv_trans {A B C : PL.Proposition Atom}
    (hAB : ImpEquiv A B) (hBC : ImpEquiv B C) : ImpEquiv A C :=
  ⟨hilbertCutSingletonDeriv ImpAxiom.mem_implyK ImpAxiom.mem_implyS hAB.1 hBC.1,
   hilbertCutSingletonDeriv ImpAxiom.mem_implyK ImpAxiom.mem_implyS hBC.2 hAB.2⟩

/-! ## Setoid, Quotient Type, and Quotient Map -/

/-- The `ImpAxiom`-equivalence setoid on `Proposition Atom`. -/
def impPropositionSetoid : Setoid (PL.Proposition Atom) where
  r := ImpEquiv
  iseqv := {
    refl := impEquiv_refl
    symm := impEquiv_symm
    trans := impEquiv_trans
  }

/-- The **Hilbert Lindenbaum algebra for IPL⟨→,⊤⟩**: the quotient of `Proposition Atom`
by `ImpAxiom`-derivational equivalence. This is the universal Hilbert algebra for the
implicational fragment. -/
def ImpLindenbaumAlgebra (Atom : Type*) : Type _ :=
  Quotient (@impPropositionSetoid Atom)

/-- The quotient map: sends `A` to its equivalence class `[A]` in the Hilbert
Lindenbaum algebra for the implicational fragment. -/
def impLindenbaumMk (A : PL.Proposition Atom) :
    ImpLindenbaumAlgebra Atom :=
  Quotient.mk impPropositionSetoid A

/-! ## Order on the Quotient -/

/-- `[A] ≤ [B]` iff `Deriv ImpAxiom [A] B`. Well-defined by congruence. -/
def impLindenbaumLe
    (x y : ImpLindenbaumAlgebra Atom) : Prop :=
  Quotient.liftOn₂ x y
    (fun A B => Deriv ImpAxiom [A] B)
    (fun _ _ _ _ hA hB => propext ⟨
      fun h =>
        hilbertCutSingletonDeriv ImpAxiom.mem_implyK ImpAxiom.mem_implyS
          (hilbertCutSingletonDeriv ImpAxiom.mem_implyK ImpAxiom.mem_implyS hA.2 h)
          hB.1,
      fun h =>
        hilbertCutSingletonDeriv ImpAxiom.mem_implyK ImpAxiom.mem_implyS
          (hilbertCutSingletonDeriv ImpAxiom.mem_implyK ImpAxiom.mem_implyS hA.1 h)
          hB.2⟩)

/-- The order on the Hilbert Lindenbaum algebra reduces to derivability on representatives. -/
@[simp]
theorem impLindenbaumLe_mk (A B : PL.Proposition Atom) :
    impLindenbaumLe (impLindenbaumMk A) (impLindenbaumMk B) ↔
    Deriv ImpAxiom [A] B :=
  Iff.rfl

/-! ## Congruence Lemma for Quotient Implication -/

/-- Imp-congruence: if `A ≈ A'` and `B ≈ B'` then `A → B ≈ A' → B'`. -/
theorem impEquivImpCongr {A A' B B' : PL.Proposition Atom}
    (hA : ImpEquiv A A') (hB : ImpEquiv B B') :
    ImpEquiv (A.imp B) (A'.imp B') := by
  constructor
  · -- [A → B] ⊢ A' → B'
    apply hilbertImpIDeriv ImpAxiom.mem_implyK ImpAxiom.mem_implyS
    -- context: A' :: [A → B], need [A', A → B] ⊢ B'
    have hAimp : Deriv ImpAxiom [A', A.imp B] (A.imp B) :=
      assumption_deriv (by simp)
    have hA_part : Deriv ImpAxiom [A', A.imp B] A :=
      hilbertWeakenSingleton hA.2
    have hB_part := hilbertImpEDeriv hAimp hA_part
    exact hilbertCutListDeriv ImpAxiom.mem_implyK ImpAxiom.mem_implyS hB_part hB.1
  · -- [A' → B'] ⊢ A → B
    apply hilbertImpIDeriv ImpAxiom.mem_implyK ImpAxiom.mem_implyS
    have hA'imp : Deriv ImpAxiom [A, A'.imp B'] (A'.imp B') :=
      assumption_deriv (by simp)
    have hA'_part : Deriv ImpAxiom [A, A'.imp B'] A' :=
      hilbertWeakenSingleton hA.1
    have hB'_part := hilbertImpEDeriv hA'imp hA'_part
    exact hilbertCutListDeriv ImpAxiom.mem_implyK ImpAxiom.mem_implyS hB'_part hB.2

/-! ## Implication Operation on the Quotient -/

/-- Hilbert implication: `[A] ⇨ [B] = [A → B]`. -/
def impLindenbaumHimp
    (x y : ImpLindenbaumAlgebra Atom) :
    ImpLindenbaumAlgebra Atom :=
  Quotient.lift₂
    (fun A B => impLindenbaumMk (A.imp B))
    (fun _ _ _ _ hA hB => Quotient.sound (impEquivImpCongr hA hB))
    x y

/-- `[A → B] = [A] ⇨ [B]`. -/
@[simp]
theorem impLindenbaumHimp_mk (A B : PL.Proposition Atom) :
    impLindenbaumHimp (impLindenbaumMk A) (impLindenbaumMk B) =
    impLindenbaumMk (A.imp B) := rfl

/-! ## HilbertAlgebra Axiom Lemmas -/

/-- Reflexivity: `[A] ≤ [A]` via the assumption rule. -/
theorem impLindenbaumLe_refl
    (x : ImpLindenbaumAlgebra Atom) :
    impLindenbaumLe x x := by
  obtain ⟨A, rfl⟩ := Quotient.exists_rep x
  exact assumption_deriv List.mem_cons_self

/-- Transitivity via cut. -/
theorem impLindenbaumLe_trans
    (x y z : ImpLindenbaumAlgebra Atom)
    (hxy : impLindenbaumLe x y) (hyz : impLindenbaumLe y z) :
    impLindenbaumLe x z := by
  obtain ⟨A, rfl⟩ := Quotient.exists_rep x
  obtain ⟨B, rfl⟩ := Quotient.exists_rep y
  obtain ⟨C, rfl⟩ := Quotient.exists_rep z
  exact hilbertCutSingletonDeriv ImpAxiom.mem_implyK ImpAxiom.mem_implyS hxy hyz

/-- Antisymmetry via `Quotient.sound`. -/
theorem impLindenbaumLe_antisymm
    (x y : ImpLindenbaumAlgebra Atom)
    (hxy : impLindenbaumLe x y) (hyx : impLindenbaumLe y x) :
    x = y := by
  obtain ⟨A, rfl⟩ := Quotient.exists_rep x
  obtain ⟨B, rfl⟩ := Quotient.exists_rep y
  exact Quotient.sound ⟨hxy, hyx⟩

/-- `le_top`: `[A] ≤ ⊤` where top is `[⊥ → ⊥]`. -/
theorem impLindenbaumLe_top
    (x : ImpLindenbaumAlgebra Atom) :
    impLindenbaumLe x (impLindenbaumMk (bot.imp bot)) := by
  obtain ⟨A, rfl⟩ := Quotient.exists_rep x
  apply hilbertImpIDeriv ImpAxiom.mem_implyK ImpAxiom.mem_implyS
  exact assumption_deriv List.mem_cons_self

/-- K axiom in the Lindenbaum algebra: `[A] ⇨ ([B] ⇨ [A]) = ⊤`. -/
theorem impLindenbaumHimp_K (A B : PL.Proposition Atom) :
    impLindenbaumHimp (impLindenbaumMk A)
      (impLindenbaumHimp (impLindenbaumMk B) (impLindenbaumMk A)) =
    impLindenbaumMk (bot.imp bot) := by
  simp only [impLindenbaumHimp_mk]
  apply Quotient.sound
  constructor
  · -- [A → (B → A)] ⊢ ⊥ → ⊥
    apply hilbertImpIDeriv ImpAxiom.mem_implyK ImpAxiom.mem_implyS
    exact assumption_deriv List.mem_cons_self
  · -- [⊥ → ⊥] ⊢ A → (B → A)
    exact weakening_deriv ⟨.ax [] _ (.implyK A B)⟩ (fun _ h => nomatch h)

/-- S axiom in the Lindenbaum algebra: the S combinator identity holds. -/
theorem impLindenbaumHimp_S (A B C : PL.Proposition Atom) :
    impLindenbaumHimp
      (impLindenbaumHimp (impLindenbaumMk A)
        (impLindenbaumHimp (impLindenbaumMk B) (impLindenbaumMk C)))
      (impLindenbaumHimp
        (impLindenbaumHimp (impLindenbaumMk A) (impLindenbaumMk B))
        (impLindenbaumHimp (impLindenbaumMk A) (impLindenbaumMk C))) =
    impLindenbaumMk (bot.imp bot) := by
  simp only [impLindenbaumHimp_mk]
  apply Quotient.sound
  constructor
  · -- [(A → B → C) → (A → B) → (A → C)] ⊢ ⊥ → ⊥
    apply hilbertImpIDeriv ImpAxiom.mem_implyK ImpAxiom.mem_implyS
    exact assumption_deriv List.mem_cons_self
  · -- [⊥ → ⊥] ⊢ (A → B → C) → (A → B) → (A → C)
    exact weakening_deriv ⟨.ax [] _ (.implyS A B C)⟩ (fun _ h => nomatch h)

/-- Self-implication in the Lindenbaum algebra: `[A] ⇨ [A] = ⊤`. -/
theorem impLindenbaumHimp_self (A : PL.Proposition Atom) :
    impLindenbaumHimp (impLindenbaumMk A) (impLindenbaumMk A) =
    impLindenbaumMk (bot.imp bot) := by
  simp only [impLindenbaumHimp_mk]
  apply Quotient.sound
  constructor
  · -- [A → A] ⊢ ⊥ → ⊥
    apply hilbertImpIDeriv ImpAxiom.mem_implyK ImpAxiom.mem_implyS
    exact assumption_deriv List.mem_cons_self
  · -- [⊥ → ⊥] ⊢ A → A
    have hAA : Deriv (@ImpAxiom Atom) [] (A.imp A) :=
      hilbertImpIDeriv ImpAxiom.mem_implyK ImpAxiom.mem_implyS
        (assumption_deriv List.mem_cons_self)
    exact weakening_deriv hAA (fun _ h => nomatch h)

/-! ## HilbertAlgebra Instance -/

/-- The Hilbert Lindenbaum algebra for `ImpAxiom` is a `HilbertAlgebra`.

This is the central algebraic result: the quotient of `Proposition Atom` by
`ImpAxiom`-derivational equivalence satisfies all four Hilbert algebra axioms. -/
instance impLindenbaumHA :
    HilbertAlgebra (ImpLindenbaumAlgebra Atom) where
  top := impLindenbaumMk (bot.imp bot)
  himp := impLindenbaumHimp
  himp_K x y := by
    obtain ⟨A, rfl⟩ := Quotient.exists_rep x
    obtain ⟨B, rfl⟩ := Quotient.exists_rep y
    exact impLindenbaumHimp_K A B
  himp_S x y z := by
    obtain ⟨A, rfl⟩ := Quotient.exists_rep x
    obtain ⟨B, rfl⟩ := Quotient.exists_rep y
    obtain ⟨C, rfl⟩ := Quotient.exists_rep z
    exact impLindenbaumHimp_S A B C
  himp_antisymm x y hxy hyx := by
    -- hxy : impLindenbaumHimp x y = ⊤, i.e., [A → B] = [⊥ → ⊥]
    -- hyx : impLindenbaumHimp y x = ⊤, i.e., [B → A] = [⊥ → ⊥]
    obtain ⟨A, rfl⟩ := Quotient.exists_rep x
    obtain ⟨B, rfl⟩ := Quotient.exists_rep y
    -- hxy : [A→B] = ⊤ = [⊥→⊥]; hyx : [B→A] = ⊤ = [⊥→⊥] (definitionally)
    have hAB : ImpEquiv (A.imp B) (bot.imp bot) :=
      Quotient.exact (hxy : impLindenbaumMk (A.imp B) = impLindenbaumMk (bot.imp bot))
    have hBA : ImpEquiv (B.imp A) (bot.imp bot) :=
      Quotient.exact (hyx : impLindenbaumMk (B.imp A) = impLindenbaumMk (bot.imp bot))
    have hBotBot : Derivable (@ImpAxiom Atom) ((bot : PL.Proposition Atom).imp bot) :=
      hilbertImpIDeriv ImpAxiom.mem_implyK ImpAxiom.mem_implyS
        (assumption_deriv List.mem_cons_self)
    have hDerAB : Derivable (@ImpAxiom Atom) (A.imp B) :=
      hilbertCutListDeriv ImpAxiom.mem_implyK ImpAxiom.mem_implyS hBotBot hAB.2
    have hDerBA : Derivable (@ImpAxiom Atom) (B.imp A) :=
      hilbertCutListDeriv ImpAxiom.mem_implyK ImpAxiom.mem_implyS hBotBot hBA.2
    apply Quotient.sound
    constructor
    · have hWeakAB : Deriv ImpAxiom [A] (A.imp B) :=
        weakening_deriv hDerAB (fun _ h => nomatch h)
      exact hilbertImpEDeriv hWeakAB (assumption_deriv List.mem_cons_self)
    · have hWeakBA : Deriv ImpAxiom [B] (B.imp A) :=
        weakening_deriv hDerBA (fun _ h => nomatch h)
      exact hilbertImpEDeriv hWeakBA (assumption_deriv List.mem_cons_self)
  himp_self x := by
    obtain ⟨A, rfl⟩ := Quotient.exists_rep x
    exact impLindenbaumHimp_self A

/-! ## API Simp Lemmas -/

/-- `[A] ≤ [B] ↔ Deriv ImpAxiom [A] B`.

Under the HilbertAlgebra order, `[A] ≤ [B]` iff `[A] ⇨ [B] = ⊤`, i.e.,
`[A → B] = [⊥ → ⊥]`. This is equivalent to `[A] ⊢ B` by cut and impI/impE. -/
@[simp]
theorem impLindenbaumMk_le_mk (A B : PL.Proposition Atom) :
    impLindenbaumMk A ≤ impLindenbaumMk B ↔
    Deriv ImpAxiom [A] B := by
  constructor
  · -- forward: [A] ≤ [B] → [A] ⊢ B
    -- In the HilbertAlgebra order: [A] ≤ [B] means [A] ⇨ [B] = ⊤ = [⊥→⊥]
    -- i.e., [A→B] = [⊥→⊥] (by impLindenbaumHimp_mk), so ImpEquiv (A.imp B) (bot.imp bot)
    intro hle
    have hEq : impLindenbaumMk (A.imp B) = impLindenbaumMk (bot.imp bot) := hle
    have heq : ImpEquiv (A.imp B) (bot.imp bot) := Quotient.exact hEq
    have hBotBot : Derivable (@ImpAxiom Atom) ((bot : PL.Proposition Atom).imp bot) :=
      hilbertImpIDeriv ImpAxiom.mem_implyK ImpAxiom.mem_implyS
        (assumption_deriv List.mem_cons_self)
    have hDerAB : Derivable (@ImpAxiom Atom) (A.imp B) :=
      hilbertCutListDeriv ImpAxiom.mem_implyK ImpAxiom.mem_implyS hBotBot heq.2
    have hABweak : Deriv ImpAxiom [A] (A.imp B) :=
      weakening_deriv hDerAB (fun _ h => nomatch h)
    exact hilbertImpEDeriv hABweak (assumption_deriv List.mem_cons_self)
  · -- backward: [A] ⊢ B → [A] ≤ [B]
    -- need: [A] ⇨ [B] = ⊤, i.e., [A→B] = [⊥→⊥]
    intro hAB
    change impLindenbaumMk (A.imp B) = impLindenbaumMk (bot.imp bot)
    apply Quotient.sound
    constructor
    · apply hilbertImpIDeriv ImpAxiom.mem_implyK ImpAxiom.mem_implyS
      exact assumption_deriv (by simp)
    · exact weakening_deriv
        (hilbertImpIDeriv ImpAxiom.mem_implyK ImpAxiom.mem_implyS hAB)
        (fun _ h => nomatch h)

/-- `[A → B] = [A] ⇨ [B]`. -/
@[simp]
theorem impLindenbaumMk_himp (A B : PL.Proposition Atom) :
    impLindenbaumMk (A.imp B) =
    impLindenbaumMk A ⇨ impLindenbaumMk B := rfl

/-- Top in the Hilbert Lindenbaum algebra is `[⊥ → ⊥]`. -/
@[simp]
theorem impLindenbaumTop :
    (⊤ : ImpLindenbaumAlgebra Atom) =
    impLindenbaumMk (bot.imp bot) := rfl

/-! ## Top Characterization -/

/-- `[A] = ⊤` in the Hilbert Lindenbaum algebra iff `A` is `ImpAxiom`-derivable
from the empty context. -/
theorem impLindenbaumMk_eq_top_iff {A : PL.Proposition Atom} :
    impLindenbaumMk A = ⊤ ↔ Derivable ImpAxiom A := by
  simp only [impLindenbaumTop]
  constructor
  · -- Forward: [A] = [⊥ → ⊥] → Derivable ImpAxiom A
    intro h
    have heq : ImpEquiv A (bot.imp bot) :=
      Quotient.exact h
    -- From heq.2 and Derivable (bot → bot), cut gives Derivable ImpAxiom A
    have hBotBot : Derivable (@ImpAxiom Atom) ((bot : PL.Proposition Atom).imp bot) :=
      hilbertImpIDeriv ImpAxiom.mem_implyK ImpAxiom.mem_implyS
        (assumption_deriv List.mem_cons_self)
    exact hilbertCutListDeriv ImpAxiom.mem_implyK ImpAxiom.mem_implyS hBotBot heq.2
  · -- Backward: Derivable ImpAxiom A → [A] = [⊥ → ⊥]
    intro hA
    apply Quotient.sound
    constructor
    · -- [A] ⊢ ⊥ → ⊥: use impI
      apply hilbertImpIDeriv ImpAxiom.mem_implyK ImpAxiom.mem_implyS
      exact assumption_deriv (by simp)
    · -- [⊥ → ⊥] ⊢ A: weaken Derivable A to [⊥ → ⊥] ⊢ A
      exact weakening_deriv hA (fun _ h => nomatch h)

/-! ## Canonical Valuation and Truth Lemma -/

/-- The canonical variable assignment into the Hilbert Lindenbaum algebra:
sends each atom `x` to its equivalence class `[x]`. -/
def impCanonicalV :
    Atom → ImpLindenbaumAlgebra Atom :=
  fun x => impLindenbaumMk (.atom x)

/-- **Truth Lemma** (restricted to `IsImpTopOnly`): evaluating an imp-top-only proposition
under the canonical valuation gives exactly its equivalence class.

`HilbertEvaluate impCanonicalV A = [A]` for `IsImpTopOnly` formulas.

The restriction is necessary because `HilbertEvaluate` maps `bot`, `and`, and `or` to
`⊤`, but `[bot]`, `[and a b]`, and `[or a b]` are not the top element in the Lindenbaum
algebra (since `ImpAxiom` has no EFQ or conjunction axioms). -/
theorem impCanonicalV_spec (A : PL.Proposition Atom)
    (hA : A.IsImpTopOnly = true) :
    HilbertEvaluate impCanonicalV A =
    impLindenbaumMk A := by
  induction A with
  | atom x => rfl
  | bot => simp [Proposition.IsImpTopOnly] at hA
  | imp a b iha ihb =>
    simp only [Proposition.IsImpTopOnly, Bool.and_eq_true] at hA
    simp only [HilbertEvaluate, iha hA.1, ihb hA.2, impLindenbaumMk_himp]
  | and _ _ _ _ => simp [Proposition.IsImpTopOnly] at hA
  | or _ _ _ _ => simp [Proposition.IsImpTopOnly] at hA

/-! ## Completeness Theorem -/

/-- **Hilbert Completeness for IPL⟨→,⊤⟩** (restricted to `IsImpTopOnly` formulas):
if an imp-top-only formula is valid in every Hilbert algebra, then it is
`ImpAxiom`-derivable.

The restriction to `IsImpTopOnly` is necessary: `bot` is vacuously Hilbert-valid
(since `HilbertEvaluate v bot = ⊤` by definition) but not derivable in `ImpAxiom`
(no EFQ axiom is available). -/
theorem imp_hilbert_completeness {Atom : Type u} {φ : PL.Proposition Atom}
    (hfrag : φ.IsImpTopOnly = true)
    (h : HilbertValid.{u, u} φ) :
    Derivable ImpAxiom φ := by
  -- Instantiate HilbertValid at the Hilbert Lindenbaum algebra
  have hLind : HilbertEvaluate impCanonicalV φ = ⊤ :=
    h (ImpLindenbaumAlgebra Atom) impCanonicalV
  -- Apply the truth lemma (valid since φ is IsImpTopOnly)
  rw [impCanonicalV_spec φ hfrag] at hLind
  -- Extract derivability via mk_eq_top_iff
  exact impLindenbaumMk_eq_top_iff.mp hLind

/-- **Hilbert Biconditional for IPL⟨→,⊤⟩**: For imp-top-only formulas, derivability and
Hilbert validity coincide. -/
theorem imp_hilbert_iff {Atom : Type u} {φ : PL.Proposition Atom}
    (hfrag : φ.IsImpTopOnly = true) :
    Derivable ImpAxiom φ ↔ HilbertValid.{u, u} φ :=
  ⟨imp_hilbert_soundness_derivable,
   imp_hilbert_completeness hfrag⟩

end Cslib.Logic.PL

end

end
