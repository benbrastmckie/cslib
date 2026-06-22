/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Propositional.Semantics.Algebra.Completeness
public import Cslib.Logics.Propositional.NaturalDeduction.Basic
public import Mathlib.Order.Heyting.Regular

/-! # Glivenko's Theorem

This module proves Glivenko's theorem: if a formula `A` is derivable in CPL (classical
propositional logic), then `¬¬A` is derivable in IPL (intuitionistic propositional logic).

The proof uses the algebraic approach via the regular elements of a Heyting algebra.
The **regular elements** of a HeytingAlgebra `H` (those `a` satisfying `a^cc = a`) form a
BooleanAlgebra (Mathlib's `Heyting.Regular.instBooleanAlgebra`). By lifting a valuation
`v : Atom → H` to `v' : Atom → Heyting.Regular H` via the double-complement map, BA-validity
of `A` in `Heyting.Regular H` implies HA-validity of `¬¬A` in `H`.

The algebraic core is `glivenko_algebraic`, and the proof-theoretic result is `glivenko`.

## References

* [V. I. Glivenko, *Sur quelques points de la Logique de M. Brouwer*][Glivenko1929]
* [A. Rasiowa, *An Algebraic Approach to Non-Classical Logics*][Rasiowa1974]
-/

@[expose] public section

universe u

namespace Cslib.Logic.PL

open Proposition Theory Cslib.Logic.InferenceSystem Cslib.Logic.InferenceSystem.DerivableIn

/-! ## Embedding into Regular Subalgebra -/

/-- Regular-lifted evaluation: evaluate a formula using a valuation lifted to the Regular
subalgebra via the double-complement map `Heyting.Regular.toRegular`. -/
private abbrev evalR {Atom : Type u} {alpha : Type u} [HeytingAlgebra alpha]
    (v : Atom → alpha) (A : Proposition Atom) : Heyting.Regular alpha :=
  AlgEvaluate (fun x => Heyting.Regular.toRegular (v x)) ⊥ A

/-- Embedding lemma: evaluation in `Heyting.Regular alpha` gives the double complement of
evaluation in `alpha`. That is, `(evalR v A).val = (AlgEvaluate v ⊥ A)^cc`.

The proof is by structural induction on `A`:
- **atom**: `toRegular x = (x^cc, ...)`, so `.val = x^cc = x^cc`. ✓
- **bot**: `Heyting.Regular.coe_bot` gives `⊥.val = ⊥`, and `⊥^cc = ⊥`. ✓
- **imp**: `coe_himp` gives `(a ⇨ b).val = a.val ⇨ b.val`; apply `compl_compl_himp_distrib`. ✓
- **and**: `coe_inf` gives `(a ⊓ b).val = a.val ⊓ b.val`; apply `compl_compl_inf_distrib`. ✓
- **or**: `coe_sup` gives `(a ⊔ b).val = (a.val ⊔ b.val)^cc`; reduce using `isRegular_compl`. ✓ -/
private theorem eval_regular_val
    {Atom : Type u} {alpha : Type u} [HeytingAlgebra alpha]
    (v : Atom → alpha) (A : Proposition Atom) :
    (evalR v A).val = (AlgEvaluate v (⊥ : alpha) A)ᶜᶜ := by
  induction A with
  | atom x => rfl
  | bot => simp [evalR, AlgEvaluate, compl_bot, compl_top]
  | imp a b iha ihb =>
    change (evalR v a ⇨ evalR v b).val = _
    rw [Heyting.Regular.coe_himp, iha, ihb, AlgEvaluate_imp, compl_compl_himp_distrib]
  | and a b iha ihb =>
    change (evalR v a ⊓ evalR v b).val = _
    rw [Heyting.Regular.coe_inf, iha, ihb, AlgEvaluate_and, compl_compl_inf_distrib]
  | or a b iha ihb =>
    change (evalR v a ⊔ evalR v b).val = _
    rw [Heyting.Regular.coe_sup, iha, ihb, AlgEvaluate_or]
    congr 1
    rw [compl_sup, compl_sup, Heyting.isRegular_compl, Heyting.isRegular_compl]

/-! ## Algebraic Glivenko -/

/-- Algebraic Glivenko: if `A` is valid in every BooleanAlgebra, then `¬¬A` is valid in every
HeytingAlgebra.

The proof lifts the valuation `v : Atom → H` to `v' : Atom → Heyting.Regular H` via
`Heyting.Regular.toRegular`. Since `Heyting.Regular H` is a BooleanAlgebra, BA-validity gives
`evalR v A = ⊤`. Taking `.val` and applying `eval_regular_val` yields `(AlgEvaluate v ⊥ A)^cc = ⊤`.
Since `¬¬A` evaluates to `(AlgEvaluate v ⊥ A)^cc` (by `himp_bot`), the goal follows. -/
theorem glivenko_algebraic {Atom : Type u} {A : Proposition Atom}
    (h : ∀ (H : Type u) [BooleanAlgebra H] (v : Atom → H),
      AlgEvaluate v (⊥ : H) A = ⊤) :
    ∀ (H : Type u) [HeytingAlgebra H] (v : Atom → H),
      AlgEvaluate v (⊥ : H) (¬¬A) = ⊤ := by
  intro H _ v
  simp only [Proposition.neg, AlgEvaluate_imp, AlgEvaluate_bot]
  rw [HeytingAlgebra.himp_bot, HeytingAlgebra.himp_bot]
  have hBA := h (Heyting.Regular H) (fun x => Heyting.Regular.toRegular (v x))
  have := congr_arg Heyting.Regular.val hBA
  rw [eval_regular_val, Heyting.Regular.coe_top] at this
  exact this

/-! ## Theory Instances -/

variable {Atom : Type u} [DecidableEq Atom]

/-- `IPL ∪ CPL` is an intuitionistic theory: the efq axiom `⊥ → A` is in `IPL ⊆ IPL ∪ CPL`. -/
instance : IsIntuitionistic (IPL ∪ CPL : Theory Atom) where
  efq A := Set.mem_union_left _ (Set.mem_range.mpr ⟨A, rfl⟩)

/-- `IPL ∪ CPL` is a classical theory: the DNE axiom `¬¬A → A` is in `CPL ⊆ IPL ∪ CPL`. -/
instance : IsClassical (IPL ∪ CPL : Theory Atom) where
  dne A := Set.mem_union_right _ (Set.mem_range.mpr ⟨A, rfl⟩)

/-! ## Proof-Theoretic Glivenko -/

/-- Glivenko's theorem: if `A` is derivable in `IPL ∪ CPL` (classical propositional logic),
then `¬¬A` is derivable in IPL (intuitionistic propositional logic).

The proof uses algebraic completeness:
1. Convert the CPL derivability hypothesis via `alg_complete_classical` to BA-validity
   (with the theory hypothesis that `IPL ∪ CPL` axioms evaluate to `⊤`).
2. Apply `glivenko_algebraic` to get HA-validity of `¬¬A`.
3. Convert back via `IPL.alg_complete`.

The theory hypothesis for `IPL ∪ CPL` is discharged by case analysis:
- `IPL` axioms `⊥ → C` evaluate to `⊤` by `simp [AlgEvaluate]`.
- `CPL` axioms `¬¬C → C` evaluate to `⊤` because in any `BooleanAlgebra`,
  `compl_compl` gives `C^cc = C`, so `(C^c ⇨ ⊥)^c ⇨ ⊥ ⇨ C = ⊤` reduces to `C ⇨ C = ⊤`. -/
theorem glivenko {A : Proposition Atom}
    (h : DerivableIn (IPL ∪ CPL : Theory Atom) A) :
    DerivableIn (IPL : Theory Atom) (¬¬A) := by
  rw [alg_complete_classical] at h
  rw [IPL.alg_complete]
  intro H _ v
  apply glivenko_algebraic
  intro H' _ v'
  apply h v'
  intro B hB
  rcases (Set.mem_union B IPL CPL).mp hB with hIPL | hCPL
  · obtain ⟨C, rfl⟩ := Set.mem_range.mp hIPL
    simp [AlgEvaluate]
  · obtain ⟨C, rfl⟩ := Set.mem_range.mp hCPL
    simp only [Proposition.neg, AlgEvaluate_imp, AlgEvaluate_bot]
    rw [himp_eq_top_iff, HeytingAlgebra.himp_bot, HeytingAlgebra.himp_bot, compl_compl]

end Cslib.Logic.PL
