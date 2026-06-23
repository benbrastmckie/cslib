/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

import Cslib.Init

public import Cslib.Logics.Propositional.Semantics.Algebra.Brouwerian
public import Cslib.Logics.Propositional.Semantics.Algebra.FragmentPredicates
public import Mathlib.Order.UpperLower.Principal

/-! # Free Join Completion: Brouwerian Semilattice to Heyting Algebra

This module constructs a `HeytingAlgebra` from any `BrouwerianSemilattice` via the
**free join completion** — the principal downset embedding into `LowerSet B`.

Given a Brouwerian semilattice `B`, the type `LowerSet B` of downward-closed subsets already
carries a `HeytingAlgebra` instance in Mathlib (via `CompletelyDistribLattice`). The principal
downset map `LowerSet.Iic : B → LowerSet B` sending `a ↦ ↓a` preserves:
- `⊓`: `LowerSet.Iic (a ⊓ b) = LowerSet.Iic a ⊓ LowerSet.Iic b` (Mathlib)
- `⊤`: `LowerSet.Iic ⊤ = ⊤` (Mathlib)
- `⇨`: `LowerSet.Iic (a ⇨ b) = LowerSet.Iic a ⇨ LowerSet.Iic b` (proved here)

The main results are:
1. `iicHimp`: `LowerSet.Iic` preserves Heyting implication.
2. `iicEqTopIff`: `LowerSet.Iic x = ⊤ ↔ x = ⊤`.
3. `iicBrouwerianEvaluateEqAlgEvaluate`: commutation of `LowerSet.Iic` with evaluation
   on or-bot-free formulas.
4. `brouwerianEmbeddingLemma`: `BrouwerianEvaluate v φ = ⊤ ↔ AlgEvaluate (LowerSet.Iic ∘ v) ⊥ φ = ⊤`
   for or-bot-free formulas `φ`.

This embedding lemma is used to transfer Brouwerian semilattice validity to Heyting algebra
validity on the or-bot-free fragment, which is the key step in algebraic completeness proofs
for the `{⊓, ⇨, ⊤}` fragment.

## References

* [W. Nemitz, *Implicative semi-lattices*][Nemitz1965]
* [P. Köhler, *Brouwerian semilattices*][Kohler1981]
* [A. Rasiowa, *An Algebraic Approach to Non-Classical Logics*][Rasiowa1974]
-/

@[expose] public section

namespace Cslib.Logic.PL

variable {Atom B : Type*} [BrouwerianSemilattice B]

/-! ## Preservation of Heyting Implication -/

/-- The principal downset map `LowerSet.Iic` preserves Heyting implication.

The proof proceeds via `le_antisymm`:
- **Forward** (≤): Given `x ∈ ↓(a ⇨ b)`, i.e. `x ≤ a ⇨ b`, apply modus ponens on `LowerSet B`
  using `himp_inf_le`.
- **Backward** (≥): Given `x ∈ ↓a ⇨ ↓b`, use the adjunction on `B` to reduce to showing
  `x ⊓ a ≤ b`, which follows from modus ponens `himp_inf_le` on `LowerSet B`. -/
theorem iicHimp (a b : B) :
    LowerSet.Iic (a ⇨ b) = LowerSet.Iic a ⇨ LowerSet.Iic b := by
  apply le_antisymm
  · rw [le_himp_iff, ← LowerSet.Iic_inf]
    intro x hx
    exact LowerSet.mem_Iic_iff.mpr
      (le_trans (LowerSet.mem_Iic_iff.mp hx) BrouwerianSemilattice.himp_inf_le)
  · intro x hx
    refine LowerSet.mem_Iic_iff.mpr
      ((BrouwerianSemilattice.le_himp_iff x a b).mpr ?_)
    have hxa : x ⊓ a ∈ (LowerSet.Iic a ⇨ LowerSet.Iic b : LowerSet B) :=
      (LowerSet.Iic a ⇨ LowerSet.Iic b).lower inf_le_left hx
    have hxaMem : x ⊓ a ∈ LowerSet.Iic a :=
      LowerSet.mem_Iic_iff.mpr inf_le_right
    exact LowerSet.mem_Iic_iff.mp
      (himp_inf_le (α := LowerSet B) ⟨hxa, hxaMem⟩)

/-! ## Top Preservation -/

/-- `LowerSet.Iic x = ⊤` if and only if `x = ⊤`.

This follows from injectivity of `LowerSet.Iic` and the fact that `LowerSet.Iic ⊤ = ⊤`. -/
theorem iicEqTopIff {x : B} :
    LowerSet.Iic x = ⊤ ↔ x = ⊤ := by
  constructor
  · intro h
    exact LowerSet.Iic_injective (h.trans LowerSet.Iic_top.symm)
  · intro h
    rw [h, LowerSet.Iic_top]

/-! ## Commutation Lemma -/

/-- For or-bot-free formulas, `LowerSet.Iic` commutes with evaluation:
`AlgEvaluate (LowerSet.Iic ∘ v) ⊥ φ = LowerSet.Iic (BrouwerianEvaluate v φ)`.

The proof is by structural induction on `φ`:
- **atom**: both sides are `LowerSet.Iic (v x)` by definition.
- **bot**: excluded by `IsOrBotFree`.
- **imp**: apply `iicHimp` and the inductive hypothesis.
- **and**: apply `LowerSet.Iic_inf` and the inductive hypothesis.
- **or**: excluded by `IsOrBotFree`. -/
theorem iicBrouwerianEvaluateEqAlgEvaluate
    (v : Atom → B) (φ : Proposition Atom) (hφ : φ.IsOrBotFree = true) :
    AlgEvaluate (LowerSet.Iic ∘ v) (⊥ : LowerSet B) φ =
      LowerSet.Iic (BrouwerianEvaluate v φ) := by
  induction φ with
  | atom x => rfl
  | bot => simp [Proposition.IsOrBotFree] at hφ
  | imp a b iha ihb =>
    simp only [Proposition.IsOrBotFree, Bool.and_eq_true] at hφ
    simp only [AlgEvaluate_imp, BrouwerianEvaluate_imp, iha hφ.1, ihb hφ.2]
    exact (iicHimp _ _).symm
  | and a b iha ihb =>
    simp only [Proposition.IsOrBotFree, Bool.and_eq_true] at hφ
    simp only [AlgEvaluate_and, BrouwerianEvaluate_and, iha hφ.1, ihb hφ.2]
    exact (LowerSet.Iic_inf _ _).symm
  | or _ _ _ _ => simp [Proposition.IsOrBotFree] at hφ

/-! ## Embedding Lemma -/

/-- Embedding lemma: for or-bot-free formulas, Brouwerian validity is equivalent to validity
in the `LowerSet` Heyting algebra under the principal downset embedding.

`BrouwerianEvaluate v φ = ⊤ ↔ AlgEvaluate (LowerSet.Iic ∘ v) ⊥ φ = ⊤`

This is the key bridge between Brouwerian semilattice semantics and Heyting algebra semantics
on the `{⊓, ⇨, ⊤}` fragment. It follows directly from `iicBrouwerianEvaluateEqAlgEvaluate`
and injectivity of `LowerSet.Iic`. -/
theorem brouwerianEmbeddingLemma
    (v : Atom → B) (φ : Proposition Atom) (hφ : φ.IsOrBotFree = true) :
    BrouwerianEvaluate v φ = ⊤ ↔
      AlgEvaluate (LowerSet.Iic ∘ v) (⊥ : LowerSet B) φ = ⊤ := by
  rw [iicBrouwerianEvaluateEqAlgEvaluate v φ hφ]
  constructor
  · intro h; rw [h, LowerSet.Iic_top]
  · intro h; exact LowerSet.Iic_injective (h.trans LowerSet.Iic_top.symm)

end Cslib.Logic.PL
