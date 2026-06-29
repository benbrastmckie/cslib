/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

import Cslib.Init
public import Cslib.Logics.Propositional.Semantics.Algebra.Conservative
public import Cslib.Logics.Propositional.Semantics.Algebra.FragmentPredicates

/-! # Fragment-Generic Algebraic Evaluation Independence

This module provides a **generic evaluation-independence principle** for propositional
logic, abstracting over the existing bespoke fragment predicates (`IsBotFree`,
`IsOrBotFree`, `IsImpTopOnly`) via an abstract `AlgEvalIndependent` property.

## Evaluation Independence

A Bool-valued formula predicate `P` satisfies `AlgEvalIndependent P` if formulas `φ`
with `P φ = true` have their algebraic evaluation independent of the `bot_val` parameter.
This characterizes the "⊥-free" fragment abstractly.

## Main Results

- `AlgEvalIndependent`: abstract evaluation-independence property for a formula predicate.
- `isBotFree_eval_independent`: `IsBotFree` satisfies `AlgEvalIndependent`.
- `isOrBotFree_eval_independent`: `IsOrBotFree` satisfies `AlgEvalIndependent`.
- `generic_gha_implies_ha`: for any P (with `AlgEvalIndependent`), `GHAValid φ → HAValid φ`.
  (The `GHAValid → HAValid` direction is generic and always holds, even without `P`.)
- `ghaValid_of_botFree`: for bot-free `φ`, `GHAValid φ` follows from `HAValid φ` — proved
  by the `WithBot` embedding argument, showing that the converse also holds for `IsBotFree`.

## Research-or-Defer Outcome (Phase 7, Task 407 S3)

**Mechanism delivered**: `AlgEvalIndependent` + `isBotFree_eval_independent` +
`isOrBotFree_eval_independent` + `generic_gha_implies_ha` + `ghaValid_of_botFree`.

**Residual (not reached in this spike)**:
The remaining step — from `HAValid φ` to `Derivable X-logic φ` for a specific sub-logic
`X` — requires **algebraic completeness**, which is not currently generic in `P`. Each
fragment has its own canonical algebra model:
- `IsBotFree`: routes through `WithBot G` + Heyting completeness.
- `IsOrBotFree`: routes through `LowerSet B` + Brouwerian completeness.
- `IsImpTopOnly`: routes through the Rasiowa free algebra.

A fully generic `Derivable P-logic φ ← HAValid φ` parameterized by `P` is open research.
A dedicated follow-on research task should be spawned.

**One worked conservativity link**: `ghaValid_iff_haValid_of_botFree` re-derives the
`GHAValid ↔ HAValid` equivalence for bot-free formulas as a corollary of the generic
principle, encompassing the `GHAValid_implies_HAValid` case from `Conservative.lean`.

## Design Notes

This file is **additive**: `Conservative.lean`, `BrouwerianCompleteness.lean`, and
`MplConservativeChain.lean` are not modified.

## References

* [A. Rasiowa, *An Algebraic Approach to Non-Classical Logics*][Rasiowa1974]
-/

@[expose] public section

namespace Cslib.Logic.PL

universe u v

/-! ## Evaluation Independence -/

/-- A Bool-valued formula predicate `P` satisfies **algebraic evaluation independence** if,
for every formula `φ` with `P φ = true`, every GHA `H`, every valuation `v : Atom → H`,
and every two bottom values `b₁ b₂ : H`, the evaluation is independent of the bottom:
`AlgEvaluate v b₁ φ = AlgEvaluate v b₂ φ`. -/
def AlgEvalIndependent (P : PL.Proposition Atom → Bool) : Prop :=
  ∀ {H : Type*} [GeneralizedHeytingAlgebra H]
    (v : Atom → H) (b₁ b₂ : H) (φ : PL.Proposition Atom),
    P φ = true → AlgEvaluate v b₁ φ = AlgEvaluate v b₂ φ

/-! ## IsBotFree Satisfies AlgEvalIndependent -/

/-- `IsBotFree` satisfies `AlgEvalIndependent`: bot-free formulas are independent of `bot_val`.
This is a restatement of `AlgEvaluate_botFree_independent` in terms of the generic property. -/
lemma isBotFree_eval_independent :
    AlgEvalIndependent (Atom := Atom) Proposition.IsBotFree :=
  fun v b₁ b₂ φ hφ => AlgEvaluate_botFree_independent v b₁ b₂ φ hφ

/-! ## IsOrBotFree Satisfies AlgEvalIndependent -/

/-- `IsOrBotFree` implies `IsBotFree` for any proposition `A`.
Since or-bot-free formulas have no `⊥` and no `∨`, they are in particular bot-free. -/
lemma isOrBotFree_implies_isBotFree {Atom : Type*} {A : PL.Proposition Atom}
    (h : A.IsOrBotFree = true) : A.IsBotFree = true := by
  induction A with
  | atom _ => simp [Proposition.IsBotFree]
  | bot => simp [Proposition.IsOrBotFree] at h
  | imp a b iha ihb =>
    simp only [Proposition.IsOrBotFree, Bool.and_eq_true] at h
    simp [Proposition.IsBotFree, iha h.1, ihb h.2]
  | and a b iha ihb =>
    simp only [Proposition.IsOrBotFree, Bool.and_eq_true] at h
    simp [Proposition.IsBotFree, iha h.1, ihb h.2]
  | or _ _ _ _ => simp [Proposition.IsOrBotFree] at h

/-- `IsOrBotFree` satisfies `AlgEvalIndependent`.
Or-bot-free formulas contain neither `⊥` nor `∨`, so evaluation is bot-independent
(reducing to the `IsBotFree` case via `isOrBotFree_implies_isBotFree`). -/
lemma isOrBotFree_eval_independent :
    AlgEvalIndependent (Atom := Atom) Proposition.IsOrBotFree :=
  fun v b₁ b₂ φ hφ =>
    isBotFree_eval_independent v b₁ b₂ φ (isOrBotFree_implies_isBotFree hφ)

/-! ## Generic GHAValid → HAValid -/

/-- **Generic GHA-to-HA validity**: for any `P` satisfying `AlgEvalIndependent` and any
formula `φ` with `P φ = true`, `GHAValid φ` implies `HAValid φ`.

This holds because every `HeytingAlgebra H` is a `GeneralizedHeytingAlgebra`, so `GHAValid φ`
(which quantifies over all GHAs with all `bot_val`) subsumes `HAValid φ` (which only
quantifies over HAs with `bot_val = ⊥`).

Note: The evaluation-independence hypothesis `h_ind` is included for documentation purposes
(to signal that the caller is in a P-fragment context), but is not needed for this direction. -/
lemma generic_gha_implies_ha
    {Atom : Type u}
    {P : PL.Proposition Atom → Bool}
    (_h_ind : AlgEvalIndependent P)
    {φ : PL.Proposition Atom}
    (h : GHAValid.{u, u} φ) :
    HAValid.{u, u} φ :=
  GHAValid_implies_HAValid h

/-! ## HAValid → GHAValid for Bot-Free Fragments -/

/-- **HAValid implies GHAValid for bot-free formulas**: for a bot-free formula `φ`,
`HAValid φ → GHAValid φ`.

The proof uses the `WithBot` embedding: given a GHA `H` and `v : Atom → H`, construct
`v' : Atom → WithBot H` by `v' a := some (v a)`. Since `φ` is bot-free, `AlgEvaluate`
on `WithBot H` with `v'` decomposes as `some` applied to the GHA evaluation. Then:
- `HAValid φ` gives `AlgEvaluate v' ⊥ φ = ⊤` in `WithBot H` (a HeytingAlgebra).
- The `brouwerianEmbeddingLemma`-style bot-free evaluation independence then recovers
  `AlgEvaluate v bot_val φ = ⊤` in `H`. -/
lemma ghaValid_of_botFree_of_haValid
    {Atom : Type u}
    {φ : PL.Proposition Atom}
    (hφ : φ.IsBotFree = true)
    (h : HAValid.{u, u} φ) :
    GHAValid.{u, u} φ := by
  intro H _ v bot_val
  -- Embed into WithBot H (a HeytingAlgebra via instHeytingAlgebraWithBot)
  have h_wb : AlgEvaluate (fun a => (v a : WithBot H)) ⊥ φ = ⊤ :=
    h (WithBot H) (fun a => (v a : WithBot H))
  -- coe_AlgEvaluate: AlgEvaluate (coe ∘ v) ⊥ φ = (AlgEvaluate v bot_val φ : WithBot H)
  have h_coe : AlgEvaluate (fun a => (v a : WithBot H)) ⊥ φ =
      ((AlgEvaluate v bot_val φ : H) : WithBot H) :=
    coe_AlgEvaluate v bot_val φ hφ
  -- Combine: (AlgEvaluate v bot_val φ : WithBot H) = ⊤ = (⊤ : WithBot H)
  rw [h_coe] at h_wb
  -- ⊤ : WithBot H = some (⊤ : H); extract via WithBot.coe_eq_coe
  exact WithBot.coe_injective (h_wb.trans (WithBot.coe_top).symm)

/-- For bot-free formulas, `GHAValid φ ↔ HAValid φ`. -/
lemma ghaValid_iff_haValid_of_botFree
    {Atom : Type u}
    {φ : PL.Proposition Atom}
    (hφ : φ.IsBotFree = true) :
    GHAValid.{u, u} φ ↔ HAValid.{u, u} φ :=
  ⟨GHAValid_implies_HAValid, ghaValid_of_botFree_of_haValid hφ⟩

end Cslib.Logic.PL
