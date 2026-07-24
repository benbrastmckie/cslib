/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Propositional.Defs
public import Mathlib.Data.Fintype.Pi

/-! # Bivalent and Boolean Evaluators for Propositional Logic

This module defines both the `Prop`-valued bivalent semantics and the computable Boolean
evaluation function for propositional logic.

## Main Definitions

- `Valuation`: A (bivalent) propositional valuation assigns a truth value to each atom.
- `Evaluate`: Evaluate a proposition under a valuation (recursive, using `Prop` values).
- `Tautology`: A proposition is a tautology iff it is true under every valuation.
- `BoolValuation`: A Boolean propositional valuation assigns a `Bool` to each atom.
- `BoolEvaluate`: Evaluate a proposition under a Boolean valuation, returning `Bool`.

## Main Results

- `BoolEvaluate_eq_iff`: Bridge lemma connecting `BoolEvaluate v φ = true` to
  `Evaluate (fun a => v a = true) φ`, enabling decidable evaluation.
- `instDecidableBoolEvaluate`: Decidability of `Evaluate` under Boolean valuations.

## Design Notes

`BoolEvaluate` exists alongside `Evaluate` because DPLL/SAT procedures need computable
`Bool` evaluation, while canonical model construction in strong completeness requires `Prop`
(set membership `fun p => p ∈ S` is not decidable in general). The bridge lemma connects
the two worlds: `Bool` computation to `Prop` metatheory.

`BoolEvaluate` and `instDecidableTautology` are the canonical computable DPLL/SAT decision
path for classical propositional logic. A future DPLL/Tseitin/CNF procedure should refine
these two declarations and reuse this module's own direct `Bool ↔ Prop` bridge
(`BoolEvaluate_eq_iff`, `Evaluate_eq_BoolEvaluate`, `tautology_iff_boolEvaluate_true`, all
defined above) rather than re-deriving it.

See also `Semantics/Algebra/Bridge.lean` for an algebraic reformulation of the
`Evaluate` / `BoolEvaluate` / `AlgEvaluate` correspondence; it is an independent, self-contained
development with no in-tree consumer, not the canonical bridge for future work to route through.

## References

* [A. Chagrov, M. Zakharyaschev, *Modal Logic*][ChagrovZakharyaschev1997], Section 1.2
-/

@[expose] public section

namespace Cslib.Logic.PL

variable {Atom : Type*}

/-! ## Prop-Valued Bivalent Semantics -/

/-- A (bivalent) propositional valuation assigns a truth value to each atom. -/
abbrev Valuation (Atom : Type*) := Atom → Prop

/-- Evaluate a proposition under a valuation.

This is the propositional specialization of modal `Satisfies`, without the box case. -/
def Evaluate (v : Valuation Atom) : PL.Proposition Atom → Prop
  | .atom x => v x
  | .bot => False
  | .imp a b => Evaluate v a → Evaluate v b
  | .and a b => Evaluate v a ∧ Evaluate v b
  | .or a b => Evaluate v a ∨ Evaluate v b

@[simp] theorem Evaluate_atom (v : Valuation Atom) (x : Atom) :
    Evaluate v (.atom x) = v x := rfl

@[simp] theorem Evaluate_bot (v : Valuation Atom) :
    Evaluate v (.bot) = False := rfl

@[simp] theorem Evaluate_imp (v : Valuation Atom) (a b : PL.Proposition Atom) :
    Evaluate v (.imp a b) = (Evaluate v a → Evaluate v b) := rfl

@[simp] theorem Evaluate_and (v : Valuation Atom) (a b : PL.Proposition Atom) :
    Evaluate v (.and a b) = (Evaluate v a ∧ Evaluate v b) := rfl

@[simp] theorem Evaluate_or (v : Valuation Atom) (a b : PL.Proposition Atom) :
    Evaluate v (.or a b) = (Evaluate v a ∨ Evaluate v b) := rfl

/-- A proposition is a tautology iff it is true under every valuation. -/
def Tautology (φ : PL.Proposition Atom) : Prop :=
  ∀ (v : Valuation Atom), Evaluate v φ

/-! ## Boolean Evaluation -/

/-- A Boolean propositional valuation assigns a `Bool` value to each atom. -/
abbrev BoolValuation (Atom : Type*) := Atom → Bool

/-- Computable Boolean evaluation of a proposition; mirrors `Evaluate` with `Bool` instead of
`Prop`. Use `BoolEvaluate_eq_iff` to connect results to `Evaluate`. -/
def BoolEvaluate (v : BoolValuation Atom) : PL.Proposition Atom → Bool
  | .atom x => v x
  | .bot => false
  | .imp a b => !BoolEvaluate v a || BoolEvaluate v b
  | .and a b => BoolEvaluate v a && BoolEvaluate v b
  | .or a b => BoolEvaluate v a || BoolEvaluate v b

@[simp] theorem BoolEvaluate_atom (v : BoolValuation Atom) (x : Atom) :
    BoolEvaluate v (.atom x) = v x := rfl

@[simp] theorem BoolEvaluate_bot (v : BoolValuation Atom) :
    BoolEvaluate v (.bot) = false := rfl

@[simp] theorem BoolEvaluate_imp (v : BoolValuation Atom) (a b : PL.Proposition Atom) :
    BoolEvaluate v (.imp a b) = (!BoolEvaluate v a || BoolEvaluate v b) := rfl

@[simp] theorem BoolEvaluate_and (v : BoolValuation Atom) (a b : PL.Proposition Atom) :
    BoolEvaluate v (.and a b) = (BoolEvaluate v a && BoolEvaluate v b) := rfl

@[simp] theorem BoolEvaluate_or (v : BoolValuation Atom) (a b : PL.Proposition Atom) :
    BoolEvaluate v (.or a b) = (BoolEvaluate v a || BoolEvaluate v b) := rfl

/-- Bridge lemma: `BoolEvaluate v φ = true` iff `Evaluate (fun a => v a = true) φ`.
The `imp` case uses `cases` on `Bool` since `!a || b = true ↔ (a = true → b = true)`
is not automatic from `simp`. -/
theorem BoolEvaluate_eq_iff (v : BoolValuation Atom) (φ : PL.Proposition Atom) :
    BoolEvaluate v φ = true ↔ Evaluate (fun a => v a = true) φ := by
  induction φ with
  | atom x => simp [BoolEvaluate, Evaluate]
  | bot => simp [BoolEvaluate, Evaluate]
  | imp a b iha ihb =>
    simp only [BoolEvaluate, Evaluate_imp, ← iha, ← ihb]
    cases BoolEvaluate v a <;> cases BoolEvaluate v b <;> simp
  | and a b iha ihb => simp [BoolEvaluate, Evaluate, iha, ihb]
  | or a b iha ihb => simp [BoolEvaluate, Evaluate, iha, ihb]

/-- Negation form of the bridge: `BoolEvaluate v φ = false` iff
`¬ Evaluate (fun a => v a = true) φ`. -/
theorem BoolEvaluate_eq_false_iff (v : BoolValuation Atom) (φ : PL.Proposition Atom) :
    BoolEvaluate v φ = false ↔ ¬Evaluate (fun a => v a = true) φ := by
  rw [← BoolEvaluate_eq_iff]
  cases BoolEvaluate v φ <;> simp

/-- Every propositional valuation with decidable atoms factors through `BoolEvaluate`. -/
theorem Evaluate_eq_BoolEvaluate (v : Valuation Atom) [∀ a, Decidable (v a)]
    (φ : PL.Proposition Atom) :
    Evaluate v φ ↔ BoolEvaluate (fun a => decide (v a)) φ = true := by
  rw [BoolEvaluate_eq_iff]
  induction φ with
  | atom x => simp [Evaluate, decide_eq_true_eq]
  | bot => simp [Evaluate]
  | imp a b iha ihb => simp [Evaluate, iha, ihb]
  | and a b iha ihb => simp [Evaluate, iha, ihb]
  | or a b iha ihb => simp [Evaluate, iha, ihb]

/-- `Evaluate` under a Boolean valuation is decidable, via `BoolEvaluate_eq_iff`. -/
instance instDecidableBoolEvaluate (v : BoolValuation Atom) (φ : PL.Proposition Atom) :
    Decidable (Evaluate (fun a => v a = true) φ) :=
  decidable_of_iff _ (BoolEvaluate_eq_iff v φ)

/-! ## Decidability of Tautology -/

/-- Bridge lemma: `Tautology φ` iff `BoolEvaluate v φ = true` for all Boolean valuations.

The forward direction applies `Tautology` to the Boolean-induced valuation `fun a => v a = true`.
The backward direction uses `Evaluate_eq_BoolEvaluate` to reduce any classical valuation
to a Boolean one, which requires `[∀ a, Decidable (v a)]`; we satisfy this via classical choice. -/
theorem tautology_iff_boolEvaluate_true (φ : PL.Proposition Atom) :
    Tautology φ ↔ ∀ (v : BoolValuation Atom), BoolEvaluate v φ = true := by
  constructor
  · intro hT v
    rw [BoolEvaluate_eq_iff]
    exact hT (fun a => v a = true)
  · intro hB v
    -- Use classical decidability to convert any valuation to a Boolean one
    haveI : ∀ a, Decidable (v a) := fun a => Classical.propDecidable (v a)
    rw [Evaluate_eq_BoolEvaluate v φ]
    exact hB (fun a => decide (v a))

/-- `Tautology φ` is decidable when `Atom` is a `Fintype` with `DecidableEq`.

The decision procedure enumerates all `2^n` Boolean valuations (where `n = |Atom|`) and
checks whether `BoolEvaluate v φ = true` for all of them. This is constructive:
`BoolValuation Atom = Atom → Bool` is a `Fintype` via `Pi.instFintype` (which requires
`DecidableEq Atom` to build the enumeration), and `BoolEvaluate` is computable. -/
instance instDecidableTautology [Fintype Atom] [DecidableEq Atom] (φ : PL.Proposition Atom) :
    Decidable (Tautology φ) :=
  decidable_of_iff (∀ v : BoolValuation Atom, BoolEvaluate v φ = true)
    (tautology_iff_boolEvaluate_true φ).symm

end Cslib.Logic.PL
