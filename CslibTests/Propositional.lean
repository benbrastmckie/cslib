/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public meta import Cslib.Logics.Propositional.Semantics.Bool
public meta import Cslib.Logics.Propositional.Semantics.Algebra.HilbertCompleteness
public meta import Cslib.Logics.Propositional.Tableau.Classical.DecisionProcedure
public meta import Mathlib.Data.Fintype.Pi

/-! # Propositional Logic Tests

This file tests core propositional infrastructure:
- `BoolEvaluate` computable Boolean evaluation
- `Tautology` decidability via `instDecidableTautology`
- Soundness round-trip: `Tautology φ` implies `BoolEvaluate v φ = true` for all `v`

## Atom Type

We use `Bool` as a two-atom type. This gives `2^2 = 4` Boolean valuations
(each of the 4 functions `Bool → Bool`), making decidability tests fast.
`false` plays the role of atom p, `true` plays the role of atom q.
-/

namespace CslibTests.Propositional

open Cslib.Logic.PL

/-! ## BoolEvaluate Evaluation Tests -/

/-- Evaluating a positive atom under all-true valuation gives true. -/
theorem boolEvaluate_atom_allTrue :
    BoolEvaluate (Atom := Bool) (fun _ => true) (.atom false) = true := by decide

/-- Evaluating `⊥` under any valuation gives false. -/
theorem boolEvaluate_bot_false :
    BoolEvaluate (Atom := Bool) (fun _ => true) (.bot) = false := by decide

/-- Evaluating `p ∧ q` under all-true valuation gives true. -/
theorem boolEvaluate_and_allTrue :
    BoolEvaluate (Atom := Bool) (fun _ => true)
      (.and (.atom false) (.atom true)) = true := by decide

/-- Evaluating `p ∧ q` under p-true, q-false valuation gives false. -/
theorem boolEvaluate_and_pTrue_qFalse :
    BoolEvaluate (Atom := Bool) (fun a => !a)
      (.and (.atom false) (.atom true)) = false := by decide

/-- Evaluating `p ∨ q` under p-false, q-true valuation gives true. -/
theorem boolEvaluate_or_pFalse_qTrue :
    BoolEvaluate (Atom := Bool) (fun a => a)
      (.or (.atom false) (.atom true)) = true := by decide

/-- Evaluating `p → q` under p-true, q-false valuation gives false. -/
theorem boolEvaluate_imp_pTrue_qFalse :
    BoolEvaluate (Atom := Bool) (fun a => !a)
      (.imp (.atom false) (.atom true)) = false := by decide

/-! ## Decidable Tautology Tests -/

/-- `p ∨ ¬p` is a tautology: the Decidable instance confirms it. -/
example : decide (Tautology (Atom := Bool)
    (.or (.atom false) (.imp (.atom false) .bot))) = true := by decide

/-- `p → p` is a tautology (identity). -/
example : decide (Tautology (Atom := Bool)
    (.imp (.atom false) (.atom false))) = true := by decide

/-- `p → q → p` is a tautology (weakening / ImplyK axiom). -/
example : decide (Tautology (Atom := Bool)
    (.imp (.atom false) (.imp (.atom true) (.atom false)))) = true := by decide

/-- `p` alone is NOT a tautology. -/
example : decide (Tautology (Atom := Bool) (.atom false)) = false := by decide

/-- `p ∧ q` alone is NOT a tautology. -/
example : decide (Tautology (Atom := Bool)
    (.and (.atom false) (.atom true))) = false := by decide

/-- Double negation elimination `¬¬p → p` is a tautology (classical). -/
example : decide (Tautology (Atom := Bool)
    (.imp (.imp (.imp (.atom false) .bot) .bot) (.atom false))) = true := by decide

/-- De Morgan: `¬(p ∧ q) → ¬p ∨ ¬q` is a tautology. -/
example : decide (Tautology (Atom := Bool)
    (.imp
      (.imp (.and (.atom false) (.atom true)) .bot)
      (.or (.imp (.atom false) .bot) (.imp (.atom true) .bot)))) = true := by decide

/-! ## Soundness Round-Trip -/

/-- Soundness: if `Tautology φ` then `BoolEvaluate v φ = true` for all Boolean valuations `v`.
This exercises the bridge lemma `tautology_iff_boolEvaluate_true`. -/
theorem tautology_soundness (φ : Proposition Bool) (hτ : Tautology φ)
    (v : BoolValuation Bool) : BoolEvaluate v φ = true := by
  rw [BoolEvaluate_eq_iff]
  exact hτ (fun a => v a = true)

/-- Completeness direction: if `BoolEvaluate v φ = true` for all `v`, then `Tautology φ`. -/
theorem boolEvaluate_complete (φ : Proposition Bool)
    (h : ∀ v : BoolValuation Bool, BoolEvaluate v φ = true) : Tautology φ :=
  (tautology_iff_boolEvaluate_true φ).mpr h

end CslibTests.Propositional
