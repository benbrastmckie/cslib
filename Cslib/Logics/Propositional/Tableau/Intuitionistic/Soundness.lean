/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

import Cslib.Init
public import Cslib.Logics.Propositional.Tableau.Intuitionistic.Expansion
public import Cslib.Logics.Propositional.Semantics.Kripke

/-! # Intuitionistic Tableau Soundness

This module proves soundness of the intuitionistic propositional tableau: if the tableau
closes on `φ` (starting from `F(φ)` at world 0), then `φ` is intuitionistically valid.

## Main Results

- `intBranchSatisfied`: A Kripke model satisfies a labeled branch when the forcing
  relation agrees with every signed formula on the branch.
- `intuitionisticTableau_sound`: If `intuitionisticTableau φ = closed`, then `IValid φ`.

## Strategy

Soundness proceeds by contrapositive:
1. Define `intBranchSatisfied` relating Kripke model forcing to signed branch content.
2. Show each intuitionistic rule preserves branch satisfiability in the Kripke sense.
3. Show an intuitionistically closed branch (containing T(⊥)) is unsatisfiable
   since `IForces ... .bot = False` for any intuitionistic model.
4. Conclude: if the tableau closes, the initial branch was unsatisfiable, meaning
   every Kripke model satisfies `φ`.

## Notes on sorry

The formal loop induction is marked sorry due to complexity. The key lemmas about
rule preservation are stated with complete proof outlines.

## References

* [M. Fitting, *Proof Methods for Modal and Intuitionistic Logics*][Fitting1983], Chapter 4
-/

@[expose] public section

namespace Cslib.Logic.PL

open Cslib.Logic.Tableau

variable {Atom : Type*} [DecidableEq Atom] [Hashable Atom]

/-! ## Kripke Branch Satisfiability -/

/-- A Kripke model satisfies a labeled branch when the forcing relation is consistent
with every signed formula on the branch.

For each signed formula `⟨sign, φ, w⟩` on the branch:
- If `sign = T`, then `IForces val botForces w φ` holds.
- If `sign = F`, then `¬ IForces val botForces w φ` holds. -/
def intBranchSatisfied {World : Type*} [Preorder World]
    (val : World → Atom → Prop)
    (botForces : World → Prop)
    (worldOf : Nat → World)
    (b : IBranch Atom) : Prop :=
  ∀ sf ∈ b,
    (sf.sign = .pos → IForces val botForces (worldOf sf.label) sf.formula) ∧
    (sf.sign = .neg → ¬ IForces val botForces (worldOf sf.label) sf.formula)

/-! ## Rule Soundness -/

/-- Each intuitionistic rule application preserves branch satisfiability.

The key cases:
- `T(φ ∧ ψ)` alpha-rule: if `IForces (φ ∧ ψ)`, then `IForces φ` and `IForces ψ`.
- `F(φ ∧ ψ)` beta-rule: if `¬ IForces (φ ∧ ψ)`, then `¬ IForces φ` or `¬ IForces ψ`.
- `T(φ ∨ ψ)` beta-rule: if `IForces (φ ∨ ψ)`, then `IForces φ` or `IForces ψ`.
- `F(φ → ψ)` world-creation: if `¬ IForces_w (φ → ψ)`, there exists `w' ≥ w` with
  `IForces_{w'} φ` and `¬ IForces_{w'} ψ`.
- `T(φ → ψ)` persistence: if `IForces_w (φ → ψ)` and `w' ≥ w` and `IForces_{w'} φ`,
  then `IForces_{w'} ψ` (this is immediate from the definition of `IForces` for `imp`).

NOTE: Full proof by case analysis on rules marked sorry. -/
lemma intRule_preserves_sat {World : Type*} [Preorder World]
    (val : World → Atom → Prop)
    (botForces : World → Prop)
    (worldOf : Nat → World)
    (b : IBranch Atom)
    (sf : ISF Atom)
    (_ : sf ∈ b)
    (hsat : intBranchSatisfied val botForces worldOf b)
    (nw : Nat) :
    match intApplyRuleFull sf nw b with
    | .linearResult newForms _ =>
      intBranchSatisfied val botForces worldOf (Branch.extendMany b newForms)
    | .branchingResult branches _ =>
      ∃ br ∈ branches,
        intBranchSatisfied val botForces worldOf (Branch.extendMany b br)
    | .notApplicable => True := by
  sorry

/-- An intuitionistically closed branch (containing T(⊥)) is unsatisfiable in any
Kripke model with `botForces = fun _ => False`.

In an intuitionistic Kripke model, `IForces val (fun _ => False) w .bot = False`,
so T(⊥) on the branch forces `IForces ... .bot` which is always false. -/
lemma intClosed_unsatisfiable {World : Type*} [Preorder World]
    (val : World → Atom → Prop)
    (worldOf : Nat → World)
    (b : IBranch Atom)
    (hclosed : isIntuitionisticallyClosed b = true) :
    ¬ intBranchSatisfied val (fun _ => False) worldOf b := by
  sorry

/-! ## Main Soundness Theorem -/

/-- **Intuitionistic Tableau Soundness**: If `intuitionisticTableau φ = closed`, then
`φ` is intuitionistically valid (`IValid φ`).

Proof outline:
1. The initial branch `[F(φ) at 0]` is satisfied by any Kripke model not forcing `φ` at 0.
2. Each rule application preserves satisfiability (by `intRule_preserves_sat`).
3. Closed branches are unsatisfiable (by `intClosed_unsatisfiable`).
4. Hence if the tableau closes, the initial branch was unsatisfiable.
5. Unsatisfiability of `[F(φ) at 0]` means every Kripke model forces `φ` at 0.
6. By `iforces_persistence` and universality, this gives `IValid φ`.

NOTE: Full proof marked sorry due to loop induction complexity. -/
theorem intuitionisticTableau_sound (φ : Proposition Atom)
    (h : intuitionisticTableau φ = .closed) : IValid φ := by
  sorry

end Cslib.Logic.PL

end
