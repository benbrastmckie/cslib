/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

import Cslib.Init
public import Cslib.Logics.Propositional.Tableau.Intuitionistic.Soundness

/-! # Minimal Tableau Soundness

This module proves soundness of the minimal propositional tableau: if the tableau
closes on `φ` (starting from `F(φ)` at world 0), then `φ` is minimally valid.

## Main Results

- `minBranchSatisfied`: A Kripke model satisfies a labeled branch when the forcing
  relation agrees with every signed formula on the branch.
- `minClosed_unsatisfiable`: A minimally closed branch is unsatisfiable in any Kripke model.
- `minimalTableau_sound`: If `minimalTableau φ = closed`, then `MValid φ`.

## Strategy

Soundness proceeds by contrapositive, reusing the intuitionistic infrastructure:

1. `minClosed_unsatisfiable` uses `Branch.hasContradiction`: a minimally closed branch
   contains T(φ) and F(φ) at the same world, which contradicts `IForces val bf w φ`
   and `¬ IForces val bf w φ` for any `botForces`. This is simpler than the intuitionistic
   case (which required `botForces = fun _ => False` specifically).

2. `minimalTableau_sound` instantiates `intExpandBranches_closed_unsat` with
   `isMinimallyClosed` and `minClosed_unsatisfiable`, mirroring `intuitionisticTableau_sound`.

## Design

`minBranchSatisfied` is definitionally equal to `intBranchSatisfied` -- both are
`∀ sf ∈ b, (sf.sign = .pos → IForces ... sf.formula) ∧ (sf.sign = .neg → ¬ IForces ...)`.
The difference is only in how `botForces` is instantiated at use sites.

## Notes on sorry

`intExpandBranches_closed_unsat` is sorry'd in `Intuitionistic.Soundness`. The soundness
proof here inherits that sorry. Both become sorry-free once the loop invariant is proved.

## References

* [M. Fitting, *Proof Methods for Modal and Intuitionistic Logics*][Fitting1983], Chapter 4
-/

@[expose] public section

namespace Cslib.Logic.PL

open Cslib.Logic.Tableau

variable {Atom : Type*} [DecidableEq Atom] [Hashable Atom]

/-! ## Minimal Branch Satisfiability -/

/-- A Kripke model satisfies a labeled branch when the forcing relation is consistent
with every signed formula on the branch.

For each signed formula `⟨sign, φ, w⟩` on the branch:
- If `sign = T`, then `IForces val botForces w φ` holds.
- If `sign = F`, then `¬ IForces val botForces w φ` holds.

This definition is identical to `intBranchSatisfied`: the difference between minimal and
intuitionistic satisfiability lies only in the choice of `botForces` at use sites. -/
def minBranchSatisfied {World : Type*} [Preorder World]
    (val : World → Atom → Prop)
    (botForces : World → Prop)
    (worldOf : Nat → World)
    (b : IBranch Atom) : Prop :=
  ∀ sf ∈ b,
    (sf.sign = .pos → IForces val botForces (worldOf sf.label) sf.formula) ∧
    (sf.sign = .neg → ¬ IForces val botForces (worldOf sf.label) sf.formula)

/-! ## Closure Unsatisfiability -/

/-- A minimally closed branch is unsatisfiable in any Kripke model.

`isMinimallyClosed b = true` means `Branch.hasContradiction b = true`, i.e., there
exist T(φ) and F(φ) at the same world label for some formula φ. The branch satisfier
then provides both `IForces val botForces w φ` and `¬ IForces val botForces w φ`,
a contradiction regardless of the choice of `botForces`. -/
lemma minClosed_unsatisfiable {World : Type*} [Preorder World]
    (val : World → Atom → Prop)
    (botForces : World → Prop)
    (worldOf : Nat → World)
    (b : IBranch Atom)
    (hclosed : isMinimallyClosed b = true) :
    ¬ intBranchSatisfied val botForces worldOf b := by
  intro hsat
  -- isMinimallyClosed = Branch.hasContradiction = findContradiction.isSome
  simp only [isMinimallyClosed, Branch.hasContradiction, Branch.findContradiction] at hclosed
  -- Extract witness sf_pos from findSome?
  rw [List.findSome?_isSome_iff] at hclosed
  obtain ⟨sf_pos, hsf_pos_mem, hcond⟩ := hclosed
  -- hcond : (if sf_pos.isPos then if b.any ... then some (...) else none else none).isSome
  split_ifs at hcond with hispos hneg
  · -- sf_pos is positive and there is a negative match: derive contradiction
    -- hneg : (b.any fun sf' => sf'.sign == .neg && ...) = true
    rw [List.any_eq_true] at hneg
    obtain ⟨sf_neg, hsf_neg_mem, hneg_cond⟩ := hneg
    simp only [Bool.and_eq_true] at hneg_cond
    obtain ⟨⟨hneg_sign_b, hneg_form_b⟩, hneg_label_b⟩ := hneg_cond
    -- Convert BEq results to =
    simp only [beq_iff_eq] at hneg_sign_b hneg_label_b
    have hneg_form_eq : sf_neg.formula = sf_pos.formula :=
      eq_of_beq hneg_form_b
    -- sf_pos.sign = .pos from isPos
    simp only [SignedFormula.isPos, Sign.isPos] at hispos
    have hpos_sign : sf_pos.sign = .pos := by
      rcases sf_pos with ⟨sign, _, _⟩; cases sign <;> simp_all
    -- Get satisfaction info from the branch satisfier
    have hsat_pos := hsat sf_pos hsf_pos_mem
    have hsat_neg := hsat sf_neg hsf_neg_mem
    rw [hpos_sign] at hsat_pos
    rw [hneg_sign_b, hneg_label_b, hneg_form_eq] at hsat_neg
    exact hsat_neg.2 rfl (hsat_pos.1 rfl)
  · simp at hcond
  · simp at hcond

/-! ## Main Soundness Theorem -/

/-- **Minimal Tableau Soundness**: If `minimalTableau φ = closed`, then `MValid φ`.

The proof instantiates `intExpandBranches_closed_unsat` with `isMinimallyClosed` and
`minClosed_unsatisfiable`, mirroring `intuitionisticTableau_sound` exactly. The key
differences from the intuitionistic case:
- `botForces` is arbitrary (from the MValid quantifier).
- `isMinimallyClosed` (all complementary pairs) is used instead of `isIntuitionisticallyClosed`.

NOTE: Inherits sorry from `intExpandBranches_closed_unsat` in `Intuitionistic.Soundness`. -/
theorem minimalTableau_sound (φ : Proposition Atom)
    (h : minimalTableau φ = .closed) : MValid φ := by
  intro World _ val botForces v_uc bf_uc w₀
  by_contra hneg
  let worldOf : Nat → World := fun _ => w₀
  have hsat : intBranchSatisfied val botForces worldOf [⟨.neg, φ, 0⟩] := by
    intro sf hmem
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
    subst hmem
    exact ⟨fun h' => absurd h' (Sign.noConfusion), fun _ => hneg⟩
  simp only [minimalTableau] at h
  exact intExpandBranches_closed_unsat val botForces v_uc bf_uc _
    isMinimallyClosed
    (fun worldOf' b hcl => minClosed_unsatisfiable val botForces worldOf' b hcl)
    _ _ _ _ (by rfl) (by rfl) h
    [⟨.neg, φ, 0⟩] (by simp) worldOf hsat

end Cslib.Logic.PL

end
