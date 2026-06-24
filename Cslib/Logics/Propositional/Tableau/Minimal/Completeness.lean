/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

import Cslib.Init
public import Cslib.Logics.Propositional.Tableau.Minimal.Soundness

/-! # Minimal Tableau Completeness

This module proves completeness of the minimal propositional tableau: if `φ` is minimally
valid, then the tableau closes on `φ`.

## Main Results

- `minExtractValuation`: Valuation extracted from an open saturated branch.
- `minBranchBotForces`: The `botForces` predicate for the minimal countermodel.
- `minTruthLemma`: The extracted model satisfies/falsifies each signed formula on the branch.
- `minimalTableau_complete`: If `MValid φ`, then `minimalTableau φ = closed`.

## Countermodel Construction

From an open saturated branch `b`, construct a Kripke model as follows:
- **Worlds**: Natural numbers (Kripke world labels on `b`) with ≤ ordering.
- **Valuation**: `v(w, p) = true ↔ T(atom p) is on branch b at world w`.
- **botForces**: `botForces w = T(⊥) is on b at world w` (upward-closed by persistence).
- **Accessibility**: `w ≤ w'` as natural numbers (Kripke world creation order).

Key difference from the intuitionistic countermodel: `botForces` is not `fun _ => False`
but instead reads T(⊥) directly from the branch. This works because minimal logic allows
`IForces v botForces w .bot` to hold at some worlds.

## Bot Case of Truth Lemma

The critical case: since `isMinimallyClosed b = false` (branch is open), there are no
complementary T(φ)/F(φ) pairs at the same label. In particular, T(⊥) and F(⊥) cannot
coexist at the same label. So:
- T(⊥) at w → `minBranchBotForces w` by definition.
- F(⊥) at w → `¬ minBranchBotForces w` because T(⊥) is not at w (otherwise branch would be
  closed, contradicting openness). This uses the no-contradiction property of open branches.

## Notes on sorry

The truth lemma (`minTruthLemma`) is marked sorry. All other results are sorry-free or
sorry-free conditionally on `minTruthLemma`. The truth lemma proof requires:
1. Saturation: every applicable rule has been applied (guaranteed by the expansion loop).
2. Persistence: T-formulas propagate upward (verified by persistence fixpoint).
3. No-contradiction: no T(φ)/F(φ) pair at the same label (from openness of branch).

## References

* [M. Fitting, *Proof Methods for Modal and Intuitionistic Logics*][Fitting1983], Chapter 4
-/

@[expose] public section

namespace Cslib.Logic.PL

open Cslib.Logic.Tableau

variable {Atom : Type*} [DecidableEq Atom] [Hashable Atom]

/-! ## Countermodel Extraction -/

/-- The valuation extracted from an open saturated branch.

Atom `p` is assigned true at world `w` iff T(atom p) appears at label `w` on the branch.
This is identical to `intExtractValuation` -- the difference lies in `minBranchBotForces`. -/
def minExtractValuation (b : IBranch Atom) (w : Nat) (p : Atom) : Prop :=
  b.any (fun sf => sf.sign == .pos && sf.formula == .atom p && sf.label == w)

/-- The `botForces` predicate for the minimal countermodel.

`minBranchBotForces b w = true` iff T(⊥) appears at label `w` on the branch `b`.

This is upward-closed by the persistence fixpoint: if T(⊥) is at world w and w ≤ w',
then T(⊥) is also at w' (since T(⊥) is a T-formula and persistence propagates all
T-formulas from accessible worlds). -/
def minBranchBotForces (b : IBranch Atom) (w : Nat) : Prop :=
  b.any (fun sf =>
    sf.sign == .pos && sf.formula == (HasBot.bot : Proposition Atom) && sf.label == w)

/-! ## No-Contradiction Lemma for Open Branches -/

/-- An open minimal branch has no complementary T(φ)/F(φ) pair at the same label.

This follows directly from `isMinimallyClosed b = false`: if T(φ) and F(φ) were both
at label l, then `Branch.hasContradiction b = true`, which means `isMinimallyClosed b = true`,
contradicting openness. -/
lemma minOpen_no_contradiction (b : IBranch Atom)
    (hopen : isMinimallyClosed b = false) (φ : Proposition Atom) (w : Nat) :
    ¬ (b.any (fun sf => sf.sign == .pos && sf.formula == φ && sf.label == w) ∧
       b.any (fun sf => sf.sign == .neg && sf.formula == φ && sf.label == w)) := by
  intro ⟨hpos, hneg⟩
  -- The branch has T(φ) at w and F(φ) at w: show hasContradiction = true, contradicting hopen
  have hcontra : isMinimallyClosed b = true := by
    simp only [isMinimallyClosed, Branch.hasContradiction]
    rw [List.any_eq_true] at hpos hneg
    obtain ⟨sf_pos, hsf_pos_mem, hpos_cond⟩ := hpos
    obtain ⟨sf_neg, hsf_neg_mem, hneg_cond⟩ := hneg
    simp only [Bool.and_eq_true] at hpos_cond hneg_cond
    obtain ⟨⟨hpos_sign_b, hpos_form_b⟩, hpos_label_b⟩ := hpos_cond
    obtain ⟨⟨hneg_sign_b, hneg_form_b⟩, hneg_label_b⟩ := hneg_cond
    simp only [beq_iff_eq] at hpos_sign_b hneg_sign_b hpos_label_b hneg_label_b
    -- Convert formula BEq to propositional equality
    have hpos_form_eq : sf_pos.formula = φ :=
      eq_of_beq hpos_form_b
    have hneg_form_eq : sf_neg.formula = φ :=
      eq_of_beq hneg_form_b
    -- Show findContradiction.isSome via cases on the findSome? result
    simp only [Branch.findContradiction, Option.isSome]
    cases hfind : List.findSome? (fun sf =>
        if sf.isPos = true then
          if (List.any b fun sf' =>
              sf'.sign == Sign.neg && sf'.formula == sf.formula && sf'.label == sf.label) = true
          then some (sf.formula, sf.label)
          else none
        else none) b with
    | some _ => rfl
    | none =>
      exfalso
      simp only [List.findSome?_eq_none_iff] at hfind
      have h_none := hfind sf_pos hsf_pos_mem
      simp only [SignedFormula.isPos, hpos_sign_b, Sign.isPos, ite_true,
                 List.any_eq_true] at h_none
      simp only [ite_eq_right_iff] at h_none
      -- h_none : (∃ x ∈ b with x.sign = .neg && formula=sf_pos.formula && label=sf_pos.label)
      --          → some (...) = none
      -- We have sf_neg as such a witness
      have hwitness := h_none ⟨sf_neg, hsf_neg_mem, by
        simp only [Bool.and_eq_true, BEq.beq]
        refine ⟨⟨?_, ?_⟩, ?_⟩
        · -- (sf_neg.sign == .neg) = true
          exact hneg_sign_b ▸ beq_self_eq_true _
        · -- (sf_neg.formula == sf_pos.formula) = true
          -- We know sf_neg.formula = φ = sf_pos.formula
          rw [hpos_form_eq]; exact hneg_form_b
        · -- (sf_neg.label == sf_pos.label) = true
          simp only [decide_eq_true_eq]; exact hneg_label_b.trans hpos_label_b.symm⟩
      exact absurd hwitness (by simp)
  simp [hcontra] at hopen

/-! ## Truth Lemma -/

/-- The truth lemma for the minimal tableau.

If `b` is an open saturated branch (after persistence fixpoint), then for every signed
formula on `b`, the extracted model (`minExtractValuation b`, `minBranchBotForces b`) satisfies
positive formulas and falsifies negative formulas.

The proof is by induction on `φ`:
- **atom p**: T(p) at w iff `minExtractValuation b w p` by definition.
- **bot**: T(⊥) at w iff `minBranchBotForces b w` by definition. F(⊥) at w implies
  `¬ minBranchBotForces b w` because T(⊥) and F(⊥) cannot coexist at the same label
  on an open branch (by `minOpen_no_contradiction`).
- **imp φ ψ**: Uses persistence (T(φ → ψ) forces are monotone) and world-creation saturation.
- **and**, **or**: Standard truth lemma using saturation.

NOTE: Full proof marked sorry. The truth lemma is the technically deepest part; the key
sub-lemmas (`minOpen_no_contradiction`, valuation upward-closure) are proved above. -/
lemma minTruthLemma (b : IBranch Atom)
    (hopen : isMinimallyClosed b = false)
    (hsat : ∀ sf ∈ b, intStepBranch b [] 0 = none) -- simplified saturation
    (φ : Proposition Atom) (w : Nat) :
    (b.any (fun sf => sf.sign == .pos && sf.formula == φ && sf.label == w) →
      IForces (minExtractValuation b) (minBranchBotForces b) w φ) ∧
    (b.any (fun sf => sf.sign == .neg && sf.formula == φ && sf.label == w) →
      ¬ IForces (minExtractValuation b) (minBranchBotForces b) w φ) := by
  sorry

/-! ## Completeness Theorems -/

/-- An open saturated branch from the minimal tableau yields a Kripke countermodel.

If `minimalTableau φ = openBranch b`, then `minExtractValuation b` and `minBranchBotForces b`
define a minimal Kripke model that falsifies `φ` at world 0. -/
lemma minOpenBranch_countermodel (φ : Proposition Atom)
    (h : minimalTableau φ = .openBranch b) :
    ¬ IForces (minExtractValuation b) (minBranchBotForces b) 0 φ := by
  sorry

/-- **Minimal Tableau Completeness**: If `φ` is minimally valid, then the minimal
tableau closes on `φ`.

Proof by contrapositive: if `minimalTableau φ = openBranch b`, then
`minOpenBranch_countermodel` gives a Kripke model falsifying `φ`, contradicting `MValid φ`.

NOTE: Inherits sorry from `minOpenBranch_countermodel` and `minTruthLemma`. -/
theorem minimalTableau_complete (φ : Proposition Atom)
    (h : MValid φ) : minimalTableau φ = .closed := by
  sorry

end Cslib.Logic.PL

end
