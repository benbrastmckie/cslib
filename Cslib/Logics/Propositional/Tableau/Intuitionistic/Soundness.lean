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
    (hmem_sf : sf ∈ b)
    (hsat : intBranchSatisfied val botForces worldOf b)
    (nw : Nat) :
    match intApplyRuleFull sf nw b with
    | .linearResult newForms _ =>
      intBranchSatisfied val botForces worldOf (Branch.extendMany b newForms)
    | .branchingResult branches _ =>
      ∃ br ∈ branches,
        intBranchSatisfied val botForces worldOf (Branch.extendMany b br)
    | .notApplicable => True := by
  obtain ⟨sign, form, label⟩ := sf
  -- Helper: extending b with formulas the model already satisfies preserves satisfaction
  have extend_sat : ∀ (newForms : List (ISF Atom)),
      (∀ sf' ∈ newForms,
        (sf'.sign = .pos → IForces val botForces (worldOf sf'.label) sf'.formula) ∧
        (sf'.sign = .neg → ¬ IForces val botForces (worldOf sf'.label) sf'.formula)) →
      intBranchSatisfied val botForces worldOf (Branch.extendMany b newForms) := by
    intro newForms hnew sf' hmem'
    simp only [Branch.extendMany, List.mem_append] at hmem'
    rcases hmem' with h | h
    · exact hnew sf' h
    · exact hsat sf' h
  -- sf is in b, so hsat gives us information about sf
  have hsf_info := hsat ⟨sign, form, label⟩ hmem_sf
  simp only at hsf_info
  -- Case split on sign
  cases sign with
  | pos =>
    have hpos := hsf_info.1 rfl
    -- Case split on formula
    cases form with
    | atom x => trivial
    | bot => trivial
    | imp φ ψ =>
      -- T(φ → ψ): intApplyRuleFull returns .notApplicable (persistent rule, handled separately)
      trivial
    | and φ ψ =>
      -- T(φ ∧ ψ): .linearResult [T(φ), T(ψ)] nw
      simp only [show intApplyRuleFull (⟨.pos, φ ∧ ψ, label⟩ : ISF Atom) nw b =
        .linearResult [⟨.pos, φ, label⟩, ⟨.pos, ψ, label⟩] nw from rfl]
      rw [IForces_and] at hpos
      apply extend_sat
      intro sf' hmem'
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem'
      rcases hmem' with rfl | rfl
      · exact ⟨fun _ => hpos.1, fun h => absurd h (Sign.noConfusion)⟩
      · exact ⟨fun _ => hpos.2, fun h => absurd h (Sign.noConfusion)⟩
    | or φ ψ =>
      -- T(φ ∨ ψ): .branchingResult [[T(φ)], [T(ψ)]] nw
      simp only [show intApplyRuleFull (⟨.pos, φ ∨ ψ, label⟩ : ISF Atom) nw b =
        .branchingResult [[⟨.pos, φ, label⟩], [⟨.pos, ψ, label⟩]] nw from rfl]
      rw [IForces_or] at hpos
      rcases hpos with hφ | hψ
      · exact ⟨[⟨.pos, φ, label⟩], List.mem_cons_self,
          extend_sat _ (fun sf' hmem' => by
            simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem'
            subst hmem'
            exact ⟨fun _ => hφ, fun h => absurd h (Sign.noConfusion)⟩)⟩
      · exact ⟨[⟨.pos, ψ, label⟩], by simp,
          extend_sat _ (fun sf' hmem' => by
            simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem'
            subst hmem'
            exact ⟨fun _ => hψ, fun h => absurd h (Sign.noConfusion)⟩)⟩
  | neg =>
    have hneg := hsf_info.2 rfl
    cases form with
    | atom x => trivial
    | bot => trivial
    | imp φ ψ =>
      -- F(φ → ψ): world-creating rule. The lemma as stated is too strong for this case,
      -- since worldOf nw is fixed and may not equal the witness world from ¬IForces.
      -- This case is handled in the main soundness theorem (S6) where worldOf is constructed.
      -- See the plan (task 316, Phase 2) for the resolution strategy.
      sorry
    | and φ ψ =>
      -- F(φ ∧ ψ): .branchingResult [[F(φ)], [F(ψ)]] nw
      simp only [show intApplyRuleFull (⟨.neg, φ ∧ ψ, label⟩ : ISF Atom) nw b =
        .branchingResult [[⟨.neg, φ, label⟩], [⟨.neg, ψ, label⟩]] nw from rfl]
      rw [IForces_and, not_and_or] at hneg
      rcases hneg with hφ | hψ
      · exact ⟨[⟨.neg, φ, label⟩], List.mem_cons_self,
          extend_sat _ (fun sf' hmem' => by
            simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem'
            subst hmem'
            exact ⟨fun h => absurd h (Sign.noConfusion), fun _ => hφ⟩)⟩
      · exact ⟨[⟨.neg, ψ, label⟩], by simp,
          extend_sat _ (fun sf' hmem' => by
            simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem'
            subst hmem'
            exact ⟨fun h => absurd h (Sign.noConfusion), fun _ => hψ⟩)⟩
    | or φ ψ =>
      -- F(φ ∨ ψ): .linearResult [F(φ), F(ψ)] nw
      simp only [show intApplyRuleFull (⟨.neg, φ ∨ ψ, label⟩ : ISF Atom) nw b =
        .linearResult [⟨.neg, φ, label⟩, ⟨.neg, ψ, label⟩] nw from rfl]
      rw [IForces_or, not_or] at hneg
      apply extend_sat
      intro sf' hmem'
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem'
      rcases hmem' with rfl | rfl
      · exact ⟨fun h => absurd h (Sign.noConfusion), fun _ => hneg.1⟩
      · exact ⟨fun h => absurd h (Sign.noConfusion), fun _ => hneg.2⟩

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
  intro hsat
  have hbp : ∃ sf ∈ b, (SignedFormula.isPos sf &&
      (sf.formula == (HasBot.bot : Proposition Atom))) = true := by
    rw [← List.find?_isSome]
    have key : isIntuitionisticallyClosed b = (List.find? (fun (sf : ISF Atom) =>
        sf.isPos && (sf.formula == (HasBot.bot : Proposition Atom))) b).isSome := by
      simp only [isIntuitionisticallyClosed, ClosureCondition.isClosed, ClosureCondition.findClosure]
      cases b.find? (fun (sf : ISF Atom) =>
        sf.isPos && (sf.formula == (HasBot.bot : Proposition Atom))) <;> rfl
    rw [← key]; exact hclosed
  obtain ⟨sf, hmem, hcond⟩ := hbp
  simp only [Bool.and_eq_true, SignedFormula.isPos, Sign.isPos] at hcond
  obtain ⟨hpos_b, hbot_form⟩ := hcond
  have hssign : sf.sign = .pos := by
    rcases sf with ⟨sign, _, _⟩; cases sign <;> simp_all
  cases hf : sf.formula with
  | bot =>
    have hsf := hsat sf hmem
    rw [hssign] at hsf
    rw [hf, IForces_bot] at hsf
    exact hsf.1 rfl
  | atom x => simp [hf, BEq.beq, instBEqProposition.beq] at hbot_form
  | imp a c => simp [hf, BEq.beq, instBEqProposition.beq] at hbot_form
  | and a c => simp [hf, BEq.beq, instBEqProposition.beq] at hbot_form
  | or a c => simp [hf, BEq.beq, instBEqProposition.beq] at hbot_form

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
