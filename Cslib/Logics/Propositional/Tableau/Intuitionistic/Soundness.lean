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
3. Show an intuitionistically closed branch (containing T(⊥), or a T(φ)/F(φ) pair) is
   unsatisfiable since `IForces ... .bot = False` for any intuitionistic model, and
   complementary pairs contradict satisfiability directly.
4. Conclude: if the tableau closes, the initial branch was unsatisfiable, meaning
   every Kripke model satisfies `φ`.

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

omit [DecidableEq Atom] [Hashable Atom] in
/-- Each intuitionistic rule application preserves branch satisfiability.

The key cases:
- `T(φ ∧ ψ)` alpha-rule: if `IForces (φ ∧ ψ)`, then `IForces φ` and `IForces ψ`.
- `F(φ ∧ ψ)` beta-rule: if `¬ IForces (φ ∧ ψ)`, then `¬ IForces φ` or `¬ IForces ψ`.
- `T(φ ∨ ψ)` beta-rule: if `IForces (φ ∨ ψ)`, then `IForces φ` or `IForces ψ`.
- `F(φ → ψ)` world-creation: if `¬ IForces_w (φ → ψ)`, there exists `w' ≥ w` with
  `IForces_{w'} φ` and `¬ IForces_{w'} ψ`. The new world label `nw` maps to `w'`
  via `Function.update worldOf nw w'`.

For `linearResult newForms _ _`, the conclusion provides an existential `worldOf'` so that
the F(imp) world-creating case can update the `worldOf` mapping at the fresh label `nw`.

The freshness hypothesis `hnw : ∀ sf' ∈ b, sf'.label ≠ nw` ensures that `nw` is not
already present in `b`, making the `Function.update` well-defined for branch formulas. -/
lemma intRule_preserves_sat {World : Type*} [Preorder World]
    (val : World → Atom → Prop)
    (botForces : World → Prop)
    (v_uc : ∀ {w w' : World} (p : Atom), w ≤ w' → val w p → val w' p)
    (bf_uc : ∀ {w w' : World}, w ≤ w' → botForces w → botForces w')
    (worldOf : Nat → World)
    (b : IBranch Atom)
    (sf : ISF Atom)
    (hmem_sf : sf ∈ b)
    (hsat : intBranchSatisfied val botForces worldOf b)
    (nw : Nat)
    (hnw : ∀ sf' ∈ b, sf'.label ≠ nw) :
    match intApplyRuleFull sf nw b with
    | .linearResult newForms _ newEdge =>
      ∃ worldOf' : Nat → World,
        (∀ k, k ≠ nw → worldOf' k = worldOf k) ∧
        intBranchSatisfied val botForces worldOf' (Branch.extendMany b newForms) ∧
        match newEdge with
        | none => True
        | some (c, p) => worldOf p ≤ worldOf' c
    | .branchingResult branches _ =>
      ∃ br ∈ branches,
        intBranchSatisfied val botForces worldOf (Branch.extendMany b br)
    | .notApplicable => True := by
  obtain ⟨sign, form, label⟩ := sf
  -- Helper: extending b with formulas the model satisfies preserves satisfaction
  have extend_sat : ∀ (newForms : List (ISF Atom)) (wo : Nat → World),
      (∀ sf' ∈ newForms,
        (sf'.sign = .pos → IForces val botForces (wo sf'.label) sf'.formula) ∧
        (sf'.sign = .neg → ¬ IForces val botForces (wo sf'.label) sf'.formula)) →
      (∀ sf' ∈ b,
        (sf'.sign = .pos → IForces val botForces (wo sf'.label) sf'.formula) ∧
        (sf'.sign = .neg → ¬ IForces val botForces (wo sf'.label) sf'.formula)) →
      intBranchSatisfied val botForces wo (Branch.extendMany b newForms) := by
    intro newForms wo hnew hb_wo sf' hmem'
    simp only [Branch.extendMany, List.mem_append] at hmem'
    rcases hmem' with h | h
    · exact hnew sf' h
    · exact hb_wo sf' h
  -- Helper: restate hsat with an alternate worldOf
  have hsat_wo : ∀ (wo : Nat → World),
      (∀ k, wo k = worldOf k) →
      ∀ sf' ∈ b,
        (sf'.sign = .pos → IForces val botForces (wo sf'.label) sf'.formula) ∧
        (sf'.sign = .neg → ¬ IForces val botForces (wo sf'.label) sf'.formula) := by
    intro wo heq sf' hmem'
    rw [heq]
    exact hsat sf' hmem'
  -- sf is in b, so hsat gives us information about sf
  have hsf_info := hsat ⟨sign, form, label⟩ hmem_sf
  simp only at hsf_info
  -- Case split on sign
  cases sign with
  | pos =>
    have hpos := hsf_info.1 rfl
    cases form with
    | atom x => trivial
    | bot => trivial
    | imp φ ψ =>
      -- T(φ → ψ): intApplyRuleFull returns .notApplicable
      trivial
    | and φ ψ =>
      -- T(φ ∧ ψ): .linearResult [T(φ), T(ψ)] nw none; worldOf unchanged
      simp only [show intApplyRuleFull (⟨.pos, φ ∧ ψ, label⟩ : ISF Atom) nw b =
        .linearResult [⟨.pos, φ, label⟩, ⟨.pos, ψ, label⟩] nw none from rfl]
      refine ⟨worldOf, fun _ _ => rfl, ?_, trivial⟩
      rw [IForces_and] at hpos
      apply extend_sat _ worldOf
      · intro sf' hmem'
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem'
        rcases hmem' with rfl | rfl
        · exact ⟨fun _ => hpos.1, fun h => absurd h (Sign.noConfusion)⟩
        · exact ⟨fun _ => hpos.2, fun h => absurd h (Sign.noConfusion)⟩
      · exact hsat
    | or φ ψ =>
      -- T(φ ∨ ψ): .branchingResult [[T(φ)], [T(ψ)]] nw
      simp only [show intApplyRuleFull (⟨.pos, φ ∨ ψ, label⟩ : ISF Atom) nw b =
        .branchingResult [[⟨.pos, φ, label⟩], [⟨.pos, ψ, label⟩]] nw from rfl]
      rw [IForces_or] at hpos
      rcases hpos with hφ | hψ
      · exact ⟨[⟨.pos, φ, label⟩], List.mem_cons_self,
          extend_sat _ worldOf
            (fun sf' hmem' => by
              simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem'
              subst hmem'
              exact ⟨fun _ => hφ, fun h => absurd h (Sign.noConfusion)⟩)
            hsat⟩
      · exact ⟨[⟨.pos, ψ, label⟩], by simp,
          extend_sat _ worldOf
            (fun sf' hmem' => by
              simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem'
              subst hmem'
              exact ⟨fun _ => hψ, fun h => absurd h (Sign.noConfusion)⟩)
            hsat⟩
  | neg =>
    have hneg := hsf_info.2 rfl
    cases form with
    | atom x => trivial
    | bot => trivial
    | imp φ ψ =>
      -- F(φ → ψ): world-creating rule.
      -- intApplyRuleFull returns .linearResult (newForms ++ persistent) (nw + 1) (some (nw, label))
      -- where newForms = [T(φ, nw), F(ψ, nw)] ++ propagatePersistence b label nw
      simp only [intApplyRuleFull, intFImpRule]
      -- hneg : ¬ IForces val botForces (worldOf label) (φ → ψ)
      rw [IForces_imp] at hneg
      push Not at hneg
      obtain ⟨w', hw'_ge, hw'_φ, hw'_ψ⟩ := hneg
      -- Provide updated worldOf: map nw to w', keep others unchanged
      -- Note: we use Function.update worldOf nw w' directly (no let binding)
      refine ⟨Function.update worldOf nw w', fun k hk => ?_, ?_, ?_⟩
      · -- worldOf' k = worldOf k for k ≠ nw
        show Function.update worldOf nw w' k = worldOf k
        simp [hk]
      · -- Show intBranchSatisfied val botForces (Function.update worldOf nw w') ...
        apply extend_sat _ (Function.update worldOf nw w')
        · -- Verify the new formulas
          intro sf' hmem'
          simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hmem'
          -- New formulas: [T(φ, nw), F(ψ, nw)] ++ propagatePersistence b label nw
          rcases hmem' with (rfl | rfl) | hmem_pers
          · -- T(φ, nw): IForces val botForces (Function.update worldOf nw w' nw) φ
            simp only [Function.update_self]
            exact ⟨fun _ => hw'_φ, fun h => absurd h (Sign.noConfusion)⟩
          · -- F(ψ, nw): ¬ IForces val botForces (Function.update worldOf nw w' nw) ψ
            simp only [Function.update_self]
            exact ⟨fun h => absurd h (Sign.noConfusion), fun _ => hw'_ψ⟩
          · -- Propagated T-formulas: propagatePersistence b label nw
            -- These are of the form T(α, nw) where α ∈ posFormulasAt b label
            simp only [propagatePersistence, posFormulasAt, List.mem_map,
              List.mem_filterMap] at hmem_pers
            obtain ⟨α, ⟨sf_b, hsf_b_mem, hsf_b_val⟩, rfl⟩ := hmem_pers
            -- sf' is now ⟨.pos, α, nw⟩; worldOf' nw = w' by Function.update
            simp only [Function.update_self]
            split_ifs at hsf_b_val with hcond
            · -- sf_b satisfies the filter condition: sign=pos && label=world
              simp only [Option.some.injEq] at hsf_b_val
              simp only [Bool.and_eq_true, beq_iff_eq] at hcond
              obtain ⟨hsign_eq, hlabel_eq⟩ := hcond
              have hα_forces : IForces val botForces (worldOf label) α := by
                have := (hsat sf_b hsf_b_mem).1 hsign_eq
                rwa [hsf_b_val, hlabel_eq] at this
              -- By persistence: worldOf label ≤ w', so IForces ... w' α
              exact ⟨fun _ => iforces_persistence v_uc bf_uc hw'_ge hα_forces,
                fun h => absurd h (Sign.noConfusion)⟩
        · -- Old branch formulas: Function.update worldOf nw w' k = worldOf k for k ≠ nw
          -- By freshness hnw: ∀ sf' ∈ b, sf'.label ≠ nw
          intro sf' hmem'
          have hne : sf'.label ≠ nw := hnw sf' hmem'
          have heq : Function.update worldOf nw w' sf'.label = worldOf sf'.label := by
            simp [hne]
          rw [heq]
          exact hsat sf' hmem'
      · -- Ordering: worldOf label ≤ Function.update worldOf nw w' nw
        simp only [Function.update_self]
        exact hw'_ge
    | and φ ψ =>
      -- F(φ ∧ ψ): .branchingResult [[F(φ)], [F(ψ)]] nw
      simp only [show intApplyRuleFull (⟨.neg, φ ∧ ψ, label⟩ : ISF Atom) nw b =
        .branchingResult [[⟨.neg, φ, label⟩], [⟨.neg, ψ, label⟩]] nw from rfl]
      rw [IForces_and, not_and_or] at hneg
      rcases hneg with hφ | hψ
      · exact ⟨[⟨.neg, φ, label⟩], List.mem_cons_self,
          extend_sat _ worldOf
            (fun sf' hmem' => by
              simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem'
              subst hmem'
              exact ⟨fun h => absurd h (Sign.noConfusion), fun _ => hφ⟩)
            hsat⟩
      · exact ⟨[⟨.neg, ψ, label⟩], by simp,
          extend_sat _ worldOf
            (fun sf' hmem' => by
              simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem'
              subst hmem'
              exact ⟨fun h => absurd h (Sign.noConfusion), fun _ => hψ⟩)
            hsat⟩
    | or φ ψ =>
      -- F(φ ∨ ψ): .linearResult [F(φ), F(ψ)] nw none; worldOf unchanged
      simp only [show intApplyRuleFull (⟨.neg, φ ∨ ψ, label⟩ : ISF Atom) nw b =
        .linearResult [⟨.neg, φ, label⟩, ⟨.neg, ψ, label⟩] nw none from rfl]
      refine ⟨worldOf, fun _ _ => rfl, ?_, trivial⟩
      rw [IForces_or, not_or] at hneg
      apply extend_sat _ worldOf
      · intro sf' hmem'
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem'
        rcases hmem' with rfl | rfl
        · exact ⟨fun h => absurd h (Sign.noConfusion), fun _ => hneg.1⟩
        · exact ⟨fun h => absurd h (Sign.noConfusion), fun _ => hneg.2⟩
      · exact hsat

omit [Hashable Atom] in
/-- An intuitionistically closed branch is unsatisfiable in any Kripke model with
`botForces = fun _ => False`.

`isIntuitionisticallyClosed b = true` iff either:
1. T(⊥) appears at some label (`IntuitionisticClosure` fires), or
2. T(φ) and F(φ) coexist at the same label for some φ (`Branch.hasContradiction` fires).

Case 1: `IForces val (fun _ => False) w .bot = False`, so T(⊥) forces a contradiction.
Case 2: The branch satisfier provides both `IForces ... φ` and `¬ IForces ... φ`,
a direct contradiction. -/
lemma intClosed_unsatisfiable {World : Type*} [Preorder World]
    (val : World → Atom → Prop)
    (worldOf : Nat → World)
    (b : IBranch Atom)
    (hclosed : isIntuitionisticallyClosed b = true) :
    ¬ intBranchSatisfied val (fun _ => False) worldOf b := by
  intro hsat
  simp only [isIntuitionisticallyClosed, Bool.or_eq_true] at hclosed
  rcases hclosed with hbot | hcontra
  · -- Case 1: T(⊥) is on the branch
    have hbp : ∃ sf ∈ b, (SignedFormula.isPos sf &&
        (sf.formula == (HasBot.bot : Proposition Atom))) = true := by
      rw [← List.find?_isSome]
      have key : @ClosureCondition.isClosed _ _
          IntuitionisticClosure.instClosureConditionOfBEqOfHasBot b =
          (List.find? (fun (sf : ISF Atom) =>
          sf.isPos && (sf.formula == (HasBot.bot : Proposition Atom))) b).isSome := by
        simp only [ClosureCondition.isClosed, ClosureCondition.findClosure]
        cases b.find? (fun (sf : ISF Atom) =>
          sf.isPos && (sf.formula == (HasBot.bot : Proposition Atom))) <;> rfl
      rw [← key]; exact hbot
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
    | atom x => simp [beq_iff_eq, hf] at hbot_form
    | imp a c => simp [beq_iff_eq, hf] at hbot_form
    | and a c => simp [beq_iff_eq, hf] at hbot_form
    | or a c => simp [beq_iff_eq, hf] at hbot_form
  · -- Case 2: complementary pair T(φ)/F(φ) at same label
    simp only [Branch.hasContradiction, Branch.findContradiction] at hcontra
    rw [List.findSome?_isSome_iff] at hcontra
    obtain ⟨sf_pos, hsf_pos_mem, hcond⟩ := hcontra
    split_ifs at hcond with hispos hneg
    · rw [List.any_eq_true] at hneg
      obtain ⟨sf_neg, hsf_neg_mem, hneg_cond⟩ := hneg
      simp only [Bool.and_eq_true] at hneg_cond
      obtain ⟨⟨hneg_sign_b, hneg_form_b⟩, hneg_label_b⟩ := hneg_cond
      simp only [beq_iff_eq] at hneg_sign_b hneg_label_b
      have hneg_form_eq : sf_neg.formula = sf_pos.formula := eq_of_beq hneg_form_b
      simp only [SignedFormula.isPos, Sign.isPos] at hispos
      have hpos_sign : sf_pos.sign = .pos := by
        rcases sf_pos with ⟨sign, _, _⟩; cases sign <;> simp_all
      have hsat_pos := hsat sf_pos hsf_pos_mem
      have hsat_neg := hsat sf_neg hsf_neg_mem
      rw [hpos_sign] at hsat_pos
      rw [hneg_sign_b, hneg_label_b, hneg_form_eq] at hsat_neg
      exact hsat_neg.2 rfl (hsat_pos.1 rfl)
    · simp at hcond
    · simp at hcond

/-! ## Loop Induction Lemma -/

/-- `worldOf` is monotone with respect to an edge list `edges`: accessibility implies
order. Used in the soundness invariant to ensure persistence rules are sound. -/
def MonotoneEdges {World : Type*} [Preorder World]
    (worldOf : Nat → World) (edges : IEdges) : Prop :=
  ∀ w w', isAccessible edges w w' = true → worldOf w ≤ worldOf w'

omit [Hashable Atom] in
/-- Applying all T(φ→ψ) rules preserves branch satisfiability when `worldOf` is
monotone with respect to the edge set. -/
private lemma applyAllTImpRules_sat
    {World : Type*} [Preorder World]
    (val : World → Atom → Prop) (botForces : World → Prop)
    (_v_uc : ∀ {w w' : World} (p : Atom), w ≤ w' → val w p → val w' p)
    (_bf_uc : ∀ {w w' : World}, w ≤ w' → botForces w → botForces w')
    (worldOf : Nat → World)
    (b : IBranch Atom) (edges : IEdges)
    (hsat : intBranchSatisfied val botForces worldOf b)
    (hmono : MonotoneEdges worldOf edges) :
    intBranchSatisfied val botForces worldOf (applyAllTImpRules b edges) := by
  intro sf hmem
  simp only [applyAllTImpRules, List.mem_append] at hmem
  rcases hmem with h | h
  · exact hsat sf h
  · simp only [List.mem_flatten, List.mem_filterMap] at h
    obtain ⟨newForms, ⟨⟨sign_o, form_o, label_o⟩, hmem_outer, houter⟩, hmem_inner⟩ := h
    cases sign_o with
    | neg => simp only at houter; exact absurd houter (by simp)
    | pos =>
      cases form_o with
      | atom _ => simp only at houter; exact absurd houter (by simp)
      | bot => simp only at houter; exact absurd houter (by simp)
      | and _ _ => simp only at houter; exact absurd houter (by simp)
      | or _ _ => simp only at houter; exact absurd houter (by simp)
      | imp φ ψ =>
        simp only [] at houter
        by_cases hemp : (intTImpRule φ ψ label_o edges b).isEmpty = true
        · simp only [hemp, ite_true] at houter; exact absurd houter (by simp)
        · simp only [Bool.false_eq_true, hemp, ite_false, Option.some.injEq] at houter
          rw [← houter] at hmem_inner
          simp only [intTImpRule, List.mem_filterMap] at hmem_inner
          obtain ⟨w', hw'_acc, hw'_sf⟩ := hmem_inner
          simp only [List.mem_filter, List.mem_eraseDups, List.mem_map] at hw'_acc
          obtain ⟨_, hw'_access⟩ := hw'_acc
          by_cases hphi : (b.any fun sf =>
              sf.sign == .pos && sf.formula == φ && sf.label == w') = true
          · by_cases hpsi : (b.any fun sf =>
                sf.sign == .pos && sf.formula == ψ && sf.label == w') = true
            · simp [hphi, hpsi] at hw'_sf
            · simp only [hphi, ↓reduceIte, hpsi, Bool.false_eq_true, Option.some.injEq] at hw'_sf
              -- hw'_sf : ⟨.pos, ψ, w'⟩ = sf
              rw [← hw'_sf]
              have himpimp := (hsat ⟨.pos, .imp φ ψ, label_o⟩ hmem_outer).1 rfl
              simp only [IForces_imp] at himpimp
              have hle : worldOf label_o ≤ worldOf w' := hmono _ _ hw'_access
              have hphi_forces : IForces val botForces (worldOf w') φ := by
                rw [List.any_eq_true] at hphi
                obtain ⟨sf', hmem', hcond⟩ := hphi
                simp only [Bool.and_eq_true, beq_iff_eq] at hcond
                obtain ⟨⟨hsign, hform⟩, hlabel⟩ := hcond
                have := (hsat sf' hmem').1 hsign
                rw [hform, hlabel] at this; exact this
              exact ⟨fun _ => himpimp (worldOf w') hle hphi_forces,
                    fun h => by simp at h⟩
          · simp [hphi] at hw'_sf

omit [Hashable Atom] in
/-- Persistence fixpoint preserves satisfiability when `worldOf` is monotone. -/
private lemma applyPersistenceFixpoint_sat
    {World : Type*} [Preorder World]
    (val : World → Atom → Prop) (botForces : World → Prop)
    (v_uc : ∀ {w w' : World} (p : Atom), w ≤ w' → val w p → val w' p)
    (bf_uc : ∀ {w w' : World}, w ≤ w' → botForces w → botForces w')
    (worldOf : Nat → World)
    (b : IBranch Atom) (edges : IEdges) (fuelP : Nat)
    (hsat : intBranchSatisfied val botForces worldOf b)
    (hmono : MonotoneEdges worldOf edges) :
    intBranchSatisfied val botForces worldOf (applyPersistenceFixpoint b edges fuelP) := by
  induction fuelP generalizing b with
  | zero => simpa [applyPersistenceFixpoint] using hsat
  | succ k ih =>
    simp only [applyPersistenceFixpoint]
    split_ifs with heq
    · exact hsat
    · exact ih _ (applyAllTImpRules_sat val botForces v_uc bf_uc worldOf b edges hsat hmono)

omit [DecidableEq Atom] [Hashable Atom] in
/-- A satisfiable branch cannot be closed. -/
private lemma closurePred_false_of_sat
    {World : Type*} [Preorder World]
    (val : World → Atom → Prop) (botForces : World → Prop)
    (worldOf : Nat → World)
    (b : IBranch Atom)
    (closurePred : IBranch Atom → Bool)
    (closed_unsat : ∀ (wo : Nat → World) (b' : IBranch Atom),
        closurePred b' = true → ¬ intBranchSatisfied val botForces wo b')
    (hsat : intBranchSatisfied val botForces worldOf b) :
    closurePred b = false := by
  by_contra h
  simp only [Bool.not_eq_false] at h
  exact closed_unsat worldOf b h hsat

/-- One-step lemma: if `child` is a direct child of `source` in `edges`, then
`source` can access `child` according to `isAccessible`. -/
private lemma isAccessible_one_step
    (edges : IEdges) (child source : Nat)
    (hmem : (child, source) ∈ edges) :
    isAccessible edges source child = true := by
  simp only [isAccessible]
  by_cases heq : source == child
  · simp [heq]
  · simp only [heq, Bool.false_eq_true, ite_false]
    have hne : edges ≠ [] := List.ne_nil_of_mem hmem
    have hpos : 0 < edges.length := by
      rwa [List.length_pos_iff_ne_nil]
    cases hn : edges.length with
    | zero => omega
    | succ m =>
      rw [isAccessible.go, List.any_eq_true]
      exact ⟨child, by simp only [List.mem_filterMap]; exact ⟨(child, source), hmem, by simp⟩,
             by simp⟩

/-- When `nw` is not a parent in `edges`, the `go` function from `nw` with any
non-empty fuel always returns `false` for any target (the DFS has no children to explore). -/
private lemma isAccessible_go_nw_no_children
    (edges : IEdges) (nw target : Nat)
    (hno_parent : ∀ child, (child, nw) ∉ edges)
    (fuel : Nat) :
    isAccessible.go edges target nw fuel = false := by
  induction fuel with
  | zero => rfl
  | succ k ih =>
    simp only [isAccessible.go]
    apply List.any_eq_false.mpr
    intro child hmem
    simp only [List.mem_filterMap] at hmem
    obtain ⟨⟨c, p⟩, hedges, hfilt⟩ := hmem
    simp only at hfilt
    by_cases hcond : p == nw
    · simp only [hcond, ite_true, Option.some.injEq] at hfilt
      simp only [beq_iff_eq] at hcond
      subst hcond; subst hfilt
      exact absurd hedges (hno_parent c)
    · simp only [hcond, Bool.false_eq_true, ite_false] at hfilt
      exact absurd hfilt (by simp)

/-- If `nw` is not a parent in `edges ++ [(nw, parentLabel)]` (i.e., parentLabel ≠ nw),
then it is not a parent in the extended edges either. -/
private lemma not_parent_in_extended
    (edges : IEdges) (nw parentLabel : Nat)
    (hno_parent : ∀ child, (child, nw) ∉ edges)
    (hne : parentLabel ≠ nw) :
    ∀ child, (child, nw) ∉ edges ++ [(nw, parentLabel)] := by
  intro child h
  simp only [List.mem_append, List.mem_singleton] at h
  rcases h with h | h
  · exact hno_parent child h
  · simp only [Prod.mk.injEq] at h
    exact hne h.2.symm

/-- `isAccessible.go` is monotone in fuel: if it returns true with less fuel,
it also returns true with more fuel (for the same starting node). -/
private lemma isAccessible_go_mono_fuel
    (edges : IEdges) (target current : Nat) (fuel1 fuel2 : Nat)
    (hle : fuel1 ≤ fuel2)
    (h : isAccessible.go edges target current fuel1 = true) :
    isAccessible.go edges target current fuel2 = true := by
  have key : ∀ (f1 f2 curr : Nat),
      f1 ≤ f2 → isAccessible.go edges target curr f1 = true →
      isAccessible.go edges target curr f2 = true := by
    intro f1; induction f1 with
    | zero => simp [isAccessible.go]
    | succ k ih =>
      intro f2 curr hle' hany
      simp only [isAccessible.go] at hany
      cases f2 with
      | zero => omega
      | succ m =>
        simp only [isAccessible.go]
        rw [List.any_eq_true] at hany ⊢
        obtain ⟨child, hmem, hchild⟩ := hany
        refine ⟨child, hmem, ?_⟩
        split_ifs with heq
        · rfl
        · simp only [heq, Bool.false_eq_true, ite_false] at hchild
          exact ih m child (Nat.le_of_succ_le_succ hle') hchild
  exact key _ _ _ hle h

/-- `MonotoneEdges` extended to work with any fuel: if `isAccessible.go edges target source k`
returns true and `worldOf` is monotone for the edges, then `worldOf source ≤ worldOf target`.

This avoids the need to use a fixed `edges.length` fuel when applying monotonicity. -/
private lemma monotoneEdges_go {World : Type*} [Preorder World]
    (worldOf : Nat → World) (edges : IEdges) (target source : Nat) (k : Nat)
    (hmono : MonotoneEdges worldOf edges)
    (hacc : isAccessible.go edges target source k = true) :
    worldOf source ≤ worldOf target := by
  revert source
  induction k with
  | zero => simp [isAccessible.go]
  | succ m ih =>
    intro source hacc
    simp only [isAccessible.go, List.any_eq_true] at hacc
    obtain ⟨ch, hmem, hch⟩ := hacc
    simp only [List.mem_filterMap] at hmem
    obtain ⟨⟨c, p⟩, hedges, hfilt⟩ := hmem
    simp only at hfilt
    by_cases hcond : p == source
    · simp only [hcond, ite_true, Option.some.injEq] at hfilt
      simp only [beq_iff_eq] at hcond
      -- c = ch, p = source, so (ch, source) ∈ edges
      rw [hfilt, hcond] at hedges
      -- hedges : (ch, source) ∈ edges
      -- isAccessible_one_step: source → ch
      have h1 : isAccessible edges source ch = true := isAccessible_one_step edges ch source hedges
      have hle1 : worldOf source ≤ worldOf ch := hmono _ _ h1
      -- Process hch
      by_cases heq : ch == target
      · -- ch is the target
        simp only [beq_iff_eq] at heq; subst heq
        exact hle1
      · -- ch is not target; recurse
        simp only [heq, Bool.false_eq_true, ite_false] at hch
        have hle2 : worldOf ch ≤ worldOf target := ih ch hch
        exact le_trans hle1 hle2
    · simp only [hcond, Bool.false_eq_true, ite_false] at hfilt
      exact absurd hfilt (by simp)

/-- If `isAccessible.go` on `edges ++ [(nw, parentLabel)]` returns true for target `nw`
starting from `source` using `fuel` steps, and `nw` is completely fresh (not a child or
parent in `edges`, and `parentLabel ≠ nw`), then either `source = parentLabel` or
`isAccessible.go edges parentLabel source fuel = true`.

Note: the conclusion uses the SAME fuel as the hypothesis, which allows chaining steps. -/
private lemma isAccessible_go_reach_nw_implies_reach_parent
    (edges : IEdges) (nw parentLabel : Nat)
    (hno_child : ∀ parent, (nw, parent) ∉ edges) -- nw not a child in old edges
    (hno_parent : ∀ child, (child, nw) ∉ edges) -- nw not a parent in old edges
    (hne : parentLabel ≠ nw)
    (source : Nat) (fuel : Nat)
    (hacc : isAccessible.go (edges ++ [(nw, parentLabel)]) nw source fuel = true) :
    isAccessible.go edges parentLabel source fuel = true ∨ source = parentLabel := by
  revert source
  induction fuel with
  | zero => simp [isAccessible.go]
  | succ k ih =>
    intro source hacc
    simp only [isAccessible.go] at hacc
    rw [List.any_eq_true] at hacc
    obtain ⟨ch, hmem, hchild⟩ := hacc
    simp only [List.mem_filterMap, List.mem_append, List.mem_singleton] at hmem
    obtain ⟨⟨c, p⟩, hedge, hfilt⟩ := hmem
    simp only at hfilt
    by_cases hcond : p == source
    · -- p = source, so c = ch is the child of source
      simp only [hcond, ite_true, Option.some.injEq] at hfilt
      simp only [beq_iff_eq] at hcond
      rw [hfilt, hcond] at hedge
      -- hedge : (ch, source) ∈ edges ∨ (ch, source) = (nw, parentLabel)
      rcases hedge with horig | hext
      · -- edge (ch, source) is in original edges
        by_cases heq : ch == nw
        · -- ch = nw, but (nw, source) in orig edges contradicts hno_child
          simp only [beq_iff_eq] at heq; subst heq
          exact absurd horig (hno_child source)
        · -- ch ≠ nw; apply IH to ch: either parentLabel reachable from ch in k steps,
          -- or ch = parentLabel
          simp only [heq, Bool.false_eq_true, ite_false] at hchild
          rcases ih ch hchild with hreach | rfl
          · -- parentLabel reachable from ch in k steps; chain: source → ch uses 1 more step.
            -- isAccessible.go edges parentLabel source (k+1) = true by one step to ch.
            left
            rw [isAccessible.go, List.any_eq_true]
            refine ⟨ch, ?_, ?_⟩
            · rw [List.mem_filterMap]; exact ⟨(ch, source), ⟨horig, by simp⟩⟩
            · split_ifs with hceq
              · rfl
              · exact hreach
          · -- ch = parentLabel: source → ch is one step in original edges
            left
            rw [isAccessible.go, List.any_eq_true]
            refine ⟨ch, ?_, ?_⟩
            · rw [List.mem_filterMap]; exact ⟨(ch, source), ⟨horig, by simp⟩⟩
            · simp
      · simp only [Prod.mk.injEq] at hext
        obtain ⟨rfl, rfl⟩ := hext
        simp only [beq_self_eq_true, ite_true] at hchild
        right; rfl
    · simp only [hcond, Bool.false_eq_true, ite_false] at hfilt
      exact absurd hfilt (by simp)

/-- When searching for a target `w2 ≠ nw` in the extended edge set `edges ++ [(nw, parentLabel)]`,
the new edge never contributes: the DFS in extended edges is equivalent to the DFS in original
edges (since `nw` is a dead-end — it has no outgoing edges to explore in the DFS). -/
private lemma isAccessible_go_strip_new_edge
    (edges : IEdges) (nw parentLabel : Nat)
    (hnw_not_parent : ∀ child, (child, nw) ∉ edges) -- nw has no children in old edges
    (hnw_ne_parent : parentLabel ≠ nw) -- edge is not a self-loop
    (w2 source : Nat) (hw2 : w2 ≠ nw)
    (fuel : Nat)
    (hacc : isAccessible.go (edges ++ [(nw, parentLabel)]) w2 source fuel = true) :
    isAccessible.go edges w2 source fuel = true := by
  revert source
  induction fuel with
  | zero => simp [isAccessible.go]
  | succ k ih =>
    intro source hacc
    simp only [isAccessible.go, List.any_eq_true] at hacc
    obtain ⟨ch, hmem, hch⟩ := hacc
    simp only [List.mem_filterMap, List.mem_append, List.mem_singleton] at hmem
    obtain ⟨⟨c, p⟩, hedge, hfilt⟩ := hmem
    simp only at hfilt
    by_cases hcond : p == source
    · simp only [hcond, ite_true, Option.some.injEq] at hfilt
      simp only [beq_iff_eq] at hcond
      rw [hfilt, hcond] at hedge
      -- hedge : (ch, source) ∈ edges ∨ (ch, source) = (nw, parentLabel)
      rcases hedge with horig | hext
      · -- Old edge: use it directly in old DFS
        rw [isAccessible.go, List.any_eq_true]
        by_cases heq : ch == w2
        · -- ch is the target w2
          refine ⟨ch, ?_, ?_⟩
          · rw [List.mem_filterMap]; exact ⟨(ch, source), ⟨horig, by simp⟩⟩
          · simp [heq]
        · -- ch is not the target; recurse
          simp only [heq, Bool.false_eq_true, ite_false] at hch
          have ih_result := ih ch hch
          refine ⟨ch, ?_, ?_⟩
          · rw [List.mem_filterMap]; exact ⟨(ch, source), ⟨horig, by simp⟩⟩
          · simp [heq, ih_result]
      · -- New edge: (ch, source) = (nw, parentLabel), so ch = nw, source = parentLabel
        -- Compute helper facts before destructuring
        -- (so we can reference nw and parentLabel by name)
        have hno_children_ext : ∀ child', (child', nw) ∉ edges ++ [(nw, parentLabel)] :=
          not_parent_in_extended edges nw parentLabel hnw_not_parent hnw_ne_parent
        have hnw_ne_w2 : (nw == w2) = false := by simp [Ne.symm hw2]
        simp only [Prod.mk.injEq] at hext
        obtain ⟨rfl, rfl⟩ := hext
        -- Now ch = nw, source = parentLabel; hch has ch = nw and source = parentLabel
        -- hnw_ne_w2 has nw = ch now; hch reduces (ch == w2 = false) to DFS part
        simp only [hnw_ne_w2, Bool.false_eq_true, ite_false] at hch
        -- After rfl, nw became ch; use isAccessible_go_nw_no_children with ch
        have hfalse : isAccessible.go (edges ++ [(ch, source)]) w2 ch k = false :=
          isAccessible_go_nw_no_children (edges ++ [(ch, source)]) ch w2 hno_children_ext k
        exact absurd hch (by rw [hfalse]; simp)
    · simp only [hcond, Bool.false_eq_true, ite_false] at hfilt
      exact absurd hfilt (by simp)

/-- After a world-creating F(imp) step, the new `worldOf'` is monotone for the extended
edge set `edges ++ [(nw, parentLabel)]` whenever the original `worldOf` was monotone
for `edges` and `worldOf parentLabel ≤ worldOf' nw`.

Requires: `nw` is completely fresh — it does not appear anywhere in `edges`. -/
private lemma monotoneEdges_update
    {World : Type*} [Preorder World]
    (worldOf : Nat → World)
    (edges : IEdges)
    (nw parentLabel : Nat)
    (w' : World)
    (hnw_not_child : ∀ parent, (nw, parent) ∉ edges)  -- nw not a child in old edges
    (hnw_not_parent : ∀ child, (child, nw) ∉ edges)   -- nw not a parent in old edges
    (hnw_ne_parent : parentLabel ≠ nw)                  -- new edge is not a self-loop
    (hmono : MonotoneEdges worldOf edges)
    (hle : worldOf parentLabel ≤ w') :
    MonotoneEdges (Function.update worldOf nw w') (edges ++ [(nw, parentLabel)]) := by
  intro w1 w2 hacc
  simp only [MonotoneEdges] at hmono
  -- Unfold isAccessible on extended edges
  simp only [isAccessible] at hacc
  by_cases heq12 : w1 == w2
  · -- w1 = w2: reflexivity
    simp only [beq_iff_eq] at heq12; subst heq12; exact le_refl _
  · simp only [heq12, Bool.false_eq_true, ite_false] at hacc
    -- hacc : isAccessible.go (extended) w2 w1 (edges.length + 1) = true
    -- (since (extended).length = edges.length + 1)
    simp only [List.length_append, List.length_singleton] at hacc
    -- Case split on w2
    by_cases hw2_nw : w2 == nw
    · -- w2 = nw
      simp only [beq_iff_eq] at hw2_nw; subst hw2_nw
      -- hacc : isAccessible.go extended w2 w1 (edges.length + 1) = true
      -- (nw was substituted by w2 via subst hw2_nw)
      -- Case split on w1
      by_cases hw1_nw : w1 == w2
      · -- w1 = w2: impossible since heq12 : ¬(w1 == w2) = true
        simp only [beq_iff_eq] at hw1_nw
        -- w1 = w2, but heq12 : ¬(w1 == w2) = true, contradiction
        subst hw1_nw
        simp at heq12
      · -- w1 ≠ w2 (= nw)
        simp only [beq_iff_eq] at hw1_nw
        -- (Function.update worldOf w2 w') w1 = worldOf w1 (since w1 ≠ w2)
        -- (Function.update worldOf w2 w') w2 = w'
        rw [Function.update_of_ne hw1_nw, Function.update_self]
        -- Need worldOf w1 ≤ w'
        -- Apply isAccessible_go_reach_nw_implies_reach_parent to hacc
        -- (nw = w2 after substitution, parentLabel unchanged)
        rcases isAccessible_go_reach_nw_implies_reach_parent edges w2 parentLabel
            hnw_not_child hnw_not_parent hnw_ne_parent w1 (edges.length + 1) hacc
          with hreach | rfl
        · -- isAccessible.go edges parentLabel w1 (edges.length + 1) = true
          -- Use monotoneEdges_go to get worldOf w1 ≤ worldOf parentLabel
          exact le_trans (monotoneEdges_go worldOf edges parentLabel w1 (edges.length + 1)
                           hmono hreach) hle
        · -- w1 = parentLabel
          exact hle
    · -- w2 ≠ nw
      simp only [beq_iff_eq] at hw2_nw
      -- hacc : isAccessible.go extended w2 w1 (edges.length + 1) = true
      -- Strip new edge: since w2 ≠ nw, the path stays in old edges
      have hacc_old : isAccessible.go edges w2 w1 (edges.length + 1) = true :=
        isAccessible_go_strip_new_edge edges nw parentLabel hnw_not_parent hnw_ne_parent
          w2 w1 hw2_nw (edges.length + 1) hacc
      -- Case split on w1
      by_cases hw1_nw : w1 == nw
      · -- w1 = nw: nw has no children in old edges, so DFS from nw can't reach w2 ≠ nw
        -- Actually hacc_old says isAccessible.go edges w2 nw (edges.length+1) = true
        -- but nw has no children in old edges → contradiction
        simp only [beq_iff_eq] at hw1_nw; subst hw1_nw
        -- nw was substituted by w1 via subst hw1_nw
        rw [isAccessible_go_nw_no_children edges w1 w2 hnw_not_parent
            (edges.length + 1)] at hacc_old
        exact absurd hacc_old (by simp)
      · -- w1 ≠ nw, w2 ≠ nw
        simp only [beq_iff_eq] at hw1_nw
        rw [Function.update_of_ne hw1_nw, Function.update_of_ne hw2_nw]
        -- Need worldOf w1 ≤ worldOf w2
        -- Use monotoneEdges_go with any fuel (edges.length + 1)
        exact monotoneEdges_go worldOf edges w2 w1 (edges.length + 1) hmono hacc_old

/-! ## Freshness Invariant -/

/-- Branch freshness invariant: all signed-formula labels on `b` are strictly below `nw`,
and all edge endpoints in `edges` are strictly below `nw`.

This ensures that when the F(→) world-creating rule introduces a fresh label `nwH`
(the current `nextWorld` counter), `nwH` does not already appear on the branch or in
the edge set, making `Function.update worldOf nwH w'` well-defined for all existing labels. -/
def FreshAbove (b : IBranch Atom) (edges : IEdges) (nw : Nat) : Prop :=
  (∀ sf ∈ b, sf.label < nw) ∧ (∀ c p : Nat, (c, p) ∈ edges → c < nw ∧ p < nw)

omit [Hashable Atom] in
/-- `applyAllTImpRules` preserves `FreshAbove`: the T(φ→ψ) persistence rule only adds
formulas at world labels already present on the branch, so no new labels are introduced. -/
private lemma freshAbove_applyAllTImpRules (b : IBranch Atom) (edges : IEdges) (nw : Nat)
    (hfresh : FreshAbove b edges nw) :
    FreshAbove (applyAllTImpRules b edges) edges nw := by
  obtain ⟨hbounds, hedges⟩ := hfresh
  refine ⟨?_, hedges⟩
  intro sf hmem
  simp only [applyAllTImpRules, List.mem_append, List.mem_flatten, List.mem_filterMap] at hmem
  rcases hmem with hmem | ⟨newForms, ⟨sf', hmem', houter⟩, hmem_inner⟩
  · exact hbounds sf hmem
  · cases hsign : sf'.sign with
    | neg => simp only [hsign] at houter; simp at houter
    | pos =>
      cases hform : sf'.formula with
      | atom _ | bot | and _ _ | or _ _ =>
          simp only [hsign, hform] at houter; simp at houter
      | imp φ ψ =>
        simp only [hsign, hform] at houter
        split_ifs at houter with hemp
        · simp only [Option.some.injEq] at houter
          rw [← houter] at hmem_inner
          simp only [intTImpRule, List.mem_filterMap] at hmem_inner
          obtain ⟨w', hw'_mem, hw'_sf⟩ := hmem_inner
          simp only [List.mem_filter, List.mem_eraseDups, List.mem_map] at hw'_mem
          obtain ⟨⟨sf'', hmem'', hlab⟩, _⟩ := hw'_mem
          split_ifs at hw'_sf with hany1 hany2
          · simp only [Option.some.injEq] at hw'_sf
            rw [← hw'_sf]; simp only; rw [← hlab]
            exact hbounds sf'' hmem''

omit [Hashable Atom] in
/-- The persistence fixpoint preserves `FreshAbove`. -/
private lemma freshAbove_applyPersistenceFixpoint (b : IBranch Atom) (edges : IEdges) (nw : Nat)
    (fuel : Nat) (hfresh : FreshAbove b edges nw) :
    FreshAbove (applyPersistenceFixpoint b edges fuel) edges nw := by
  induction fuel generalizing b with
  | zero => simpa [applyPersistenceFixpoint] using hfresh
  | succ k ih =>
    simp only [applyPersistenceFixpoint]
    split_ifs
    · exact hfresh
    · exact ih _ (freshAbove_applyAllTImpRules b edges nw hfresh)

omit [DecidableEq Atom] [Hashable Atom] in
/-- A non-world-creating expansion step preserves `FreshAbove` when all new forms use
existing labels (`sf'.label < nw` for all `sf' ∈ newForms`). -/
private lemma freshAbove_extendMany (b : IBranch Atom) (edges : IEdges) (nw : Nat)
    (newForms : List (ISF Atom))
    (hfresh : FreshAbove b edges nw)
    (hnew : ∀ sf' ∈ newForms, sf'.label < nw) :
    FreshAbove (Branch.extendMany b newForms) edges nw :=
  ⟨fun sf hmem => by
      simp only [Branch.extendMany, List.mem_append] at hmem
      rcases hmem with h | h
      · exact hnew sf h
      · exact hfresh.1 sf h,
    hfresh.2⟩

omit [DecidableEq Atom] [Hashable Atom] in
/-- The F(→) world-creating step produces `FreshAbove … (nw+1)` for the new branch
and extended edge set. The new world `nw` and its parent edge both become `< nw + 1`. -/
private lemma freshAbove_world_create (b : IBranch Atom) (edges : IEdges) (nw parentLabel : Nat)
    (newForms : List (ISF Atom))
    (hfresh : FreshAbove b edges nw)
    (hparent_lt : parentLabel < nw)
    (hnew : ∀ sf' ∈ newForms, sf'.label ≤ nw) :
    FreshAbove (Branch.extendMany b newForms) (edges ++ [(nw, parentLabel)]) (nw + 1) :=
  ⟨fun sf hmem => by
      simp only [Branch.extendMany, List.mem_append] at hmem
      rcases hmem with h | h
      · exact Nat.lt_succ_of_le (hnew sf h)
      · exact Nat.lt_succ_of_lt (hfresh.1 sf h),
    fun c p hmem => by
      simp only [List.mem_append, List.mem_singleton] at hmem
      rcases hmem with h | h
      · exact ⟨Nat.lt_succ_of_lt (hfresh.2 c p h).1,
               Nat.lt_succ_of_lt (hfresh.2 c p h).2⟩
      · simp only [Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨Nat.lt_succ_self _, Nat.lt_succ_of_lt hparent_lt⟩⟩

/-- When `FreshAbove b edges nw` holds and `worldOf'` agrees with `worldOf` on all
labels `≠ nw`, then `MonotoneEdges worldOf' edges` follows from `MonotoneEdges worldOf edges`.

Used for non-world-creating (T∧/F∨) rule applications where the world function only
changes at the fresh label `nw`, which is not in the existing edge set. -/
private lemma monotoneEdges_of_agree
    {World : Type*} [Preorder World]
    (wo wo' : Nat → World) (edges : IEdges) (nw : Nat)
    (hfresh_edges : ∀ c p, (c, p) ∈ edges → c < nw ∧ p < nw)
    (hagree : ∀ k, k ≠ nw → wo' k = wo k)
    (hmono : MonotoneEdges wo edges) :
    MonotoneEdges wo' edges := by
  intro w1 w2 hacc
  simp only [isAccessible] at hacc
  split_ifs at hacc with heq
  · simp only [beq_iff_eq] at heq; subst heq; exact le_refl _
  · have hw2_child : ∃ p, (w2, p) ∈ edges := by
      have key : ∀ k start, isAccessible.go edges w2 start k = true → ∃ p, (w2, p) ∈ edges := by
        intro k
        induction k with
        | zero => simp [isAccessible.go]
        | succ m ih =>
          intro start hgo
          simp only [isAccessible.go, List.any_eq_true, List.mem_filterMap] at hgo
          obtain ⟨child, ⟨⟨c, p⟩, he, hfilt⟩, hchild⟩ := hgo
          simp only at hfilt
          split_ifs at hfilt with hcond
          · simp only [Option.some.injEq] at hfilt
            subst hfilt
            split_ifs at hchild with heq2
            · simp only [beq_iff_eq] at heq2; subst heq2
              exact ⟨p, he⟩
            · exact ih c hchild
      exact key _ w1 hacc
    have hw1_parent : ∃ c, (c, w1) ∈ edges := by
      have key : ∀ k start, isAccessible.go edges w2 start k = true → ∃ c, (c, start) ∈ edges := by
        intro k
        induction k with
        | zero => simp [isAccessible.go]
        | succ m ih =>
          intro start hgo
          simp only [isAccessible.go, List.any_eq_true, List.mem_filterMap] at hgo
          obtain ⟨child, ⟨⟨c, p⟩, he, hfilt⟩, _⟩ := hgo
          simp only at hfilt
          split_ifs at hfilt with hcond
          · simp only [Option.some.injEq] at hfilt
            subst hfilt
            simp only [beq_iff_eq] at hcond; subst hcond
            exact ⟨c, he⟩
      exact key _ w1 hacc
    obtain ⟨c_w1, hc_w1⟩ := hw1_parent
    obtain ⟨p_w2, hp_w2⟩ := hw2_child
    have hw1_lt : w1 < nw := (hfresh_edges c_w1 w1 hc_w1).2
    have hw2_lt : w2 < nw := (hfresh_edges w2 p_w2 hp_w2).1
    have hw1_ne : w1 ≠ nw := Nat.ne_of_lt hw1_lt
    have hw2_ne : w2 ≠ nw := Nat.ne_of_lt hw2_lt
    rw [hagree w1 hw1_ne, hagree w2 hw2_ne]
    exact hmono w1 w2 (by simp only [isAccessible, heq, Bool.false_eq_true, ite_false]; exact hacc)

omit [DecidableEq Atom] [Hashable Atom] in
/-- For a non-world-creating linear result (`newEdge = none`), all new forms have the
same label as the expanded signed formula `sf`. -/
private lemma intApplyRuleFull_none_labels
    (sf : ISF Atom) (nwH : Nat) (b : IBranch Atom)
    (newForms : List (ISF Atom)) (nw' : Nat)
    (h : intApplyRuleFull sf nwH b = .linearResult newForms nw' none) :
    ∀ sf' ∈ newForms, sf'.label = sf.label := by
  obtain ⟨sign, form, label⟩ := sf
  simp only [intApplyRuleFull] at h
  cases sign with
  | pos =>
    cases form with
    | and φ ψ =>
      simp only [IntRuleResult.linearResult.injEq] at h
      obtain ⟨rfl, _, _⟩ := h
      intro sf' hmem'
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem'
      rcases hmem' with rfl | rfl <;> rfl
    | _ => simp at h
  | neg =>
    cases form with
    | or φ ψ =>
      simp only [IntRuleResult.linearResult.injEq] at h
      obtain ⟨rfl, _, _⟩ := h
      intro sf' hmem'
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem'
      rcases hmem' with rfl | rfl <;> rfl
    | imp φ ψ => simp [intFImpRule] at h
    | _ => simp at h

omit [DecidableEq Atom] [Hashable Atom] in
/-- For a branching result, all new forms in each branch have the same label as `sf`. -/
private lemma intApplyRuleFull_branching_labels
    (sf : ISF Atom) (nwH : Nat) (b : IBranch Atom)
    (branches' : List (List (ISF Atom))) (nw' : Nat)
    (h : intApplyRuleFull sf nwH b = .branchingResult branches' nw') :
    ∀ br ∈ branches', ∀ sf' ∈ br, sf'.label = sf.label := by
  obtain ⟨sign, form, label⟩ := sf
  simp only [intApplyRuleFull] at h
  cases sign with
  | pos =>
    cases form with
    | or φ ψ =>
      simp only [IntRuleResult.branchingResult.injEq] at h
      obtain ⟨rfl, _⟩ := h
      intro br hbr sf' hsf'
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hbr
      rcases hbr with rfl | rfl
      · simp only [List.mem_cons, List.mem_nil_iff, or_false] at hsf'; rcases hsf' with rfl; rfl
      · simp only [List.mem_cons, List.mem_nil_iff, or_false] at hsf'; rcases hsf' with rfl; rfl
    | _ => simp at h
  | neg =>
    cases form with
    | and φ ψ =>
      simp only [IntRuleResult.branchingResult.injEq] at h
      obtain ⟨rfl, _⟩ := h
      intro br hbr sf' hsf'
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hbr
      rcases hbr with rfl | rfl
      · simp only [List.mem_cons, List.mem_nil_iff, or_false] at hsf'; rcases hsf' with rfl; rfl
      · simp only [List.mem_cons, List.mem_nil_iff, or_false] at hsf'; rcases hsf' with rfl; rfl
    | _ => simp at h

omit [DecidableEq Atom] [Hashable Atom] in
/-- For a world-creating linear result (`newEdge = some e`), the new edge is `(nwH, sf.label)`,
`nw' = nwH + 1`, and all new forms have label `= nwH`. -/
private lemma intApplyRuleFull_some_info
    (sf : ISF Atom) (nwH : Nat) (b : IBranch Atom)
    (newForms : List (ISF Atom)) (nw' : Nat) (e : Nat × Nat)
    (h : intApplyRuleFull sf nwH b = .linearResult newForms nw' (some e)) :
    e = (nwH, sf.label) ∧ nw' = nwH + 1 ∧ ∀ sf' ∈ newForms, sf'.label = nwH := by
  obtain ⟨sign, form, label⟩ := sf
  simp only [intApplyRuleFull] at h
  cases sign with
  | pos => cases form <;> simp at h
  | neg =>
    cases form with
    | imp φ ψ =>
      simp only [intFImpRule] at h
      simp only [IntRuleResult.linearResult.injEq] at h
      obtain ⟨rfl, rfl, he⟩ := h
      simp only [Option.some.injEq] at he; subst he
      refine ⟨rfl, rfl, ?_⟩
      intro sf' hmem'
      simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hmem'
      rcases hmem' with (rfl | rfl) | hmem_pers
      · rfl
      · rfl
      · simp only [propagatePersistence, posFormulasAt, List.mem_map] at hmem_pers
        obtain ⟨_, _, rfl⟩ := hmem_pers; rfl
    | _ => simp at h

omit [DecidableEq Atom] [Hashable Atom] in
/-- For a non-world-creating linear result (`newEdge = none`), the next world number `nw'`
equals the current world number `nwH`. -/
private lemma intApplyRuleFull_none_nw
    (sf : ISF Atom) (nwH : Nat) (b : IBranch Atom)
    (newForms : List (ISF Atom)) (nw' : Nat)
    (h : intApplyRuleFull sf nwH b = .linearResult newForms nw' none) :
    nw' = nwH := by
  obtain ⟨sign, form, label⟩ := sf
  simp only [intApplyRuleFull] at h
  cases sign with
  | pos =>
    cases form with
    | and φ ψ =>
      simp only [IntRuleResult.linearResult.injEq] at h
      obtain ⟨_, rfl, _⟩ := h; rfl
    | _ => simp at h
  | neg =>
    cases form with
    | or φ ψ =>
      simp only [IntRuleResult.linearResult.injEq] at h
      obtain ⟨_, rfl, _⟩ := h; rfl
    | imp φ ψ => simp [intFImpRule] at h
    | _ => simp at h

omit [DecidableEq Atom] [Hashable Atom] in
/-- For a branching result, the next world number `nw'` equals the current world number `nwH`. -/
private lemma intApplyRuleFull_branching_nw
    (sf : ISF Atom) (nwH : Nat) (b : IBranch Atom)
    (branches' : List (List (ISF Atom))) (nw' : Nat)
    (h : intApplyRuleFull sf nwH b = .branchingResult branches' nw') :
    nw' = nwH := by
  obtain ⟨sign, form, label⟩ := sf
  simp only [intApplyRuleFull] at h
  cases sign with
  | pos =>
    cases form with
    | or φ ψ =>
      simp only [IntRuleResult.branchingResult.injEq] at h
      obtain ⟨_, rfl⟩ := h; rfl
    | _ => simp at h
  | neg =>
    cases form with
    | and φ ψ =>
      simp only [IntRuleResult.branchingResult.injEq] at h
      obtain ⟨_, rfl⟩ := h; rfl
    | _ => simp at h

omit [Hashable Atom] in
/-- If `intExpandBranches` returns `closed`, then every input branch is unsatisfiable.

This is the core loop invariant for the soundness proof. The proof requires:
1. Persistence fixpoint preserves satisfiability (with monotone `worldOf`)
2. Step expansion preserves satisfiability (via `intRule_preserves_sat`)
3. Closed branches are unsatisfiable (via `closed_unsat`)

The `closed_unsat` parameter generalizes over closure predicates (intuitionistic vs minimal).
The `edgeSets` parameter tracks parent-child accessibility edges, one set per branch.

The proof requires showing persistence preserves satisfiability (which needs monotone
`worldOf`: `n ≤ m → worldOf n ≤ worldOf m`), step expansion preserves satisfiability
(which needs `intRule_preserves_sat`), and threading the existential `worldOf'` from
world-creating steps through the induction. -/
lemma intExpandBranches_closed_unsat
    {World : Type*} [Preorder World]
    (val : World → Atom → Prop) (botForces : World → Prop)
    (v_uc : ∀ {w w' : World} (p : Atom), w ≤ w' → val w p → val w' p)
    (bf_uc : ∀ {w w' : World}, w ≤ w' → botForces w → botForces w')
    (fuel : Nat)
    (closurePred : IBranch Atom → Bool)
    (closed_unsat : ∀ (worldOf : Nat → World) (b : IBranch Atom),
        closurePred b = true → ¬ intBranchSatisfied val botForces worldOf b) :
    ∀ (branches : List (IBranch Atom))
      (expandedSets : List (List (ISF Atom)))
      (nextWorlds : List Nat)
      (edgeSets : List IEdges),
      expandedSets.length = branches.length →
      nextWorlds.length = branches.length →
      edgeSets.length = branches.length →
      (∀ b edges nw, ((b, edges), nw) ∈ (branches.zip edgeSets).zip nextWorlds →
          FreshAbove b edges nw) →
      intExpandBranches branches expandedSets nextWorlds edgeSets fuel closurePred = .closed →
      ∀ (b : IBranch Atom) (edges : IEdges),
          (b, edges) ∈ branches.zip edgeSets →
          ∀ (worldOf : Nat → World),
          MonotoneEdges worldOf edges →
          ¬ intBranchSatisfied val botForces worldOf b := by
  -- Prove the conclusion by induction on fuel, tracking edgeSets and MonotoneEdges per branch.
  -- The inner induction on the go-loop is captured by the `key` suffices inside succ case.
  suffices hcore : ∀ (fuel' : Nat)
      (branches : List (IBranch Atom))
      (expandedSets : List (List (ISF Atom)))
      (nextWorlds : List Nat)
      (edgeSets : List IEdges),
      expandedSets.length = branches.length →
      nextWorlds.length = branches.length →
      edgeSets.length = branches.length →
      (∀ b e nw, ((b, e), nw) ∈ (branches.zip edgeSets).zip nextWorlds →
          FreshAbove b e nw) →
      intExpandBranches branches expandedSets nextWorlds edgeSets fuel' closurePred = .closed →
      ∀ (b : IBranch Atom) (edges : IEdges),
          (b, edges) ∈ branches.zip edgeSets →
          ∀ (worldOf : Nat → World),
          MonotoneEdges worldOf edges →
          ¬ intBranchSatisfied val botForces worldOf b by
    intro branches expandedSets nextWorlds edgeSets hlength_exp hlength_nw hlength_edges
        hfresh_all h b edges hbe worldOf hmono hsat
    exact hcore fuel branches expandedSets nextWorlds edgeSets
        hlength_exp hlength_nw hlength_edges hfresh_all h b edges hbe worldOf hmono hsat
  -- Prove hcore by induction on fuel'
  intro fuel'
  induction fuel' with
  | zero =>
    intro branches expandedSets nextWorlds edgeSets _ _ _ _ h b edges hzip worldOf _ hsat
    simp only [intExpandBranches] at h
    split at h
    · exact absurd h (by simp)
    · rename_i hfind
      have hb : b ∈ branches := (List.of_mem_zip hzip).1
      have hfn := List.findSome?_eq_none_iff.mp hfind b hb
      split_ifs at hfn with hcl
      · exact closed_unsat worldOf b hcl hsat
  | succ fuel'' ih =>
    intro branches expandedSets nextWorlds edgeSets hlength_exp hlength_nw hlength_edges
        hfresh_branches h b edges hzip worldOf hmono hsat
    -- Prove the suffices claim by induction on the go-loop
    -- Inner loop: go branches expandedSets nextWorlds edgeSets [] [] [] []
    -- We need to track the pending list
    suffices key : ∀ (pending : List (IBranch Atom))
        (pendingExp : List (List (ISF Atom)))
        (pendingNW : List Nat)
        (pendingEdges : List IEdges)
        (done : List (IBranch Atom))
        (doneExp : List (List (ISF Atom)))
        (doneNW : List Nat)
        (doneEdges : List IEdges),
        pendingExp.length = pending.length →
        pendingNW.length = pending.length →
        pendingEdges.length = pending.length →
        doneExp.length = done.length →
        doneNW.length = done.length →
        doneEdges.length = done.length →
        (∀ b e nw, ((b, e), nw) ∈ (pending.zip pendingEdges).zip pendingNW →
            FreshAbove b e nw) →
        (∀ b e nw, ((b, e), nw) ∈ (done.zip doneEdges).zip doneNW →
            FreshAbove b e nw) →
        intExpandBranches.go closurePred fuel'' pending pendingExp pendingNW pendingEdges
            done doneExp doneNW doneEdges = .closed →
        ∀ bp edgesP, (bp, edgesP) ∈ pending.zip pendingEdges →
            ∀ (wo : Nat → World), MonotoneEdges wo edgesP →
            ¬ intBranchSatisfied val botForces wo bp from by
      -- Apply key with pending = branches, done = []
      simp only [intExpandBranches] at h
      exact key branches expandedSets nextWorlds edgeSets [] [] [] []
        hlength_exp hlength_nw hlength_edges (by simp) (by simp) (by simp)
        hfresh_branches
        (fun _ _ _ hmem => by simp at hmem)
        (by simpa [intExpandBranches] using h)
        b edges hzip worldOf hmono hsat
    -- Prove key by induction on pending
    intro pending
    induction pending with
    | nil =>
      intro pendingExp pendingNW pendingEdges done doneExp doneNW doneEdges
        _ _ _ _ _ _ _ _ _ bp edgesP hzip_p
      simp only [List.zip_nil_left, List.mem_nil_iff] at hzip_p
    | cons bh bt ih_inner =>
      intro pendingExp pendingNW pendingEdges done doneExp doneNW doneEdges
        hlength_exp hlength_nw hlength_edges hdlength_exp hdlength_nw hdlength_edges
        hfreshPend hfreshDone
        hgo bp edgesP hzip_p wo hmono_p hsat_p
      simp only [List.length_cons] at hlength_exp hlength_nw hlength_edges
      cases hpendingExp : pendingExp with
      | nil => simp [hpendingExp] at hlength_exp
      | cons eH eT =>
        cases hpendingNW : pendingNW with
        | nil => simp [hpendingNW] at hlength_nw
        | cons nwH nwT =>
          cases hpendingEdges : pendingEdges with
          | nil => simp [hpendingEdges] at hlength_edges
          | cons edgesH edgesT =>
            rw [hpendingExp] at hlength_exp
            rw [hpendingNW] at hlength_nw
            rw [hpendingEdges] at hlength_edges
            simp only [List.length_cons] at hlength_exp hlength_nw hlength_edges
            -- Reduce hlength_exp/nw/edges from n+1=m+1 form to n=m for downstream use
            replace hlength_exp : eT.length = bt.length := by omega
            replace hlength_nw : nwT.length = bt.length := by omega
            replace hlength_edges : edgesT.length = bt.length := by omega
            rw [hpendingEdges] at hzip_p
            rw [hpendingExp, hpendingNW, hpendingEdges] at hgo
            simp only [List.zip_cons_cons, List.mem_cons] at hzip_p
            set bPers := applyPersistenceFixpoint bh edgesH (fuel'' + 1) with hbPers_def
            -- Extract freshness for the head from the pending invariant
            have hfreshHead : FreshAbove bh edgesH nwH :=
                hfreshPend bh edgesH nwH (by
                    rw [hpendingNW, hpendingEdges]
                    simp only [List.zip_cons_cons, List.mem_cons]
                    exact Or.inl trivial)
            have hfreshTail : ∀ b e nw,
                    ((b, e), nw) ∈ (bt.zip edgesT).zip nwT → FreshAbove b e nw :=
                fun b e nw h => hfreshPend b e nw (by
                    rw [hpendingNW, hpendingEdges]
                    simp only [List.zip_cons_cons, List.mem_cons]
                    exact Or.inr h)
            -- Persistence fixpoint preserves FreshAbove
            have hfreshAbove_pers : FreshAbove bPers edgesH nwH :=
                freshAbove_applyPersistenceFixpoint bh edgesH nwH (fuel'' + 1) hfreshHead
            simp only [intExpandBranches.go] at hgo
            by_cases hcl : closurePred bPers = true
            · rw [if_pos hcl] at hgo
              rcases hzip_p with ⟨rfl, rfl⟩ | hmem_rest
              · -- bp = bh, edgesP = edgesH (rcases eliminates edgesH → use edgesP)
                have hsat_pers : intBranchSatisfied val botForces wo bPers :=
                  applyPersistenceFixpoint_sat val botForces v_uc bf_uc wo bh edgesP (fuel'' + 1)
                    hsat_p hmono_p
                exact closed_unsat wo bPers hcl hsat_pers
              · -- Freshness for done ++ [bPers] with doneEdges ++ [edgesH] and doneNW ++ [nwH]
                have hfreshDoneNew : ∀ b e nw,
                    ((b, e), nw) ∈ ((done ++ [bPers]).zip (doneEdges ++ [edgesH])).zip
                        (doneNW ++ [nwH]) → FreshAbove b e nw := by
                  intro b e nw hmem
                  have hlen_de : done.length = doneEdges.length := by omega
                  have hlen_denz : (done.zip doneEdges).length = doneNW.length := by
                    rw [List.length_zip]
                    have : min done.length doneEdges.length = done.length :=
                      Nat.min_eq_left (by omega)
                    omega
                  rw [List.zip_append hlen_de, List.zip_append hlen_denz,
                      List.mem_append] at hmem
                  simp only [List.zip_cons_cons, List.zip_nil_right, List.mem_cons,
                             List.mem_nil_iff, or_false, Prod.mk.injEq] at hmem
                  rcases hmem with h1 | ⟨⟨rfl, rfl⟩, rfl⟩
                  · exact hfreshDone b e nw h1
                  · exact hfreshAbove_pers
                exact ih_inner eT nwT edgesT (done ++ [bPers]) (doneExp ++ [eH]) (doneNW ++ [nwH])
                    (doneEdges ++ [edgesH])
                    hlength_exp hlength_nw hlength_edges (by simp [hdlength_exp])
                    (by simp [hdlength_nw]) (by simp [hdlength_edges])
                    hfreshTail hfreshDoneNew
                    hgo bp edgesP hmem_rest wo hmono_p hsat_p
            · rw [if_neg hcl] at hgo
              cases hstep : intStepBranch bPers eH nwH with
              | none => rw [hstep] at hgo; simp at hgo
              | some step =>
                obtain ⟨result, newExp⟩ := step
                rw [hstep] at hgo
                -- hgo is already unfolded; no further simp needed here
                -- Extract sf from intStepBranch
                obtain ⟨sf, hsf_mem, hresult_sf⟩ :
                    ∃ sf ∈ bPers, intApplyRuleFull sf nwH bPers = result := by
                  simp only [intStepBranch] at hstep
                  obtain ⟨sf, hmem, hval⟩ := List.exists_of_findSome?_eq_some hstep
                  refine ⟨sf, hmem, ?_⟩
                  cases h : intApplyRuleFull sf nwH bPers with
                  | notApplicable => simp [h] at hval
                  | linearResult a b c =>
                    simp only [h] at hval
                    by_cases hexp : (eH.any fun x => x == sf) = true
                    · simp [hexp] at hval
                    · simp only [hexp, Bool.false_eq_true, ite_false, Option.some.injEq,
                          Prod.mk.injEq] at hval
                      exact hval.1
                  | branchingResult a b =>
                    simp only [h] at hval
                    by_cases hexp : (eH.any fun x => x == sf) = true
                    · simp [hexp] at hval
                    · simp only [hexp, Bool.false_eq_true, ite_false, Option.some.injEq,
                          Prod.mk.injEq] at hval
                      exact hval.1
                cases hresult : result with
                | linearResult newForms nw' newEdge =>
                  rw [hresult] at hgo hstep hresult_sf
                  -- Freshness: all labels in bPers are < nwH, hence ≠ nwH
                  have hfresh : ∀ sf' ∈ bPers, sf'.label ≠ nwH :=
                    fun sf' hmem' => Nat.ne_of_lt (hfreshAbove_pers.1 sf' hmem')
                  -- edges' is shared across both sub-cases of hzip_p
                  set edges' := match newEdge with | none => edgesH | some e => edgesH ++ [e]
                      with hedges'_def
                  rcases hzip_p with ⟨rfl, rfl⟩ | hmem_rest
                  · -- linearResult bp=bh case: apply intRule_preserves_sat + ih
                    simp only [] at hgo
                    -- Satisfaction of bPers under wo
                    have hsat_pers : intBranchSatisfied val botForces wo bPers :=
                      applyPersistenceFixpoint_sat val botForces v_uc bf_uc wo bh edgesP
                        (fuel'' + 1) hsat_p hmono_p
                    -- Apply intRule_preserves_sat to get worldOf' with agreement and ordering
                    have hpres := intRule_preserves_sat val botForces v_uc bf_uc wo bPers sf
                        hsf_mem hsat_pers nwH hfresh
                    rw [hresult_sf] at hpres
                    obtain ⟨worldOf', hagree, hsat_new, hord⟩ := hpres
                    -- Freshness for the expanded branch
                    have hfreshNew : FreshAbove (Branch.extendMany bPers newForms) edges' nw' := by
                      rcases hnE : newEdge with _ | e_val
                      · rw [hnE] at hresult_sf
                        have hnw'eq :=
                          intApplyRuleFull_none_nw sf nwH bPers newForms nw' hresult_sf
                        have hlabels :=
                          intApplyRuleFull_none_labels sf nwH bPers newForms nw' hresult_sf
                        rw [show edges' = edgesP from by simp [hedges'_def, hnE], hnw'eq]
                        exact freshAbove_extendMany bPers edgesP nwH newForms hfreshAbove_pers
                          (fun sf' h' => hlabels sf' h' ▸ hfreshAbove_pers.1 sf hsf_mem)
                      · rw [hnE] at hresult_sf
                        obtain ⟨he, hnw'eq, hlabels⟩ :=
                          intApplyRuleFull_some_info sf nwH bPers newForms nw' e_val hresult_sf
                        rw [show edges' = edgesP ++ [e_val] from by simp [hedges'_def, hnE],
                            he, hnw'eq]
                        exact freshAbove_world_create bPers edgesP nwH sf.label newForms
                          hfreshAbove_pers (hfreshAbove_pers.1 sf hsf_mem)
                          (fun sf' h' => Nat.le_of_eq (hlabels sf' h'))
                    -- Combined freshness for done ++ [extendMany bPers newForms] ++ bt
                    have hfreshCombLin : ∀ b e nw,
                        ((b, e), nw) ∈ ((done ++ [Branch.extendMany bPers newForms] ++ bt).zip
                                        (doneEdges ++ [edges'] ++ edgesT)).zip
                                       (doneNW ++ [nw'] ++ nwT) → FreshAbove b e nw := by
                      intro b e nw hmem
                      have hlen1 : (done ++ [Branch.extendMany bPers newForms]).length =
                                   (doneEdges ++ [edges']).length := by simp; omega
                      have hlen2 : (done ++ [Branch.extendMany bPers newForms]).length =
                                   (doneNW ++ [nw']).length := by simp; omega
                      rw [List.zip_append hlen1] at hmem
                      have hlen2_adj :
                          ((done ++ [Branch.extendMany bPers newForms]).zip
                           (doneEdges ++ [edges'])).length =
                           (doneNW ++ [nw']).length := by
                        rw [List.length_zip,
                            Nat.min_eq_left (Nat.le_of_eq hlen1)]; exact hlen2
                      rw [List.zip_append hlen2_adj, List.mem_append] at hmem
                      rcases hmem with h_front | h_back
                      · have hlen_de : done.length = doneEdges.length := by omega
                        have hlen_denz : (done.zip doneEdges).length = doneNW.length := by
                          rw [List.length_zip]
                          exact (Nat.min_eq_left (by omega)).trans (by omega)
                        rw [List.zip_append hlen_de, List.zip_append hlen_denz,
                            List.mem_append] at h_front
                        simp only [List.zip_cons_cons, List.zip_nil_right, List.mem_cons,
                                   List.mem_nil_iff, or_false, Prod.mk.injEq] at h_front
                        rcases h_front with h1 | ⟨⟨rfl, rfl⟩, rfl⟩
                        · exact hfreshDone b e nw h1
                        · exact hfreshNew
                      · exact hfreshTail b e nw h_back
                    -- Monotonicity of worldOf' for edges'
                    have hmono_new : MonotoneEdges worldOf' edges' := by
                      rcases hnE : newEdge with _ | ⟨c, p⟩
                      · -- None: edges' = edgesP; worldOf' agrees with wo on edgesP
                        rw [show edges' = edgesP from by simp [hedges'_def, hnE]]
                        exact monotoneEdges_of_agree wo worldOf' edgesP nwH
                            hfreshAbove_pers.2 hagree hmono_p
                      · -- Some (c, p): edges' = edgesP ++ [(c, p)]
                        rw [hnE] at hresult_sf
                        obtain ⟨he_val, _, _⟩ :=
                          intApplyRuleFull_some_info sf nwH bPers newForms nw' (c, p)
                            hresult_sf
                        simp only [Prod.mk.injEq] at he_val
                        obtain ⟨hc, hp⟩ := he_val
                        subst hc; subst hp
                        -- hord reduces to wo sf.label ≤ worldOf' c
                        simp only [hnE] at hord
                        rw [show edges' = edgesP ++ [(c, sf.label)] from
                            by simp [hedges'_def, hnE]]
                        -- worldOf' = Function.update wo c (worldOf' c) by hagree
                        have hwo'_eq : worldOf' = Function.update wo c (worldOf' c) := by
                          funext k
                          by_cases hk : k = c
                          · subst hk; simp
                          · rw [Function.update_of_ne hk, hagree k hk]
                        rw [hwo'_eq]
                        exact monotoneEdges_update wo edgesP c sf.label (worldOf' c)
                            (fun par h =>
                              absurd (hfreshAbove_pers.2 c par h).1 (Nat.lt_irrefl _))
                            (fun ch h =>
                              absurd (hfreshAbove_pers.2 ch c h).2 (Nat.lt_irrefl _))
                            (Nat.ne_of_lt (hfreshAbove_pers.1 sf hsf_mem))
                            hmono_p hord
                    -- Apply ih to get contradiction from hsat_new
                    refine absurd hsat_new
                        (ih _ _ _ _ (by simp [hdlength_exp, hlength_exp])
                          (by simp [hdlength_nw, hlength_nw])
                          (by simp [hdlength_edges, hlength_edges])
                          hfreshCombLin hgo (Branch.extendMany bPers newForms) edges' ?_
                          worldOf' hmono_new)
                    rw [List.zip_append (by simp [hdlength_edges]), List.mem_append]
                    apply Or.inl
                    rw [List.zip_append (by omega : done.length = doneEdges.length),
                        List.mem_append]
                    exact Or.inr (by simp)
                  · -- linearResult bp∈bt case: bp is in the tail bt with edges edgesT;
                    -- after expanding, bp is still in the new branch list at the same position.
                    simp only [] at hgo
                    -- Build freshness for done ++ [extendMany bPers newForms] ++ bt
                    have hfreshNew : FreshAbove (Branch.extendMany bPers newForms) edges' nw' := by
                      rcases hnE : newEdge with _ | e_val
                      · rw [hnE] at hresult_sf
                        have hnw'eq :=
                          intApplyRuleFull_none_nw sf nwH bPers newForms nw' hresult_sf
                        have hlabels :=
                          intApplyRuleFull_none_labels sf nwH bPers newForms nw' hresult_sf
                        rw [show edges' = edgesH from by simp [hedges'_def, hnE], hnw'eq]
                        exact freshAbove_extendMany bPers edgesH nwH newForms hfreshAbove_pers
                          (fun sf' h' => hlabels sf' h' ▸ hfreshAbove_pers.1 sf hsf_mem)
                      · rw [hnE] at hresult_sf
                        obtain ⟨he, hnw'eq, hlabels⟩ :=
                          intApplyRuleFull_some_info sf nwH bPers newForms nw' e_val hresult_sf
                        rw [show edges' = edgesH ++ [e_val] from by simp [hedges'_def, hnE],
                            he, hnw'eq]
                        exact freshAbove_world_create bPers edgesH nwH sf.label newForms
                          hfreshAbove_pers (hfreshAbove_pers.1 sf hsf_mem)
                          (fun sf' h' => Nat.le_of_eq (hlabels sf' h'))
                    have hfreshCombLin : ∀ b e nw,
                        ((b, e), nw) ∈ ((done ++ [Branch.extendMany bPers newForms] ++ bt).zip
                                        (doneEdges ++ [edges'] ++ edgesT)).zip
                                       (doneNW ++ [nw'] ++ nwT) → FreshAbove b e nw := by
                      intro b e nw hmem
                      have hlen1 : (done ++ [Branch.extendMany bPers newForms]).length =
                                   (doneEdges ++ [edges']).length := by simp; omega
                      have hlen2 : (done ++ [Branch.extendMany bPers newForms]).length =
                                   (doneNW ++ [nw']).length := by simp; omega
                      rw [List.zip_append hlen1] at hmem
                      have hlen2_adj :
                          ((done ++ [Branch.extendMany bPers newForms]).zip
                           (doneEdges ++ [edges'])).length =
                           (doneNW ++ [nw']).length := by
                        rw [List.length_zip,
                            Nat.min_eq_left (Nat.le_of_eq hlen1)]; exact hlen2
                      rw [List.zip_append hlen2_adj, List.mem_append] at hmem
                      rcases hmem with h_front | h_back
                      · have hlen_de : done.length = doneEdges.length := by omega
                        have hlen_denz : (done.zip doneEdges).length = doneNW.length := by
                          rw [List.length_zip]
                          exact (Nat.min_eq_left (by omega)).trans (by omega)
                        rw [List.zip_append hlen_de, List.zip_append hlen_denz,
                            List.mem_append] at h_front
                        simp only [List.zip_cons_cons, List.zip_nil_right, List.mem_cons,
                                   List.mem_nil_iff, or_false, Prod.mk.injEq] at h_front
                        rcases h_front with h1 | ⟨⟨rfl, rfl⟩, rfl⟩
                        · exact hfreshDone b e nw h1
                        · exact hfreshNew
                      · exact hfreshTail b e nw h_back
                    refine ih _ _ _ _ (by simp [hdlength_exp, hlength_exp])
                        (by simp [hdlength_nw, hlength_nw])
                        (by simp [hdlength_edges, hlength_edges])
                        hfreshCombLin hgo bp edgesP ?_ wo hmono_p hsat_p
                    rw [List.zip_append (by simp [hdlength_edges]), List.mem_append]
                    exact Or.inr hmem_rest
                | branchingResult branches' nw' =>
                  rw [hresult] at hgo hstep hresult_sf
                  -- Freshness: all labels in bPers are < nwH, hence ≠ nwH
                  have hfresh : ∀ sf' ∈ bPers, sf'.label ≠ nwH :=
                    fun sf' hmem' => Nat.ne_of_lt (hfreshAbove_pers.1 sf' hmem')
                  -- nw' = nwH for branching rules (no new world created)
                  have hnw'eq : nw' = nwH :=
                    intApplyRuleFull_branching_nw sf nwH bPers branches' nw' hresult_sf
                  -- FreshAbove for each branch in branches'.map (extendMany bPers ·)
                  have hfreshBr : ∀ br ∈ branches',
                      FreshAbove (Branch.extendMany bPers br) edgesH nwH := by
                    intro br hbr
                    have hlabels := intApplyRuleFull_branching_labels sf nwH bPers branches' nw'
                        hresult_sf br hbr
                    exact freshAbove_extendMany bPers edgesH nwH br hfreshAbove_pers
                        (fun sf' hmem' => hlabels sf' hmem' ▸ hfreshAbove_pers.1 sf hsf_mem)
                  -- Combined freshness for done ++ branches'.map (extendMany bPers ·) ++ bt
                  have hfreshCombBr : ∀ b e nw,
                      ((b, e), nw) ∈
                        ((done ++ branches'.map (Branch.extendMany bPers ·) ++ bt).zip
                         (doneEdges ++ branches'.map (fun _ => edgesH) ++ edgesT)).zip
                        (doneNW ++ branches'.map (fun _ => nwH) ++ nwT) →
                        FreshAbove b e nw := by
                    intro b e nw hmem
                    have hlenBr : branches'.length = branches'.length := rfl
                    have hlen1 : (done ++ branches'.map (Branch.extendMany bPers ·)).length =
                                 (doneEdges ++ branches'.map (fun _ => edgesH)).length := by
                      simp; omega
                    have hlen2 : (done ++ branches'.map (Branch.extendMany bPers ·)).length =
                                 (doneNW ++ branches'.map (fun _ => nwH)).length := by
                      simp; omega
                    rw [List.zip_append hlen1] at hmem
                    have hlen2_adj :
                        ((done ++ branches'.map (Branch.extendMany bPers ·)).zip
                         (doneEdges ++ branches'.map (fun _ => edgesH))).length =
                         (doneNW ++ branches'.map (fun _ => nwH)).length := by
                      rw [List.length_zip,
                          Nat.min_eq_left (Nat.le_of_eq hlen1)]; exact hlen2
                    rw [List.zip_append hlen2_adj, List.mem_append] at hmem
                    rcases hmem with h_front | h_back
                    · have hlen_de : done.length = doneEdges.length := by omega
                      have hlen_denz : (done.zip doneEdges).length = doneNW.length := by
                        rw [List.length_zip]
                        exact (Nat.min_eq_left (by omega)).trans (by omega)
                      rw [List.zip_append hlen_de, List.zip_append hlen_denz,
                          List.mem_append] at h_front
                      rcases h_front with h1 | h1
                      · exact hfreshDone b e nw h1
                      · -- in branches'.map part: extract index, then use hfreshBr
                        obtain ⟨i, hi_lt, hi_eq⟩ := List.mem_iff_getElem.mp h1
                        simp only [List.getElem_zip, List.getElem_map] at hi_eq
                        obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hi_eq
                        have hi_br : i < branches'.length := by
                          simp only [List.length_zip, List.length_map, Nat.min_self] at hi_lt
                          exact hi_lt
                        exact hfreshBr branches'[i] (List.getElem_mem hi_br)
                    · exact hfreshTail b e nw h_back
                  rcases hzip_p with ⟨rfl, rfl⟩ | hmem_rest
                  · -- branchingResult bp=bh case: apply intRule_preserves_sat + ih
                    simp only [] at hgo
                    have hsat_pers : intBranchSatisfied val botForces wo bPers :=
                      applyPersistenceFixpoint_sat val botForces v_uc bf_uc wo bh edgesP
                        (fuel'' + 1) hsat_p hmono_p
                    have hpres := intRule_preserves_sat val botForces v_uc bf_uc wo bPers sf
                        hsf_mem hsat_pers nwH hfresh
                    rw [hresult_sf] at hpres
                    obtain ⟨br, hbr_mem, hsat_br⟩ := hpres
                    have hmem : (Branch.extendMany bPers br, edgesP) ∈
                        (done ++ branches'.map (Branch.extendMany bPers ·) ++ bt).zip
                        (doneEdges ++ branches'.map (fun _ => edgesP) ++ edgesT) := by
                      rw [List.zip_append (by simp [hdlength_edges])]
                      simp only [List.mem_append]
                      refine Or.inl ?_
                      rw [List.zip_append (by exact hdlength_edges.symm)]
                      simp only [List.mem_append]
                      refine Or.inr ?_
                      obtain ⟨i, hi_lt, hi_eq⟩ := List.mem_iff_getElem.mp hbr_mem
                      apply List.mem_iff_getElem.mpr
                      exact ⟨i, by simp [hi_lt],
                        by simp [List.getElem_zip, List.getElem_map, hi_eq]⟩
                    -- For the ih freshness: note edgesP = edgesH (from ⟨rfl, rfl⟩) and nw'=nwH
                    have hfreshCombBrH : ∀ b e nw,
                        ((b, e), nw) ∈
                          ((done ++ branches'.map (Branch.extendMany bPers ·) ++ bt).zip
                           (doneEdges ++ branches'.map (fun _ => edgesP) ++ edgesT)).zip
                          (doneNW ++ branches'.map (fun _ => nw') ++ nwT) →
                          FreshAbove b e nw := by
                      rw [hnw'eq]; exact hfreshCombBr
                    exact ih _ _ _ _ (by simp [hdlength_exp, hlength_exp])
                        (by simp [hdlength_nw, hlength_nw])
                        (by simp [hdlength_edges, hlength_edges])
                        hfreshCombBrH
                        hgo (Branch.extendMany bPers br) edgesP hmem wo hmono_p hsat_br
                  · -- branchingResult bp∈bt case: bp is in the tail bt with edges edgesT;
                    -- after expanding, bp is still in the new branch list at the same position.
                    simp only [] at hgo
                    have hfreshCombBrT : ∀ b e nw,
                        ((b, e), nw) ∈
                          ((done ++ branches'.map (Branch.extendMany bPers ·) ++ bt).zip
                           (doneEdges ++ branches'.map (fun _ => edgesH) ++ edgesT)).zip
                          (doneNW ++ branches'.map (fun _ => nw') ++ nwT) →
                          FreshAbove b e nw := by
                      rw [hnw'eq]; exact hfreshCombBr
                    refine ih _ _ _ _ (by simp [hdlength_exp, hlength_exp])
                        (by simp [hdlength_nw, hlength_nw])
                        (by simp [hdlength_edges, hlength_edges])
                        hfreshCombBrT hgo bp edgesP ?_ wo hmono_p hsat_p
                    rw [List.zip_append (by simp [hdlength_edges]), List.mem_append]
                    exact Or.inr hmem_rest
                | notApplicable =>
                  rw [hresult] at hgo; simp at hgo

/-! ## Main Soundness Theorem -/

omit [Hashable Atom] in
/-- **Intuitionistic Tableau Soundness**: If `intuitionisticTableau φ = closed`, then
`φ` is intuitionistically valid (`IValid φ`).

Proof outline:
1. By contrapositive: assume ¬ IValid φ, extract a world `w₀` where φ fails.
2. The initial branch `[F(φ) at 0]` is satisfied with worldOf 0 = w₀.
3. By `intExpandBranches_closed_unsat`, no satisfiable branch can yield a closed tableau.
4. Contradiction with `h : intuitionisticTableau φ = closed`. -/
theorem intuitionisticTableau_sound (φ : Proposition Atom)
    (h : intuitionisticTableau φ = .closed) : IValid φ := by
  intro World _ val v_uc w₀
  by_contra hneg
  let worldOf : Nat → World := fun _ => w₀
  have hsat : intBranchSatisfied val (fun _ => False) worldOf [⟨.neg, φ, 0⟩] := by
    intro sf hmem
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
    subst hmem
    exact ⟨fun h => absurd h (Sign.noConfusion), fun _ => hneg⟩
  simp only [intuitionisticTableau] at h
  -- Apply the closed unsat lemma with the initial single-branch configuration.
  -- edgeSets = [[]] (one empty edge set, matching the one branch).
  -- worldOf = fun _ => w₀ is monotone for [] trivially (only constraint: w = w').
  apply intExpandBranches_closed_unsat val (fun _ => False) v_uc
    (fun {_ _} _ hf => absurd hf id) _
    isIntuitionisticallyClosed
    (fun worldOf' b hcl => intClosed_unsatisfiable val worldOf' b hcl)
    [[⟨.neg, φ, 0⟩]] [[]] [1] [[]] (by rfl) (by rfl) (by rfl)
      (by
        intro b edges nw hmem
        simp only [List.zip_cons_cons, List.zip_nil_right,
          List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hmem
        obtain ⟨⟨hb, he⟩, hnw⟩ := hmem
        subst hb; subst he; subst hnw
        refine ⟨?_, ?_⟩
        · intro sf hsf
          simp only [List.mem_cons, List.mem_nil_iff, or_false] at hsf
          simp [hsf]
        · intro c p hcp
          simp only [List.not_mem_nil] at hcp) h
    [⟨.neg, φ, 0⟩] []
  · simp [List.zip_cons_cons, List.zip_nil_right]
  · exact fun w w' hacc => by
      simp only [isAccessible] at hacc
      split_ifs at hacc with heq
      · -- heq : w == w' = true, so w = w' and worldOf w ≤ worldOf w' by reflexivity
        have hw : w = w' := by exact_mod_cast beq_iff_eq.mp heq
        exact le_of_eq (congrArg worldOf hw)
      · simp [isAccessible.go] at hacc
  · exact hsat

/-! ## Countermodel Extraction

These definitions are placed here (rather than in `Int/Completeness.lean`) so that
`Intuitionistic/Scheme.lean` can import them without creating a circular dependency with
`Int/Completeness.lean`. -/

/-- The valuation extracted from an open saturated branch.

Atom `p` is assigned true at world `w` iff T(atom p) appears at label `w` on the branch.
This is the shared valuation used by both the intuitionistic and minimal countermodel
constructions. -/
def intExtractValuation (b : IBranch Atom) (w : Nat) (p : Atom) : Prop :=
  b.any (fun sf => sf.sign == .pos && sf.formula == .atom p && sf.label == w)

/-- The `botForces` predicate for the intuitionistic countermodel: always False.

In intuitionistic logic, ⊥ is never forced. This predicate serves as the `botForces`
parameter for the parameterized `IForces` semantics in the intuitionistic countermodel. -/
def intBotForces : Nat → Prop := fun _ => False

end Cslib.Logic.PL

end
