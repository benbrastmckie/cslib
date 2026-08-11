/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

import Cslib.Init
public import Cslib.Logics.Propositional.Tableau.Intuitionistic.Expansion
public import Cslib.Logics.Propositional.Semantics.Kripke
public import Mathlib.Data.List.Basic

/-! # Intuitionistic Tableau Soundness

This module proves soundness of the intuitionistic propositional tableau: if the tableau
closes on `φ` (starting from `F(φ)` at world 0), then `φ` is intuitionistically valid.

## Main Results

- `intBranchSatisfied`: A Kripke model satisfies a labeled branch when the forcing
  relation agrees with every signed formula on the branch.
- `intClosed_unsatisfiable`: A closed branch (via `isIntuitionisticallyClosed`) is
  unsatisfiable in any Kripke model with `botForces = fun _ => False`.

The engine-quantifying soundness theorem (`intuitionisticTableau_sound`, and its generic
parametrization `tableau_sound`) now lives in `Intuitionistic/Scheme.lean`, alongside the
per-branch-fuel expansion engine `intExpandBranches` it is stated over; this module supplies
the Kripke-side lemmas (`intBranchSatisfied`, `intRule_preserves_sat`,
`intClosed_unsatisfiable`, `FreshAbove`/`MonotoneEdges`) those proofs consume.

## Strategy

Soundness proceeds by contrapositive:
1. Define `intBranchSatisfied` relating Kripke model forcing to signed branch content.
2. Show each intuitionistic rule preserves branch satisfiability in the Kripke sense.
3. Show an intuitionistically closed branch (containing T(⊥), or a T(φ)/F(φ) pair) is
   unsatisfiable since `IForces ... .bot = False` for any intuitionistic model, and
   complementary pairs contradict satisfiability directly.
4. `Scheme.lean`'s `intExpandBranches_closed_unsat`/`tableau_sound` conclude: if the tableau
   closes, the initial branch was unsatisfiable, meaning every Kripke model satisfies `φ`.

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
      -- T(φ → ψ): .branchingResult [[F(φ)], [T(ψ)]] nw (Deliverable 6, Fitting `T(→)` split).
      -- Reflexively at `label`: either φ fails at `label` (pick the F(φ) branch), or φ holds
      -- at `label` and `hpos` (applied reflexively via `le_rfl`) forces ψ at `label` too
      -- (pick the T(ψ) branch). Either way some branch stays satisfied.
      simp only [show intApplyRuleFull (⟨.pos, φ.imp ψ, label⟩ : ISF Atom) nw b =
        .branchingResult [[⟨.neg, φ, label⟩], [⟨.pos, ψ, label⟩]] nw from rfl]
      rw [IForces_imp] at hpos
      by_cases hφ : IForces val botForces (worldOf label) φ
      · have hψ : IForces val botForces (worldOf label) ψ := hpos (worldOf label) le_rfl hφ
        exact ⟨[⟨.pos, ψ, label⟩], by simp,
          extend_sat _ worldOf
            (fun sf' hmem' => by
              simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem'
              subst hmem'
              exact ⟨fun _ => hψ, fun h => absurd h (Sign.noConfusion)⟩)
            hsat⟩
      · exact ⟨[⟨.neg, φ, label⟩], List.mem_cons_self,
          extend_sat _ worldOf
            (fun sf' hmem' => by
              simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem'
              subst hmem'
              exact ⟨fun h => absurd h (Sign.noConfusion), fun _ => hφ⟩)
            hsat⟩
    | and φ ψ =>
      -- T(φ ∧ ψ): .linearResult [T(φ), T(ψ)] nw none; worldOf unchanged
      simp only [show intApplyRuleFull (⟨.pos, φ.and ψ, label⟩ : ISF Atom) nw b =
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
      simp only [show intApplyRuleFull (⟨.pos, φ.or ψ, label⟩ : ISF Atom) nw b =
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
      simp only [show intApplyRuleFull (⟨.neg, φ.and ψ, label⟩ : ISF Atom) nw b =
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
      simp only [show intApplyRuleFull (⟨.neg, φ.or ψ, label⟩ : ISF Atom) nw b =
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
    (v_uc : ∀ {w w' : World} (p : Atom), w ≤ w' → val w p → val w' p)
    (bf_uc : ∀ {w w' : World}, w ≤ w' → botForces w → botForces w')
    (worldOf : Nat → World)
    (b : IBranch Atom) (edges : IEdges)
    (hsat : intBranchSatisfied val botForces worldOf b)
    (hmono : MonotoneEdges worldOf edges) :
    intBranchSatisfied val botForces worldOf (applyAllTImpRules b edges) := by
  intro sf hmem
  simp only [applyAllTImpRules, List.mem_append] at hmem
  rcases hmem with (h | h) | h
  · exact hsat sf h
  · -- `newForms.flatten`: the ψ-consequence propagation, imp-shaped sources only (unaffected
    -- by the generalized copy channel added below).
    simp only [List.mem_flatten, List.mem_filterMap] at h
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
            · simp only [hphi, ↓reduceIte, hpsi, Bool.false_eq_true, Option.some.injEq]
                at hw'_sf
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
  · -- `genCopies.flatten`: the generalized copy channel — a copy of ANY positive formula
    -- `χ` at an accessible world `w'`. Sound by `iforces_persistence`, which applies to any
    -- formula (not just `imp`), unlike the ψ-consequence case above.
    simp only [List.mem_flatten, List.mem_filterMap] at h
    obtain ⟨cs, ⟨⟨sign_o, form_o, label_o⟩, hmem_outer, hmatch⟩, hmem_cs⟩ := h
    cases sign_o with
    | neg => simp only at hmatch; exact absurd hmatch (by simp)
    | pos =>
      simp only at hmatch
      by_cases hemp : (List.filterMap
          (fun w' =>
            if b.any (fun y => y.sign == .pos && y.formula == form_o && y.label == w') then none
            else some (⟨.pos, form_o, w'⟩ : ISF Atom))
          (List.filter (isAccessible edges label_o ·) (b.map (·.label)).eraseDups)).isEmpty
          = true
      · simp only [hemp, ite_true] at hmatch; exact absurd hmatch (by simp)
      · simp only [Bool.false_eq_true, hemp, ite_false, Option.some.injEq] at hmatch
        rw [← hmatch] at hmem_cs
        simp only [List.mem_filterMap, List.mem_filter, List.mem_eraseDups,
          List.mem_map] at hmem_cs
        obtain ⟨w', hw'_acc, hcopy⟩ := hmem_cs
        obtain ⟨_, hw'_access⟩ := hw'_acc
        split_ifs at hcopy with hcond
        simp only [Option.some.injEq] at hcopy
        rw [← hcopy]
        have hforces_o := (hsat ⟨.pos, form_o, label_o⟩ hmem_outer).1 rfl
        have hle : worldOf label_o ≤ worldOf w' := hmono _ _ hw'_access
        have hpersist := iforces_persistence v_uc bf_uc hle hforces_o
        exact ⟨fun _ => hpersist, fun h => by simp at h⟩

omit [Hashable Atom] in
/-- Persistence fixpoint preserves satisfiability when `worldOf` is monotone. -/
lemma applyPersistenceFixpoint_sat
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
lemma monotoneEdges_update
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
  simp only [applyAllTImpRules, List.mem_append] at hmem
  rcases hmem with (hmem | hmem) | hmem
  · exact hbounds sf hmem
  · -- `newForms.flatten`: the ψ-consequence propagation (imp-shaped sources only).
    simp only [List.mem_flatten, List.mem_filterMap] at hmem
    obtain ⟨newForms, ⟨sf', hmem', houter⟩, hmem_inner⟩ := hmem
    cases hsign : sf'.sign with
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
  · -- `genCopies.flatten`: the generalized copy channel — the copy's label is drawn from
    -- `b.map (·.label)` directly, so it is bounded exactly like any other pre-existing label.
    simp only [List.mem_flatten, List.mem_filterMap] at hmem
    obtain ⟨cs, ⟨sf', hmem', hmatch⟩, hmem_cs⟩ := hmem
    cases hsign : sf'.sign with
    | neg => simp only [hsign] at hmatch; simp at hmatch
    | pos =>
      simp only [hsign] at hmatch
      split_ifs at hmatch with hemp
      · simp only [Option.some.injEq] at hmatch
        rw [← hmatch] at hmem_cs
        simp only [List.mem_filterMap, List.mem_filter, List.mem_eraseDups,
          List.mem_map] at hmem_cs
        obtain ⟨w', ⟨⟨sf'', hmem'', hlab⟩, -⟩, hcopy⟩ := hmem_cs
        split_ifs at hcopy with hcond
        simp only [Option.some.injEq] at hcopy
        rw [← hcopy]; simp only; rw [← hlab]
        exact hbounds sf'' hmem''

omit [Hashable Atom] in
/-- The persistence fixpoint preserves `FreshAbove`. -/
lemma freshAbove_applyPersistenceFixpoint (b : IBranch Atom) (edges : IEdges) (nw : Nat)
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
lemma freshAbove_extendMany (b : IBranch Atom) (edges : IEdges) (nw : Nat)
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
lemma freshAbove_world_create (b : IBranch Atom) (edges : IEdges) (nw parentLabel : Nat)
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
lemma monotoneEdges_of_agree
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
lemma intApplyRuleFull_none_labels
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
lemma intApplyRuleFull_branching_labels
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
    | imp φ ψ =>
      -- T(φ → ψ): .branchingResult [[F(φ)], [T(ψ)]] nwH (Deliverable 6), same label shape.
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
lemma intApplyRuleFull_some_info
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
lemma intApplyRuleFull_none_nw
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
lemma intApplyRuleFull_branching_nw
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
    | imp φ ψ =>
      simp only [IntRuleResult.branchingResult.injEq] at h
      obtain ⟨_, rfl⟩ := h; rfl
    | _ => simp at h
  | neg =>
    cases form with
    | and φ ψ =>
      simp only [IntRuleResult.branchingResult.injEq] at h
      obtain ⟨_, rfl⟩ := h; rfl
    | _ => simp at h

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
parameter for the parameterized `IForces` semantics in the intuitionistic countermodel.
Note: `@[nolint unusedArguments]` is needed because the `ℕ` world parameter is part of
the `botForces` predicate signature but is not used in this constant-False definition. -/
@[nolint unusedArguments]
def intBotForces : Nat → Prop := fun _ => False

end Cslib.Logic.PL

end
