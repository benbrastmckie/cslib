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
    | .linearResult newForms _ _ =>
      ∃ worldOf' : Nat → World,
        (∀ k, k ≠ nw → worldOf' k = worldOf k) ∧
        intBranchSatisfied val botForces worldOf' (Branch.extendMany b newForms)
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
      refine ⟨worldOf, fun _ _ => rfl, ?_⟩
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
      refine ⟨Function.update worldOf nw w', fun k hk => ?_, ?_⟩
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
      refine ⟨worldOf, fun _ _ => rfl, ?_⟩
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

/-- Shorthand: `worldOf` is monotone with respect to an edge list `edges`. -/
private def MonotoneEdges {World : Type*} [Preorder World]
    (worldOf : Nat → World) (edges : IEdges) : Prop :=
  ∀ w w', isAccessible edges w w' = true → worldOf w ≤ worldOf w'

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
  rcases hmem with hmem_b | hmem_new
  · exact hsat sf hmem_b
  · -- sf came from the filterMap flatten: T(ψ, w') for some T(φ→ψ, w) in b
    simp only [List.mem_flatten, List.mem_filterMap] at hmem_new
    obtain ⟨newList, ⟨sfImp, hmem_sfImp, hfilt⟩, hmem_sf_in_list⟩ := hmem_new
    -- hfilt : some newList = (if ... then some (intTImpRule ...) else none)
    split_ifs at hfilt with hcond
    · simp only [Option.some.injEq] at hfilt
      rw [← hfilt] at hmem_sf_in_list
      -- sf ∈ intTImpRule φ ψ w edges b
      simp only [intTImpRule, List.mem_filterMap] at hmem_sf_in_list
      obtain ⟨w', hw'_acc, hfilt2⟩ := hmem_sf_in_list
      split_ifs at hfilt2 with hphi_at_w' hpsi_at_w'
      · simp only [Option.some.injEq] at hfilt2
        rw [← hfilt2]
        -- sf = ⟨.pos, ψ, w'⟩ (from sfImp = ⟨.pos, φ→ψ, w⟩)
        rcases sfImp with ⟨sign, form, label⟩
        simp only [Bool.and_eq_true, beq_iff_eq] at hcond
        obtain ⟨hsign_eq, hform_imp⟩ := hcond
        -- hsign_eq: sign = .pos, hform_imp: form = .imp φ ψ (after split_ifs)
        -- From hsat applied to sfImp
        constructor
        · intro _
          -- Need: IForces val botForces (worldOf w') ψ
          -- From sfImp: IForces val botForces (worldOf label) (φ→ψ)
          have himp := (hsat ⟨sign, form, label⟩ hmem_sfImp).1 (by rw [hsign_eq])
          -- From hphi_at_w': T(φ, w') is on b
          rw [List.any_eq_true] at hphi_at_w'
          obtain ⟨sfPhi, hsfPhi_mem, hsfPhi_cond⟩ := hphi_at_w'
          simp only [Bool.and_eq_true, beq_iff_eq] at hsfPhi_cond
          obtain ⟨⟨hsign_phi, hform_phi⟩, hlabel_phi⟩ := hsfPhi_cond
          have hphi := (hsat sfPhi hsfPhi_mem).1 (by rw [hsign_phi])
          rw [← hform_phi, ← hlabel_phi] at hphi
          -- Now we need IForces val botForces (worldOf label) (form) applied
          -- to get IForces val botForces (worldOf w') ψ
          -- form = φ → ψ, IForces val botForces (worldOf label) (φ → ψ)
          -- = ∀ w'', worldOf label ≤ w'' → IForces val botForces w'' φ → IForces val botForces w'' ψ
          -- hw'_acc: isAccessible edges label w' = true (by List.eraseDups/filter logic)
          -- but wait: w' comes from accessibleWorlds = ... filter (isAccessible edges w ·)
          -- and sfImp has label = w (the world of the T(φ→ψ) formula)
          simp only [List.mem_eraseDups, List.mem_filter] at hw'_acc
          obtain ⟨_, hw'_accessible⟩ := hw'_acc
          have hle : worldOf label ≤ worldOf w' := hmono label w' hw'_accessible
          rw [hform_imp] at himp
          simp only [IForces_imp] at himp
          exact himp (worldOf w') hle (by rw [← hform_phi] at hphi; exact hphi)
        · intro h
          exact absurd h (Sign.noConfusion)
      · simp at hfilt2
      · simp at hfilt2
    · simp at hfilt

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
    · apply ih
      · exact applyAllTImpRules_sat val botForces v_uc bf_uc worldOf b edges hsat hmono
      · intro w w' hacc
        exact hmono w w' hacc

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
  push_neg at h
  rw [Bool.not_eq_false] at h
  exact closed_unsat worldOf b h hsat

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
    have hchildren : (edges.filterMap fun (child, parent) =>
        if parent == nw then some child else none) = [] := by
      apply List.filterMap_eq_nil.mpr
      intro pair hmem
      rcases pair with ⟨child, parent⟩
      simp only
      by_cases hpar : parent == nw
      · simp only [hpar]
        simp only [beq_iff_eq] at hpar
        subst hpar
        exact absurd hmem (hno_parent child)
      · simp [hpar]
    rw [hchildren]
    simp

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
  induction hle with
  | refl => exact h
  | step hle' ih =>
    rename_i k
    cases Nat.eq_or_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (Nat.succ_le_succ hle')) with
    | inl heq => rw [← heq]; exact ih h
    | inr hlt =>
      cases fuel2 with
      | zero => exact absurd hle' (by omega)
      | succ m =>
        simp only [isAccessible.go]
        simp only [isAccessible.go] at ih
        apply List.any_mono
        · intro child hmem
          by_cases heq : child == target
          · simp [heq]
          · simp only [heq, Bool.false_eq_true, ↓reduceIte, Bool.false_or]
            apply ih
            simp only [heq, Bool.false_eq_true, ↓reduceIte, Bool.false_or] at h
            exact List.any_of_any hmem h
        · exact (List.filterMap_id _).symm ▸ List.Sublist.refl _

/-- If `isAccessible.go` on `edges ++ [(nw, parentLabel)]` returns true for target `nw`
starting from `source`, and `nw` is completely fresh (not a child or parent in `edges`,
and `parentLabel ≠ nw`), then either `source = parentLabel` or
`isAccessible.go edges parentLabel source edges.length = true`. -/
private lemma isAccessible_go_reach_nw_implies_reach_parent
    (edges : IEdges) (nw parentLabel : Nat)
    (hno_child : ∀ parent, (nw, parent) ∉ edges)  -- nw not a child in old edges
    (hno_parent : ∀ child, (child, nw) ∉ edges)   -- nw not a parent in old edges
    (hne : parentLabel ≠ nw)
    (source : Nat) (fuel : Nat)
    (hacc : isAccessible.go (edges ++ [(nw, parentLabel)]) nw source fuel = true) :
    isAccessible.go edges parentLabel source edges.length = true ∨ source = parentLabel := by
  induction fuel generalizing source with
  | zero => simp [isAccessible.go] at hacc
  | succ k ih =>
    simp only [isAccessible.go] at hacc
    rw [List.any_eq_true] at hacc
    obtain ⟨child, hmem_child, hchild_reaches⟩ := hacc
    simp only [List.mem_filterMap, List.mem_append, List.mem_singleton] at hmem_child
    obtain ⟨pair, hpair_mem, hpair_filt⟩ := hmem_child
    rcases hpair_mem with hmem_old | hmem_new
    · -- pair ∈ old edges
      rcases pair with ⟨c, p⟩
      simp only [Bool.ite_eq_true_iff] at hpair_filt
      split_ifs at hpair_filt with hpar
      · simp only [Option.some.injEq, beq_iff_eq] at hpair_filt hpar
        subst hpar
        -- child = c, (c, source) ∈ edges
        rw [← hpair_filt] at hchild_reaches
        simp only [Bool.or_eq_true, beq_iff_eq] at hchild_reaches
        rcases hchild_reaches with rfl | hgo
        · -- child = nw, but (nw, source) ∈ edges contradicts hno_child
          exact absurd hmem_old (hno_child source)
        · -- isAccessible.go (ext) nw c k = true; apply IH to c
          rcases ih c hgo with hreach | rfl
          · left
            -- isAccessible.go edges parentLabel c edges.length = true
            -- We need: isAccessible.go edges parentLabel source edges.length = true
            -- since (c, source) ∈ edges: c is a child of source → parentLabel reachable from source via c
            simp only [isAccessible.go]
            apply List.any_eq_true.mpr
            refine ⟨c, ?_, ?_⟩
            · simp only [List.mem_filterMap]
              exact ⟨(c, source), hmem_old, by simp⟩
            · simp only [Bool.or_eq_true, beq_iff_eq]
              right
              exact hreach
          · -- c = parentLabel
            -- (parentLabel, source) ∈ edges → parentLabel is a child of source
            -- → isAccessible.go edges parentLabel source ≥ 1 step
            left
            simp only [isAccessible.go]
            apply List.any_eq_true.mpr
            refine ⟨parentLabel, ?_, ?_⟩
            · simp only [List.mem_filterMap]
              exact ⟨(parentLabel, source), hmem_old, by simp⟩
            · simp
      · simp at hpair_filt
    · -- pair = (nw, parentLabel): source = parentLabel (the new edge fires)
      simp only [Prod.mk.injEq] at hmem_new
      obtain ⟨rfl, rfl⟩ := hmem_new
      simp only at hpair_filt
      split_ifs at hpair_filt with hpar
      · simp only [Option.some.injEq, beq_iff_eq] at hpair_filt hpar
        subst hpar
        -- source = parentLabel, child = nw
        rw [← hpair_filt] at hchild_reaches
        simp only [Bool.or_eq_true, beq_iff_eq] at hchild_reaches
        rcases hchild_reaches with rfl | hgo_nw
        · -- child = nw = nw (target): source = parentLabel ✓
          right; rfl
        · -- isAccessible.go (ext) nw nw k = true — we need to show this is false
          -- since nw has no children in ext
          have hfalse :=
            isAccessible_go_nw_no_children (edges ++ [(nw, parentLabel)]) nw nw
              (not_parent_in_extended edges nw parentLabel hno_parent hne) k
          rw [hfalse] at hgo_nw; exact absurd hgo_nw (by simp)
      · simp at hpair_filt
      · simp at hpair_filt

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
  simp only [Function.update_apply]
  by_cases hw1 : w1 = nw
  · subst hw1
    -- nw → w2: we need worldOf' nw ≤ worldOf' w2, i.e., w' ≤ worldOf' w2
    -- Since nw has no children in extended edges (nw not a parent in old edges, and
    -- new edge has parentLabel ≠ nw as parent), isAccessible (ext) nw w2 means w2 = nw
    have h_no_parent_ext : ∀ child, (child, nw) ∉ edges ++ [(nw, parentLabel)] :=
      not_parent_in_extended edges nw parentLabel hnw_not_parent hnw_ne_parent
    simp only [isAccessible] at hacc
    split_ifs at hacc with heq
    · simp only [beq_iff_eq] at heq
      subst heq
      simp only [if_pos rfl]
    · -- isAccessible.go (ext) w2 nw (length) = true, but nw has no children
      exfalso
      have hfalse : isAccessible.go (edges ++ [(nw, parentLabel)]) w2 nw
          (edges ++ [(nw, parentLabel)]).length = false :=
        isAccessible_go_nw_no_children (edges ++ [(nw, parentLabel)]) nw w2 h_no_parent_ext _
      rw [hfalse] at hacc
      exact absurd hacc (by simp)
  · by_cases hw2 : w2 = nw
    · subst hw2
      -- w1 → nw (w1 ≠ nw): need worldOf w1 ≤ w' = worldOf' nw
      simp only [if_pos rfl, if_neg hw1]
      -- The only path to nw is through parentLabel (new edge (nw, parentLabel))
      -- So isAccessible (ext) w1 nw = true implies isAccessible edges w1 parentLabel
      -- or w1 = parentLabel
      simp only [isAccessible] at hacc
      split_ifs at hacc with heq
      · simp only [beq_iff_eq] at heq
        exact absurd heq hw1
      · -- hacc : isAccessible.go (ext) nw w1 (length) = true
        have reach := isAccessible_go_reach_nw_implies_reach_parent
          edges nw parentLabel hnw_not_child hnw_not_parent hnw_ne_parent w1 _ hacc
        rcases reach with hreach | rfl
        · -- isAccessible edges parentLabel w1 (edges.length) = true
          have hle2 := hmono w1 parentLabel hreach
          exact le_trans hle2 hle
        · -- w1 = parentLabel directly
          exact hle
    · -- w1 ≠ nw, w2 ≠ nw: isAccessible (ext) w1 w2 = true implies isAccessible edges w1 w2
      simp only [if_neg hw1, if_neg hw2]
      -- Since nw has no children in extended edges, any path from w1 to w2 ≠ nw
      -- can't go through nw as an intermediate (nw is a dead end in ext)
      -- So the path exists in the original edges
      -- We prove: isAccessible (ext) w1 w2 = true → isAccessible edges w1 w2 = true
      have hmono_go : isAccessible edges w1 w2 = true := by
        simp only [isAccessible] at hacc ⊢
        split_ifs at hacc ⊢ with heq
        · exact heq ▸ (by simp)
        · -- isAccessible.go (ext) w2 w1 (ext_length) = true
          -- Need: isAccessible.go edges w2 w1 (edges.length) = true
          -- The key: any path from w1 to w2 in ext not going through nw as endpoint
          -- Since nw has no children in ext, paths through nw are dead ends → not useful
          -- So paths from w1 to w2 using the new edge must pass through parentLabel → nw → ...
          -- but nw has no children → dead end. So no new paths reach w2 ≠ nw.
          -- Formal proof: by induction on the DFS fuel
          suffices ∀ source fuel,
              isAccessible.go (edges ++ [(nw, parentLabel)]) w2 source fuel = true →
              source ≠ nw →
              isAccessible.go edges w2 source edges.length = true by
            apply this w1 _ hacc hw1
          intro source fuelG
          induction fuelG generalizing source with
          | zero => simp [isAccessible.go]
          | succ k ih =>
            intro hgo hne_nw
            simp only [isAccessible.go] at hgo
            rw [List.any_eq_true] at hgo
            obtain ⟨child, hmem_child, hchild_cond⟩ := hgo
            simp only [List.mem_filterMap, List.mem_append, List.mem_singleton] at hmem_child
            obtain ⟨pair, hpair_mem, hpair_filt⟩ := hmem_child
            rcases hpair_mem with hmem_old | hmem_new
            · -- child came from old edges
              rcases pair with ⟨c, p⟩
              simp only [Bool.ite_eq_true_iff] at hpair_filt
              split_ifs at hpair_filt with hpar
              · simp only [Option.some.injEq] at hpair_filt
                simp only [beq_iff_eq] at hpar
                subst hpar
                -- child = c, (c, source) ∈ edges
                rw [← hpair_filt] at hchild_cond
                simp only [Bool.or_eq_true, beq_iff_eq] at hchild_cond
                rcases hchild_cond with rfl | hgo2
                · -- child = w2: done, show source → w2 directly in 1 step
                  simp only [isAccessible.go]
                  apply List.any_eq_true.mpr
                  refine ⟨c, ?_, ?_⟩
                  · simp only [List.mem_filterMap]
                    exact ⟨(c, source), hmem_old, by simp⟩
                  · simp
                · -- child ≠ w2: need to recurse
                  -- First check: is child = nw?
                  by_cases hchild_nw : c = nw
                  · subst hchild_nw
                    -- (nw, source) ∈ edges: nw appears as child in old edges
                    exact absurd hmem_old (hnw_not_child source)
                  · -- child ≠ nw: can apply IH
                    have hih := ih c (by rwa [← hpair_filt]) hchild_nw
                    simp only [isAccessible.go]
                    apply List.any_eq_true.mpr
                    refine ⟨c, ?_, ?_⟩
                    · simp only [List.mem_filterMap]
                      exact ⟨(c, source), hmem_old, by simp⟩
                    · simp only [beq_iff_eq, Bool.or_eq_true]
                      right
                      exact hih
              · simp at hpair_filt
            · -- pair = (nw, parentLabel): source = parentLabel, child = nw
              simp only [Prod.mk.injEq] at hmem_new
              obtain ⟨rfl, rfl⟩ := hmem_new
              simp only at hpair_filt
              split_ifs at hpair_filt with hpar
              · simp only [Option.some.injEq, beq_iff_eq] at hpair_filt hpar
                subst hpar
                -- source = parentLabel, child = nw
                rw [← hpair_filt] at hchild_cond
                simp only [Bool.or_eq_true, beq_iff_eq] at hchild_cond
                rcases hchild_cond with rfl | hgo_nw
                · -- child = nw = w2: but hw2 : w2 ≠ nw — contradiction
                  exact absurd rfl hw2
                · -- isAccessible.go (ext) w2 nw k = true
                  -- But nw has no children in ext → go nw k = false
                  have hfalse :=
                    isAccessible_go_nw_no_children (edges ++ [(nw, parentLabel)]) nw w2
                      (not_parent_in_extended edges nw parentLabel hnw_not_parent hnw_ne_parent) k
                  rw [hfalse] at hgo_nw
                  exact absurd hgo_nw (by simp)
              · simp at hpair_filt
      exact hmono_go

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
      intExpandBranches branches expandedSets nextWorlds edgeSets fuel closurePred = .closed →
      ∀ b ∈ branches, ∀ (worldOf : Nat → World),
          ¬ intBranchSatisfied val botForces worldOf b := by
  sorry

/-! ## Main Soundness Theorem -/

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
  exact intExpandBranches_closed_unsat val (fun _ => False) v_uc
    (fun {_ _} _ hf => absurd hf id) _
    isIntuitionisticallyClosed
    (fun worldOf' b hcl => intClosed_unsatisfiable val worldOf' b hcl)
    _ _ _ _ (by rfl) (by rfl) h
    [⟨.neg, φ, 0⟩] (by simp) worldOf hsat

end Cslib.Logic.PL

end
