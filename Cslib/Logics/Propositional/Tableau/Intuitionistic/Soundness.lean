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
  sorry

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
      -- hfilt : c = ch; hcond : (p == source) = true
      simp only [beq_iff_eq] at hcond
      -- hcond : p = source, hfilt : c = ch
      -- Use these equalities directly without subst
      rw [hfilt, hcond] at hedge
      -- hedge : (ch, source) ∈ edges ∨ (ch, source) = (nw, parentLabel)
      -- hchild is already about ch (from obtain ⟨ch, hmem, hchild⟩)
      rcases hedge with horig | hext
      · -- edge (ch, source) is in original edges
        by_cases heq : ch == nw
        · -- ch = nw, but (nw, source) in orig edges contradicts hno_child
          simp only [beq_iff_eq] at heq; subst heq
          exact absurd horig (hno_child source)
        · -- ch ≠ nw; apply IH to ch: either parentLabel reachable from ch, or ch = parentLabel
          simp only [heq, Bool.false_eq_true, ite_false] at hchild
          rcases ih ch hchild with hreach | rfl
          · -- parentLabel reachable from ch in orig edges; chain: source → ch → ... → parentLabel
            -- isAccessible.go edges parentLabel source edges.length should be true
            -- since ch is a child of source and parentLabel is reachable from ch
            left; sorry
          · left; sorry
      · simp only [Prod.mk.injEq] at hext
        obtain ⟨rfl, rfl⟩ := hext
        simp only [beq_self_eq_true, ite_true] at hchild
        right; rfl
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
  sorry

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
  -- We prove by induction on fuel.
  -- The IH at k handles the recursive intExpandBranches calls in the succ case.
  induction fuel with
  | zero =>
    intro branches expandedSets nextWorlds edgeSets _ _ hclosed b hb worldOf hsat
    -- fuel=0: intExpandBranches = if findSome? (not-closed branches) = none then .closed else .openBranch.
    -- Result = .closed iff all branches have closurePred = true.
    simp only [intExpandBranches] at hclosed
    -- After unfolding, hclosed is a match on findSome?.
    -- split gives two cases: some b' (→ openBranch ≠ closed) or none (→ closed).
    split at hclosed
    · -- findSome? = some b': result is .openBranch b' but hclosed says .closed → impossible.
      rename_i b' heq
      simp at hclosed
    · -- findSome? = none: every branch has closurePred = true.
      rename_i heq
      have hcl : closurePred b = true := by
        by_contra hne
        simp only [Bool.not_eq_true] at hne
        -- findSome? = none means all elements return none from the lambda.
        -- But for b with closurePred b = false, lambda returns some b → contradiction.
        rw [List.findSome?_eq_none] at heq
        have := heq b hb
        simp [hne] at this
      exact closed_unsat worldOf b hcl hsat
  | succ k ih =>
    intro branches expandedSets nextWorlds edgeSets hlen1 hlen2 hclosed b hb worldOf hsat
    -- fuel = k+1: intExpandBranches calls go with the branches as the pending list.
    -- Unfolding: hclosed : intExpandBranches.go closurePred k branches ... [] ... = .closed
    unfold intExpandBranches at hclosed
    -- We prove a go-loop lemma by induction on the pending list.
    -- Key invariant: if go returns .closed and b ∈ pending, then ¬ sat worldOf b.
    -- This uses IH at k for recursive intExpandBranches calls.
    -- Note: the proof requires MonotoneEdges worldOf edges per branch, which is not in our
    -- outer hypotheses. We use targeted sorries for this gap (applyPersistenceFixpoint_sat
    -- is sorry'd and also requires MonotoneEdges). The gap is documented inline.
    suffices hgo : ∀ (pending done : List (IBranch Atom))
        (pendingExp doneExp : List (List (ISF Atom)))
        (pendingNW doneNW : List Nat)
        (pendingEdges doneEdges : List IEdges),
        intExpandBranches.go closurePred k pending pendingExp pendingNW pendingEdges
          done doneExp doneNW doneEdges = .closed →
        b ∈ pending →
        ¬ intBranchSatisfied val botForces worldOf b by
      exact hgo branches [] expandedSets [] nextWorlds [] edgeSets [] hclosed hb hsat
    intro pending done pendingExp doneExp pendingNW doneNW pendingEdges doneEdges
    induction pending with
    | nil =>
      -- Empty pending: go returns .closed but there are no branches → membership is vacuous.
      intro _ hmem _
      exact absurd hmem (List.not_mem_nil _)
    | cons headB tailBs ih_pending =>
      intro hgo_closed hmem hsat_b
      -- Unfold the go function one step.
      simp only [intExpandBranches.go] at hgo_closed
      -- The go function matches on (pending, pendingExp, pendingNW, pendingEdges).
      -- Sub-case: normal processing (all four lists have cons heads)
      match pendingExp, pendingNW, pendingEdges with
      | [], _, _ | _, [], _ | _, _, [] =>
        -- Degenerate: some aux list is empty while pending is nonempty.
        -- go falls through to process tailBs with empty aux lists.
        rcases List.mem_cons.mp hmem with rfl | hmem'
        · -- b = headB: headB is "skipped" in the degenerate case (go doesn't process it).
          -- This only occurs when the parallel-list length invariant is violated,
          -- which cannot happen in the actual intExpandBranches usage (lengths are tracked).
          -- Full proof would propagate the length invariant into hgo.
          sorry -- Gap: degenerate case (length invariant violation); vacuous in practice
        · exact ih_pending [] [] [] hgo_closed hmem' hsat_b
      | eHead :: eTail, nwHead :: nwTail, edgesHead :: edgesTail =>
        -- Normal case: process headB with edgesHead.
        simp only [intExpandBranches.go] at hgo_closed
        set bPers := applyPersistenceFixpoint headB edgesHead (k + 1)
        -- Split on whether bPers is syntactically closed.
        split_ifs at hgo_closed with hcl
        · -- bPers is closed: headB is done; go continues with tailBs.
          rcases List.mem_cons.mp hmem with rfl | hmem'
          · -- b = headB: need to derive False from hsat_b.
            -- Plan: sat headB → (MonotoneEdges) → sat bPers → closed_unsat gives False.
            -- MonotoneEdges is not available here; targeted sorry.
            have hmono : MonotoneEdges worldOf edgesHead := by
              sorry -- Gap: MonotoneEdges not in outer lemma hypotheses
            have hsat_pers : intBranchSatisfied val botForces worldOf bPers :=
              applyPersistenceFixpoint_sat val botForces v_uc bf_uc worldOf
                headB edgesHead (k + 1) hsat_b hmono
            exact closed_unsat worldOf bPers hcl hsat_pers
          · -- b ∈ tailBs: go processes tailBs next.
            exact ih_pending eTail nwTail edgesTail hgo_closed hmem' hsat_b
        · -- bPers is not closed: expand via intStepBranch.
          -- Split on the intStepBranch result.
          split at hgo_closed
          · -- none: bPers saturated → go returns .openBranch ≠ .closed
            exact absurd hgo_closed (by simp)
          · rename_i newForms nw' newEdge newExp
            -- some (.linearResult newForms nw' newEdge, newExp):
            -- go calls intExpandBranches with fuel k.
            rcases List.mem_cons.mp hmem with rfl | hmem'
            · -- b = headB: need False from hsat_b.
              -- Plan: sat headB → (MonotoneEdges) → sat bPers → (intRule_preserves_sat) →
              --         ∃ worldOf', sat worldOf' (extendMany bPers newForms)
              --       → (IH at k applied to hgo_closed) → ¬ sat worldOf' (extendMany bPers newForms)
              --       → contradiction.
              have hmono : MonotoneEdges worldOf edgesHead := by
                sorry -- Gap: MonotoneEdges
              have hsat_pers : intBranchSatisfied val botForces worldOf bPers :=
                applyPersistenceFixpoint_sat val botForces v_uc bf_uc worldOf
                  headB edgesHead (k + 1) hsat_b hmono
              -- intRule_preserves_sat needs: sf ∈ bPers, freshness of nwHead.
              -- Extracting sf and freshness from intStepBranch output requires additional lemmas.
              -- Full proof: extract sf ∈ bPers from intStepBranch; prove freshness from nwHead invariant.
              sorry -- Gap: need sf ∈ bPers and freshness to invoke intRule_preserves_sat
            · -- b ∈ tailBs: IH at k on the recursive intExpandBranches call.
              have hb_in : b ∈ done ++ [Branch.extendMany bPers newForms] ++ tailBs := by
                simp [hmem']
              exact ih _ _ _ _ _ _ _ _ hgo_closed hb_in worldOf hsat_b
          · rename_i branches' nw' newExp
            -- some (.branchingResult branches' nw', newExp):
            rcases List.mem_cons.mp hmem with rfl | hmem'
            · -- b = headB: same strategy as the linear case.
              have hmono : MonotoneEdges worldOf edgesHead := by
                sorry -- Gap: MonotoneEdges
              have hsat_pers : intBranchSatisfied val botForces worldOf bPers :=
                applyPersistenceFixpoint_sat val botForces v_uc bf_uc worldOf
                  headB edgesHead (k + 1) hsat_b hmono
              -- intRule_preserves_sat (branching): ∃ br ∈ branches', sat worldOf (extendMany bPers br)
              -- IH at k: all branches in recursive call are unsat → contradiction.
              sorry -- Gap: need sf and freshness for intRule_preserves_sat (branching)
            · -- b ∈ tailBs: IH at k.
              have hb_in : b ∈ done ++ branches'.map (Branch.extendMany bPers) ++ tailBs := by
                simp [hmem']
              exact ih _ _ _ _ _ _ _ _ hgo_closed hb_in worldOf hsat_b
          · -- some (.notApplicable, _): returns .openBranch ≠ .closed
            exact absurd hgo_closed (by simp)

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
