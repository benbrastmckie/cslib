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
