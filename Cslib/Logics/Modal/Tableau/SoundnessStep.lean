/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

import Cslib.Init
public import Cslib.Logics.Modal.Tableau.Saturation

/-! # Modal K Tableau Soundness

This module proves soundness of the modal K tableau: if the tableau closes on `φ`
(starting from `F(φ)` at world 0), then `φ` is K-valid (satisfied in all Kripke models).

## Main Results

- `branchSatisfiable`: Satisfiability of a branch via a Kripke model with a world assignment.
- `modalClosed_unsat`: A classically closed modal branch is unsatisfiable.
- `modalExpandBranches_closed_unsat`: Key loop soundness (fuel induction).
- `kValid`: K-validity: true in all Kripke models at all worlds.
- `modalTableau_sound`: `modalTableau φ = .closed → kValid φ`.

## Strategy

Soundness follows from two sub-lemmas:
1. `modalStepBranch_preserves_sat`: Each rule application preserves branch satisfiability
   (stated with an explicit freshness hypothesis `hInv`; proved in `SoundnessStep.lean`).
2. `modalClosed_unsat`: A classically closed branch is unsatisfiable.

Together these imply: if the tableau closes, the initial branch `[F(φ)@0]` was
unsatisfiable, so `φ` holds in all models at all worlds.

## Notes on the Freshness Invariant

`modalStepBranch_preserves_sat` requires the invariant `hInv` that all world indices in
`acc.edges` are labels already in the branch (so the fresh world created by modal rules
has a strictly larger index than any world in `acc`). This invariant holds at the initial
call (empty acc, one-element branch) and is maintained by the loop; it is passed as an
explicit hypothesis to avoid the need for a separate invariant induction.

## References

* [M. Fitting, *Proof Methods for Modal and Intuitionistic Logics*][Fitting1983], Chapter 2
-/

@[expose] public section

namespace Cslib.Logic.Modal.Tableau

open Cslib.Logic.Tableau Cslib.Logic.Modal

universe v u
variable {Atom : Type v} [DecidableEq Atom] [Hashable Atom]

/-! ## Branch Satisfiability -/

/-- A branch `b` with accessibility relation `acc` is satisfiable if there exists a
Kripke model `m` over some world type `W`, a world assignment `f : WorldIndex → W`, such that:
- The model's accessibility extends `acc`: if `acc.hasEdge w w'` then `m.r (f w) (f w')`.
- Every T(φ)@w on the branch: `Satisfies m (f w) φ`.
- Every F(φ)@w on the branch: `¬Satisfies m (f w) φ`. -/
def branchSatisfiable
    (b : List (SignedFormula (Proposition Atom) WorldIndex))
    (acc : Accessibility) : Prop :=
  ∃ (W : Type*) (m : Model W Atom) (f : WorldIndex → W),
    (∀ w w', acc.hasEdge w w' → m.r (f w) (f w')) ∧
    ∀ sf ∈ b,
      (sf.sign = .pos → Satisfies m (f sf.label) sf.formula) ∧
      (sf.sign = .neg → ¬Satisfies m (f sf.label) sf.formula)

/-! ## Closed Branches are Unsatisfiable -/

/-- Helper: recover propositional equality from BEq equality for `Proposition Atom`.

`Proposition Atom` derives `DecidableEq`, and its `BEq` instance is the generic
`decide (a = b)` instance obtained from `DecidableEq` (`Init.Prelude`'s
`instance (priority := 500) [DecidableEq α] : BEq α`). That same generic mechanism also
provides a `LawfulBEq (Proposition Atom)` instance (`instance [DecidableEq α] : LawfulBEq α`
in `Init.Core`), so `eq_of_beq` is available directly -- no structural induction on
`Proposition` is needed (and the naive structural arms do not typecheck, since `==` on
`Proposition Atom` does not definitionally reduce constructor-by-constructor). -/
private def Proposition.beqToEq {Atom : Type*} [DecidableEq Atom] :
    ∀ (a b : Proposition Atom), (a == b) = true → a = b :=
  fun _ _ h => LawfulBEq.eq_of_beq h

omit [Hashable Atom] in
/-- A modally closed branch is unsatisfiable with any accessibility relation.

Classical closure means T(⊥) is present (never satisfiable) or T(φ)/F(φ) coexist at the
same world label `w` (forcing simultaneous true and false). -/
lemma modalClosed_unsat
    (b : List (SignedFormula (Proposition Atom) WorldIndex))
    (hclosed : isModalClosed b = true)
    (acc : Accessibility) :
    ¬branchSatisfiable b acc := by
  intro ⟨W, m, f, _, hb⟩
  simp only [isModalClosed, ClosureCondition.isClosed, ClosureCondition.findClosure] at hclosed
  -- Extract the closure reason
  have hsome : (ClosureCondition.findClosure b).isSome = true := hclosed
  rw [Option.isSome_iff_exists] at hsome
  obtain ⟨cr, hcr⟩ := hsome
  cases hfind : b.find? (fun sf => sf.isPos && sf.formula == (HasBot.bot : Proposition Atom)) with
  | some sf =>
    -- T(⊥) is on the branch
    have hmem := List.mem_of_find?_eq_some hfind
    have hpred := List.find?_some hfind
    simp only [Bool.and_eq_true, SignedFormula.isPos] at hpred
    obtain ⟨hpos, hbot⟩ := hpred
    have hsat := (hb sf hmem).1 (by
      cases h : sf.sign with
      | pos => rfl
      | neg => simp [h, Sign.isPos] at hpos)
    have hformbot : sf.formula = (HasBot.bot : Proposition Atom) :=
      Proposition.beqToEq _ _ hbot
    rw [hformbot] at hsat
    change False at hsat
    exact hsat
  | none =>
    -- T(φ)/F(φ) contradiction
    simp only [hfind, ClosureCondition.findClosure] at hcr
    cases hcontra : Branch.findContradiction b with
    | none => simp [hfind, hcontra, ClosureCondition.findClosure] at hclosed
    | some pair =>
      obtain ⟨phi, l⟩ := pair
      simp only [Branch.findContradiction] at hcontra
      obtain ⟨sf, hsfmem, hsfcond⟩ := List.exists_of_findSome?_eq_some hcontra
      simp only [SignedFormula.isPos] at hsfcond
      by_cases hpos : sf.sign = .pos
      · simp only [hpos, Sign.isPos, ite_true, Option.ite_some_none_eq_some] at hsfcond
        obtain ⟨hany, _⟩ := hsfcond
        have htrue := (hb sf hsfmem).1 (by simp [hpos])
        obtain ⟨sf_neg, hmemneg, hsfneg⟩ := List.any_eq_true.mp hany
        simp only [Bool.and_eq_true] at hsfneg
        obtain ⟨⟨hsneg, hformEq⟩, hlabEq⟩ := hsfneg
        have hneg : sf_neg.sign = .neg := by
          cases h : sf_neg.sign with
          | pos => simp [h] at hsneg
          | neg => rfl
        have hformfeq : sf_neg.formula = sf.formula := Proposition.beqToEq _ _ hformEq
        have hlabfeq : sf_neg.label = sf.label := LawfulBEq.eq_of_beq hlabEq
        have hfalse := (hb sf_neg hmemneg).2 (by simp [hneg])
        rw [hformfeq, hlabfeq] at hfalse
        exact absurd htrue hfalse
      · cases hsf : sf.sign with
        | pos => exact absurd hsf hpos
        | neg => simp [hsf, Sign.isPos] at hsfcond

/-! ## Rule-Application Semantic Preservation -/

/-- The freshness invariant: all world indices in `acc` are strictly below `modalNextWorld b`.

This holds initially (acc = empty) and is maintained when a fresh world is created, since
`addEdge lbl (modalNextWorld b)` only adds the fresh index, and subsequent branch growth
keeps the invariant for the updated branch. -/
def accFreshInv
    (b : List (SignedFormula (Proposition Atom) WorldIndex))
    (acc : Accessibility) : Prop :=
  ∀ w w', acc.hasEdge w w' → w < modalNextWorld b ∧ w' < modalNextWorld b

omit [DecidableEq Atom] [Hashable Atom] in
/-- `accFreshInv` holds trivially for the empty accessibility relation. -/
lemma accFreshInv_empty
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) :
    accFreshInv b Accessibility.empty := by
  intro w w' hedge
  simp only [Accessibility.empty, Accessibility.hasEdge, List.any_nil] at hedge
  exact absurd hedge (by decide)

omit [DecidableEq Atom] [Hashable Atom] in
/-- Helper for the negative-implication α-rule (positive antecedent): if `F(A → C)` at world
`lbl` fails to be satisfied by `(m, f)`, and `b` (with accessibility `acc`) is otherwise
satisfiable via `(m, f)`, then `[T(A)@lbl, F(C)@lbl] ++ b` is satisfiable via `(m, f)`.

This is the shared tail of the ~18 leaf case-arms of `modalStepBranch_preserves_sat` for the
negative-implication α-rule where the antecedent `A` is not itself a negated implication
(`A ≠ A₁ → ⊥`); see `negImp_alpha_preserved_neg` for that shape. -/
private lemma negImp_alpha_preserved
    {A C : Proposition Atom} {lbl : WorldIndex}
    {b : List (SignedFormula (Proposition Atom) WorldIndex)}
    {acc : Accessibility}
    {W : Type u} {m : Model W Atom} {f : WorldIndex → W}
    (hacc : ∀ w w', acc.hasEdge w w' → m.r (f w) (f w'))
    (hb : ∀ sf ∈ b, (sf.sign = .pos → Satisfies m (f sf.label) sf.formula) ∧
                    (sf.sign = .neg → ¬Satisfies m (f sf.label) sf.formula))
    (hneg : ¬Satisfies m (f lbl) (Proposition.imp A C)) :
    branchSatisfiable.{v, u} ([⟨.pos, A, lbl⟩, ⟨.neg, C, lbl⟩] ++ b) acc := by
  simp only [Satisfies] at hneg
  have hsa : Satisfies m (f lbl) A := by by_contra h; exact hneg (fun ha => absurd ha h)
  have hnc : ¬Satisfies m (f lbl) C := fun hC => hneg (fun _ => hC)
  refine ⟨W, m, f, hacc, ?_⟩
  intro sf' hmem'
  simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hmem'
  rcases hmem' with (rfl | rfl) | hmem_old
  · exact ⟨fun _ => hsa, fun h => by simp at h⟩
  · exact ⟨fun h => by simp at h, fun _ => hnc⟩
  · exact hb sf' hmem_old

omit [DecidableEq Atom] [Hashable Atom] in
/-- Helper for the negative-implication α-rule (negation antecedent `A = A₁ → ⊥`): if
`F((A₁ → ⊥) → C)` at world `lbl` fails to be satisfied by `(m, f)`, and `b` (with accessibility
`acc`) is otherwise satisfiable via `(m, f)`, then `[F(A₁)@lbl, F(C)@lbl] ++ b` is satisfiable
via `(m, f)`.

This is the shared tail of the 4 leaf case-arms of `modalStepBranch_preserves_sat` for the
negative-implication α-rule where the antecedent is a negated implication. -/
private lemma negImp_alpha_preserved_neg
    {A1 C : Proposition Atom} {lbl : WorldIndex}
    {b : List (SignedFormula (Proposition Atom) WorldIndex)}
    {acc : Accessibility}
    {W : Type u} {m : Model W Atom} {f : WorldIndex → W}
    (hacc : ∀ w w', acc.hasEdge w w' → m.r (f w) (f w'))
    (hb : ∀ sf ∈ b, (sf.sign = .pos → Satisfies m (f sf.label) sf.formula) ∧
                    (sf.sign = .neg → ¬Satisfies m (f sf.label) sf.formula))
    (hneg : ¬Satisfies m (f lbl) (Proposition.imp (Proposition.imp A1 Proposition.bot) C)) :
    branchSatisfiable.{v, u} ([⟨.neg, A1, lbl⟩, ⟨.neg, C, lbl⟩] ++ b) acc := by
  simp only [Satisfies] at hneg
  have hna1 : ¬Satisfies m (f lbl) A1 := fun ha1 => hneg (fun hcon => absurd ha1 hcon)
  have hnc : ¬Satisfies m (f lbl) C := fun hC => hneg (fun _ => hC)
  refine ⟨W, m, f, hacc, ?_⟩
  intro sf' hmem'
  simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hmem'
  rcases hmem' with (rfl | rfl) | hmem_old
  · exact ⟨fun h => by simp at h, fun _ => hna1⟩
  · exact ⟨fun h => by simp at h, fun _ => hnc⟩
  · exact hb sf' hmem_old

/-- If `modalStepBranch b e acc = some (newBs, newExps, newAcc)` and `b` is satisfiable
(with the freshness invariant `hInv`), then some branch in `newBs` is satisfiable.

This is the core semantic preservation lemma. The key cases are:
- `boxPos`/`diamondNeg`: Universal propagation using `Satisfies.box_iff_forall`.
- `diamondPos`/`boxNeg`: Fresh world creation; extends the assignment `f` to map the
  fresh world index to a semantic witness. The freshness invariant ensures old edges
  in `acc` are not affected by extending `f`. -/
theorem modalStepBranch_preserves_sat
    (b : List (SignedFormula (Proposition Atom) WorldIndex))
    (e : List (SignedFormula (Proposition Atom) WorldIndex))
    (acc : Accessibility)
    (newBs : List (List (SignedFormula (Proposition Atom) WorldIndex)))
    (newExps : List (List (SignedFormula (Proposition Atom) WorldIndex)))
    (newAcc : Accessibility)
    (hstep : modalStepBranch b e acc = some (newBs, newExps, newAcc))
    (hsat : branchSatisfiable.{v, u} b acc)
    (hInv : accFreshInv b acc) :
    ∃ b' ∈ newBs, branchSatisfiable.{v, u} b' newAcc := by
  obtain ⟨W, m, f, hacc, hb⟩ := hsat
  simp only [modalStepBranch] at hstep
  obtain ⟨sf, hsfmem, hsf⟩ := List.exists_of_findSome?_eq_some hstep
  -- After split_ifs, only the false branch (sf not in expanded) survives,
  -- because the true branch gives none = some(...) which is absurd.
  split_ifs at hsf with hexp
  -- Only the case where hexp : ¬(e.any ... = true) remains
  obtain ⟨sign, formula, lbl⟩ := sf
  have hsf_b := hb ⟨sign, formula, lbl⟩ hsfmem
  -- Case split on sign and formula to determine which rule fired
  cases sign with
  | pos =>
      have hpos : Satisfies m (f lbl) formula := hsf_b.1 rfl
      -- Unfold propResult for pos formulas (modalApplyOne exposes tryAllPropRules)
      simp only [modalApplyOne] at hsf
      cases formula with
      | atom p =>
        -- No prop rule or modal rule applies to T(atom p)
        simp [tryAllPropRules, applyPropRule, modalAndOf?, modalOrOf?,
          modalImpOf?, modalNegOf?, List.map, List.find?, RuleResult.isApplicable] at hsf
      | bot =>
        -- T(⊥) means Satisfies m (f lbl) ⊥ = False, contradiction
        simp only [Satisfies] at hpos
      | box φ =>
        -- T(□φ): tryAllPropRules returns notApplicable, then boxPos fires
        simp [tryAllPropRules, applyPropRule, modalAndOf?, modalOrOf?,
          modalImpOf?, modalNegOf?, List.map, List.find?, RuleResult.isApplicable] at hsf
        -- boxPos: result = .persistent (boxPropagation b acc φ lbl)
        -- if boxPropagation is empty → notApplicable (simp eliminates)
        -- otherwise → persistent newForms
        split_ifs at hsf with hemp
        · simp only [Option.some.injEq, Prod.mk.injEq] at hsf
          obtain ⟨hnewBs, _, hnewAcc⟩ := hsf
          subst hnewBs hnewAcc
          -- boxPos: newBs = [boxPropagation b acc φ lbl ++ b], acc unchanged
          refine ⟨boxPropagation b acc φ lbl ++ b, List.mem_cons_self, W, m, f, hacc, ?_⟩
          intro sf' hmem'
          simp only [List.mem_append] at hmem'
          rcases hmem' with hmem_new | hmem_old
          · -- sf' ∈ boxPropagation b acc φ lbl
            -- Each such sf' = ⟨.pos, φ, w'⟩ where acc.hasEdge lbl w' = true
            simp only [boxPropagation, Accessibility.successorsOf, List.mem_filterMap] at hmem_new
            obtain ⟨w', hw'mem, hsf'⟩ := hmem_new
            -- hw'mem already reduced by the previous simp to ∃ a, a ∈ acc.edges ∧ ...
            obtain ⟨⟨src, tgt⟩, hedge_mem, hsrc⟩ := hw'mem
            simp only [beq_iff_eq] at hsrc
            split_ifs at hsrc with hsrceq
            · simp only [Option.some.injEq] at hsrc
              subst hsrc
              -- acc.hasEdge lbl w' = true since (src, w') ∈ acc.edges and src = lbl
              have hedge : acc.hasEdge lbl tgt = true := by
                rw [show lbl = src from hsrceq.symm]
                simp only [Accessibility.hasEdge, List.any_eq_true]
                exact ⟨(src, tgt), hedge_mem, by simp⟩
              -- sf' = ⟨.pos, φ, tgt⟩ (from hsf' after splitting if b.any)
              split_ifs at hsf' with hinb
              · simp only [Option.some.injEq] at hsf'
                subst hsf'
                -- Need: (sf' = ⟨.pos, φ, tgt⟩).sign = .pos → Satisfies m (f tgt) φ
                -- and .neg → ¬Satisfies
                constructor
                · intro _
                  -- hpos : Satisfies m (f lbl) (□φ) = ∀ w', m.r (f lbl) w' → Satisfies m w' φ
                  simp only [Satisfies] at hpos
                  exact hpos (f tgt) (hacc lbl tgt hedge)
                · intro h; simp at h
          · exact hb sf' hmem_old
      | imp a c =>
        -- T(a → c): rule depends on structure of a and c
        cases c with
        | bot =>
          -- c = ⊥
          cases a with
          | atom name =>
            simp [tryAllPropRules, applyPropRule, modalAndOf?, modalOrOf?,
              modalImpOf?, modalNegOf?, List.map, List.find?, RuleResult.isApplicable,
              Option.some.injEq, Prod.mk.injEq] at hsf
            obtain ⟨hnewBs, _, hnewAcc⟩ := hsf
            subst hnewBs hnewAcc
            refine ⟨[⟨.neg, Proposition.atom name, lbl⟩] ++ b,
              List.mem_cons_self, W, m, f, hacc, ?_⟩
            intro sf' hmem'
            simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hmem'
            rcases hmem' with rfl | hmem_old
            · refine ⟨fun h => by simp at h, fun _ => ?_⟩
              simp only [Satisfies] at hpos
              exact fun ha => hpos ha
            · exact hb sf' hmem_old
          | bot =>
            simp [tryAllPropRules, applyPropRule, modalAndOf?, modalOrOf?,
              modalImpOf?, modalNegOf?, List.map, List.find?, RuleResult.isApplicable,
              Option.some.injEq, Prod.mk.injEq] at hsf
            obtain ⟨hnewBs, _, hnewAcc⟩ := hsf
            subst hnewBs hnewAcc
            refine ⟨[⟨.neg, Proposition.bot, lbl⟩] ++ b, List.mem_cons_self, W, m, f, hacc, ?_⟩
            intro sf' hmem'
            simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hmem'
            rcases hmem' with rfl | hmem_old
            · refine ⟨fun h => by simp at h, fun _ => ?_⟩
              simp only [Satisfies] at hpos
              exact fun ha => hpos ha
            · exact hb sf' hmem_old
          | box bb =>
            simp [tryAllPropRules, applyPropRule, modalAndOf?, modalOrOf?,
              modalImpOf?, modalNegOf?, List.map, List.find?, RuleResult.isApplicable,
              Option.some.injEq, Prod.mk.injEq] at hsf
            obtain ⟨hnewBs, _, hnewAcc⟩ := hsf
            subst hnewBs hnewAcc
            refine ⟨[⟨.neg, Proposition.box bb, lbl⟩] ++ b, List.mem_cons_self, W, m, f, hacc, ?_⟩
            intro sf' hmem'
            simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hmem'
            rcases hmem' with rfl | hmem_old
            · refine ⟨fun h => by simp at h, fun _ => ?_⟩
              simp only [Satisfies] at hpos
              exact fun ha => hpos ha
            · exact hb sf' hmem_old
          | imp a1 a2 =>
            cases a2 with
            | bot =>
              simp [tryAllPropRules, applyPropRule, modalAndOf?, modalOrOf?,
                modalImpOf?, modalNegOf?, List.map, List.find?, RuleResult.isApplicable,
                Option.some.injEq, Prod.mk.injEq] at hsf
              obtain ⟨hnewBs, _, hnewAcc⟩ := hsf
              subst hnewBs hnewAcc
              simp only [Satisfies] at hpos
              rcases Classical.em (Satisfies m (f lbl) a1) with ha1 | ha1
              · refine ⟨[⟨.pos, a1, lbl⟩] ++ b, List.mem_cons_self, W, m, f, hacc, ?_⟩
                intro sf' hmem'
                simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hmem'
                rcases hmem' with rfl | hmem_old
                · exact ⟨fun _ => ha1, fun h => by simp at h⟩
                · exact hb sf' hmem_old
              · refine ⟨[⟨.pos, Proposition.bot, lbl⟩] ++ b,
                  List.mem_cons_of_mem _ List.mem_cons_self,
                  W, m, f, hacc, ?_⟩
                intro sf' hmem'
                simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hmem'
                rcases hmem' with rfl | hmem_old
                · exact ⟨fun _ => hpos ha1, fun h => by simp at h⟩
                · exact hb sf' hmem_old
            | atom a2n =>
              simp [tryAllPropRules, applyPropRule, modalAndOf?, modalOrOf?,
                modalImpOf?, modalNegOf?, List.map, List.find?, RuleResult.isApplicable,
                Option.some.injEq, Prod.mk.injEq] at hsf
              obtain ⟨hnewBs, _, hnewAcc⟩ := hsf
              subst hnewBs hnewAcc
              refine ⟨[⟨.neg, Proposition.imp a1 (Proposition.atom a2n), lbl⟩] ++ b,
                List.mem_cons_self, W, m, f, hacc, ?_⟩
              intro sf' hmem'
              simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hmem'
              rcases hmem' with rfl | hmem_old
              · refine ⟨fun h => by simp at h, fun _ => ?_⟩
                simp only [Satisfies] at hpos
                exact fun ha => hpos ha
              · exact hb sf' hmem_old
            | box a2b =>
              simp [tryAllPropRules, applyPropRule, modalAndOf?, modalOrOf?,
                modalImpOf?, modalNegOf?, List.map, List.find?, RuleResult.isApplicable,
                Option.some.injEq, Prod.mk.injEq] at hsf
              obtain ⟨hnewBs, _, hnewAcc⟩ := hsf
              subst hnewBs hnewAcc
              refine ⟨[⟨.neg, Proposition.imp a1 (Proposition.box a2b), lbl⟩] ++ b,
                List.mem_cons_self, W, m, f, hacc, ?_⟩
              intro sf' hmem'
              simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hmem'
              rcases hmem' with rfl | hmem_old
              · refine ⟨fun h => by simp at h, fun _ => ?_⟩
                simp only [Satisfies] at hpos
                exact fun ha => hpos ha
              · exact hb sf' hmem_old
            | imp b1 b2 =>
              cases b2 with
              | bot =>
                simp [tryAllPropRules, applyPropRule, modalAndOf?, modalOrOf?,
                  modalImpOf?, modalNegOf?, List.map, List.find?, RuleResult.isApplicable,
                  Option.some.injEq, Prod.mk.injEq] at hsf
                obtain ⟨hnewBs, _, hnewAcc⟩ := hsf
                subst hnewBs hnewAcc
                simp only [Satisfies] at hpos
                have ha1 : Satisfies m (f lbl) a1 := by
                  by_contra h
                  exact hpos (fun ha _ => absurd ha h)
                have hb1 : Satisfies m (f lbl) b1 := by
                  by_contra h
                  exact hpos (fun _ hbb => absurd hbb h)
                refine ⟨[⟨.pos, a1, lbl⟩, ⟨.pos, b1, lbl⟩] ++ b,
                  List.mem_cons_self, W, m, f, hacc, ?_⟩
                intro sf' hmem'
                simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hmem'
                rcases hmem' with (rfl | rfl) | hmem_old
                · exact ⟨fun _ => ha1, fun h => by simp at h⟩
                · exact ⟨fun _ => hb1, fun h => by simp at h⟩
                · exact hb sf' hmem_old
              | atom b2n =>
                simp [tryAllPropRules, applyPropRule, modalAndOf?, modalOrOf?,
                  modalImpOf?, modalNegOf?, List.map, List.find?, RuleResult.isApplicable,
                  Option.some.injEq, Prod.mk.injEq] at hsf
                obtain ⟨hnewBs, _, hnewAcc⟩ := hsf
                subst hnewBs hnewAcc
                refine ⟨[⟨.neg,
                    Proposition.imp a1 (Proposition.imp b1 (Proposition.atom b2n)), lbl⟩] ++ b,
                  List.mem_cons_self, W, m, f, hacc, ?_⟩
                intro sf' hmem'
                simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hmem'
                rcases hmem' with rfl | hmem_old
                · refine ⟨fun h => by simp at h, fun _ => ?_⟩
                  simp only [Satisfies] at hpos
                  exact fun ha => hpos ha
                · exact hb sf' hmem_old
              | box b2b =>
                simp [tryAllPropRules, applyPropRule, modalAndOf?, modalOrOf?,
                  modalImpOf?, modalNegOf?, List.map, List.find?, RuleResult.isApplicable,
                  Option.some.injEq, Prod.mk.injEq] at hsf
                obtain ⟨hnewBs, _, hnewAcc⟩ := hsf
                subst hnewBs hnewAcc
                refine ⟨[⟨.neg,
                    Proposition.imp a1 (Proposition.imp b1 (Proposition.box b2b)), lbl⟩] ++ b,
                  List.mem_cons_self, W, m, f, hacc, ?_⟩
                intro sf' hmem'
                simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hmem'
                rcases hmem' with rfl | hmem_old
                · refine ⟨fun h => by simp at h, fun _ => ?_⟩
                  simp only [Satisfies] at hpos
                  exact fun ha => hpos ha
                · exact hb sf' hmem_old
              | imp b3 b4 =>
                simp [tryAllPropRules, applyPropRule, modalAndOf?, modalOrOf?,
                  modalImpOf?, modalNegOf?, List.map, List.find?, RuleResult.isApplicable,
                  Option.some.injEq, Prod.mk.injEq] at hsf
                obtain ⟨hnewBs, _, hnewAcc⟩ := hsf
                subst hnewBs hnewAcc
                refine ⟨[⟨.neg,
                    Proposition.imp a1 (Proposition.imp b1 (Proposition.imp b3 b4)), lbl⟩] ++ b,
                  List.mem_cons_self, W, m, f, hacc, ?_⟩
                intro sf' hmem'
                simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hmem'
                rcases hmem' with rfl | hmem_old
                · refine ⟨fun h => by simp at h, fun _ => ?_⟩
                  simp only [Satisfies] at hpos
                  exact fun ha => hpos ha
                · exact hb sf' hmem_old
        | atom cn =>
          cases a with
          | atom an =>
            simp [tryAllPropRules, applyPropRule, modalAndOf?, modalOrOf?,
              modalImpOf?, modalNegOf?, List.map, List.find?, RuleResult.isApplicable,
              Option.some.injEq, Prod.mk.injEq] at hsf
            obtain ⟨hnewBs, _, hnewAcc⟩ := hsf
            subst hnewBs hnewAcc
            simp only [Satisfies] at hpos
            rcases Classical.em (Satisfies m (f lbl) (Proposition.atom an)) with ha | ha
            · refine ⟨[⟨.pos, Proposition.atom cn, lbl⟩] ++ b,
                List.mem_cons_of_mem _ List.mem_cons_self,
                W, m, f, hacc, ?_⟩
              intro sf' hmem'
              simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hmem'
              rcases hmem' with rfl | hmem_old
              · exact ⟨fun _ => hpos ha, fun h => by simp at h⟩
              · exact hb sf' hmem_old
            · refine ⟨[⟨.neg, Proposition.atom an, lbl⟩] ++ b,
                List.mem_cons_self, W, m, f, hacc, ?_⟩
              intro sf' hmem'
              simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hmem'
              rcases hmem' with rfl | hmem_old
              · exact ⟨fun h => by simp at h, fun _ => ha⟩
              · exact hb sf' hmem_old
          | bot =>
            simp [tryAllPropRules, applyPropRule, modalAndOf?, modalOrOf?,
              modalImpOf?, modalNegOf?, List.map, List.find?, RuleResult.isApplicable,
              Option.some.injEq, Prod.mk.injEq] at hsf
            obtain ⟨hnewBs, _, hnewAcc⟩ := hsf
            subst hnewBs hnewAcc
            simp only [Satisfies] at hpos
            rcases Classical.em (Satisfies m (f lbl) (Proposition.bot)) with ha | ha
            · refine ⟨[⟨.pos, Proposition.atom cn, lbl⟩] ++ b,
                List.mem_cons_of_mem _ List.mem_cons_self,
                W, m, f, hacc, ?_⟩
              intro sf' hmem'
              simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hmem'
              rcases hmem' with rfl | hmem_old
              · exact ⟨fun _ => hpos ha, fun h => by simp at h⟩
              · exact hb sf' hmem_old
            · refine ⟨[⟨.neg, Proposition.bot, lbl⟩] ++ b,
                List.mem_cons_self, W, m, f, hacc, ?_⟩
              intro sf' hmem'
              simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hmem'
              rcases hmem' with rfl | hmem_old
              · exact ⟨fun h => by simp at h, fun _ => ha⟩
              · exact hb sf' hmem_old
          | box ab =>
            simp [tryAllPropRules, applyPropRule, modalAndOf?, modalOrOf?,
              modalImpOf?, modalNegOf?, List.map, List.find?, RuleResult.isApplicable,
              Option.some.injEq, Prod.mk.injEq] at hsf
            obtain ⟨hnewBs, _, hnewAcc⟩ := hsf
            subst hnewBs hnewAcc
            simp only [Satisfies] at hpos
            rcases Classical.em (Satisfies m (f lbl) (Proposition.box ab)) with ha | ha
            · refine ⟨[⟨.pos, Proposition.atom cn, lbl⟩] ++ b,
                List.mem_cons_of_mem _ List.mem_cons_self,
                W, m, f, hacc, ?_⟩
              intro sf' hmem'
              simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hmem'
              rcases hmem' with rfl | hmem_old
              · exact ⟨fun _ => hpos ha, fun h => by simp at h⟩
              · exact hb sf' hmem_old
            · refine ⟨[⟨.neg, Proposition.box ab, lbl⟩] ++ b,
                List.mem_cons_self, W, m, f, hacc, ?_⟩
              intro sf' hmem'
              simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hmem'
              rcases hmem' with rfl | hmem_old
              · exact ⟨fun h => by simp at h, fun _ => ha⟩
              · exact hb sf' hmem_old
          | imp a1 a2 =>
            cases a2 with
            | bot =>
              simp [tryAllPropRules, applyPropRule, modalAndOf?, modalOrOf?,
                modalImpOf?, modalNegOf?, List.map, List.find?, RuleResult.isApplicable,
                Option.some.injEq, Prod.mk.injEq] at hsf
              obtain ⟨hnewBs, _, hnewAcc⟩ := hsf
              subst hnewBs hnewAcc
              simp only [Satisfies] at hpos
              rcases Classical.em (Satisfies m (f lbl) a1) with ha1 | ha1
              · refine ⟨[⟨.pos, a1, lbl⟩] ++ b, List.mem_cons_self, W, m, f, hacc, ?_⟩
                intro sf' hmem'
                simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hmem'
                rcases hmem' with rfl | hmem_old
                · exact ⟨fun _ => ha1, fun h => by simp at h⟩
                · exact hb sf' hmem_old
              · refine ⟨[⟨.pos, Proposition.atom cn, lbl⟩] ++ b,
                  List.mem_cons_of_mem _ List.mem_cons_self,
                  W, m, f, hacc, ?_⟩
                intro sf' hmem'
                simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hmem'
                rcases hmem' with rfl | hmem_old
                · exact ⟨fun _ => hpos ha1, fun h => by simp at h⟩
                · exact hb sf' hmem_old
            | atom a2n =>
              simp [tryAllPropRules, applyPropRule, modalAndOf?, modalOrOf?,
                modalImpOf?, modalNegOf?, List.map, List.find?, RuleResult.isApplicable,
                Option.some.injEq, Prod.mk.injEq] at hsf
              obtain ⟨hnewBs, _, hnewAcc⟩ := hsf
              subst hnewBs hnewAcc
              simp only [Satisfies] at hpos
              rcases Classical.em (Satisfies m (f lbl) (Proposition.imp a1 (Proposition.atom a2n)))
                with ha | ha
              · refine ⟨[⟨.pos, Proposition.atom cn, lbl⟩] ++ b,
                  List.mem_cons_of_mem _ List.mem_cons_self,
                  W, m, f, hacc, ?_⟩
                intro sf' hmem'
                simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hmem'
                rcases hmem' with rfl | hmem_old
                · exact ⟨fun _ => hpos ha, fun h => by simp at h⟩
                · exact hb sf' hmem_old
              · refine ⟨[⟨.neg, Proposition.imp a1 (Proposition.atom a2n), lbl⟩] ++ b,
                  List.mem_cons_self, W, m, f, hacc, ?_⟩
                intro sf' hmem'
                simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hmem'
                rcases hmem' with rfl | hmem_old
                · exact ⟨fun h => by simp at h, fun _ => ha⟩
                · exact hb sf' hmem_old
            | box a2b =>
              simp [tryAllPropRules, applyPropRule, modalAndOf?, modalOrOf?,
                modalImpOf?, modalNegOf?, List.map, List.find?, RuleResult.isApplicable,
                Option.some.injEq, Prod.mk.injEq] at hsf
              obtain ⟨hnewBs, _, hnewAcc⟩ := hsf
              subst hnewBs hnewAcc
              simp only [Satisfies] at hpos
              rcases Classical.em (Satisfies m (f lbl) (Proposition.imp a1 (Proposition.box a2b)))
                with ha | ha
              · refine ⟨[⟨.pos, Proposition.atom cn, lbl⟩] ++ b,
                  List.mem_cons_of_mem _ List.mem_cons_self,
                  W, m, f, hacc, ?_⟩
                intro sf' hmem'
                simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hmem'
                rcases hmem' with rfl | hmem_old
                · exact ⟨fun _ => hpos ha, fun h => by simp at h⟩
                · exact hb sf' hmem_old
              · refine ⟨[⟨.neg, Proposition.imp a1 (Proposition.box a2b), lbl⟩] ++ b,
                  List.mem_cons_self, W, m, f, hacc, ?_⟩
                intro sf' hmem'
                simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hmem'
                rcases hmem' with rfl | hmem_old
                · exact ⟨fun h => by simp at h, fun _ => ha⟩
                · exact hb sf' hmem_old
            | imp b1 b2 =>
              simp [tryAllPropRules, applyPropRule, modalAndOf?, modalOrOf?,
                modalImpOf?, modalNegOf?, List.map, List.find?, RuleResult.isApplicable,
                Option.some.injEq, Prod.mk.injEq] at hsf
              obtain ⟨hnewBs, _, hnewAcc⟩ := hsf
              subst hnewBs hnewAcc
              simp only [Satisfies] at hpos
              rcases Classical.em (Satisfies m (f lbl) (Proposition.imp a1 (Proposition.imp b1 b2)))
                with ha | ha
              · refine ⟨[⟨.pos, Proposition.atom cn, lbl⟩] ++ b,
                  List.mem_cons_of_mem _ List.mem_cons_self,
                  W, m, f, hacc, ?_⟩
                intro sf' hmem'
                simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hmem'
                rcases hmem' with rfl | hmem_old
                · exact ⟨fun _ => hpos ha, fun h => by simp at h⟩
                · exact hb sf' hmem_old
              · refine ⟨[⟨.neg, Proposition.imp a1 (Proposition.imp b1 b2), lbl⟩] ++ b,
                  List.mem_cons_self, W, m, f, hacc, ?_⟩
                intro sf' hmem'
                simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hmem'
                rcases hmem' with rfl | hmem_old
                · exact ⟨fun h => by simp at h, fun _ => ha⟩
                · exact hb sf' hmem_old
        | imp c1 c2 =>
          cases a with
          | atom an =>
            simp [tryAllPropRules, applyPropRule, modalAndOf?, modalOrOf?,
              modalImpOf?, modalNegOf?, List.map, List.find?, RuleResult.isApplicable,
              Option.some.injEq, Prod.mk.injEq] at hsf
            obtain ⟨hnewBs, _, hnewAcc⟩ := hsf
            subst hnewBs hnewAcc
            simp only [Satisfies] at hpos
            rcases Classical.em (Satisfies m (f lbl) (Proposition.atom an)) with ha | ha
            · refine ⟨[⟨.pos, Proposition.imp c1 c2, lbl⟩] ++ b,
                List.mem_cons_of_mem _ List.mem_cons_self,
                W, m, f, hacc, ?_⟩
              intro sf' hmem'
              simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hmem'
              rcases hmem' with rfl | hmem_old
              · exact ⟨fun _ => hpos ha, fun h => by simp at h⟩
              · exact hb sf' hmem_old
            · refine ⟨[⟨.neg, Proposition.atom an, lbl⟩] ++ b,
                List.mem_cons_self, W, m, f, hacc, ?_⟩
              intro sf' hmem'
              simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hmem'
              rcases hmem' with rfl | hmem_old
              · exact ⟨fun h => by simp at h, fun _ => ha⟩
              · exact hb sf' hmem_old
          | bot =>
            simp [tryAllPropRules, applyPropRule, modalAndOf?, modalOrOf?,
              modalImpOf?, modalNegOf?, List.map, List.find?, RuleResult.isApplicable,
              Option.some.injEq, Prod.mk.injEq] at hsf
            obtain ⟨hnewBs, _, hnewAcc⟩ := hsf
            subst hnewBs hnewAcc
            simp only [Satisfies] at hpos
            rcases Classical.em (Satisfies m (f lbl) (Proposition.bot)) with ha | ha
            · refine ⟨[⟨.pos, Proposition.imp c1 c2, lbl⟩] ++ b,
                List.mem_cons_of_mem _ List.mem_cons_self,
                W, m, f, hacc, ?_⟩
              intro sf' hmem'
              simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hmem'
              rcases hmem' with rfl | hmem_old
              · exact ⟨fun _ => hpos ha, fun h => by simp at h⟩
              · exact hb sf' hmem_old
            · refine ⟨[⟨.neg, Proposition.bot, lbl⟩] ++ b,
                List.mem_cons_self, W, m, f, hacc, ?_⟩
              intro sf' hmem'
              simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hmem'
              rcases hmem' with rfl | hmem_old
              · exact ⟨fun h => by simp at h, fun _ => ha⟩
              · exact hb sf' hmem_old
          | box ab =>
            simp [tryAllPropRules, applyPropRule, modalAndOf?, modalOrOf?,
              modalImpOf?, modalNegOf?, List.map, List.find?, RuleResult.isApplicable,
              Option.some.injEq, Prod.mk.injEq] at hsf
            obtain ⟨hnewBs, _, hnewAcc⟩ := hsf
            subst hnewBs hnewAcc
            simp only [Satisfies] at hpos
            rcases Classical.em (Satisfies m (f lbl) (Proposition.box ab)) with ha | ha
            · refine ⟨[⟨.pos, Proposition.imp c1 c2, lbl⟩] ++ b,
                List.mem_cons_of_mem _ List.mem_cons_self,
                W, m, f, hacc, ?_⟩
              intro sf' hmem'
              simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hmem'
              rcases hmem' with rfl | hmem_old
              · exact ⟨fun _ => hpos ha, fun h => by simp at h⟩
              · exact hb sf' hmem_old
            · refine ⟨[⟨.neg, Proposition.box ab, lbl⟩] ++ b,
                List.mem_cons_self, W, m, f, hacc, ?_⟩
              intro sf' hmem'
              simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hmem'
              rcases hmem' with rfl | hmem_old
              · exact ⟨fun h => by simp at h, fun _ => ha⟩
              · exact hb sf' hmem_old
          | imp a1 a2 =>
            cases a2 with
            | bot =>
              simp [tryAllPropRules, applyPropRule, modalAndOf?, modalOrOf?,
                modalImpOf?, modalNegOf?, List.map, List.find?, RuleResult.isApplicable,
                Option.some.injEq, Prod.mk.injEq] at hsf
              obtain ⟨hnewBs, _, hnewAcc⟩ := hsf
              subst hnewBs hnewAcc
              simp only [Satisfies] at hpos
              rcases Classical.em (Satisfies m (f lbl) a1) with ha1 | ha1
              · refine ⟨[⟨.pos, a1, lbl⟩] ++ b, List.mem_cons_self, W, m, f, hacc, ?_⟩
                intro sf' hmem'
                simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hmem'
                rcases hmem' with rfl | hmem_old
                · exact ⟨fun _ => ha1, fun h => by simp at h⟩
                · exact hb sf' hmem_old
              · refine ⟨[⟨.pos, Proposition.imp c1 c2, lbl⟩] ++ b,
                  List.mem_cons_of_mem _ List.mem_cons_self,
                  W, m, f, hacc, ?_⟩
                intro sf' hmem'
                simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hmem'
                rcases hmem' with rfl | hmem_old
                · exact ⟨fun _ => hpos ha1, fun h => by simp at h⟩
                · exact hb sf' hmem_old
            | atom a2n =>
              simp [tryAllPropRules, applyPropRule, modalAndOf?, modalOrOf?,
                modalImpOf?, modalNegOf?, List.map, List.find?, RuleResult.isApplicable,
                Option.some.injEq, Prod.mk.injEq] at hsf
              obtain ⟨hnewBs, _, hnewAcc⟩ := hsf
              subst hnewBs hnewAcc
              simp only [Satisfies] at hpos
              rcases Classical.em (Satisfies m (f lbl) (Proposition.imp a1 (Proposition.atom a2n)))
                with ha | ha
              · refine ⟨[⟨.pos, Proposition.imp c1 c2, lbl⟩] ++ b,
                  List.mem_cons_of_mem _ List.mem_cons_self,
                  W, m, f, hacc, ?_⟩
                intro sf' hmem'
                simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hmem'
                rcases hmem' with rfl | hmem_old
                · exact ⟨fun _ => hpos ha, fun h => by simp at h⟩
                · exact hb sf' hmem_old
              · refine ⟨[⟨.neg, Proposition.imp a1 (Proposition.atom a2n), lbl⟩] ++ b,
                  List.mem_cons_self, W, m, f, hacc, ?_⟩
                intro sf' hmem'
                simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hmem'
                rcases hmem' with rfl | hmem_old
                · exact ⟨fun h => by simp at h, fun _ => ha⟩
                · exact hb sf' hmem_old
            | box a2b =>
              simp [tryAllPropRules, applyPropRule, modalAndOf?, modalOrOf?,
                modalImpOf?, modalNegOf?, List.map, List.find?, RuleResult.isApplicable,
                Option.some.injEq, Prod.mk.injEq] at hsf
              obtain ⟨hnewBs, _, hnewAcc⟩ := hsf
              subst hnewBs hnewAcc
              simp only [Satisfies] at hpos
              rcases Classical.em (Satisfies m (f lbl) (Proposition.imp a1 (Proposition.box a2b)))
                with ha | ha
              · refine ⟨[⟨.pos, Proposition.imp c1 c2, lbl⟩] ++ b,
                  List.mem_cons_of_mem _ List.mem_cons_self,
                  W, m, f, hacc, ?_⟩
                intro sf' hmem'
                simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hmem'
                rcases hmem' with rfl | hmem_old
                · exact ⟨fun _ => hpos ha, fun h => by simp at h⟩
                · exact hb sf' hmem_old
              · refine ⟨[⟨.neg, Proposition.imp a1 (Proposition.box a2b), lbl⟩] ++ b,
                  List.mem_cons_self, W, m, f, hacc, ?_⟩
                intro sf' hmem'
                simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hmem'
                rcases hmem' with rfl | hmem_old
                · exact ⟨fun h => by simp at h, fun _ => ha⟩
                · exact hb sf' hmem_old
            | imp b1 b2 =>
              simp [tryAllPropRules, applyPropRule, modalAndOf?, modalOrOf?,
                modalImpOf?, modalNegOf?, List.map, List.find?, RuleResult.isApplicable,
                Option.some.injEq, Prod.mk.injEq] at hsf
              obtain ⟨hnewBs, _, hnewAcc⟩ := hsf
              subst hnewBs hnewAcc
              simp only [Satisfies] at hpos
              rcases Classical.em (Satisfies m (f lbl) (Proposition.imp a1 (Proposition.imp b1 b2)))
                with ha | ha
              · refine ⟨[⟨.pos, Proposition.imp c1 c2, lbl⟩] ++ b,
                  List.mem_cons_of_mem _ List.mem_cons_self,
                  W, m, f, hacc, ?_⟩
                intro sf' hmem'
                simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hmem'
                rcases hmem' with rfl | hmem_old
                · exact ⟨fun _ => hpos ha, fun h => by simp at h⟩
                · exact hb sf' hmem_old
              · refine ⟨[⟨.neg, Proposition.imp a1 (Proposition.imp b1 b2), lbl⟩] ++ b,
                  List.mem_cons_self, W, m, f, hacc, ?_⟩
                intro sf' hmem'
                simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hmem'
                rcases hmem' with rfl | hmem_old
                · exact ⟨fun h => by simp at h, fun _ => ha⟩
                · exact hb sf' hmem_old
        | box cb =>
          cases a with
          | atom an =>
            simp [tryAllPropRules, applyPropRule, modalAndOf?, modalOrOf?,
              modalImpOf?, modalNegOf?, List.map, List.find?, RuleResult.isApplicable,
              Option.some.injEq, Prod.mk.injEq] at hsf
            obtain ⟨hnewBs, _, hnewAcc⟩ := hsf
            subst hnewBs hnewAcc
            simp only [Satisfies] at hpos
            rcases Classical.em (Satisfies m (f lbl) (Proposition.atom an)) with ha | ha
            · refine ⟨[⟨.pos, Proposition.box cb, lbl⟩] ++ b,
                List.mem_cons_of_mem _ List.mem_cons_self,
                W, m, f, hacc, ?_⟩
              intro sf' hmem'
              simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hmem'
              rcases hmem' with rfl | hmem_old
              · exact ⟨fun _ => hpos ha, fun h => by simp at h⟩
              · exact hb sf' hmem_old
            · refine ⟨[⟨.neg, Proposition.atom an, lbl⟩] ++ b,
                List.mem_cons_self, W, m, f, hacc, ?_⟩
              intro sf' hmem'
              simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hmem'
              rcases hmem' with rfl | hmem_old
              · exact ⟨fun h => by simp at h, fun _ => ha⟩
              · exact hb sf' hmem_old
          | bot =>
            simp [tryAllPropRules, applyPropRule, modalAndOf?, modalOrOf?,
              modalImpOf?, modalNegOf?, List.map, List.find?, RuleResult.isApplicable,
              Option.some.injEq, Prod.mk.injEq] at hsf
            obtain ⟨hnewBs, _, hnewAcc⟩ := hsf
            subst hnewBs hnewAcc
            simp only [Satisfies] at hpos
            rcases Classical.em (Satisfies m (f lbl) (Proposition.bot)) with ha | ha
            · refine ⟨[⟨.pos, Proposition.box cb, lbl⟩] ++ b,
                List.mem_cons_of_mem _ List.mem_cons_self,
                W, m, f, hacc, ?_⟩
              intro sf' hmem'
              simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hmem'
              rcases hmem' with rfl | hmem_old
              · exact ⟨fun _ => hpos ha, fun h => by simp at h⟩
              · exact hb sf' hmem_old
            · refine ⟨[⟨.neg, Proposition.bot, lbl⟩] ++ b,
                List.mem_cons_self, W, m, f, hacc, ?_⟩
              intro sf' hmem'
              simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hmem'
              rcases hmem' with rfl | hmem_old
              · exact ⟨fun h => by simp at h, fun _ => ha⟩
              · exact hb sf' hmem_old
          | box ab =>
            simp [tryAllPropRules, applyPropRule, modalAndOf?, modalOrOf?,
              modalImpOf?, modalNegOf?, List.map, List.find?, RuleResult.isApplicable,
              Option.some.injEq, Prod.mk.injEq] at hsf
            obtain ⟨hnewBs, _, hnewAcc⟩ := hsf
            subst hnewBs hnewAcc
            simp only [Satisfies] at hpos
            rcases Classical.em (Satisfies m (f lbl) (Proposition.box ab)) with ha | ha
            · refine ⟨[⟨.pos, Proposition.box cb, lbl⟩] ++ b,
                List.mem_cons_of_mem _ List.mem_cons_self,
                W, m, f, hacc, ?_⟩
              intro sf' hmem'
              simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hmem'
              rcases hmem' with rfl | hmem_old
              · exact ⟨fun _ => hpos ha, fun h => by simp at h⟩
              · exact hb sf' hmem_old
            · refine ⟨[⟨.neg, Proposition.box ab, lbl⟩] ++ b,
                List.mem_cons_self, W, m, f, hacc, ?_⟩
              intro sf' hmem'
              simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hmem'
              rcases hmem' with rfl | hmem_old
              · exact ⟨fun h => by simp at h, fun _ => ha⟩
              · exact hb sf' hmem_old
          | imp a1 a2 =>
            cases a2 with
            | bot =>
              simp [tryAllPropRules, applyPropRule, modalAndOf?, modalOrOf?,
                modalImpOf?, modalNegOf?, List.map, List.find?, RuleResult.isApplicable,
                Option.some.injEq, Prod.mk.injEq] at hsf
              obtain ⟨hnewBs, _, hnewAcc⟩ := hsf
              subst hnewBs hnewAcc
              simp only [Satisfies] at hpos
              rcases Classical.em (Satisfies m (f lbl) a1) with ha1 | ha1
              · refine ⟨[⟨.pos, a1, lbl⟩] ++ b, List.mem_cons_self, W, m, f, hacc, ?_⟩
                intro sf' hmem'
                simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hmem'
                rcases hmem' with rfl | hmem_old
                · exact ⟨fun _ => ha1, fun h => by simp at h⟩
                · exact hb sf' hmem_old
              · refine ⟨[⟨.pos, Proposition.box cb, lbl⟩] ++ b,
                  List.mem_cons_of_mem _ List.mem_cons_self,
                  W, m, f, hacc, ?_⟩
                intro sf' hmem'
                simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hmem'
                rcases hmem' with rfl | hmem_old
                · exact ⟨fun _ => hpos ha1, fun h => by simp at h⟩
                · exact hb sf' hmem_old
            | atom a2n =>
              simp [tryAllPropRules, applyPropRule, modalAndOf?, modalOrOf?,
                modalImpOf?, modalNegOf?, List.map, List.find?, RuleResult.isApplicable,
                Option.some.injEq, Prod.mk.injEq] at hsf
              obtain ⟨hnewBs, _, hnewAcc⟩ := hsf
              subst hnewBs hnewAcc
              simp only [Satisfies] at hpos
              rcases Classical.em (Satisfies m (f lbl) (Proposition.imp a1 (Proposition.atom a2n)))
                with ha | ha
              · refine ⟨[⟨.pos, Proposition.box cb, lbl⟩] ++ b,
                  List.mem_cons_of_mem _ List.mem_cons_self,
                  W, m, f, hacc, ?_⟩
                intro sf' hmem'
                simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hmem'
                rcases hmem' with rfl | hmem_old
                · exact ⟨fun _ => hpos ha, fun h => by simp at h⟩
                · exact hb sf' hmem_old
              · refine ⟨[⟨.neg, Proposition.imp a1 (Proposition.atom a2n), lbl⟩] ++ b,
                  List.mem_cons_self, W, m, f, hacc, ?_⟩
                intro sf' hmem'
                simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hmem'
                rcases hmem' with rfl | hmem_old
                · exact ⟨fun h => by simp at h, fun _ => ha⟩
                · exact hb sf' hmem_old
            | box a2b =>
              simp [tryAllPropRules, applyPropRule, modalAndOf?, modalOrOf?,
                modalImpOf?, modalNegOf?, List.map, List.find?, RuleResult.isApplicable,
                Option.some.injEq, Prod.mk.injEq] at hsf
              obtain ⟨hnewBs, _, hnewAcc⟩ := hsf
              subst hnewBs hnewAcc
              simp only [Satisfies] at hpos
              rcases Classical.em (Satisfies m (f lbl) (Proposition.imp a1 (Proposition.box a2b)))
                with ha | ha
              · refine ⟨[⟨.pos, Proposition.box cb, lbl⟩] ++ b,
                  List.mem_cons_of_mem _ List.mem_cons_self,
                  W, m, f, hacc, ?_⟩
                intro sf' hmem'
                simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hmem'
                rcases hmem' with rfl | hmem_old
                · exact ⟨fun _ => hpos ha, fun h => by simp at h⟩
                · exact hb sf' hmem_old
              · refine ⟨[⟨.neg, Proposition.imp a1 (Proposition.box a2b), lbl⟩] ++ b,
                  List.mem_cons_self, W, m, f, hacc, ?_⟩
                intro sf' hmem'
                simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hmem'
                rcases hmem' with rfl | hmem_old
                · exact ⟨fun h => by simp at h, fun _ => ha⟩
                · exact hb sf' hmem_old
            | imp b1 b2 =>
              simp [tryAllPropRules, applyPropRule, modalAndOf?, modalOrOf?,
                modalImpOf?, modalNegOf?, List.map, List.find?, RuleResult.isApplicable,
                Option.some.injEq, Prod.mk.injEq] at hsf
              obtain ⟨hnewBs, _, hnewAcc⟩ := hsf
              subst hnewBs hnewAcc
              simp only [Satisfies] at hpos
              rcases Classical.em (Satisfies m (f lbl) (Proposition.imp a1 (Proposition.imp b1 b2)))
                with ha | ha
              · refine ⟨[⟨.pos, Proposition.box cb, lbl⟩] ++ b,
                  List.mem_cons_of_mem _ List.mem_cons_self,
                  W, m, f, hacc, ?_⟩
                intro sf' hmem'
                simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hmem'
                rcases hmem' with rfl | hmem_old
                · exact ⟨fun _ => hpos ha, fun h => by simp at h⟩
                · exact hb sf' hmem_old
              · refine ⟨[⟨.neg, Proposition.imp a1 (Proposition.imp b1 b2), lbl⟩] ++ b,
                  List.mem_cons_self, W, m, f, hacc, ?_⟩
                intro sf' hmem'
                simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hmem'
                rcases hmem' with rfl | hmem_old
                · exact ⟨fun h => by simp at h, fun _ => ha⟩
                · exact hb sf' hmem_old
    | neg =>
      have hneg : ¬Satisfies m (f lbl) formula := hsf_b.2 rfl
      -- Unfold propResult for neg formulas (modalApplyOne exposes tryAllPropRules)
      simp only [modalApplyOne] at hsf
      cases formula with
      | atom p =>
        simp [tryAllPropRules, applyPropRule, modalAndOf?, modalOrOf?,
          modalImpOf?, modalNegOf?, List.map, List.find?, RuleResult.isApplicable] at hsf
      | bot =>
        -- F(⊥): no rule applies (⊥ is not a negation, not an and/or/imp for neg)
        simp [tryAllPropRules, applyPropRule, modalAndOf?, modalOrOf?,
          modalImpOf?, modalNegOf?, List.map, List.find?, RuleResult.isApplicable] at hsf
      | box φ =>
        -- F(□φ): boxNeg rule → linear [F(φ)@w', boxProps, diaNegProps], newAcc = acc.addEdge lbl w'
        -- w' = modalNextWorld b
        simp only [tryAllPropRules, applyPropRule, modalAndOf?, modalOrOf?,
          modalImpOf?, modalNegOf?, List.map, List.find?, RuleResult.isApplicable,
          Option.getD_some, Option.getD_none, Bool.false_eq_true, if_false,
          Option.some.injEq, Prod.mk.injEq] at hsf
        obtain ⟨hnewBs, _, hnewAcc⟩ := hsf
        subst hnewBs hnewAcc
        -- boxNeg: w' = modalNextWorld b is fresh
        -- hneg : ¬Satisfies m (f lbl) (□φ) = ∃ ww, m.r (f lbl) ww ∧ ¬Satisfies m ww φ
        -- (classically: ¬(∀ w', m.r (f lbl) w' → Satisfies m w' φ))
        simp only [Satisfies] at hneg
        push_neg at hneg
        obtain ⟨ww, hwwr, hwwφ⟩ := hneg
        -- Fresh world: w' = modalNextWorld b
        let w' := modalNextWorld b
        -- Extend f: map w' to ww, keep old mapping for all other worlds
        let f' : WorldIndex → W := fun n => if n = w' then ww else f n
        -- newAcc = acc.addEdge lbl w'
        let newAcc' := acc.addEdge lbl w'
        -- The new branch is (witness :: boxProps ++ diaNegProps) ++ b
        let witness : SignedFormula (Proposition Atom) WorldIndex := ⟨.neg, φ, w'⟩
        let boxProps : List (SignedFormula (Proposition Atom) WorldIndex) :=
          (boxPositivesOf b).filterMap fun (ψ, src) =>
            if src == lbl then
              let sf' : SignedFormula (Proposition Atom) WorldIndex := ⟨.pos, ψ, w'⟩
              if b.any (· == sf') then none else some sf'
            else none
        let diaNegProps : List (SignedFormula (Proposition Atom) WorldIndex) :=
          b.filterMap fun sf' =>
            if sf'.sign == .neg && sf'.label == lbl then
              match sf'.formula with
              | .imp (.box (.imp ψ .bot)) .bot =>
                let prop : SignedFormula (Proposition Atom) WorldIndex := ⟨.neg, ψ, w'⟩
                if b.any (· == prop) then none else some prop
              | _ => none
            else none
        refine ⟨(witness :: boxProps ++ diaNegProps) ++ b, List.mem_cons_self,
          W, m, f', ?_, ?_⟩
        · -- Show newAcc' = acc.addEdge lbl w' is respected by (m, f')
          intro u v hedge
          simp only [Accessibility.addEdge, Accessibility.hasEdge, List.any_cons,
            Bool.or_eq_true] at hedge
          rcases hedge with hedge | hedge
          · -- New edge: (lbl, w')
            simp only [Bool.and_eq_true, beq_iff_eq] at hedge
            obtain ⟨rfl, rfl⟩ := hedge
            -- f' lbl = f lbl (lbl < w' by freshness, so lbl ≠ w')
            -- f' w' = ww
            have hlbl_ne : lbl ≠ w' :=
              Nat.ne_of_lt (modalNextWorld_gt b ⟨.neg, .box φ, lbl⟩ hsfmem)
            rw [show f' lbl = f lbl from if_neg hlbl_ne,
              show f' w' = ww from if_pos rfl]
            exact hwwr
          · -- Old edge in acc
            -- f' u = f u if u ≠ w' and f' v = f v if v ≠ w'
            have huw' : u ≠ w' := by
              intro heq
              have hfresh := (hInv u v hedge).1
              rw [heq] at hfresh
              simp only [w'] at hfresh
              exact Nat.lt_irrefl _ hfresh
            have hvw' : v ≠ w' := by
              intro heq
              have hfresh := (hInv u v hedge).2
              rw [heq] at hfresh
              simp only [w'] at hfresh
              exact Nat.lt_irrefl _ hfresh
            simp only [f', if_neg huw', if_neg hvw']
            exact hacc u v hedge
        · -- Show (witness :: boxProps ++ diaNegProps) ++ b is satisfied by (m, f')
          intro sf' hmem'
          simp only [List.mem_append, List.mem_cons] at hmem'
          rcases hmem' with ((rfl | hmem_bp) | hmem_dn) | hmem_old
          · -- sf' = witness = ⟨.neg, φ, w'⟩
            constructor
            · intro h; simp at h
            · intro _
              -- Need ¬Satisfies m (f' w') φ = ¬Satisfies m ww φ = hwwφ
              simp only [witness, f', if_pos rfl]
              exact hwwφ
          · -- sf' ∈ boxProps: sf' = ⟨.pos, ψ, w'⟩ where T(□ψ)@lbl ∈ b
            simp only [boxProps, List.mem_filterMap] at hmem_bp
            obtain ⟨⟨ψ, src⟩, hpairMem, hsf'_from⟩ := hmem_bp
            split_ifs at hsf'_from with hsrceq hinb
            simp only [Option.some.injEq] at hsf'_from
            subst hsf'_from
            simp only [boxPositivesOf, List.mem_filterMap] at hpairMem
            obtain ⟨bsf, hbsfMem, hbsfeq⟩ := hpairMem
            split_ifs at hbsfeq with hbsfpos
            cases hbf : bsf.formula with
            | box ψ' =>
              rw [hbf] at hbsfeq
              simp only [Option.some.injEq, Prod.mk.injEq] at hbsfeq
              obtain ⟨hψ, hsrc⟩ := hbsfeq
              have hsrc_lbl : bsf.label = lbl := by rw [hsrc]; simpa using hsrceq
              have hbox_sat := (hb bsf hbsfMem).1 (by simpa using hbsfpos)
              rw [hbf, hsrc_lbl] at hbox_sat
              simp only [Satisfies] at hbox_sat
              refine ⟨fun _ => ?_, fun h => by simp at h⟩
              simp only [f', if_pos rfl]
              rw [← hψ]
              exact hbox_sat ww hwwr
            | _ => simp [hbf] at hbsfeq
          · -- sf' ∈ diaNegProps: sf' = ⟨.neg, ψ, w'⟩ where F(◇ψ)@lbl ∈ b
            simp only [diaNegProps, List.mem_filterMap] at hmem_dn
            obtain ⟨bsf, hbsfMem, hbsfprop⟩ := hmem_dn
            split_ifs at hbsfprop with hbsfsign
            cases hbf : bsf.formula with
            | imp bx bt =>
              cases hbx : bx with
              | box inner =>
                cases hin : inner with
                | imp ψ bott =>
                  cases hbott : bott with
                  | bot =>
                    cases hbt : bt with
                    | bot =>
                      simp only [hbf, hbx, hin, hbott, hbt] at hbsfprop
                      split_ifs at hbsfprop with hinb
                      simp only [Option.some.injEq] at hbsfprop
                      subst hbsfprop
                      have hsign : bsf.sign = .neg ∧ bsf.label = lbl := by
                        simp only [Bool.and_eq_true, beq_iff_eq] at hbsfsign
                        exact hbsfsign
                      have hdiaNeg := (hb bsf hbsfMem).2 hsign.1
                      rw [hbf, hbx, hin, hbott, hbt, hsign.2] at hdiaNeg
                      simp only [Satisfies] at hdiaNeg
                      refine ⟨fun h => by simp at h, fun _ => ?_⟩
                      simp only [f', if_pos rfl]
                      intro hψ
                      exact hdiaNeg (fun hall => hall ww hwwr hψ)
                    | _ => simp_all
                  | _ => simp_all
                | _ => simp_all
              | _ => simp_all
            | _ => simp_all
          · -- sf' ∈ b: use hb with f' which agrees with f on old worlds
            -- sf'.label ≠ w' because sf'.label < w' by freshness
            have hlabel_ne : sf'.label ≠ w' :=
              Nat.ne_of_lt (modalNextWorld_gt b sf' hmem_old)
            have hf'_eq : f' sf'.label = f sf'.label := by
              simp only [f', if_neg hlabel_ne]
            constructor
            · intro hsign
              rw [hf'_eq]
              exact (hb sf' hmem_old).1 hsign
            · intro hsign
              rw [hf'_eq]
              exact (hb sf' hmem_old).2 hsign
      | imp a c =>
        -- F(a → c): rule depends on structure of a and c
        cases c with
        | bot =>
          cases a with
          | atom name =>
            simp [tryAllPropRules, applyPropRule, modalAndOf?, modalOrOf?,
              modalImpOf?, modalNegOf?, List.map, List.find?, RuleResult.isApplicable,
              Option.some.injEq, Prod.mk.injEq] at hsf
            obtain ⟨hnewBs, _, hnewAcc⟩ := hsf
            subst hnewBs hnewAcc
            refine ⟨[⟨.pos, Proposition.atom name, lbl⟩] ++ b,
              List.mem_cons_self, W, m, f, hacc, ?_⟩
            intro sf' hmem'
            simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hmem'
            rcases hmem' with rfl | hmem_old
            · refine ⟨fun _ => ?_, fun h => by simp at h⟩
              by_contra hcon
              simp only [Satisfies] at hneg
              exact hneg (fun ha => absurd ha hcon)
            · exact hb sf' hmem_old
          | bot =>
            simp [tryAllPropRules, applyPropRule, modalAndOf?, modalOrOf?,
              modalImpOf?, modalNegOf?, List.map, List.find?, RuleResult.isApplicable,
              Option.some.injEq, Prod.mk.injEq] at hsf
            obtain ⟨hnewBs, _, hnewAcc⟩ := hsf
            subst hnewBs hnewAcc
            refine ⟨[⟨.pos, Proposition.bot, lbl⟩] ++ b, List.mem_cons_self, W, m, f, hacc, ?_⟩
            intro sf' hmem'
            simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hmem'
            rcases hmem' with rfl | hmem_old
            · refine ⟨fun _ => ?_, fun h => by simp at h⟩
              by_contra hcon
              simp only [Satisfies] at hneg
              exact hneg (fun ha => absurd ha hcon)
            · exact hb sf' hmem_old
          | box bb =>
            simp [tryAllPropRules, applyPropRule, modalAndOf?, modalOrOf?,
              modalImpOf?, modalNegOf?, List.map, List.find?, RuleResult.isApplicable,
              Option.some.injEq, Prod.mk.injEq] at hsf
            obtain ⟨hnewBs, _, hnewAcc⟩ := hsf
            subst hnewBs hnewAcc
            refine ⟨[⟨.pos, Proposition.box bb, lbl⟩] ++ b, List.mem_cons_self, W, m, f, hacc, ?_⟩
            intro sf' hmem'
            simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hmem'
            rcases hmem' with rfl | hmem_old
            · refine ⟨fun _ => ?_, fun h => by simp at h⟩
              by_contra hcon
              simp only [Satisfies] at hneg
              exact hneg (fun ha => absurd ha hcon)
            · exact hb sf' hmem_old
          | imp a1 a2 =>
            cases a2 with
            | bot =>
              simp [tryAllPropRules, applyPropRule, modalAndOf?, modalOrOf?,
                modalImpOf?, modalNegOf?, List.map, List.find?, RuleResult.isApplicable,
                Option.some.injEq, Prod.mk.injEq] at hsf
              obtain ⟨hnewBs, _, hnewAcc⟩ := hsf
              subst hnewBs hnewAcc
              exact ⟨_, List.mem_cons_self, negImp_alpha_preserved_neg hacc hb hneg⟩
            | atom a2n =>
              simp [tryAllPropRules, applyPropRule, modalAndOf?, modalOrOf?,
                modalImpOf?, modalNegOf?, List.map, List.find?, RuleResult.isApplicable,
                Option.some.injEq, Prod.mk.injEq] at hsf
              obtain ⟨hnewBs, _, hnewAcc⟩ := hsf
              subst hnewBs hnewAcc
              refine ⟨[⟨.pos, Proposition.imp a1 (Proposition.atom a2n), lbl⟩] ++ b,
                List.mem_cons_self, W, m, f, hacc, ?_⟩
              intro sf' hmem'
              simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hmem'
              rcases hmem' with rfl | hmem_old
              · refine ⟨fun _ => ?_, fun h => by simp at h⟩
                by_contra hcon
                simp only [Satisfies] at hneg
                exact hneg (fun ha => absurd ha hcon)
              · exact hb sf' hmem_old
            | box a2b =>
              simp [tryAllPropRules, applyPropRule, modalAndOf?, modalOrOf?,
                modalImpOf?, modalNegOf?, List.map, List.find?, RuleResult.isApplicable,
                Option.some.injEq, Prod.mk.injEq] at hsf
              obtain ⟨hnewBs, _, hnewAcc⟩ := hsf
              subst hnewBs hnewAcc
              refine ⟨[⟨.pos, Proposition.imp a1 (Proposition.box a2b), lbl⟩] ++ b,
                List.mem_cons_self, W, m, f, hacc, ?_⟩
              intro sf' hmem'
              simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hmem'
              rcases hmem' with rfl | hmem_old
              · refine ⟨fun _ => ?_, fun h => by simp at h⟩
                by_contra hcon
                simp only [Satisfies] at hneg
                exact hneg (fun ha => absurd ha hcon)
              · exact hb sf' hmem_old
            | imp b1 b2 =>
              cases b2 with
              | bot =>
                simp [tryAllPropRules, applyPropRule, modalAndOf?, modalOrOf?,
                  modalImpOf?, modalNegOf?, List.map, List.find?, RuleResult.isApplicable,
                  Option.some.injEq, Prod.mk.injEq] at hsf
                obtain ⟨hnewBs, _, hnewAcc⟩ := hsf
                subst hnewBs hnewAcc
                simp only [Satisfies] at hneg
                rcases Classical.em (Satisfies m (f lbl) (a1)) with ha1 | ha1
                · refine ⟨[⟨.neg, b1, lbl⟩] ++ b,
                    List.mem_cons_of_mem _ List.mem_cons_self, W, m, f, hacc, ?_⟩
                  intro sf' hmem'
                  simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hmem'
                  rcases hmem' with rfl | hmem_old
                  · refine ⟨fun h => by simp at h, fun _ => ?_⟩
                    intro hb1
                    exact hneg (fun g => g ha1 hb1)
                  · exact hb sf' hmem_old
                · refine ⟨[⟨.neg, a1, lbl⟩] ++ b, List.mem_cons_self, W, m, f, hacc, ?_⟩
                  intro sf' hmem'
                  simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hmem'
                  rcases hmem' with rfl | hmem_old
                  · exact ⟨fun h => by simp at h, fun _ => ha1⟩
                  · exact hb sf' hmem_old
              | atom b2n =>
                simp [tryAllPropRules, applyPropRule, modalAndOf?, modalOrOf?,
                  modalImpOf?, modalNegOf?, List.map, List.find?, RuleResult.isApplicable,
                  Option.some.injEq, Prod.mk.injEq] at hsf
                obtain ⟨hnewBs, _, hnewAcc⟩ := hsf
                subst hnewBs hnewAcc
                refine ⟨[⟨.pos,
                    Proposition.imp a1 (Proposition.imp b1 (Proposition.atom b2n)), lbl⟩] ++ b,
                  List.mem_cons_self, W, m, f, hacc, ?_⟩
                intro sf' hmem'
                simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hmem'
                rcases hmem' with rfl | hmem_old
                · refine ⟨fun _ => ?_, fun h => by simp at h⟩
                  by_contra hcon
                  simp only [Satisfies] at hneg
                  exact hneg (fun ha => absurd ha hcon)
                · exact hb sf' hmem_old
              | box b2b =>
                simp [tryAllPropRules, applyPropRule, modalAndOf?, modalOrOf?,
                  modalImpOf?, modalNegOf?, List.map, List.find?, RuleResult.isApplicable,
                  Option.some.injEq, Prod.mk.injEq] at hsf
                obtain ⟨hnewBs, _, hnewAcc⟩ := hsf
                subst hnewBs hnewAcc
                refine ⟨[⟨.pos,
                    Proposition.imp a1 (Proposition.imp b1 (Proposition.box b2b)), lbl⟩] ++ b,
                  List.mem_cons_self, W, m, f, hacc, ?_⟩
                intro sf' hmem'
                simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hmem'
                rcases hmem' with rfl | hmem_old
                · refine ⟨fun _ => ?_, fun h => by simp at h⟩
                  by_contra hcon
                  simp only [Satisfies] at hneg
                  exact hneg (fun ha => absurd ha hcon)
                · exact hb sf' hmem_old
              | imp b3 b4 =>
                simp [tryAllPropRules, applyPropRule, modalAndOf?, modalOrOf?,
                  modalImpOf?, modalNegOf?, List.map, List.find?, RuleResult.isApplicable,
                  Option.some.injEq, Prod.mk.injEq] at hsf
                obtain ⟨hnewBs, _, hnewAcc⟩ := hsf
                subst hnewBs hnewAcc
                refine ⟨[⟨.pos,
                    Proposition.imp a1 (Proposition.imp b1 (Proposition.imp b3 b4)), lbl⟩] ++ b,
                  List.mem_cons_self, W, m, f, hacc, ?_⟩
                intro sf' hmem'
                simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hmem'
                rcases hmem' with rfl | hmem_old
                · refine ⟨fun _ => ?_, fun h => by simp at h⟩
                  by_contra hcon
                  simp only [Satisfies] at hneg
                  exact hneg (fun ha => absurd ha hcon)
                · exact hb sf' hmem_old
        | atom cn =>
          cases a with
          | atom an =>
            simp [tryAllPropRules, applyPropRule, modalAndOf?, modalOrOf?,
              modalImpOf?, modalNegOf?, List.map, List.find?, RuleResult.isApplicable,
              Option.some.injEq, Prod.mk.injEq] at hsf
            obtain ⟨hnewBs, _, hnewAcc⟩ := hsf
            subst hnewBs hnewAcc
            exact ⟨_, List.mem_cons_self, negImp_alpha_preserved hacc hb hneg⟩
          | bot =>
            simp [tryAllPropRules, applyPropRule, modalAndOf?, modalOrOf?,
              modalImpOf?, modalNegOf?, List.map, List.find?, RuleResult.isApplicable,
              Option.some.injEq, Prod.mk.injEq] at hsf
            obtain ⟨hnewBs, _, hnewAcc⟩ := hsf
            subst hnewBs hnewAcc
            exact ⟨_, List.mem_cons_self, negImp_alpha_preserved hacc hb hneg⟩
          | box ab =>
            simp [tryAllPropRules, applyPropRule, modalAndOf?, modalOrOf?,
              modalImpOf?, modalNegOf?, List.map, List.find?, RuleResult.isApplicable,
              Option.some.injEq, Prod.mk.injEq] at hsf
            obtain ⟨hnewBs, _, hnewAcc⟩ := hsf
            subst hnewBs hnewAcc
            exact ⟨_, List.mem_cons_self, negImp_alpha_preserved hacc hb hneg⟩
          | imp a1 a2 =>
            cases a2 with
            | bot =>
              simp [tryAllPropRules, applyPropRule, modalAndOf?, modalOrOf?,
                modalImpOf?, modalNegOf?, List.map, List.find?, RuleResult.isApplicable,
                Option.some.injEq, Prod.mk.injEq] at hsf
              obtain ⟨hnewBs, _, hnewAcc⟩ := hsf
              subst hnewBs hnewAcc
              exact ⟨_, List.mem_cons_self, negImp_alpha_preserved_neg hacc hb hneg⟩
            | atom a2n =>
              simp [tryAllPropRules, applyPropRule, modalAndOf?, modalOrOf?,
                modalImpOf?, modalNegOf?, List.map, List.find?, RuleResult.isApplicable,
                Option.some.injEq, Prod.mk.injEq] at hsf
              obtain ⟨hnewBs, _, hnewAcc⟩ := hsf
              subst hnewBs hnewAcc
              exact ⟨_, List.mem_cons_self, negImp_alpha_preserved hacc hb hneg⟩
            | box a2b =>
              simp [tryAllPropRules, applyPropRule, modalAndOf?, modalOrOf?,
                modalImpOf?, modalNegOf?, List.map, List.find?, RuleResult.isApplicable,
                Option.some.injEq, Prod.mk.injEq] at hsf
              obtain ⟨hnewBs, _, hnewAcc⟩ := hsf
              subst hnewBs hnewAcc
              exact ⟨_, List.mem_cons_self, negImp_alpha_preserved hacc hb hneg⟩
            | imp b1 b2 =>
              simp [tryAllPropRules, applyPropRule, modalAndOf?, modalOrOf?,
                modalImpOf?, modalNegOf?, List.map, List.find?, RuleResult.isApplicable,
                Option.some.injEq, Prod.mk.injEq] at hsf
              obtain ⟨hnewBs, _, hnewAcc⟩ := hsf
              subst hnewBs hnewAcc
              exact ⟨_, List.mem_cons_self, negImp_alpha_preserved hacc hb hneg⟩
        | imp c1 c2 =>
          cases a with
          | atom an =>
            simp [tryAllPropRules, applyPropRule, modalAndOf?, modalOrOf?,
              modalImpOf?, modalNegOf?, List.map, List.find?, RuleResult.isApplicable,
              Option.some.injEq, Prod.mk.injEq] at hsf
            obtain ⟨hnewBs, _, hnewAcc⟩ := hsf
            subst hnewBs hnewAcc
            exact ⟨_, List.mem_cons_self, negImp_alpha_preserved hacc hb hneg⟩
          | bot =>
            simp [tryAllPropRules, applyPropRule, modalAndOf?, modalOrOf?,
              modalImpOf?, modalNegOf?, List.map, List.find?, RuleResult.isApplicable,
              Option.some.injEq, Prod.mk.injEq] at hsf
            obtain ⟨hnewBs, _, hnewAcc⟩ := hsf
            subst hnewBs hnewAcc
            exact ⟨_, List.mem_cons_self, negImp_alpha_preserved hacc hb hneg⟩
          | box ab =>
            simp [tryAllPropRules, applyPropRule, modalAndOf?, modalOrOf?,
              modalImpOf?, modalNegOf?, List.map, List.find?, RuleResult.isApplicable,
              Option.some.injEq, Prod.mk.injEq] at hsf
            obtain ⟨hnewBs, _, hnewAcc⟩ := hsf
            subst hnewBs hnewAcc
            exact ⟨_, List.mem_cons_self, negImp_alpha_preserved hacc hb hneg⟩
          | imp a1 a2 =>
            cases a2 with
            | bot =>
              simp [tryAllPropRules, applyPropRule, modalAndOf?, modalOrOf?,
                modalImpOf?, modalNegOf?, List.map, List.find?, RuleResult.isApplicable,
                Option.some.injEq, Prod.mk.injEq] at hsf
              obtain ⟨hnewBs, _, hnewAcc⟩ := hsf
              subst hnewBs hnewAcc
              exact ⟨_, List.mem_cons_self, negImp_alpha_preserved_neg hacc hb hneg⟩
            | atom a2n =>
              simp [tryAllPropRules, applyPropRule, modalAndOf?, modalOrOf?,
                modalImpOf?, modalNegOf?, List.map, List.find?, RuleResult.isApplicable,
                Option.some.injEq, Prod.mk.injEq] at hsf
              obtain ⟨hnewBs, _, hnewAcc⟩ := hsf
              subst hnewBs hnewAcc
              exact ⟨_, List.mem_cons_self, negImp_alpha_preserved hacc hb hneg⟩
            | box a2b =>
              simp [tryAllPropRules, applyPropRule, modalAndOf?, modalOrOf?,
                modalImpOf?, modalNegOf?, List.map, List.find?, RuleResult.isApplicable,
                Option.some.injEq, Prod.mk.injEq] at hsf
              obtain ⟨hnewBs, _, hnewAcc⟩ := hsf
              subst hnewBs hnewAcc
              exact ⟨_, List.mem_cons_self, negImp_alpha_preserved hacc hb hneg⟩
            | imp b1 b2 =>
              simp [tryAllPropRules, applyPropRule, modalAndOf?, modalOrOf?,
                modalImpOf?, modalNegOf?, List.map, List.find?, RuleResult.isApplicable,
                Option.some.injEq, Prod.mk.injEq] at hsf
              obtain ⟨hnewBs, _, hnewAcc⟩ := hsf
              subst hnewBs hnewAcc
              exact ⟨_, List.mem_cons_self, negImp_alpha_preserved hacc hb hneg⟩
        | box cb =>
          cases a with
          | atom an =>
            simp [tryAllPropRules, applyPropRule, modalAndOf?, modalOrOf?,
              modalImpOf?, modalNegOf?, List.map, List.find?, RuleResult.isApplicable,
              Option.some.injEq, Prod.mk.injEq] at hsf
            obtain ⟨hnewBs, _, hnewAcc⟩ := hsf
            subst hnewBs hnewAcc
            exact ⟨_, List.mem_cons_self, negImp_alpha_preserved hacc hb hneg⟩
          | bot =>
            simp [tryAllPropRules, applyPropRule, modalAndOf?, modalOrOf?,
              modalImpOf?, modalNegOf?, List.map, List.find?, RuleResult.isApplicable,
              Option.some.injEq, Prod.mk.injEq] at hsf
            obtain ⟨hnewBs, _, hnewAcc⟩ := hsf
            subst hnewBs hnewAcc
            exact ⟨_, List.mem_cons_self, negImp_alpha_preserved hacc hb hneg⟩
          | box ab =>
            simp [tryAllPropRules, applyPropRule, modalAndOf?, modalOrOf?,
              modalImpOf?, modalNegOf?, List.map, List.find?, RuleResult.isApplicable,
              Option.some.injEq, Prod.mk.injEq] at hsf
            obtain ⟨hnewBs, _, hnewAcc⟩ := hsf
            subst hnewBs hnewAcc
            exact ⟨_, List.mem_cons_self, negImp_alpha_preserved hacc hb hneg⟩
          | imp a1 a2 =>
            cases a2 with
            | bot =>
              simp [tryAllPropRules, applyPropRule, modalAndOf?, modalOrOf?,
                modalImpOf?, modalNegOf?, List.map, List.find?, RuleResult.isApplicable,
                Option.some.injEq, Prod.mk.injEq] at hsf
              obtain ⟨hnewBs, _, hnewAcc⟩ := hsf
              subst hnewBs hnewAcc
              exact ⟨_, List.mem_cons_self, negImp_alpha_preserved_neg hacc hb hneg⟩
            | atom a2n =>
              simp [tryAllPropRules, applyPropRule, modalAndOf?, modalOrOf?,
                modalImpOf?, modalNegOf?, List.map, List.find?, RuleResult.isApplicable,
                Option.some.injEq, Prod.mk.injEq] at hsf
              obtain ⟨hnewBs, _, hnewAcc⟩ := hsf
              subst hnewBs hnewAcc
              exact ⟨_, List.mem_cons_self, negImp_alpha_preserved hacc hb hneg⟩
            | box a2b =>
              simp [tryAllPropRules, applyPropRule, modalAndOf?, modalOrOf?,
                modalImpOf?, modalNegOf?, List.map, List.find?, RuleResult.isApplicable,
                Option.some.injEq, Prod.mk.injEq] at hsf
              obtain ⟨hnewBs, _, hnewAcc⟩ := hsf
              subst hnewBs hnewAcc
              exact ⟨_, List.mem_cons_self, negImp_alpha_preserved hacc hb hneg⟩
            | imp b1 b2 =>
              simp [tryAllPropRules, applyPropRule, modalAndOf?, modalOrOf?,
                modalImpOf?, modalNegOf?, List.map, List.find?, RuleResult.isApplicable,
                Option.some.injEq, Prod.mk.injEq] at hsf
              obtain ⟨hnewBs, _, hnewAcc⟩ := hsf
              subst hnewBs hnewAcc
              exact ⟨_, List.mem_cons_self, negImp_alpha_preserved hacc hb hneg⟩
end Cslib.Logic.Modal.Tableau

end
