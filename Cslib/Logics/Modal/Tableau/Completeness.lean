/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Modal.Tableau.Saturation

/-! # Modal K Tableau Completeness

This module proves completeness of the modal K tableau: if the tableau returns an open
branch, we can extract a finite Kripke countermodel refuting the formula.

## Main Results

- `extractModel`: Extract a Kripke model from an open branch + accessibility relation.
- `modalTruthLemma`: Truth in the extracted model tracks signed membership in the branch.
- `modalOpenBranch_countermodel`: An open branch with Hintikka property yields a countermodel.
- `modalTableau_complete`: `modalTableau φ = .openBranch b acc → ¬ kValid φ`.
- `modalTableau_decides`: `modalTableau φ = .closed ↔ kValid φ`.
- `modalHintikkaClauseGen`/`_eq`, `modalStepBranchGen_none_saturated`,
  `modalStepBranchGen_hintikka_inv`: the `Completeness.lean` half of the generic
  Hintikka/saturation chain, generalized over an abstract `apply : RuleApply Atom`. Since this
  file is strictly upstream of `GenericDriver.lean` (via `FmpMeasure.lean`), these `_gen` lemmas
  take **raw** per-field hypotheses (only F8 `localShapeInvariance`) rather than a bundled
  `spec : RuleApplicationSpec apply` argument; `GenericDriver.lean`/`CompletenessLoop.lean`
  callers supply `spec.localShapeInvariance` directly. `hintikka_box_neg_gen`/
  `hintikka_diamond_pos_gen`: free (no-field) projection bridges for the B and S4 systems.

## Strategy

Given an open saturated branch `b` with accessibility relation `acc`, define
`extractModel b acc` with relation `r w w' := acc.hasEdge w w' = true` and
valuation `v w p := T(atom p)@w ∈ b`. The modal truth lemma then shows every
`T(φ)@w ∈ b` is satisfied and every `F(φ)@w ∈ b` is falsified.

## Box Rule Design

- T(□φ)@w: handled by the `persistent` clause. `boxPropagation b acc φ w` is
  either empty (all `T(φ)@w'` already in `b`) or the persistent condition forces
  them in. Either way, all successors of `w` have `T(φ)@w'` in `b`.
- F(□φ)@w: handled by the explicit witness conjunct of `modalHintikkaSet`:
  `∃ w', acc.hasEdge w w' = true ∧ F(φ)@w' ∈ b`.

## References

* [M. Fitting, *Proof Methods for Modal and Intuitionistic Logics*][Fitting1983], Chapter 2
-/

@[expose] public section

namespace Cslib.Logic.Modal.Tableau

open Cslib.Logic.Tableau Cslib.Logic.Modal

universe v u
variable {Atom : Type v} [DecidableEq Atom] [Hashable Atom]

/-! ## Model Extraction -/

/-- Extract a Kripke model from an open saturated branch `b` and accessibility relation `acc`.

The world type is `WorldIndex` (= Nat). The relation reads from `acc`; the valuation
maps atom `p` at world `w` to `true` iff `T(atom p)@w ∈ b`. -/
def extractModel
    (b : List (SignedFormula (Proposition Atom) WorldIndex))
    (acc : Accessibility) : Model WorldIndex Atom where
  r w w' := acc.hasEdge w w' = true
  v w p  := b.any (fun sf => sf.sign == .pos && sf.formula == .atom p && sf.label == w) = true

/-! ## Basic Model Properties -/

omit [Hashable Atom] in
/-- Atom satisfaction in `extractModel b acc` at world `w` is equivalent to
`T(atom p)@w` appearing on the branch `b`. -/
lemma extractModel_atom_sat_iff
    (b : List (SignedFormula (Proposition Atom) WorldIndex))
    (acc : Accessibility) (w : WorldIndex) (p : Atom) :
    Satisfies (extractModel b acc) w (.atom p) ↔
    b.any (fun sf => sf.sign == .pos && sf.formula == .atom p && sf.label == w) = true := by
  simp only [Satisfies, extractModel]

omit [Hashable Atom] in
/-- `T(atom p)@w ∈ b` implies atom `p` is satisfied at `w` in `extractModel b acc`. -/
lemma extractModel_atomPos_sat
    (b : List (SignedFormula (Proposition Atom) WorldIndex))
    (acc : Accessibility) (w : WorldIndex) (p : Atom)
    (hmem : (⟨.pos, .atom p, w⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b) :
    Satisfies (extractModel b acc) w (.atom p) := by
  rw [extractModel_atom_sat_iff, List.any_eq_true]
  exact ⟨⟨.pos, .atom p, w⟩, hmem, by simp⟩

omit [Hashable Atom] in
/-- `⊥` is never satisfied at any world in `extractModel b acc`. -/
lemma extractModel_bot_false
    (b : List (SignedFormula (Proposition Atom) WorldIndex))
    (acc : Accessibility) (w : WorldIndex) :
    ¬ Satisfies (extractModel b acc) w .bot := by
  simp [Satisfies]

/-! ## Open-Branch Helpers -/

omit [Hashable Atom] in
/-- An open modal branch contains no `T(⊥)@w` for any world `w`. -/
lemma openBranch_noTBot
    (b : List (SignedFormula (Proposition Atom) WorldIndex))
    (hopen : isModalClosed b = false) (w : WorldIndex) :
    (⟨.pos, .bot, w⟩ : SignedFormula (Proposition Atom) WorldIndex) ∉ b := by
  intro hmem
  simp only [isModalClosed, ClosureCondition.isClosed, ClosureCondition.findClosure] at hopen
  cases hfind : b.find? (fun sf => sf.isPos && sf.formula == (HasBot.bot : Proposition Atom)) with
  | some _ => simp [hfind] at hopen
  | none =>
    have hno := List.find?_eq_none.mp hfind ⟨.pos, .bot, w⟩ hmem
    simp only [SignedFormula.isPos, Sign.isPos, Bool.true_and, beq_iff_eq] at hno
    exact hno rfl

omit [Hashable Atom] in
/-- If `T(φ)@w ∈ b` and the branch is open, then `F(φ)@w ∉ b`. -/
lemma openBranch_noContradiction
    (b : List (SignedFormula (Proposition Atom) WorldIndex))
    (hopen : isModalClosed b = false) (φ : Proposition Atom) (w : WorldIndex)
    (hpos : (⟨.pos, φ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b) :
    (⟨.neg, φ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) ∉ b := by
  intro hneg
  simp only [isModalClosed, ClosureCondition.isClosed, ClosureCondition.findClosure] at hopen
  cases hfind_bot : b.find? (fun sf => sf.isPos && sf.formula == (HasBot.bot : Proposition Atom))
    with
  | some _ => simp [hfind_bot] at hopen
  | none =>
    simp only [hfind_bot] at hopen
    cases hcontra : Branch.findContradiction b with
    | some pair => simp [hcontra] at hopen
    | none =>
      simp only [Branch.findContradiction, List.findSome?_eq_none_iff] at hcontra
      have hno := hcontra ⟨.pos, φ, w⟩ hpos
      simp only [SignedFormula.isPos, Sign.isPos, ↓reduceIte] at hno
      have hany :
          b.any (fun sf' => sf'.sign == .neg && sf'.formula == φ && sf'.label == w) = true :=
        List.any_eq_true.mpr ⟨⟨.neg, φ, w⟩, hneg, by simp⟩
      simp [hany] at hno

/-! ## Per-Rule Semantic Bridge Lemmas -/

omit [Hashable Atom] in
/-- Box-positive bridge: `T(□ψ)@w ∈ b`, `acc.hasEdge w w' = true`, `modalHintikkaSet b acc`
imply `T(ψ)@w' ∈ b`.

Proof by contradiction: if `T(ψ)@w' ∉ b`, then `T(ψ)@w' ∈ boxPropagation b acc ψ w`
(since `w' ∈ successorsOf w` and the filtering only excludes formulas already in `b`).
So `boxPropagation` is non-empty and `modalApplyOne` returns `.persistent`, whose Hintikka
condition forces `T(ψ)@w' ∈ b`, a contradiction. -/
lemma hintikka_box_pos
    (b : List (SignedFormula (Proposition Atom) WorldIndex))
    (acc : Accessibility) (hH : modalHintikkaSet b acc)
    (ψ : Proposition Atom) (w w' : WorldIndex)
    (hmem : (⟨.pos, .box ψ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b)
    (hr : acc.hasEdge w w' = true) :
    (⟨.pos, ψ, w'⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b := by
  obtain ⟨_, hrule, _⟩ := hH
  -- Apply the Hintikka rule condition to T(□ψ)@w (non-boxNeg case)
  have hcond := hrule ⟨.pos, .box ψ, w⟩ hmem
  simp only at hcond
  -- Unfold modalApplyOne for T(□ψ)@w: propositional rules return none, so boxPos fires
  simp only [modalApplyOne, tryAllPropRules, applyPropRule, modalAndOf?, modalOrOf?,
    modalImpOf?, modalNegOf?, List.map, List.find?, RuleResult.isApplicable] at hcond
  -- Reduce outer if: none.getD notApplicable = notApplicable → match gives false → if false
  simp only [Option.getD_none, Bool.false_eq_true, ↓reduceIte, List.isEmpty_iff] at hcond
  -- w' is a successor of w
  have hw'_succ : w' ∈ acc.successorsOf w := by
    simp only [Accessibility.successorsOf, List.mem_filterMap]
    simp only [Accessibility.hasEdge, List.any_eq_true] at hr
    obtain ⟨⟨src, tgt⟩, hedge_mem, hbeq⟩ := hr
    simp only [Bool.and_eq_true, beq_iff_eq] at hbeq
    exact ⟨(src, tgt), hedge_mem, by simp [hbeq.1, hbeq.2]⟩
  -- The boxPos case: if boxPropagation = [] then notApplicable else persistent
  split_ifs at hcond with hemp
  · -- hemp : boxPropagation b acc ψ w = [] → every successor already has T(ψ) in b
    simp only [boxPropagation, List.filterMap_eq_nil_iff] at hemp
    have hnil := hemp w' hw'_succ
    by_cases hinb :
        (b.any fun x => x == (⟨.pos, ψ, w'⟩ : SignedFormula (Proposition Atom) WorldIndex)) = true
    · -- T(ψ)@w' already in b
      simp only [List.any_eq_true, beq_iff_eq] at hinb
      obtain ⟨sf', hsf'mem, rfl⟩ := hinb
      exact hsf'mem
    · simp only [List.any_eq_true, beq_iff_eq, exists_eq_right, ite_eq_left_iff, reduceCtorEq,
        imp_false, Decidable.not_not] at hnil
      exact hnil
  · -- hemp : boxPropagation ≠ [] → hcond : ∀ sf' ∈ boxPropagation, sf' ∈ b
    by_cases hinb :
        (b.any fun x => x == (⟨.pos, ψ, w'⟩ : SignedFormula (Proposition Atom) WorldIndex)) = true
    · -- T(ψ)@w' already in b
      simp only [List.any_eq_true, beq_iff_eq] at hinb
      obtain ⟨sf', hsf'mem, rfl⟩ := hinb
      exact hsf'mem
    · -- T(ψ)@w' ∉ b, so T(ψ)@w' ∈ boxPropagation; apply hcond
      apply hcond
      simp only [boxPropagation, List.mem_filterMap]
      exact ⟨w', hw'_succ, if_neg hinb⟩

omit [Hashable Atom] in
/-- Box-negative bridge: `F(□ψ)@w ∈ b` implies `∃ w', acc.hasEdge w w' = true ∧ F(ψ)@w' ∈ b`.

This follows directly from the third conjunct of `modalHintikkaSet`. -/
lemma hintikka_box_neg
    (b : List (SignedFormula (Proposition Atom) WorldIndex))
    (acc : Accessibility) (hH : modalHintikkaSet b acc)
    (ψ : Proposition Atom) (w : WorldIndex)
    (hmem : (⟨.neg, .box ψ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b) :
    ∃ w', acc.hasEdge w w' = true ∧
      (⟨.neg, ψ, w'⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b :=
  hH.2.2.1 ψ w hmem

omit [Hashable Atom] in
/-- Diamond-positive bridge: `T(◇ψ)@w ∈ b` implies `∃ w', acc.hasEdge w w' = true ∧ T(ψ)@w' ∈ b`
(`diamond` is now a native, genuinely-firing constructor). This follows directly
from the fourth conjunct of `modalHintikkaSet`. -/
lemma hintikka_diamond_pos
    (b : List (SignedFormula (Proposition Atom) WorldIndex))
    (acc : Accessibility) (hH : modalHintikkaSet b acc)
    (ψ : Proposition Atom) (w : WorldIndex)
    (hmem : (⟨.pos, .diamond ψ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b) :
    ∃ w', acc.hasEdge w w' = true ∧
      (⟨.pos, ψ, w'⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b :=
  hH.2.2.2 ψ w hmem

omit [Hashable Atom] in
/-- Diamond-negative bridge: `F(◇ψ)@w ∈ b`, `acc.hasEdge w w' = true`, `modalHintikkaSet b acc`
imply `F(ψ)@w' ∈ b` (`diamondNeg` universal propagation, mirroring `hintikka_box_pos`
since `diamondNeg`'s rule shape -- persistent propagation to all recorded successors -- is
structurally identical to `boxPos`, just with sign `.neg` and no `boxPositivesOf` indirection).

Proof by contradiction: if `F(ψ)@w' ∉ b`, then `F(ψ)@w'` is one of `diamondNeg`'s
propagated formulas (since `w'` is a successor of `w` and the filtering only excludes
formulas already in `b`), so the propagation list is non-empty and `modalApplyOne` returns
`.persistent`, whose Hintikka condition forces `F(ψ)@w' ∈ b`, a contradiction. -/
lemma hintikka_diamond_neg
    (b : List (SignedFormula (Proposition Atom) WorldIndex))
    (acc : Accessibility) (hH : modalHintikkaSet b acc)
    (ψ : Proposition Atom) (w w' : WorldIndex)
    (hmem : (⟨.neg, .diamond ψ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b)
    (hr : acc.hasEdge w w' = true) :
    (⟨.neg, ψ, w'⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b := by
  obtain ⟨_, hrule, _⟩ := hH
  have hcond := hrule ⟨.neg, .diamond ψ, w⟩ hmem
  simp only [modalApplyOne, tryAllPropRules, applyPropRule, modalAndOf?, modalOrOf?,
    modalImpOf?, modalNegOf?, List.map, List.find?, RuleResult.isApplicable] at hcond
  simp only [Option.getD_none, Bool.false_eq_true, ↓reduceIte, List.any_eq_true, beq_iff_eq,
    exists_eq_right, List.isEmpty_iff, List.filterMap_eq_nil_iff, ite_eq_left_iff, reduceCtorEq,
    imp_false, Decidable.not_not] at hcond
  have hw'_succ : w' ∈ acc.successorsOf w := by
    simp only [Accessibility.successorsOf, List.mem_filterMap]
    simp only [Accessibility.hasEdge, List.any_eq_true] at hr
    obtain ⟨⟨src, tgt⟩, hedge_mem, hbeq⟩ := hr
    simp only [Bool.and_eq_true, beq_iff_eq] at hbeq
    exact ⟨(src, tgt), hedge_mem, by simp [hbeq.1, hbeq.2]⟩
  split_ifs at hcond with hemp
  · exact hemp w' hw'_succ
  · by_cases hinb : (⟨.neg, ψ, w'⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b
    · exact hinb
    · exact hcond ⟨.neg, ψ, w'⟩
        (by simp only [List.mem_filterMap]; exact ⟨w', hw'_succ, if_neg hinb⟩)

/-! ## Propositional Rule Reduction (encoding-aware)

Because `Proposition Atom` Lukasiewicz-encodes `and`/`or`/`neg` as nested `imp`, a single
`imp a c` may fire the `andPos`/`orPos`/`negPos` rule rather than the proper `impPos` rule.
The truth lemma therefore cannot use uniform implication bridge lemmas; instead it reduces
`modalApplyOne` on an `imp` to a decomposer-driven case split and recurses with strong
induction on `modalComplexity`. The lemmas below provide that reduction. -/

omit [DecidableEq Atom] [Hashable Atom] in
/-- Inversion: if `modalAndOf? φ` succeeds then `φ` is the native conjunction. -/
lemma modalAndOf?_eq {φ x y : Proposition Atom} (h : modalAndOf? φ = some (x, y)) :
    φ = .and x y := by
  unfold modalAndOf? at h; split at h <;> simp_all

omit [DecidableEq Atom] [Hashable Atom] in
/-- Inversion: if `modalOrOf? φ` succeeds then `φ` is the native disjunction. -/
lemma modalOrOf?_eq {φ x y : Proposition Atom} (h : modalOrOf? φ = some (x, y)) :
    φ = .or x y := by
  unfold modalOrOf? at h; split at h <;> simp_all

omit [DecidableEq Atom] [Hashable Atom] in
/-- Inversion: if `modalImpOf? φ` succeeds then `φ` is the proper implication `x → y`. -/
lemma modalImpOf?_eq {φ x y : Proposition Atom} (h : modalImpOf? φ = some (x, y)) :
    φ = .imp x y := by
  unfold modalImpOf? at h
  split at h
  · next a b =>
    split at h
    · simp at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h; rfl
  · simp at h

omit [DecidableEq Atom] [Hashable Atom] in
/-- Inversion: if `modalNegOf? φ` succeeds then `φ` is the encoded negation `x → ⊥`. -/
lemma modalNegOf?_eq {φ x : Proposition Atom} (h : modalNegOf? φ = some x) :
    φ = .imp x .bot := by
  unfold modalNegOf? at h; split at h <;> simp_all

-- `tryAllPropRules_pos`/`_neg` relocated to `Rules.lean`: they are entirely generic
-- (no `Atom`-specific content) and needed upstream by `Rules.lean`'s Propagating-class shape
-- lemmas. Reached here transitively (`Completeness → Saturation → Rules`).

omit [Hashable Atom] in
/-- When the propositional rules apply, `modalApplyOne` returns the propositional result. -/
lemma modalApplyOne_eq_prop_of_applicable
    (sf : SignedFormula (Proposition Atom) WorldIndex)
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (h : (tryAllPropRules modalAndOf? modalOrOf? modalImpOf? modalNegOf? sf).isApplicable = true) :
    (modalApplyOne sf b acc).1
      = tryAllPropRules modalAndOf? modalOrOf? modalImpOf? modalNegOf? sf := by
  simp only [modalApplyOne]
  rw [if_pos h]

omit [Hashable Atom] in
/-- Reduction of `modalApplyOne` on a positive implication to a decomposer case split.

`and`/`or` are native constructors disjoint from `.imp`, so `modalAndOf?`/
`modalOrOf?` always return `none` on an `.imp`-shaped formula; the statement is simplified
to the `impPos`/`negPos` split only. -/
lemma modalApplyOne_imp_pos (a c : Proposition Atom) (w : WorldIndex)
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility) :
    (modalApplyOne ⟨.pos, .imp a c, w⟩ b acc).1 =
      match modalImpOf? (.imp a c) with
      | some (x, y) => .branching [[⟨.neg, x, w⟩], [⟨.pos, y, w⟩]]
      | none =>
        match modalNegOf? (.imp a c) with
        | some x => .linear [⟨.neg, x, w⟩]
        | none => .notApplicable := by
  have happ : (tryAllPropRules modalAndOf? modalOrOf? modalImpOf? modalNegOf?
      (⟨.pos, .imp a c, w⟩ : SignedFormula (Proposition Atom) WorldIndex)).isApplicable = true := by
    rw [tryAllPropRules_pos]
    simp only [modalAndOf?, modalOrOf?]
    rcases hI : modalImpOf? (.imp a c) with _ | ⟨x, y⟩
    · rcases hN : modalNegOf? (.imp a c) with _ | x
      · exfalso
        rcases c with _|_|_|_|_|_|_ <;> simp_all [modalImpOf?, modalNegOf?]
      · simp [RuleResult.isApplicable]
    · simp [RuleResult.isApplicable]
  rw [modalApplyOne_eq_prop_of_applicable ⟨.pos, .imp a c, w⟩ b acc happ, tryAllPropRules_pos]
  simp only [modalAndOf?, modalOrOf?]
  rcases modalImpOf? (.imp a c) with _ | ⟨x, y⟩ <;>
    rcases modalNegOf? (.imp a c) with _ | x <;> rfl

omit [Hashable Atom] in
/-- Reduction of `modalApplyOne` on a negative implication to a decomposer case split.

See `modalApplyOne_imp_pos` for why `modalAndOf?`/`modalOrOf?` are always `none`
on an `.imp`-shaped formula. -/
lemma modalApplyOne_imp_neg (a c : Proposition Atom) (w : WorldIndex)
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility) :
    (modalApplyOne ⟨.neg, .imp a c, w⟩ b acc).1 =
      match modalImpOf? (.imp a c) with
      | some (x, y) => .linear [⟨.pos, x, w⟩, ⟨.neg, y, w⟩]
      | none =>
        match modalNegOf? (.imp a c) with
        | some x => .linear [⟨.pos, x, w⟩]
        | none => .notApplicable := by
  have happ : (tryAllPropRules modalAndOf? modalOrOf? modalImpOf? modalNegOf?
      (⟨.neg, .imp a c, w⟩ : SignedFormula (Proposition Atom) WorldIndex)).isApplicable = true := by
    rw [tryAllPropRules_neg]
    simp only [modalAndOf?, modalOrOf?]
    rcases hI : modalImpOf? (.imp a c) with _ | ⟨x, y⟩
    · rcases hN : modalNegOf? (.imp a c) with _ | x
      · exfalso
        rcases c with _|_|_|_|_|_|_ <;> simp_all [modalImpOf?, modalNegOf?]
      · simp [RuleResult.isApplicable]
    · simp [RuleResult.isApplicable]
  rw [modalApplyOne_eq_prop_of_applicable ⟨.neg, .imp a c, w⟩ b acc happ, tryAllPropRules_neg]
  simp only [modalAndOf?, modalOrOf?]
  rcases modalImpOf? (.imp a c) with _ | ⟨x, y⟩ <;>
    rcases modalNegOf? (.imp a c) with _ | x <;> rfl

omit [Hashable Atom] in
/-- Reduction of `modalApplyOne` on a positive conjunction: `andPos` fires directly since
`modalAndOf?` matches the native `.and` constructor first in `tryAllPropRules`'s priority
order (no encoding disambiguation needed). -/
lemma modalApplyOne_and_pos (φ ψ : Proposition Atom) (w : WorldIndex)
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility) :
    (modalApplyOne ⟨.pos, .and φ ψ, w⟩ b acc).1 = .linear [⟨.pos, φ, w⟩, ⟨.pos, ψ, w⟩] := by
  have happ : (tryAllPropRules modalAndOf? modalOrOf? modalImpOf? modalNegOf?
      (⟨.pos, .and φ ψ, w⟩ : SignedFormula (Proposition Atom) WorldIndex)).isApplicable = true := by
    simp [tryAllPropRules_pos, modalAndOf?, RuleResult.isApplicable]
  rw [modalApplyOne_eq_prop_of_applicable ⟨.pos, .and φ ψ, w⟩ b acc happ, tryAllPropRules_pos]
  simp [modalAndOf?]

omit [Hashable Atom] in
/-- Reduction of `modalApplyOne` on a negative conjunction (`andNeg`, branching). -/
lemma modalApplyOne_and_neg (φ ψ : Proposition Atom) (w : WorldIndex)
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility) :
    (modalApplyOne ⟨.neg, .and φ ψ, w⟩ b acc).1 =
      .branching [[⟨.neg, φ, w⟩], [⟨.neg, ψ, w⟩]] := by
  have happ : (tryAllPropRules modalAndOf? modalOrOf? modalImpOf? modalNegOf?
      (⟨.neg, .and φ ψ, w⟩ : SignedFormula (Proposition Atom) WorldIndex)).isApplicable = true := by
    simp [tryAllPropRules_neg, modalAndOf?, RuleResult.isApplicable]
  rw [modalApplyOne_eq_prop_of_applicable ⟨.neg, .and φ ψ, w⟩ b acc happ, tryAllPropRules_neg]
  simp [modalAndOf?]

omit [Hashable Atom] in
/-- Reduction of `modalApplyOne` on a positive disjunction (`orPos`, branching). -/
lemma modalApplyOne_or_pos (φ ψ : Proposition Atom) (w : WorldIndex)
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility) :
    (modalApplyOne ⟨.pos, .or φ ψ, w⟩ b acc).1 =
      .branching [[⟨.pos, φ, w⟩], [⟨.pos, ψ, w⟩]] := by
  have happ : (tryAllPropRules modalAndOf? modalOrOf? modalImpOf? modalNegOf?
      (⟨.pos, .or φ ψ, w⟩ : SignedFormula (Proposition Atom) WorldIndex)).isApplicable = true := by
    simp [tryAllPropRules_pos, modalAndOf?, modalOrOf?, RuleResult.isApplicable]
  rw [modalApplyOne_eq_prop_of_applicable ⟨.pos, .or φ ψ, w⟩ b acc happ, tryAllPropRules_pos]
  simp [modalAndOf?, modalOrOf?]

omit [Hashable Atom] in
/-- Reduction of `modalApplyOne` on a negative disjunction (`orNeg`, linear). -/
lemma modalApplyOne_or_neg (φ ψ : Proposition Atom) (w : WorldIndex)
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility) :
    (modalApplyOne ⟨.neg, .or φ ψ, w⟩ b acc).1 =
      .linear [⟨.neg, φ, w⟩, ⟨.neg, ψ, w⟩] := by
  have happ : (tryAllPropRules modalAndOf? modalOrOf? modalImpOf? modalNegOf?
      (⟨.neg, .or φ ψ, w⟩ : SignedFormula (Proposition Atom) WorldIndex)).isApplicable = true := by
    simp [tryAllPropRules_neg, modalAndOf?, modalOrOf?, RuleResult.isApplicable]
  rw [modalApplyOne_eq_prop_of_applicable ⟨.neg, .or φ ψ, w⟩ b acc happ, tryAllPropRules_neg]
  simp [modalAndOf?, modalOrOf?]

/-! ## Modal Truth Lemma -/

omit [Hashable Atom] in
/-- Modal Truth Lemma: membership in a Hintikka branch tracks satisfaction in the
extracted Kripke model `extractModel b acc`.

For every formula `φ` and world `w`, `T(φ)@w ∈ b` implies `φ` is satisfied at `w`
in `extractModel b acc`, and `F(φ)@w ∈ b` implies it is not.

Proof by strong induction on `modalComplexity φ`. The atom case uses
`extractModel_atomPos_sat`/`openBranch_noContradiction`; the bot case uses
`openBranch_noTBot`/`extractModel_bot_false`; the box case uses the bridge lemmas
`hintikka_box_pos`/`hintikka_box_neg`.

The `imp` case must inspect the Lukasiewicz encoding: `modalApplyOne` fires the
`and`/`or`/`neg` rule when the implication is an encoded connective. We reduce
`modalApplyOne` via `modalApplyOne_imp_pos`/`modalApplyOne_imp_neg` to a decomposer
case split, then recurse on the genuine sub-formulas (which are strictly smaller in
`modalComplexity`, hence reachable by the strong-induction hypothesis). Uniform
implication bridge lemmas are impossible here precisely because `T((φ→(ψ→⊥))→⊥)` fires
the conjunction rule, not the implication rule. -/
lemma modalTruthLemma
    (b : List (SignedFormula (Proposition Atom) WorldIndex))
    (acc : Accessibility) (hH : modalHintikkaSet b acc) :
    ∀ (φ : Proposition Atom) (w : WorldIndex),
      (⟨.pos, φ, w⟩ ∈ b → Satisfies (extractModel b acc) w φ) ∧
      (⟨.neg, φ, w⟩ ∈ b → ¬ Satisfies (extractModel b acc) w φ) := by
  suffices H : ∀ (n : Nat) (φ : Proposition Atom), modalComplexity φ = n → ∀ w,
      (⟨.pos, φ, w⟩ ∈ b → Satisfies (extractModel b acc) w φ) ∧
      (⟨.neg, φ, w⟩ ∈ b → ¬ Satisfies (extractModel b acc) w φ) by
    intro φ w; exact H (modalComplexity φ) φ rfl w
  intro n
  induction n using Nat.strongRecOn with
  | ind n IHn =>
    intro φ hφ w
    have IH : ∀ (ψ : Proposition Atom), modalComplexity ψ < n → ∀ w',
        (⟨.pos, ψ, w'⟩ ∈ b → Satisfies (extractModel b acc) w' ψ) ∧
        (⟨.neg, ψ, w'⟩ ∈ b → ¬ Satisfies (extractModel b acc) w' ψ) :=
      fun ψ hlt w' => IHn (modalComplexity ψ) hlt ψ rfl w'
    cases φ with
    | atom p =>
      refine ⟨extractModel_atomPos_sat b acc w p, ?_⟩
      intro hmem hsat
      simp only [Satisfies, extractModel, List.any_eq_true] at hsat
      obtain ⟨sf, hsf_mem, hcond⟩ := hsat
      simp only [Bool.and_eq_true] at hcond
      obtain ⟨⟨hsign, hform⟩, hlab⟩ := hcond
      have hsign_eq : sf.sign = .pos := eq_of_beq hsign
      have hform_eq : sf.formula = .atom p := eq_of_beq hform
      have hlab_eq : sf.label = w := eq_of_beq hlab
      have hpos : (⟨.pos, .atom p, w⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b := by
        convert hsf_mem using 1; rcases sf with ⟨s, f, l⟩; simp_all
      exact openBranch_noContradiction b hH.1 (.atom p) w hpos hmem
    | bot =>
      refine ⟨fun hmem => absurd hmem (openBranch_noTBot b hH.1 w), ?_⟩
      intro _; exact extractModel_bot_false b acc w
    | imp a c =>
      -- `and`/`or` are native constructors disjoint from `.imp`, so the only
      -- disambiguation needed is `c = ⊥` (negation) vs `c ≠ ⊥` (proper implication) --
      -- no encoding-priority cascade through andOf?/orOf? is needed any more.
      rcases eq_or_ne c Proposition.bot with rfl | hne
      · constructor
        · -- negPos: T(a → ⊥)@w ∈ b → ¬Satisfies w a
          intro hmem
          have hcond := hH.2.1 ⟨.pos, .imp a .bot, w⟩ hmem
          simp only [modalApplyOne_imp_pos, modalImpOf?_neg, modalNegOf?_neg] at hcond
          have hxmem : (⟨.neg, a, w⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b :=
            hcond ⟨.neg, a, w⟩ (by simp)
          intro hsa
          exact (IH a (by rw [← hφ]; simp only [modalComplexity_imp, modalComplexity_bot]; omega)
            w).2 hxmem hsa
        · -- negNeg: F(a → ⊥)@w ∈ b → Satisfies w a
          intro hmem
          have hcond := hH.2.1 ⟨.neg, .imp a .bot, w⟩ hmem
          simp only [modalApplyOne_imp_neg, modalImpOf?_neg, modalNegOf?_neg] at hcond
          have hxmem : (⟨.pos, a, w⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b :=
            hcond ⟨.pos, a, w⟩ (by simp)
          intro hna
          have hlt : modalComplexity a < n := by
            rw [← hφ]; simp only [modalComplexity_imp, modalComplexity_bot]; omega
          exact hna ((IH a hlt w).1 hxmem)
      · constructor
        · -- impPos: T(a → c)@w (c ≠ ⊥) ∈ b → Satisfies w a → Satisfies w c
          intro hmem
          have hcond := hH.2.1 ⟨.pos, .imp a c, w⟩ hmem
          simp only [modalApplyOne_imp_pos, modalImpOf?_imp hne] at hcond
          intro hsa
          obtain ⟨br, hbr_mem, hbr⟩ := hcond
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hbr_mem
          rcases hbr_mem with rfl | rfl
          · exact absurd hsa ((IH a (by rw [← hφ]; simp only [modalComplexity_imp]; omega) w).2
              (hbr ⟨.neg, a, w⟩ (by simp)))
          · exact (IH c (by rw [← hφ]; simp only [modalComplexity_imp]; omega) w).1
              (hbr ⟨.pos, c, w⟩ (by simp))
        · -- impNeg: F(a → c)@w (c ≠ ⊥) ∈ b → Satisfies w a ∧ ¬Satisfies w c
          intro hmem
          have hcond := hH.2.1 ⟨.neg, .imp a c, w⟩ hmem
          simp only [modalApplyOne_imp_neg, modalImpOf?_imp hne] at hcond
          have hxmem : (⟨.pos, a, w⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b :=
            hcond ⟨.pos, a, w⟩ (by simp)
          have hymem : (⟨.neg, c, w⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b :=
            hcond ⟨.neg, c, w⟩ (by simp)
          intro hsa
          exact (IH c (by rw [← hφ]; simp only [modalComplexity_imp]; omega) w).2 hymem
            (hsa ((IH a (by rw [← hφ]; simp only [modalComplexity_imp]; omega) w).1 hxmem))
    | and φ' ψ' =>
      -- andPos/andNeg: native conjunction, no encoding-priority cascade needed.
      constructor
      · intro hmem
        have hcond := hH.2.1 ⟨.pos, .and φ' ψ', w⟩ hmem
        simp only [modalApplyOne_and_pos] at hcond
        exact ⟨(IH φ' (by rw [← hφ]; simp only [modalComplexity_and]; omega) w).1
            (hcond ⟨.pos, φ', w⟩ (by simp)),
          (IH ψ' (by rw [← hφ]; simp only [modalComplexity_and]; omega) w).1
            (hcond ⟨.pos, ψ', w⟩ (by simp))⟩
      · intro hmem
        have hcond := hH.2.1 ⟨.neg, .and φ' ψ', w⟩ hmem
        simp only [modalApplyOne_and_neg] at hcond
        obtain ⟨br, hbr_mem, hbr⟩ := hcond
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hbr_mem
        rintro ⟨hsφ, hsψ⟩
        rcases hbr_mem with rfl | rfl
        · exact absurd hsφ ((IH φ' (by rw [← hφ]; simp only [modalComplexity_and]; omega) w).2
            (hbr ⟨.neg, φ', w⟩ (by simp)))
        · exact absurd hsψ ((IH ψ' (by rw [← hφ]; simp only [modalComplexity_and]; omega) w).2
            (hbr ⟨.neg, ψ', w⟩ (by simp)))
    | or φ' ψ' =>
      -- orPos/orNeg: native disjunction, no encoding-priority cascade needed.
      constructor
      · intro hmem
        have hcond := hH.2.1 ⟨.pos, .or φ' ψ', w⟩ hmem
        simp only [modalApplyOne_or_pos] at hcond
        obtain ⟨br, hbr_mem, hbr⟩ := hcond
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hbr_mem
        rcases hbr_mem with rfl | rfl
        · exact Or.inl ((IH φ' (by rw [← hφ]; simp only [modalComplexity_or]; omega) w).1
            (hbr ⟨.pos, φ', w⟩ (by simp)))
        · exact Or.inr ((IH ψ' (by rw [← hφ]; simp only [modalComplexity_or]; omega) w).1
            (hbr ⟨.pos, ψ', w⟩ (by simp)))
      · intro hmem
        have hcond := hH.2.1 ⟨.neg, .or φ' ψ', w⟩ hmem
        simp only [modalApplyOne_or_neg] at hcond
        intro hs
        cases hs with
        | inl hsφ => exact absurd hsφ ((IH φ' (by rw [← hφ]; simp only [modalComplexity_or]; omega)
            w).2 (hcond ⟨.neg, φ', w⟩ (by simp)))
        | inr hsψ => exact absurd hsψ ((IH ψ' (by rw [← hφ]; simp only [modalComplexity_or]; omega)
            w).2 (hcond ⟨.neg, ψ', w⟩ (by simp)))
    | box ψ =>
      constructor
      · intro hmem w' hr
        exact (IH ψ (by rw [← hφ]; simp only [modalComplexity_box]; omega) w').1
          (hintikka_box_pos b acc hH ψ w w' hmem hr)
      · intro hmem hall
        obtain ⟨w', hw', hF⟩ := hintikka_box_neg b acc hH ψ w hmem
        exact (IH ψ (by rw [← hφ]; simp only [modalComplexity_box]; omega) w').2 hF (hall w' hw')
    | diamond ψ =>
      -- `diamond` is now a native, genuinely-firing constructor (see the historical
      -- note in the `## Saturation Characterisation` section below); bridged via
      -- `hintikka_diamond_pos`/the `diamondNeg` universal-propagation rule.
      constructor
      · intro hmem
        obtain ⟨w', hw', hT⟩ := hintikka_diamond_pos b acc hH ψ w hmem
        exact ⟨w', hw', (IH ψ (by rw [← hφ]; simp only [modalComplexity_diamond]; omega) w').1 hT⟩
      · intro hmem
        rintro ⟨w', hw', hsψ⟩
        exact (IH ψ (by rw [← hφ]; simp only [modalComplexity_diamond]; omega) w').2
          (hintikka_diamond_neg b acc hH ψ w w' hmem hw') hsψ

/-! ## Open-Branch Countermodel -/

omit [Hashable Atom] in
/-- An open Hintikka branch with `F(φ)@0 ∈ b` yields a Kripke countermodel to `φ`.

The extracted model `extractModel b acc` falsifies `φ` at world `0`. -/
theorem modalOpenBranch_countermodel
    (b : List (SignedFormula (Proposition Atom) WorldIndex))
    (acc : Accessibility) (φ : Proposition Atom)
    (hH : modalHintikkaSet b acc)
    (hF : (⟨.neg, φ, 0⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b) :
    ¬ Satisfies (extractModel b acc) 0 φ :=
  (modalTruthLemma b acc hH φ 0).2 hF

/-! ## Saturation Characterisation

Two single-step lemmas about `modalStepBranch`, ported from the classical propositional
tableau's `classicalStepBranch_none_saturated` / `classicalStepBranch_hintikka_inv`
(`Classical/Completeness.lean:694,722`), feeding the top-loop lemma
`modalExpandBranches_hintikka` (`CompletenessLoop.lean`).

`modalStepBranch_hintikka_inv` is stated against `(modalApplyOne sf b acc).1`, carving out
`.box _`-shaped formulas (both signs): `boxNeg` (`.neg, .box _`) mints a branch-fresh world
`modalNextWorld b`, so re-evaluating it at a strictly larger branch always yields a witness
that (by freshness) cannot lie on that branch — exactly why `modalHintikkaSet`'s own second
conjunct carves it out. `boxPos` (`.pos, .box _`) reads `boxPropagation b acc`, so it is
also branch/`acc`-dependent, but it is `.persistent` and never enters the expanded set `e`
(`Saturation.lean:116-117`; matches the `.persistent` case below, where `e` is left
unchanged), so the carve-out costs nothing in the lemma's actual use. Every other formula
shape (`.atom _`, `.bot`, `.imp _ _`) reaches `modalApplyOne`'s rule dispatch in a way that
is provably independent of the branch/`acc` (`modalApplyOne_fst_eq_of_not_box` below):
propositional rules are formula-structural, and `.atom`/`.bot` never match a modal rule.
In particular, the Lukasiewicz-encoded diamond patterns
(`.pos`/`.neg, .imp (.box (.imp _ .bot)) .bot`) are always intercepted by the propositional
negation decoder `modalNegOf?` first (it unconditionally matches `.imp a .bot`), so the
branch/`acc`-dependent `diamondPos`/`diamondNeg` arms of `modalApplyOne`'s modal-rule match
(`Rules.lean:91,142`) are dead code in practice — never actually reached. -/

/-- The box-excluded rule-application clause: for a signed formula `⟨s, φ, w⟩`, either `φ` is
`box`-shaped (vacuously `True` — handled elsewhere, see the section note above), or the
`modalApplyOne` rule output for `⟨s, φ, w⟩` evaluated at `(X, Y)` is already present on `X`.
Factored into a named `def` (rather than an inline `match` repeated at each use site) so that
Lean's equation compiler produces one shared matcher, avoiding spurious dependent-match
mismatches when the same clause is used as both a hypothesis and a goal across lemmas. -/
def modalHintikkaClause (s : Sign) (φ : Proposition Atom) (w : WorldIndex)
    (X : List (SignedFormula (Proposition Atom) WorldIndex)) (Y : Accessibility) : Prop :=
  match φ with
  | .box _ => True
  | .diamond _ => True  -- diamondPos also mints a fresh world; see the section note
  | _ =>
    match (modalApplyOne ⟨s, φ, w⟩ X Y).1 with
    | .linear out => ∀ sf' ∈ out, sf' ∈ X
    | .branching brs => ∃ br ∈ brs, ∀ sf' ∈ br, sf' ∈ X
    | .persistent out => ∀ sf' ∈ out, sf' ∈ X
    | .notApplicable => True

/-- **Generic box-excluded rule-application clause**: `modalHintikkaClause`,
generalized over an abstract `apply : RuleApply Atom`. One-token substitution
(`modalApplyOne ↦ apply`). Note this carve-out is deliberately **coarser** than
`modalHintikkaSetGen`'s conjunct 2: vacuous for *any* box/diamond-shaped `φ` (both signs),
whereas the set's conjunct 2 carves out only `.neg, .box` / `.pos, .diamond`. That gap is
exactly what `RuleApplicationSpec`'s F9/F10 fields exist to close (`GenericDriver.lean`); the
coarseness here is forced because the clause must lift along branch growth
(`modalHintikkaClauseGen_lift`), and both Propagating shapes are `b`/`acc`-dependent, so they
cannot be lifted. `modalHintikkaClause` is retained unchanged (its `unfold`/`simp only` call
sites rely on its exact normal form); see `modalHintikkaClause_eq` for the bridge. -/
def modalHintikkaClauseGen (apply : RuleApply Atom) (s : Sign) (φ : Proposition Atom)
    (w : WorldIndex) (X : List (SignedFormula (Proposition Atom) WorldIndex))
    (Y : Accessibility) : Prop :=
  match φ with
  | .box _ => True
  | .diamond _ => True
  | _ =>
    match (apply ⟨s, φ, w⟩ X Y).1 with
    | .linear out => ∀ sf' ∈ out, sf' ∈ X
    | .branching brs => ∃ br ∈ brs, ∀ sf' ∈ br, sf' ∈ X
    | .persistent out => ∀ sf' ∈ out, sf' ∈ X
    | .notApplicable => True

/-- Bridge: `modalHintikkaClause` is exactly `modalHintikkaClauseGen modalApplyOne`.
Closes by `rfl`. -/
theorem modalHintikkaClause_eq (s : Sign) (φ : Proposition Atom) (w : WorldIndex)
    (X : List (SignedFormula (Proposition Atom) WorldIndex)) (Y : Accessibility) :
    modalHintikkaClause s φ w X Y = modalHintikkaClauseGen modalApplyOne s φ w X Y := rfl

omit [Hashable Atom] in
/-- For a non-`box`/`diamond`-shaped signed formula, `modalApplyOne`'s rule result does not
depend on the branch or accessibility relation. Propositional rules are formula-structural
(`modalApplyOne_imp_pos`/`_neg`, `modalApplyOne_and_pos`/`_neg`, `modalApplyOne_or_pos`/`_neg`,
themselves independent of `b`/`acc`), and `.atom`/`.bot` formulas never match a propositional
rule nor a modal rule, so `modalApplyOne` returns the constant `.notApplicable` for them
regardless of `b`/`acc`. `diamond` is excluded alongside `box` since `diamondPos`
now genuinely mints a fresh world (`modalNextWorld b`), depending on `b`.

De-privatized: this is the K discharge for `RuleApplicationSpec`'s F8
`localShapeInvariance` field (`GenericDriver.lean`), which needs to reach this lemma from
downstream via `modalApplyOne_spec`. -/
theorem modalApplyOne_fst_eq_of_not_box
    (s : Sign) (φ : Proposition Atom) (w : WorldIndex)
    (hnb : ∀ ψ, φ ≠ .box ψ) (hnd : ∀ ψ, φ ≠ .diamond ψ)
    (b b' : List (SignedFormula (Proposition Atom) WorldIndex))
    (acc acc' : Accessibility) :
    (modalApplyOne ⟨s, φ, w⟩ b acc).1 = (modalApplyOne ⟨s, φ, w⟩ b' acc').1 := by
  cases φ with
  | atom p =>
    cases s <;> simp [modalApplyOne, tryAllPropRules_pos, tryAllPropRules_neg, modalAndOf?,
      modalOrOf?, modalImpOf?, modalNegOf?, RuleResult.isApplicable]
  | bot =>
    cases s <;> simp [modalApplyOne, tryAllPropRules_pos, tryAllPropRules_neg, modalAndOf?,
      modalOrOf?, modalImpOf?, modalNegOf?, RuleResult.isApplicable]
  | imp a c =>
    cases s with
    | pos => rw [modalApplyOne_imp_pos, modalApplyOne_imp_pos]
    | neg => rw [modalApplyOne_imp_neg, modalApplyOne_imp_neg]
  | and x y =>
    cases s with
    | pos => rw [modalApplyOne_and_pos, modalApplyOne_and_pos]
    | neg => rw [modalApplyOne_and_neg, modalApplyOne_and_neg]
  | or x y =>
    cases s with
    | pos => rw [modalApplyOne_or_pos, modalApplyOne_or_pos]
    | neg => rw [modalApplyOne_or_neg, modalApplyOne_or_neg]
  | box ψ => exact absurd rfl (hnb ψ)
  | diamond ψ => exact absurd rfl (hnd ψ)

/-- **Generic lifting lemma**: `modalHintikkaClauseGen_lift`, taking a raw
`hLocalShapeInvariance` hypothesis (`RuleApplicationSpec`'s F8 field, `GenericDriver.lean`) in
place of the K-specific `modalApplyOne_fst_eq_of_not_box`. Kept as a raw hypothesis rather than a
bundled `spec` argument: `RuleApplicationSpec` is defined in `GenericDriver.lean`, which imports
`FmpMeasure.lean`, which (transitively) imports this file -- so `Completeness.lean` must stay
upstream and take F8 raw. `GenericDriver.lean` supplies the bundled wrapper. Body is
`modalHintikkaClause_lift`'s exact proof with `modalApplyOne ↦ apply` and
`modalApplyOne_fst_eq_of_not_box ↦ hLocalShapeInvariance`. -/
private lemma modalHintikkaClauseGen_lift
    (apply : RuleApply Atom)
    (hLocalShapeInvariance : ∀ (s : Sign) (φ : Proposition Atom) (w : WorldIndex),
      (∀ ψ, φ ≠ .box ψ) → (∀ ψ, φ ≠ .diamond ψ) →
      ∀ (b b' : List (SignedFormula (Proposition Atom) WorldIndex))
        (acc acc' : Accessibility),
      (apply ⟨s, φ, w⟩ b acc).1 = (apply ⟨s, φ, w⟩ b' acc').1)
    (s : Sign) (φ : Proposition Atom) (w : WorldIndex)
    (b b' : List (SignedFormula (Proposition Atom) WorldIndex))
    (acc acc' : Accessibility) (hsub : b ⊆ b')
    (hInv : modalHintikkaClauseGen apply s φ w b acc) :
    modalHintikkaClauseGen apply s φ w b' acc' := by
  unfold modalHintikkaClauseGen at hInv ⊢
  rcases φ with p | _ | ⟨a, c⟩ | ⟨x, y⟩ | ⟨x, y⟩ | ψ | ψ
  · have heq := hLocalShapeInvariance s (.atom p) w (by intro _ h; simp at h)
        (by intro _ h; simp at h) b b' acc acc'
    simp only [heq] at hInv
    rcases hres : (apply (⟨s, .atom p, w⟩ :
        SignedFormula (Proposition Atom) WorldIndex) b' acc').1 with out | brs | out | _ <;>
      simp only [hres] at hInv ⊢
    · exact fun sf' h => hsub (hInv sf' h)
    · obtain ⟨br, hbr, hbr'⟩ := hInv
      exact ⟨br, hbr, fun sf' h => hsub (hbr' sf' h)⟩
    · exact fun sf' h => hsub (hInv sf' h)
  · have heq := hLocalShapeInvariance s .bot w (by intro _ h; simp at h)
        (by intro _ h; simp at h) b b' acc acc'
    simp only [heq] at hInv
    rcases hres : (apply (⟨s, .bot, w⟩ :
        SignedFormula (Proposition Atom) WorldIndex) b' acc').1 with out | brs | out | _ <;>
      simp only [hres] at hInv ⊢
    · exact fun sf' h => hsub (hInv sf' h)
    · obtain ⟨br, hbr, hbr'⟩ := hInv
      exact ⟨br, hbr, fun sf' h => hsub (hbr' sf' h)⟩
    · exact fun sf' h => hsub (hInv sf' h)
  · have heq := hLocalShapeInvariance s (.imp a c) w (by intro _ h; simp at h)
        (by intro _ h; simp at h) b b' acc acc'
    simp only [heq] at hInv
    rcases hres : (apply (⟨s, .imp a c, w⟩ :
        SignedFormula (Proposition Atom) WorldIndex) b' acc').1 with out | brs | out | _ <;>
      simp only [hres] at hInv ⊢
    · exact fun sf' h => hsub (hInv sf' h)
    · obtain ⟨br, hbr, hbr'⟩ := hInv
      exact ⟨br, hbr, fun sf' h => hsub (hbr' sf' h)⟩
    · exact fun sf' h => hsub (hInv sf' h)
  · have heq := hLocalShapeInvariance s (.and x y) w (by intro _ h; simp at h)
        (by intro _ h; simp at h) b b' acc acc'
    simp only [heq] at hInv
    rcases hres : (apply (⟨s, .and x y, w⟩ :
        SignedFormula (Proposition Atom) WorldIndex) b' acc').1 with out | brs | out | _ <;>
      simp only [hres] at hInv ⊢
    · exact fun sf' h => hsub (hInv sf' h)
    · obtain ⟨br, hbr, hbr'⟩ := hInv
      exact ⟨br, hbr, fun sf' h => hsub (hbr' sf' h)⟩
    · exact fun sf' h => hsub (hInv sf' h)
  · have heq := hLocalShapeInvariance s (.or x y) w (by intro _ h; simp at h)
        (by intro _ h; simp at h) b b' acc acc'
    simp only [heq] at hInv
    rcases hres : (apply (⟨s, .or x y, w⟩ :
        SignedFormula (Proposition Atom) WorldIndex) b' acc').1 with out | brs | out | _ <;>
      simp only [hres] at hInv ⊢
    · exact fun sf' h => hsub (hInv sf' h)
    · obtain ⟨br, hbr, hbr'⟩ := hInv
      exact ⟨br, hbr, fun sf' h => hsub (hbr' sf' h)⟩
    · exact fun sf' h => hsub (hInv sf' h)
  · trivial
  · trivial

/-- Lifting lemma for the box-excluded rule-application clause: if it holds for `⟨s, φ, w⟩`
against branch `b`/`acc`, it holds against any superset branch `b'` with any `acc'` (for
non-`box` `φ`; `box`-shaped `φ` is vacuous on both sides). Used by
`modalStepBranch_hintikka_inv` to lift the invariant for `sf ∈ e` from the old branch to the
new one, since `modalApplyOne`'s output for non-`box` formulas does not depend on `b`/`acc`
(`modalApplyOne_fst_eq_of_not_box`), so growing the branch only grows the witness set.

Byte-identical-statement corollary of `modalHintikkaClauseGen_lift` via
`modalHintikkaClause_eq`. -/
private lemma modalHintikkaClause_lift
    (s : Sign) (φ : Proposition Atom) (w : WorldIndex)
    (b b' : List (SignedFormula (Proposition Atom) WorldIndex))
    (acc acc' : Accessibility) (hsub : b ⊆ b')
    (hInv : modalHintikkaClause s φ w b acc) :
    modalHintikkaClause s φ w b' acc' := by
  simp only [modalHintikkaClause_eq] at hInv ⊢
  exact modalHintikkaClauseGen_lift modalApplyOne modalApplyOne_fst_eq_of_not_box s φ w b b'
    acc acc' hsub hInv

/-- **Generic saturated-leaf characterisation**: `modalStepBranchGen_none_saturated`,
generalized over an abstract `apply`. Takes **no** field -- verified rule-agnostic: the proof
only ever `rcases` on the four `RuleResult` constructor shapes, touching `apply` opaquely.
Body is `modalStepBranch_none_saturated`'s exact proof with `modalApplyOne ↦ apply` and
`modalStepBranch ↦ modalStepBranchGen apply`. -/
lemma modalStepBranchGen_none_saturated
    (apply : RuleApply Atom)
    {b e : List (SignedFormula (Proposition Atom) WorldIndex)}
    {acc : Accessibility}
    (hstep : modalStepBranchGen apply b e acc = none)
    (sf : SignedFormula (Proposition Atom) WorldIndex) (hsfb : sf ∈ b) :
    sf ∈ e ∨ (apply sf b acc).1 = .notApplicable := by
  simp only [modalStepBranchGen] at hstep
  rw [List.findSome?_eq_none_iff] at hstep
  have hbody := hstep sf hsfb
  by_cases hany : e.any (· == sf) = true
  · left
    simp only [List.any_eq_true] at hany
    obtain ⟨sf', hme, heq⟩ := hany
    simp only [beq_iff_eq] at heq
    exact heq ▸ hme
  · right
    simp only [Bool.not_eq_true] at hany
    simp only [hany] at hbody
    rcases hca : apply sf b acc with ⟨res, newAcc⟩
    simp only [hca] at hbody
    rcases res with out | brs | out | _
    · exact absurd hbody (by simp)
    · exact absurd hbody (by simp)
    · exact absurd hbody (by simp)
    · rfl

/-- When `modalStepBranch b e acc = none`, every formula on `b` is either already in the
expanded set `e` or has `modalApplyOne` (evaluated at `b`, `acc`) return `notApplicable`
(the branch is saturated). Port of `classicalStepBranch_none_saturated`
(`Classical/Completeness.lean:694`), threaded with `acc`.

Byte-identical-statement corollary of `modalStepBranchGen_none_saturated` via
`modalStepBranch_eq`. -/
lemma modalStepBranch_none_saturated
    {b e : List (SignedFormula (Proposition Atom) WorldIndex)}
    {acc : Accessibility}
    (hstep : modalStepBranch b e acc = none)
    (sf : SignedFormula (Proposition Atom) WorldIndex) (hsfb : sf ∈ b) :
    sf ∈ e ∨ (modalApplyOne sf b acc).1 = .notApplicable :=
  modalStepBranchGen_none_saturated modalApplyOne (modalStepBranch_eq b e acc ▸ hstep) sf hsfb

/-- **Generic Hintikka-invariant single-step preservation**: raw F8
(`hLocalShapeInvariance`) is its only field input; the rest is driver case-split. Body is
`modalStepBranch_hintikka_inv`'s exact proof with `modalApplyOne ↦ apply`,
`modalStepBranch ↦ modalStepBranchGen apply`, and `modalHintikkaClause ↦
modalHintikkaClauseGen apply` (via `modalHintikkaClauseGen_lift`, fed `hLocalShapeInvariance`
directly in place of `modalApplyOne_fst_eq_of_not_box`). Public (not `private`, unlike its
`_lift` helper): the composition crux in `CompletenessLoop.lean` calls this directly with
`spec.localShapeInvariance`. -/
lemma modalStepBranchGen_hintikka_inv
    (apply : RuleApply Atom)
    (hLocalShapeInvariance : ∀ (s : Sign) (φ : Proposition Atom) (w : WorldIndex),
      (∀ ψ, φ ≠ .box ψ) → (∀ ψ, φ ≠ .diamond ψ) →
      ∀ (b b' : List (SignedFormula (Proposition Atom) WorldIndex))
        (acc acc' : Accessibility),
      (apply ⟨s, φ, w⟩ b acc).1 = (apply ⟨s, φ, w⟩ b' acc').1)
    (b e : List (SignedFormula (Proposition Atom) WorldIndex))
    (acc : Accessibility)
    (newBs newExps : List (List (SignedFormula (Proposition Atom) WorldIndex)))
    (newAcc : Accessibility)
    (hstep : modalStepBranchGen apply b e acc = some (newBs, newExps, newAcc))
    (hInv_b : ∀ sf ∈ e, modalHintikkaClauseGen apply sf.sign sf.formula sf.label b acc) :
    ∀ p ∈ newBs.zip newExps, ∀ sf ∈ p.2,
      modalHintikkaClauseGen apply sf.sign sf.formula sf.label p.1 newAcc := by
  simp only [modalStepBranchGen] at hstep
  obtain ⟨sf_exp, _, hfound⟩ := List.exists_of_findSome?_eq_some hstep
  split_ifs at hfound with hexp
  rcases hca : apply sf_exp b acc with ⟨res, acc'⟩
  obtain ⟨s_exp, φ_exp, w_exp⟩ := sf_exp
  simp only [hca] at hfound
  rcases res with newForms | brs | newForms | _
  · -- linear: newBs = [newForms ++ b], newExps = [e ++ [sf_exp]], newAcc = acc'
    obtain ⟨rfl, rfl, rfl⟩ := hfound
    intro p hp sf hsfin
    obtain ⟨hp1, hp2⟩ := List.of_mem_zip hp
    simp only [List.mem_singleton] at hp1 hp2
    obtain ⟨s, φ, w⟩ := sf
    rw [hp2, List.mem_append, List.mem_singleton] at hsfin
    rw [hp1]
    rcases hsfin with hsfin | heq
    · exact modalHintikkaClauseGen_lift apply hLocalShapeInvariance s φ w b (newForms ++ b)
        acc newAcc (fun _ hx => List.mem_append.mpr (Or.inr hx)) (hInv_b ⟨s, φ, w⟩ hsfin)
    · obtain ⟨rfl, rfl, rfl⟩ := heq
      unfold modalHintikkaClauseGen
      rcases φ_exp with p' | _ | ⟨a, c⟩ | ⟨x, y⟩ | ⟨x, y⟩ | ψ | ψ
      · have heq2 := hLocalShapeInvariance s_exp (.atom p') w_exp
          (by intro _ h; simp at h) (by intro _ h; simp at h) b (newForms ++ b) acc newAcc
        have hres := heq2.symm.trans (congrArg Prod.fst hca)
        simp only [hres]
        exact fun sf' hsf' => List.mem_append.mpr (Or.inl hsf')
      · have heq2 := hLocalShapeInvariance s_exp .bot w_exp
          (by intro _ h; simp at h) (by intro _ h; simp at h) b (newForms ++ b) acc newAcc
        have hres := heq2.symm.trans (congrArg Prod.fst hca)
        simp only [hres]
        exact fun sf' hsf' => List.mem_append.mpr (Or.inl hsf')
      · have heq2 := hLocalShapeInvariance s_exp (.imp a c) w_exp
          (by intro _ h; simp at h) (by intro _ h; simp at h) b (newForms ++ b) acc newAcc
        have hres := heq2.symm.trans (congrArg Prod.fst hca)
        simp only [hres]
        exact fun sf' hsf' => List.mem_append.mpr (Or.inl hsf')
      · have heq2 := hLocalShapeInvariance s_exp (.and x y) w_exp
          (by intro _ h; simp at h) (by intro _ h; simp at h) b (newForms ++ b) acc newAcc
        have hres := heq2.symm.trans (congrArg Prod.fst hca)
        simp only [hres]
        exact fun sf' hsf' => List.mem_append.mpr (Or.inl hsf')
      · have heq2 := hLocalShapeInvariance s_exp (.or x y) w_exp
          (by intro _ h; simp at h) (by intro _ h; simp at h) b (newForms ++ b) acc newAcc
        have hres := heq2.symm.trans (congrArg Prod.fst hca)
        simp only [hres]
        exact fun sf' hsf' => List.mem_append.mpr (Or.inl hsf')
      · trivial
      · trivial
  · -- branching: newBs = brs.map (·++b), newExps = brs.map (fun _ => e++[sf_exp]), newAcc = acc'
    obtain ⟨rfl, rfl, rfl⟩ := hfound
    intro p hp sf hsfin
    obtain ⟨hp1, hp2⟩ := List.of_mem_zip hp
    rw [List.mem_map] at hp1 hp2
    obtain ⟨x, hx, hx1⟩ := hp1
    obtain ⟨x', hx', hx2⟩ := hp2
    obtain ⟨s, φ, w⟩ := sf
    rw [← hx2, List.mem_append, List.mem_singleton] at hsfin
    rw [← hx1]
    rcases hsfin with hsfin | heq
    · exact modalHintikkaClauseGen_lift apply hLocalShapeInvariance s φ w b (x ++ b) acc newAcc
        (fun _ hx'' => List.mem_append.mpr (Or.inr hx'')) (hInv_b ⟨s, φ, w⟩ hsfin)
    · obtain ⟨rfl, rfl, rfl⟩ := heq
      unfold modalHintikkaClauseGen
      rcases φ_exp with p' | _ | ⟨a, c⟩ | ⟨x2, y2⟩ | ⟨x2, y2⟩ | ψ | ψ
      · have heq2 := hLocalShapeInvariance s_exp (.atom p') w_exp
          (by intro _ h; simp at h) (by intro _ h; simp at h) b (x ++ b) acc newAcc
        have hres := heq2.symm.trans (congrArg Prod.fst hca)
        simp only [hres]
        exact ⟨x, hx, fun sf' hsf' => List.mem_append.mpr (Or.inl hsf')⟩
      · have heq2 := hLocalShapeInvariance s_exp .bot w_exp
          (by intro _ h; simp at h) (by intro _ h; simp at h) b (x ++ b) acc newAcc
        have hres := heq2.symm.trans (congrArg Prod.fst hca)
        simp only [hres]
        exact ⟨x, hx, fun sf' hsf' => List.mem_append.mpr (Or.inl hsf')⟩
      · have heq2 := hLocalShapeInvariance s_exp (.imp a c) w_exp
          (by intro _ h; simp at h) (by intro _ h; simp at h) b (x ++ b) acc newAcc
        have hres := heq2.symm.trans (congrArg Prod.fst hca)
        simp only [hres]
        exact ⟨x, hx, fun sf' hsf' => List.mem_append.mpr (Or.inl hsf')⟩
      · have heq2 := hLocalShapeInvariance s_exp (.and x2 y2) w_exp
          (by intro _ h; simp at h) (by intro _ h; simp at h) b (x ++ b) acc newAcc
        have hres := heq2.symm.trans (congrArg Prod.fst hca)
        simp only [hres]
        exact ⟨x, hx, fun sf' hsf' => List.mem_append.mpr (Or.inl hsf')⟩
      · have heq2 := hLocalShapeInvariance s_exp (.or x2 y2) w_exp
          (by intro _ h; simp at h) (by intro _ h; simp at h) b (x ++ b) acc newAcc
        have hres := heq2.symm.trans (congrArg Prod.fst hca)
        simp only [hres]
        exact ⟨x, hx, fun sf' hsf' => List.mem_append.mpr (Or.inl hsf')⟩
      · trivial
      · trivial
  · -- persistent: newBs = [newForms ++ b], newExps = [e] (unchanged), newAcc = acc'
    obtain ⟨rfl, rfl, rfl⟩ := hfound
    intro p hp sf hsfin
    obtain ⟨hp1, hp2⟩ := List.of_mem_zip hp
    simp only [List.mem_singleton] at hp1 hp2
    obtain ⟨s, φ, w⟩ := sf
    rw [hp1]
    exact modalHintikkaClauseGen_lift apply hLocalShapeInvariance s φ w b (newForms ++ b) acc
      newAcc (fun _ hx => List.mem_append.mpr (Or.inr hx)) (hInv_b ⟨s, φ, w⟩ (hp2 ▸ hsfin))
  · simp at hfound

/-- If the rule-application invariant holds for branch `b` against expanded set `e` (every
non-`box`-shaped formula in `e` has its `modalApplyOne` output already present on `b`), then
after one step `modalStepBranch b e acc = some (newBs, newExps, newAcc)`, the invariant
holds for every new branch `b'` paired with its own new expanded set from `newExps`.

Port of `classicalStepBranch_hintikka_inv` (`Classical/Completeness.lean:722`). Two
modal-specific adjustments: (1) the invariant is evaluated via `(modalApplyOne sf b acc).1`
and carves out `.box _`-shaped formulas (see the section note above); (2) the `.persistent`
case leaves the expanded set unchanged (`newExp = e`, not `e ++ [sf_exp]`), since `boxPos`
re-fires when new successors are added and is never marked expanded
(`Saturation.lean:116-117`) — so unlike the classical port's `.persistent` case (identical
to `.linear`), here there is no `sf = sf_exp` sub-case to discharge at all.

Byte-identical-statement corollary of `modalStepBranchGen_hintikka_inv` via
`modalStepBranch_eq`/`modalHintikkaClause_eq`. -/
lemma modalStepBranch_hintikka_inv
    (b e : List (SignedFormula (Proposition Atom) WorldIndex))
    (acc : Accessibility)
    (newBs newExps : List (List (SignedFormula (Proposition Atom) WorldIndex)))
    (newAcc : Accessibility)
    (hstep : modalStepBranch b e acc = some (newBs, newExps, newAcc))
    (hInv_b : ∀ sf ∈ e, modalHintikkaClause sf.sign sf.formula sf.label b acc) :
    ∀ p ∈ newBs.zip newExps, ∀ sf ∈ p.2,
      modalHintikkaClause sf.sign sf.formula sf.label p.1 newAcc := by
  simp only [modalHintikkaClause_eq] at hInv_b ⊢
  exact modalStepBranchGen_hintikka_inv modalApplyOne modalApplyOne_fst_eq_of_not_box b e acc
    newBs newExps newAcc (modalStepBranch_eq b e acc ▸ hstep) hInv_b

/-- **Free projection bridge, generic**: box-negative bridge for `modalHintikkaSetGen`
-- pure projection of conjunct 3, mentions no `apply`, costs nothing (~6 lines). Delivered for
the B and S4 systems alongside `hintikka_diamond_pos_gen`. -/
lemma hintikka_box_neg_gen
    (apply : RuleApply Atom)
    (b : List (SignedFormula (Proposition Atom) WorldIndex))
    (acc : Accessibility) (hH : modalHintikkaSetGen apply b acc)
    (ψ : Proposition Atom) (w : WorldIndex)
    (hmem : (⟨.neg, .box ψ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b) :
    ∃ w', acc.hasEdge w w' = true ∧
      (⟨.neg, ψ, w'⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b :=
  hH.2.2.1 ψ w hmem

/-- **Free projection bridge, generic**: diamond-positive bridge for
`modalHintikkaSetGen` -- pure projection of conjunct 4, mentions no `apply`. -/
lemma hintikka_diamond_pos_gen
    (apply : RuleApply Atom)
    (b : List (SignedFormula (Proposition Atom) WorldIndex))
    (acc : Accessibility) (hH : modalHintikkaSetGen apply b acc)
    (ψ : Proposition Atom) (w : WorldIndex)
    (hmem : (⟨.pos, .diamond ψ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b) :
    ∃ w', acc.hasEdge w w' = true ∧
      (⟨.pos, ψ, w'⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b :=
  hH.2.2.2 ψ w hmem

end Cslib.Logic.Modal.Tableau

end
