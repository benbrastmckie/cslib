/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

import Cslib.Init
public import Cslib.Logics.Temporal.Tableau.Soundness

/-! # Temporal Tableau Completeness

This module provides the completeness side of the temporal tableau decision
procedure: an open saturated branch yields a countermodel.

## Main Results (Proved)

- `extractModel`: Constructs a `TemporalModel Nat Atom` from a branch; atoms are
  satisfied iff T(atom p)@t appears on the branch.
- `extractModel_atom_sat_iff`: Atom satisfaction in `extractModel b` is determined
  by the presence of T(atom p)@t on the branch.
- `extractModel_bot_false`: ⊥ is never satisfied in any extracted model.
- `openBranch_noBotPos`: An open branch has no T(⊥) on it.
- `openBranch_noContradiction`: An open branch has no simultaneous T(φ)@t and F(φ)@t.
- `extractModel_atom_neg_notSat`: F(atom p)@t on an open branch implies
  ¬ Satisfies (extractModel b) t (.atom p). Proved using `List.findSome?_isSome_iff`
  to witness a contradiction pair, contradicting `openBranch_noContradiction`.

## Blocked Obligations

The following results cannot be proved in the current scope.

### Blocked (Design Issue — ordConstraints_strict Misstated)

The previously listed obligation `ordConstraints_strict` is **not** merely proof-complex:
the lemma as stated is FALSE. The `addPast t tNew` function adds `(tNew, t)` to the
constraint store, where `tNew = branchNextTime b > t`. So `(tNew, t) ∈ constraints`
but `tNew > t`, violating `∀ (a, b) ∈ constraints, a < b`.

This means the `openBranch_branchSat` approach using `D = Nat` and `f = id` cannot
work for branches with past-formula constraints. A topological-sort extraction or a
different domain is needed. See the blocked section below for details.

### Blocked (Proof Complexity — No Theoretical Blocker)

1. `temporalTruthLemma_propositional` (propositional cases): The truth lemma
   for `imp`/`neg`/`and`/`or` cases requires detailed case analysis of
   `tryAllPropRules` output in `temporalApplyOne`, reproducing the classical
   truth lemma proof but with time-indexed `temporalHintikkaSet`.
   (Note: `extractModel_atom_neg_notSat` is now proved and available.)

### Blocked (FMP Required — Theoretical Blocker)

2. `temporalTruthLemma_untl`: Until eventuality fulfilment case. Proving
   T(U(guard,event))@t ∈ b → ∃ s > t, event holds at s ∧ guard holds between,
   in the extracted model requires either FMP for PTL or an explicit loop-
   unwinding argument showing the time-subset blocking structure yields a model
   where all pending eventualities are periodically re-satisfied.

3. `temporalTruthLemma_snce`: Since eventuality fulfilment case. Symmetric
   to (2) in the past direction.

4. `openBranch_branchSat`, `temporalTableau_complete`, `instDecidableValid`:
   All blocked by the ordConstraints design issue + (2) + (3).

## Decomposition Recommendation

The most tractable path to closing these obligations:
1. Fix `ordConstraints_strict` design issue: either use a topological sort to build
   a valid time assignment `f`, or separate the past/future constraint handling.
2. For propositional truth lemma: adapt `Propositional/Tableau/Classical/Completeness.lean`.
3. For Until/Since completeness: either import PTL FMP once proved, or construct
   an explicit finite unwinding of the time-subset-blocked tableau graph.

## References

* [R. Reynolds, *An axiomatization of prior's tense logic*][Reynolds1994]
* [R. Smullyan, *First-Order Logic*][Smullyan1968] (propositional truth lemma pattern)
* Propositional Classical Completeness.lean (proof template)
-/

@[expose] public section

namespace Cslib.Logic.Temporal.Tableau

open Cslib.Logic.Tableau Cslib.Logic.Temporal

variable {Atom : Type*} [DecidableEq Atom] [Hashable Atom]

/-! ## Countermodel Extraction -/

/-- Extract a `TemporalModel Nat Atom` from an open branch.

The time domain is `Nat` (already a linear order). The valuation maps atom `p`
at time `t` to `true` iff T(atom p)@t appears on the branch.

When the branch is open and saturated (a Hintikka set), every formula on
the branch should be satisfied in this model. Proving this in full (the temporal
truth lemma) requires additional theory for the Until/Since cases; see the
module docstring. -/
def extractModel (b : TBranch Atom) : TemporalModel Nat Atom where
  valuation t p := b.any fun sf =>
    sf.sign == .pos && sf.label == t && sf.formula == .atom p

/-! ## Basic Model Properties -/

omit [Hashable Atom] in
/-- Atom satisfaction in `extractModel b` is equivalent to T(atom p)@t being on the branch. -/
lemma extractModel_atom_sat_iff (b : TBranch Atom) (t : TimeIndex) (p : Atom) :
    Satisfies (extractModel b) t (.atom p) ↔
    b.any (fun sf => sf.sign == .pos && sf.label == t && sf.formula == .atom p) := by
  simp only [Satisfies.atom_iff, extractModel]

omit [Hashable Atom] in
/-- T(atom p)@t on a branch implies atom p is satisfied in the extracted model at t. -/
lemma extractModel_atomPos_sat (b : TBranch Atom) (t : TimeIndex) (p : Atom)
    (hmem : (⟨.pos, .atom p, t⟩ : TSF Atom) ∈ b) :
    Satisfies (extractModel b) t (.atom p) := by
  rw [extractModel_atom_sat_iff, List.any_eq_true]
  exact ⟨⟨.pos, .atom p, t⟩, hmem, by simp⟩

omit [Hashable Atom] in
/-- ⊥ is never satisfied in any extracted model, at any time. -/
lemma extractModel_bot_false (b : TBranch Atom) (t : TimeIndex) :
    ¬ Satisfies (extractModel b) t .bot :=
  Satisfies.bot_false (extractModel b) t

/-! ## Open Branch Structure -/

omit [Hashable Atom] in
/-- An open temporal branch contains no T(⊥) signed formula. -/
lemma openBranch_noBotPos
    (b : TBranch Atom)
    (ord : TimeOrdering)
    (tracker : EventualityTracker Atom)
    (hopen : isTemporalClosed b ord tracker = false) :
    ¬ ∃ t, (⟨.pos, .bot, t⟩ : TSF Atom) ∈ b := by
  intro ⟨t, hmem⟩
  -- Build the isSome witness for b.find?
  have hfind : (b.find? fun sf => sf.isPos && sf.formula == (⊥ : Formula Atom)).isSome = true := by
    rw [List.find?_isSome]
    refine ⟨⟨.pos, .bot, t⟩, hmem, ?_⟩
    simp only [SignedFormula.isPos, Sign.isPos, Bool.true_and]
    exact beq_self_eq_true _
  -- The find? returning some makes findClassicalClosure return some
  cases hbotfind : b.find? (fun sf => sf.isPos && sf.formula == (⊥ : Formula Atom)) with
  | some sf =>
    -- findClassicalClosure b = some (.botPos sf.label)
    have hfclas : findClassicalClosure b = some (.botPos sf.label) := by
      simp [findClassicalClosure, hbotfind]
    -- isTemporalClosed = true
    have hclosed : isTemporalClosed b ord tracker = true := by
      simp [isTemporalClosed, findTemporalClosure, hfclas]
    simp [hclosed] at hopen
  | none => simp [hbotfind] at hfind

omit [Hashable Atom] in
/-- An open temporal branch has no complementary T(φ)/F(φ) pair at the same time label. -/
lemma openBranch_noContradiction
    (b : TBranch Atom)
    (ord : TimeOrdering)
    (tracker : EventualityTracker Atom)
    (hopen : isTemporalClosed b ord tracker = false) :
    Branch.findContradiction b = none := by
  -- Work through the findClassicalClosure / findTemporalClosure chain
  -- Step 1: findClassicalClosure must return none (otherwise isTemporalClosed = true)
  have hfclas_none : findClassicalClosure b = none := by
    cases hfclas : findClassicalClosure b with
    | some r =>
      have hclosed : isTemporalClosed b ord tracker = true := by
        simp [isTemporalClosed, findTemporalClosure, hfclas]
      simp [hclosed] at hopen
    | none => rfl
  -- Step 2: from findClassicalClosure = none, extract Branch.findContradiction = none
  simp only [findClassicalClosure] at hfclas_none
  cases hbotfind : b.find? (fun sf => sf.isPos && sf.formula == (⊥ : Formula Atom)) with
  | some sf => simp [hbotfind] at hfclas_none
  | none =>
    simp only [hbotfind] at hfclas_none
    cases hcontra : Branch.findContradiction b with
    | some pair => simp [hcontra] at hfclas_none
    | none => rfl

omit [Hashable Atom] in
/-- F(atom p)@t on an open branch implies ¬ Satisfies (extractModel b) t (atom p).

If T(atom p)@t were also on the branch, `Branch.findContradiction` would return `some`,
contradicting `openBranch_noContradiction`. We witness the contradiction via
`List.findSome?_isSome_iff` using the positive signed formula as the search element. -/
lemma extractModel_atom_neg_notSat
    (b : TBranch Atom) (ord : TimeOrdering) (tracker : EventualityTracker Atom)
    (hopen : isTemporalClosed b ord tracker = false)
    (t : TimeIndex) (p : Atom)
    (hmem : (⟨.neg, .atom p, t⟩ : TSF Atom) ∈ b) :
    ¬ Satisfies (extractModel b) t (.atom p) := by
  rw [extractModel_atom_sat_iff]
  intro h_any
  -- Extract a positive witness T(atom p)@t from the branch
  rw [List.any_eq_true] at h_any
  obtain ⟨sf_pos, hmem_pos, hcond⟩ := h_any
  simp only [Bool.and_eq_true] at hcond
  obtain ⟨⟨hpos_sign, hpos_lab⟩, hpos_form⟩ := hcond
  have hsign : sf_pos.sign = .pos := LawfulBEq.eq_of_beq hpos_sign
  have hlab : sf_pos.label = t := LawfulBEq.eq_of_beq hpos_lab
  have hform : sf_pos.formula = .atom p := LawfulBEq.eq_of_beq hpos_form
  -- An open branch has no T/F contradiction pair
  have hcontra_none : Branch.findContradiction b = none :=
    openBranch_noContradiction b ord tracker hopen
  -- But sf_pos and hmem together witness a T/F pair at (atom p, t)
  -- → Branch.findContradiction b ≠ none
  have hcontra_some : (Branch.findContradiction b).isSome = true := by
    simp only [Branch.findContradiction, List.findSome?_isSome_iff]
    refine ⟨sf_pos, hmem_pos, ?_⟩
    -- Show (predicate sf_pos).isSome = true
    have hisPos : sf_pos.isPos = true := by
      simp [SignedFormula.isPos, Sign.isPos, hsign]
    -- The inner any: F(atom p)@t witnesses the negative match
    have hinner : b.any (fun sf' =>
        sf'.sign == .neg && sf'.formula == sf_pos.formula && sf'.label == sf_pos.label) = true := by
      rw [List.any_eq_true]
      exact ⟨⟨.neg, .atom p, t⟩, hmem, by simp [hform, hlab]⟩
    simp [hisPos, hinner]
  simp [hcontra_none] at hcontra_some

/-! ## Propositional Fragment -/

/-- The propositional fragment of `Formula Atom`: formulas built from atoms, ⊥, and →.
Does not include temporal operators (until, since). Since `and`, `or`, and `neg` are
Łukasiewicz-encoded as `imp`/`bot`, this predicate covers the full classical propositional
fragment automatically. -/
inductive IsPropositional : Formula Atom → Prop where
  /-- Atomic propositions are propositional. -/
  | atom (p : Atom) : IsPropositional (.atom p)
  /-- Falsum is propositional. -/
  | bot : IsPropositional .bot
  /-- Implication of propositional formulas is propositional. -/
  | imp {φ ψ : Formula Atom} (hφ : IsPropositional φ) (hψ : IsPropositional ψ) :
      IsPropositional (.imp φ ψ)

omit [Hashable Atom] [DecidableEq Atom] in
/-- Every formula has complexity at least 1. Used as the base-case vacuity
in strong-induction proofs: `n = 0` implies no formula has `complexity ≤ 0`. -/
private lemma Formula.one_le_complexity (φ : Formula Atom) : 1 ≤ φ.complexity := by
  unfold Formula.complexity
  split <;> omega

/-! ## Remaining Blocked Obligations (BLOCKED)

The following section documents proof obligations that remain blocked.
These are stated as structured goal declarations in comments.
None use `sorry` or new axioms.

### Blocked: Ord Constraints Are Strict (DESIGN ISSUE — Lemma False as Stated)

**Status**: This lemma as stated is FALSE due to a design issue in the time-ordering scheme.

**The problem**: `addPast t tNew` adds the constraint `(tNew, t)` to `ord.constraints`,
meaning "tNew is before t" semantically. But `tNew = branchNextTime b`, which by
`branchNextTime_gt` satisfies `sf.label < tNew` for all `sf ∈ b`, so `tNew > t` in Nat.

Therefore `(tNew, t) ∈ ord.constraints` with `tNew > t`, violating the claimed
`∀ t t', (t, t') ∈ ord.constraints → t < t'`.

**Design note**: The `TimeOrdering` uses Nat labels as identifiers, not as time values.
The constraint store defines the semantic ordering. When extracting a model with `f = id`,
the model only works for branches with only `addFuture` constraints. For branches with
`addPast` (from `snce` / past-existential rules), a different extraction is needed.

**Consequence**: `openBranch_branchSat` with `D = Nat` and `f = id` cannot be proved
in general. The completeness proof requires either:
1. Restricting to formulas without `snce` (future-only temporal logic), OR
2. A topological-sort-based extraction that maps labels to a consistent linear order, OR
3. Constructing `branchSat` directly without the constraint-preserving requirement.

```lean
-- BLOCKED (design issue): ordConstraints_strict is false for branches using addPast.
-- The addPast rule adds (tNew, t) where tNew = branchNextTime b > t.
-- This makes (tNew, t) ∈ constraints but tNew > t, violating the claimed invariant.
--
-- lemma ordConstraints_strict (φ : Formula Atom) (b : TBranch Atom) (ord : TimeOrdering)
--     (hresult : temporalTableau φ = .openBranch b ord) :
--     ∀ t t', (t, t') ∈ ord.constraints → t < t' := ...
```

### Blocked: Propositional Truth Lemma (Proof Complexity)

```lean
-- BLOCKED (proof complexity): ~300 lines of case analysis per connective.
--
-- lemma temporalTruthLemma_propositional
--     (b : TBranch Atom) (ord : TimeOrdering) (tracker : EventualityTracker Atom)
--     (hH : temporalHintikkaSet b ord tracker)
--     (φ : Formula Atom) (t : TimeIndex) :
--     (b.any (fun sf => sf.sign == .pos && sf.label == t && sf.formula == φ) →
--       Satisfies (extractModel b) t φ) ∧
--     (b.any (fun sf => sf.sign == .neg && sf.label == t && sf.formula == φ) →
--       ¬ Satisfies (extractModel b) t φ) := by
--   induction φ with
--   | atom p => exact ⟨(extractModel_atom_sat_iff b t p).mpr,
--                      fun h => extractModel_atom_neg_notSat b ord tracker hH.1 t p ...⟩
--   | bot =>
--     exact ⟨fun h => absurd ... (openBranch_noBotPos ...),
--            fun _ => extractModel_bot_false ...⟩
--   | imp φ ψ ih_φ ih_ψ =>
--     -- Case analysis on temporalApplyOne sf b ord for each T/F(imp φ ψ)
--     -- which calls tryAllPropRules first, then temporal rules.
--     -- Propositional imp case: either neg, or, and, or proper imp rule.
--     sorry -- BLOCKED
--   | untl guard event ih_g ih_e =>
--     exact ⟨fun h => temporalTruthLemma_untl b ord tracker hH guard event t h,
--            fun h => ...⟩  -- BLOCKED (FMP required)
--   | snce guard event ih_g ih_e =>
--     exact ⟨fun h => temporalTruthLemma_snce b ord tracker hH guard event t h,
--            fun h => ...⟩  -- BLOCKED (FMP required)
```

### Blocked: Until Eventuality Fulfilment (FMP Required)

```lean
-- BLOCKED (FMP required): requires PTL Finite Model Property.
--
-- lemma temporalTruthLemma_untl
--     (b : TBranch Atom) (ord : TimeOrdering) (tracker : EventualityTracker Atom)
--     (hH : temporalHintikkaSet b ord tracker)
--     (guard event : Formula Atom) (t : TimeIndex)
--     (hmem : b.any (fun sf => sf.sign == .pos && sf.label == t
--               && sf.formula == .untl guard event) = true) :
--     Satisfies (extractModel b) t (.untl guard event) := by
--   -- Blocked: need FMP for PTL to show pending eventuality is eventually witnessed.
--   sorry -- BLOCKED (FMP required)
```

### Blocked: Since Eventuality Fulfilment (FMP Required)

```lean
-- BLOCKED (FMP required): symmetric to temporalTruthLemma_untl.
--
-- lemma temporalTruthLemma_snce
--     (b : TBranch Atom) (ord : TimeOrdering) (tracker : EventualityTracker Atom)
--     (hH : temporalHintikkaSet b ord tracker)
--     (guard event : Formula Atom) (t : TimeIndex)
--     (hmem : b.any (fun sf => sf.sign == .pos && sf.label == t
--               && sf.formula == .snce guard event) = true) :
--     Satisfies (extractModel b) t (.snce guard event) := by
--   sorry -- BLOCKED (FMP required)
```

### Blocked: Open Branch Satisfiability

```lean
-- BLOCKED: depends on ordConstraints_strict + full temporalTruthLemma.
--
-- lemma openBranch_branchSat
--     (b : TBranch Atom) (ord : TimeOrdering) (tracker : EventualityTracker Atom)
--     (hH : temporalHintikkaSet b ord tracker) :
--     branchSat b ord :=
--   ⟨Nat, inferInstance, inferInstance, extractModel b, id,
--    fun t t' hconstr => ordConstraints_strict ... t t' hconstr,
--    fun sf hmem => temporalTruthLemma ... sf.sign sf.label sf.formula ...⟩
```

### Blocked: Completeness Theorem

```lean
-- BLOCKED: depends on openBranch_branchSat.
--
-- lemma temporalTableau_complete (φ : Formula Atom) (h : Valid φ) :
--     temporalTableau φ = .closed := by
--   cases hresult : temporalTableau φ with
--   | closed => rfl
--   | openBranch b ord =>
--     exact absurd h (openBranch_countermodel hresult)
```

### Blocked: Decidable Instance

```lean
-- BLOCKED: requires both soundness and completeness theorems.
--
-- instance instDecidableValid (φ : Formula Atom) : Decidable (Valid φ) :=
--   match hresult : temporalTableau φ with
--   | .closed => Decidable.isTrue (temporalTableau_sound hresult)
--   | .openBranch b ord => Decidable.isFalse (openBranch_countermodel hresult)
```

-/

end Cslib.Logic.Temporal.Tableau

end
