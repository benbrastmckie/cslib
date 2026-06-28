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

## Blocked Obligations

The following results cannot be proved in the current scope.

### Blocked (Proof Complexity — No Theoretical Blocker)

These results are in principle provable without FMP but require
substantial proof engineering:

1. `temporalTruthLemma_propositional` (propositional cases): The truth lemma
   for `imp`/`neg`/`and`/`or` cases requires detailed case analysis of
   `tryAllPropRules` output in `temporalApplyOne`, reproducing the classical
   truth lemma proof but with time-indexed `temporalHintikkaSet`.

2. `ordConstraints_strict`: The `TimeOrdering` maintained by the saturation
   loop has the invariant that `(t, t') ∈ ord.constraints → t < t'`. Proving
   this requires a formal loop invariant over `temporalExpandBranches`.

3. `extractModel_atom_neg_notSat`: F(atom p)@t on an open branch implies
   ¬ Satisfies (extractModel b) t (.atom p). Follows from
   `openBranch_noContradiction` + extracting from `Branch.findContradiction`
   that T(atom p)@t cannot also be present. Requires a converse-of-`findSome?`
   lemma (e.g., `List.findSome?_ne_none_of_mem`) whose exact name in the
   current Mathlib version has not been confirmed.

### Blocked (FMP Required — Theoretical Blocker)

These results require the Finite Model Property for temporal logic over linear
orders (or an explicit loop-detection argument):

4. `temporalTruthLemma_untl`: Until eventuality fulfilment case. Proving
   T(U(guard,event))@t ∈ b → ∃ s > t, event holds at s ∧ guard holds between,
   in the extracted model requires either FMP for PTL or an explicit loop-
   unwinding argument showing the time-subset blocking structure yields a model
   where all pending eventualities are periodically re-satisfied.

5. `temporalTruthLemma_snce`: Since eventuality fulfilment case. Symmetric
   to (4) in the past direction.

6. `openBranch_branchSat`, `temporalTableau_complete`, `instDecidableValid`:
   All blocked by (2), (4), (5).

## Decomposition Recommendation

The most tractable path to closing these obligations:
1. Prove (2) via a loop invariant on `temporalExpandBranches`.
2. Prove (1) and (3) by adapting `Propositional/Tableau/Classical/Completeness.lean`.
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

/-! ## Blocked Obligations (BLOCKED)

The following section documents proof obligations that are blocked.
These are stated as structured goal declarations in comments.
None use `sorry` or new axioms.

### Blocked: F(atom p)@t on open branch → ¬Satisfies (Proof Complexity)

```lean
-- BLOCKED (proof complexity): requires List.findSome?_ne_none_of_mem or similar.
--
-- lemma extractModel_atom_neg_notSat
--     (b : TBranch Atom) (ord : TimeOrdering) (tracker : EventualityTracker Atom)
--     (hopen : isTemporalClosed b ord tracker = false)
--     (t : TimeIndex) (p : Atom)
--     (hmem : (⟨.neg, .atom p, t⟩ : TSF Atom) ∈ b) :
--     ¬ Satisfies (extractModel b) t (.atom p) := by
--   rw [extractModel_atom_sat_iff]
--   intro h_pos
--   obtain ⟨sf_pos, hsfpos_mem, hsfpos_cond⟩ := List.any_eq_true.mp h_pos
--   simp only [Bool.and_eq_true] at hsfpos_cond
--   obtain ⟨⟨hsign, hlab⟩, hform⟩ := hsfpos_cond
--   have hpos_sign : sf_pos.sign = .pos := by cases sf_pos.sign <;> simp_all
--   have hpos_lab  : sf_pos.label = t := eq_of_beq hlab
--   have hpos_form : sf_pos.formula = .atom p := eq_of_beq hform
--   -- T(.atom p)@t and F(.atom p)@t both in b → Branch.findContradiction ≠ none
--   -- But openBranch_noContradiction says it is none. Contradiction.
--   -- Key gap: need List.findSome?_ne_none_of_mem (or equivalent) to show findContradiction
--   -- returns some when the witness exists.
--   sorry -- BLOCKED
```

### Blocked: Ord Constraints Are Strict (Proof Complexity)

```lean
-- BLOCKED (proof complexity): requires formal loop invariant.
--
-- lemma ordConstraints_strict (φ : Formula Atom) (b : TBranch Atom) (ord : TimeOrdering)
--     (hresult : temporalTableau φ = .openBranch b ord) :
--     ∀ t t', (t, t') ∈ ord.constraints → t < t' := by
--   -- Key: addFuture t (branchNextTime b) always satisfies t < branchNextTime b
--   -- because branchNextTime_gt says sf.label < branchNextTime b for all sf ∈ b.
--   -- So the time `t` at which the existential rule fires is on the branch,
--   -- hence t < branchNextTime b = t'.
--   -- Requires induction over temporalExpandBranches.
--   sorry -- BLOCKED
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
