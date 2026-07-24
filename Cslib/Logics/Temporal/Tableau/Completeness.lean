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
  ¬ Satisfies (extractModel b) t (.atom p).
- `extractModelℤ`: Constructs a `TemporalModel ℤ Atom` keyed on `ord.instant`.
  This is the corrected countermodel for `openBranch_branchSat` (task 426): the time
  domain is `D = ℤ` with `f = ord.instant`, which is order-preserving by `InstantStrict`.
- `extractModelℤ_atomPos_sat`, `extractModelℤ_bot_false`: Basic properties of the ℤ model.
- `extractModelℤ_atom_neg_notSat`: Negative atom property (requires injectivity hypothesis).

## Blocked Obligations

The following results cannot be proved in the current scope.

### Ordering Design: RESOLVED (Task 426)

The false `ordConstraints_strict` (which claimed `a < b` for all `(a,b) ∈ constraints`
as Nat labels) has been replaced by `TimeOrdering.InstantStrict` and the `D = ℤ / f =
ord.instant` choice (task 426). The `openBranch_branchSat` sketch below reflects the
corrected design. Remaining blockers: (1) run-level `InstantStrict` proof (task 426
Phase 3, blocked on `processNext` refactor), (2) FMP for the Until/Since cases.

### Blocked (Proof Complexity — No Theoretical Blocker)

1. `temporalTruthLemma_propositional` (imp case): The propositional imp case requires
   detailed case analysis of `tryAllPropRules` output. Task 427 handles this.

### Blocked (FMP Required — Theoretical Blocker)

2. `temporalTruthLemma_untl`: Until eventuality fulfilment requires PTL FMP.

3. `temporalTruthLemma_snce`: Since eventuality fulfilment case (symmetric to 2).

4. `openBranch_branchSat`, `temporalTableau_complete`, `instDecidableValid`:
   Blocked by (2) + (3) + run-level `InstantStrict` (task 426 Phase 3).

## Decomposition Recommendation

1. Task 427: Complete the propositional truth lemma (imp case).
2. Task 426 Phase 3 follow-up: Factor out `processNext` to enable loop invariant induction.
3. FMP task: Prove PTL Finite Model Property for Until/Since eventualities.

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

/-! ## ℤ-Keyed Countermodel Extraction -/

/-- Extract a `TemporalModel ℤ Atom` from an open branch, keyed on the integer instant
assigned to each time label by the time ordering.

This is the corrected countermodel for `branchSat`: it uses the domain `D = ℤ` and the
order-preserving assignment `f = ord.instant`, supplying a time domain with a genuine
`LinearOrder` and `Nontrivial` instance. The valuation maps atom `p` at instant `z` to
`true` iff some signed formula T(atom p) at a time label with `ord.instant label = z`
appears on the branch.

Note: `ord.instant` may be non-injective (two labels can share an instant), making this
model well-defined but potentially "collapsing" distinct time points. For the positive atom
and ⊥ properties, non-injectivity poses no issue; the negative atom property requires
an additional injectivity hypothesis (see `extractModelℤ_atom_neg_notSat`). -/
def extractModelℤ (b : TBranch Atom) (ord : TimeOrdering) : TemporalModel ℤ Atom where
  valuation z p := b.any fun sf =>
    sf.sign == .pos && ord.instant sf.label == z && sf.formula == .atom p

omit [Hashable Atom] in
/-- Atom satisfaction in `extractModelℤ b ord` is equivalent to there being some
T(atom p)@t on the branch with `ord.instant t = z`. -/
lemma extractModelℤ_atom_sat_iff (b : TBranch Atom) (ord : TimeOrdering)
    (z : ℤ) (p : Atom) :
    Satisfies (extractModelℤ b ord) z (.atom p) ↔
    b.any (fun sf => sf.sign == .pos && ord.instant sf.label == z && sf.formula == .atom p) := by
  simp only [Satisfies.atom_iff, extractModelℤ]

omit [Hashable Atom] in
/-- T(atom p)@t on a branch implies atom p is satisfied in `extractModelℤ b ord`
at `ord.instant t`. -/
lemma extractModelℤ_atomPos_sat (b : TBranch Atom) (ord : TimeOrdering)
    (t : TimeIndex) (p : Atom)
    (hmem : (⟨.pos, .atom p, t⟩ : TSF Atom) ∈ b) :
    Satisfies (extractModelℤ b ord) (ord.instant t) (.atom p) := by
  rw [extractModelℤ_atom_sat_iff, List.any_eq_true]
  exact ⟨⟨.pos, .atom p, t⟩, hmem, by simp⟩

omit [Hashable Atom] in
/-- ⊥ is never satisfied in any `extractModelℤ` model, at any instant. -/
lemma extractModelℤ_bot_false (b : TBranch Atom) (ord : TimeOrdering) (z : ℤ) :
    ¬ Satisfies (extractModelℤ b ord) z .bot :=
  Satisfies.bot_false (extractModelℤ b ord) z

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

omit [Hashable Atom] in
/-- F(atom p)@t on an open branch implies
¬ Satisfies (extractModelℤ b ord) (ord.instant t) (atom p),
provided `ord.instant` is injective on branch labels carrying `atom p`.

This injectivity hypothesis is needed because two distinct labels `t ≠ t'` could share
an instant (`ord.instant t = ord.instant t'`); without injectivity, a T(atom p)@t' at the
same instant would make the ℤ model satisfy atom p at `ord.instant t` even when F(atom p)@t
is present. Proving injectivity of `ord.instant` on live branch labels is a separate task. -/
lemma extractModelℤ_atom_neg_notSat
    (b : TBranch Atom) (ord : TimeOrdering) (tracker : EventualityTracker Atom)
    (hopen : isTemporalClosed b ord tracker = false)
    (t : TimeIndex) (p : Atom)
    (hmem : (⟨.neg, .atom p, t⟩ : TSF Atom) ∈ b)
    (hInj : ∀ sf ∈ b, sf.formula = .atom p → sf.sign = .pos →
            ord.instant sf.label = ord.instant t → sf.label = t) :
    ¬ Satisfies (extractModelℤ b ord) (ord.instant t) (.atom p) := by
  rw [extractModelℤ_atom_sat_iff]
  intro h_any
  rw [List.any_eq_true] at h_any
  obtain ⟨sf_pos, hmem_pos, hcond⟩ := h_any
  simp only [Bool.and_eq_true] at hcond
  obtain ⟨⟨hpos_sign, hpos_inst⟩, hpos_form⟩ := hcond
  have hsign : sf_pos.sign = .pos := LawfulBEq.eq_of_beq hpos_sign
  have hinst : ord.instant sf_pos.label = ord.instant t := LawfulBEq.eq_of_beq hpos_inst
  have hform : sf_pos.formula = .atom p := LawfulBEq.eq_of_beq hpos_form
  have hlab : sf_pos.label = t := hInj sf_pos hmem_pos hform hsign hinst
  have hcontra_none : Branch.findContradiction b = none :=
    openBranch_noContradiction b ord tracker hopen
  have hcontra_some : (Branch.findContradiction b).isSome = true := by
    simp only [Branch.findContradiction, List.findSome?_isSome_iff]
    refine ⟨sf_pos, hmem_pos, ?_⟩
    have hisPos : sf_pos.isPos = true := by
      simp [SignedFormula.isPos, Sign.isPos, hsign]
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

omit [Hashable Atom] [DecidableEq Atom] in
/-- For propositional `φ`/`ψ`, `(φ.imp ψ).complexity` always takes the "generic imp" branch
of `Formula.complexity` (never the R(φ,ψ)/T(φ,ψ) special-cased overhead-1 patterns, which
require a `.untl`/`.snce` sub-term that `IsPropositional` excludes). Used to unstick
`Formula.complexity`'s pattern match when the operands are still symbolic in strong-induction
proofs: without this, `simp [Formula.complexity]` cannot determine which match arm fires for an
abstract `φ.imp ψ`. -/
private lemma IsPropositional.complexity_imp_eq {φ ψ : Formula Atom}
    (hφ : IsPropositional φ) (hψ : IsPropositional ψ) :
    (φ.imp ψ).complexity = 1 + φ.complexity + ψ.complexity := by
  cases hφ <;> cases hψ <;> rfl

omit [Hashable Atom] in
/-- Convert a `b.any` positive membership witness to list membership. -/
private lemma any_pos_mem (b : TBranch Atom) (t : TimeIndex) (φ : Formula Atom)
    (h : b.any (fun sf => sf.sign == .pos && sf.label == t && sf.formula == φ) = true) :
    (⟨.pos, φ, t⟩ : TSF Atom) ∈ b := by
  rw [List.any_eq_true] at h
  obtain ⟨sf, hmem, hcond⟩ := h
  simp only [Bool.and_eq_true, beq_iff_eq] at hcond
  obtain ⟨⟨hsign, hlabel⟩, hform⟩ := hcond
  obtain ⟨s, fm, l⟩ := sf
  simp_all

omit [Hashable Atom] in
/-- Convert a `b.any` negative membership witness to list membership. -/
private lemma any_neg_mem (b : TBranch Atom) (t : TimeIndex) (φ : Formula Atom)
    (h : b.any (fun sf => sf.sign == .neg && sf.label == t && sf.formula == φ) = true) :
    (⟨.neg, φ, t⟩ : TSF Atom) ∈ b := by
  rw [List.any_eq_true] at h
  obtain ⟨sf, hmem, hcond⟩ := h
  simp only [Bool.and_eq_true, beq_iff_eq] at hcond
  obtain ⟨⟨hsign, hlabel⟩, hform⟩ := hcond
  obtain ⟨s, fm, l⟩ := sf
  simp_all

omit [Hashable Atom] in
/-- Convert list membership to a `b.any` positive witness. -/
private lemma mem_to_any_pos (b : TBranch Atom) (t : TimeIndex) (φ : Formula Atom)
    (h : (⟨.pos, φ, t⟩ : TSF Atom) ∈ b) :
    b.any (fun sf => sf.sign == .pos && sf.label == t && sf.formula == φ) = true := by
  rw [List.any_eq_true]
  exact ⟨⟨.pos, φ, t⟩, h, by simp⟩

omit [Hashable Atom] in
/-- Convert list membership to a `b.any` negative witness. -/
private lemma mem_to_any_neg (b : TBranch Atom) (t : TimeIndex) (φ : Formula Atom)
    (h : (⟨.neg, φ, t⟩ : TSF Atom) ∈ b) :
    b.any (fun sf => sf.sign == .neg && sf.label == t && sf.formula == φ) = true := by
  rw [List.any_eq_true]
  exact ⟨⟨.neg, φ, t⟩, h, by simp⟩

/-! ## Remaining Blocked Obligations (BLOCKED)

The following section documents proof obligations that remain blocked.
These are stated as structured goal declarations in comments.
None use `sorry` or new axioms.

### Time-Ordering Invariant: InstantStrict (RESOLVED — Task 426)

**Status**: The false `ordConstraints_strict` lemma (which claimed `a < b` for all
constraint pairs `(a, b)` as Nat labels) has been REPLACED by the corrected
`InstantStrict` invariant (TimeOrdering.lean). See `TimeOrdering.InstantStrict`.

**The fix**: `TimeOrdering` now carries an `instant : Nat → ℤ` field. Each `addFuture t
tNew` sets `instant tNew = instant t + 1`, and each `addPast t tNew` sets
`instant tNew = instant t - 1`. The invariant `InstantStrict ord : ∀ a b, (a,b) ∈
ord.constraints → ord.instant a < ord.instant b` holds edge-by-edge from `empty`
through every `addFuture`/`addPast` (proved sorry-free in TimeOrdering.lean).

**Order-preservation choice**: `D = ℤ`, `f = ord.instant`. The corrected
`openBranch_branchSat` sketch (below) uses `⟨ℤ, inferInstance, inferInstance,
extractModelℤ b ord, ord.instant, hInst, …⟩` where `hInst` is the run-level
`InstantStrict ord` lemma.

**RESOLVED (task 439, task 426 Phase 3)**: `hInst` is now a concrete, sorry-free theorem:
`Cslib.Logic.Temporal.Tableau.temporalTableau_instantStrict` (`Saturation.lean`). The
blocker was structural: `processNext` was a `let rec` nested inside `temporalExpandBranches`,
so Lean generated no standalone recursion/induction principle for it. Task 439 (1) lifted the
pair into a top-level `mutual … end` block with an explicit lexicographic `termination_by`
(`Saturation.lean`), (2) proved a single-step preservation lemma
(`temporalStepBranch_preserves`) packaging the edge-by-edge `InstantStrict`/`OrdFreshWRT`
lemmas as the inductive step, and (3) threaded the invariant through the run via strong
induction on `fuel` plus structural induction on the worklist
(`temporalTableau_instantStrict`). The order-preservation component of `openBranch_branchSat`
is thus fully dischargeable; only the FMP-blocked truth lemma below remains.

**Why `ordConstraints_strict` is false**: `addPast t tNew` records `(tNew, t)` with
`tNew = branchNextTime b > t` (by `branchNextTime_gt`). So `(tNew, t) ∈ constraints`
but `tNew > t`, violating `∀ (a,b), a < b`. The Nat label is a fresh identifier, not
a semantic time value; `ord.instant` carries the semantic order instead.

### Propositional Truth Lemma

The Until/Since (`untl`/`snce`) cases remain FMP-blocked (see below); the propositional
fragment (atom/bot/imp) is handled here by strong induction on `Formula.complexity`. -/

omit [Hashable Atom] in
/-- Auxiliary truth lemma for the propositional fragment, bounded by a `Nat` fuel `n` so
that the proof can use strong (well-founded) induction on `Formula.complexity`: every strict
subformula of a propositional formula has strictly smaller complexity, so the single
induction hypothesis `ih` covers all (including the *deep* subformulas exposed by the
Łukasiewicz encoding of `and`/`or`/`neg`). -/
private lemma temporalTruthLemma_propositional_aux
    (b : TBranch Atom) (ord : TimeOrdering) (tracker : EventualityTracker Atom)
    (hH : temporalHintikkaSet b ord tracker)
    (n : Nat) :
    ∀ (φ : Formula Atom), φ.complexity ≤ n → IsPropositional φ → ∀ (t : TimeIndex),
      (b.any (fun sf => sf.sign == .pos && sf.label == t && sf.formula == φ) →
        Satisfies (extractModel b) t φ) ∧
      (b.any (fun sf => sf.sign == .neg && sf.label == t && sf.formula == φ) →
        ¬ Satisfies (extractModel b) t φ) := by
  obtain ⟨hopen, hrule⟩ := hH
  induction n with
  | zero =>
    intro φ hle hp t
    exact absurd hle (by have := Formula.one_le_complexity φ; omega)
  | succ n ih =>
    intro φ hle hp t
    cases hp with
    | atom p =>
      refine ⟨fun hmem => ?_, fun hmem => ?_⟩
      · exact extractModel_atomPos_sat b t p (any_pos_mem b t (.atom p) hmem)
      · exact extractModel_atom_neg_notSat b ord tracker hopen t p
          (any_neg_mem b t (.atom p) hmem)
    | bot =>
      refine ⟨fun hmem => ?_, fun _ => extractModel_bot_false b t⟩
      exact absurd ⟨t, any_pos_mem b t .bot hmem⟩
        (openBranch_noBotPos b ord tracker hopen)
    | imp hφ' hψ' =>
      -- φ = .imp φ' ψ'. The Łukasiewicz encoding means the fired rule depends on
      -- the structural shape of φ'/ψ': andPos/orPos/impPos/negPos (T) and their duals (F).
      -- Each output subformula has smaller complexity, so `ih` applies.
      refine ⟨fun hpos => ?_, fun hneg => ?_⟩
      · -- T-direction: T(imp φ' ψ') on branch → Satisfies m t (imp φ' ψ')
        simp only [Satisfies.imp_iff]
        intro hφ_sat
        have hmem := any_pos_mem b t _ hpos
        have hout := hrule _ hmem
        cases hφ' with
        | bot => exact absurd hφ_sat (Satisfies.bot_false _ _)
        | atom p =>
          cases hψ' with
          | bot =>
            -- negPos fires: linear [F(atom p)@t]
            simp only [temporalApplyOne, tryAllPropRules, applyPropRule, List.map, List.find?,
              tempAndOf?, tempOrOf?, tempImpOf?, tempNegOf?,
              RuleResult.isApplicable, Option.getD, reduceIte] at hout
            have hfp := hout _ (List.mem_singleton_self _)
            exact absurd hφ_sat ((ih (.atom p)
              (by simp only [Formula.complexity] at hle ⊢; omega) (.atom p) t).2
              (mem_to_any_neg b t _ hfp))
          | atom q =>
            -- impPos fires: branching [[F(atom p)], [T(atom q)]]
            simp only [temporalApplyOne, tryAllPropRules, applyPropRule, List.map, List.find?,
              tempAndOf?, tempOrOf?, tempImpOf?, tempNegOf?,
              RuleResult.isApplicable, Option.getD, reduceIte] at hout
            obtain ⟨br, hbr_mem, hbr⟩ := hout
            simp only [List.mem_cons, List.mem_nil_iff, or_false] at hbr_mem
            rcases hbr_mem with rfl | rfl
            · exact absurd hφ_sat ((ih (.atom p)
              (by simp only [Formula.complexity] at hle ⊢; omega) (.atom p) t).2
                (mem_to_any_neg b t _ (hbr _ (List.mem_singleton_self _))))
            · exact (ih (.atom q) (by simp only [Formula.complexity] at hle ⊢; omega) (.atom q) t).1
                (mem_to_any_pos b t _ (hbr _ (List.mem_singleton_self _)))
          | imp hψc hψd =>
            -- impPos fires: branching [[F(atom p)], [T(imp _ _)]]
            simp only [temporalApplyOne, tryAllPropRules, applyPropRule, List.map, List.find?,
              tempAndOf?, tempOrOf?, tempImpOf?, tempNegOf?,
              RuleResult.isApplicable, Option.getD, reduceIte] at hout
            obtain ⟨br, hbr_mem, hbr⟩ := hout
            simp only [List.mem_cons, List.mem_nil_iff, or_false] at hbr_mem
            rcases hbr_mem with rfl | rfl
            · exact absurd hφ_sat ((ih (.atom p)
              (by simp only [Formula.complexity] at hle ⊢; omega) (.atom p) t).2
                (mem_to_any_neg b t _ (hbr _ (List.mem_singleton_self _))))
            · exact (ih _
              (by simp only [Formula.complexity] at hle ⊢; omega) (IsPropositional.imp hψc hψd) t).1
                (mem_to_any_pos b t _ (hbr _ (List.mem_singleton_self _)))
        | imp ha hb =>
          cases hb with
          | bot =>
            -- φ' = imp a bot (neg-shape): orPos fires: [[T(a)@t], [T(ψ')@t]]
            simp only [temporalApplyOne, tryAllPropRules, applyPropRule, List.map, List.find?,
              tempAndOf?, tempOrOf?, tempImpOf?, tempNegOf?,
              RuleResult.isApplicable, Option.getD, reduceIte] at hout
            obtain ⟨br, hbr_mem, hbr⟩ := hout
            simp only [List.mem_cons, List.mem_nil_iff, or_false] at hbr_mem
            rcases hbr_mem with rfl | rfl
            · -- br = [T(a)@t]: sat a contradicts hφ_sat : sat a → False
              have ht_a := hbr _ (List.mem_singleton_self _)
              exact absurd ((ih _ (by simp only [Formula.complexity,
                IsPropositional.complexity_imp_eq, ha, IsPropositional.bot] at hle ⊢; omega) ha
                t).1 (mem_to_any_pos b t _ ht_a)) hφ_sat
            · -- br = [T(ψ')@t]: sat ψ'
              exact (ih _ (by simp only [Formula.complexity] at hle ⊢; omega) hψ' t).1
                (mem_to_any_pos b t _ (hbr _ (List.mem_singleton_self _)))
          | atom q =>
            -- φ' = imp a (atom q): impPos (ψ'≠bot) or negPos (ψ'=bot)
            cases hψ' with
            | bot =>
              simp only [temporalApplyOne, tryAllPropRules, applyPropRule, List.map,
                List.find?, tempAndOf?, tempOrOf?, tempImpOf?, tempNegOf?,
                RuleResult.isApplicable, Option.getD, reduceIte] at hout
              have hf := hout _ (List.mem_singleton_self _)
              exact absurd hφ_sat ((ih _
                (by simp only [Formula.complexity] at hle ⊢; omega)
                  (IsPropositional.imp ha (.atom q)) t).2
                (mem_to_any_neg b t _ hf))
            | atom r =>
              simp only [temporalApplyOne, tryAllPropRules, applyPropRule, List.map,
                List.find?, tempAndOf?, tempOrOf?, tempImpOf?, tempNegOf?,
                RuleResult.isApplicable, Option.getD, reduceIte] at hout
              obtain ⟨br, hbr_mem, hbr⟩ := hout
              simp only [List.mem_cons, List.mem_nil_iff, or_false] at hbr_mem
              rcases hbr_mem with rfl | rfl
              · exact absurd hφ_sat ((ih _
                (by simp only [Formula.complexity] at hle ⊢; omega)
                  (IsPropositional.imp ha (.atom q)) t).2
                  (mem_to_any_neg b t _ (hbr _ (List.mem_singleton_self _))))
              · exact (ih (.atom r)
                (by simp only [Formula.complexity] at hle ⊢; omega) (.atom r) t).1
                  (mem_to_any_pos b t _ (hbr _ (List.mem_singleton_self _)))
            | imp hψc hψd =>
              simp only [temporalApplyOne, tryAllPropRules, applyPropRule, List.map,
                List.find?, tempAndOf?, tempOrOf?, tempImpOf?, tempNegOf?,
                RuleResult.isApplicable, Option.getD, reduceIte] at hout
              obtain ⟨br, hbr_mem, hbr⟩ := hout
              simp only [List.mem_cons, List.mem_nil_iff, or_false] at hbr_mem
              rcases hbr_mem with rfl | rfl
              · exact absurd hφ_sat ((ih _
                (by simp only [Formula.complexity] at hle ⊢; omega)
                  (IsPropositional.imp ha (.atom q)) t).2
                  (mem_to_any_neg b t _ (hbr _ (List.mem_singleton_self _))))
              · exact (ih _
                (by simp only [Formula.complexity] at hle ⊢; omega)
                  (IsPropositional.imp hψc hψd) t).1
                  (mem_to_any_pos b t _ (hbr _ (List.mem_singleton_self _)))
          | imp hc hd =>
            cases hd with
            | bot =>
              -- φ' = imp a (imp c bot): andPos (ψ'=bot) or impPos (ψ'≠bot)
              cases hψ' with
              | bot =>
                -- andPos fires: linear [T(a)@t, T(c)@t]
                simp only [temporalApplyOne, tryAllPropRules, applyPropRule, List.map,
                  List.find?, tempAndOf?, tempOrOf?, tempImpOf?, tempNegOf?,
                  RuleResult.isApplicable, Option.getD, reduceIte] at hout
                simp only [List.forall_mem_cons] at hout
                obtain ⟨ht_a, ht_c, -⟩ := hout
                exact hφ_sat
                  ((ih _ (by simp only [Formula.complexity, IsPropositional.complexity_imp_eq,
                    hc, IsPropositional.bot] at hle ⊢; omega) ha t).1
                    (mem_to_any_pos b t _ ht_a))
                  ((ih _ (by simp only [Formula.complexity, IsPropositional.complexity_imp_eq,
                    hc, IsPropositional.bot] at hle ⊢; omega) hc t).1
                    (mem_to_any_pos b t _ ht_c))
              | atom r =>
                -- impPos fires
                simp only [temporalApplyOne, tryAllPropRules, applyPropRule, List.map,
                  List.find?, tempAndOf?, tempOrOf?, tempImpOf?, tempNegOf?,
                  RuleResult.isApplicable, Option.getD, reduceIte] at hout
                obtain ⟨br, hbr_mem, hbr⟩ := hout
                simp only [List.mem_cons, List.mem_nil_iff, or_false] at hbr_mem
                rcases hbr_mem with rfl | rfl
                · exact absurd hφ_sat ((ih _
                  (by simp only [Formula.complexity] at hle ⊢; omega)
                    (IsPropositional.imp ha (IsPropositional.imp hc .bot)) t).2
                    (mem_to_any_neg b t _ (hbr _ (List.mem_singleton_self _))))
                · exact (ih (.atom r)
                  (by simp only [Formula.complexity] at hle ⊢; omega) (.atom r) t).1
                    (mem_to_any_pos b t _ (hbr _ (List.mem_singleton_self _)))
              | imp hψc hψd =>
                simp only [temporalApplyOne, tryAllPropRules, applyPropRule, List.map,
                  List.find?, tempAndOf?, tempOrOf?, tempImpOf?, tempNegOf?,
                  RuleResult.isApplicable, Option.getD, reduceIte] at hout
                obtain ⟨br, hbr_mem, hbr⟩ := hout
                simp only [List.mem_cons, List.mem_nil_iff, or_false] at hbr_mem
                rcases hbr_mem with rfl | rfl
                · exact absurd hφ_sat ((ih _
                  (by simp only [Formula.complexity] at hle ⊢; omega)
                    (IsPropositional.imp ha (IsPropositional.imp hc .bot)) t).2
                    (mem_to_any_neg b t _ (hbr _ (List.mem_singleton_self _))))
                · exact (ih _
                  (by simp only [Formula.complexity] at hle ⊢; omega)
                    (IsPropositional.imp hψc hψd) t).1
                    (mem_to_any_pos b t _ (hbr _ (List.mem_singleton_self _)))
            | atom r =>
              -- φ' = imp a (imp c (atom r)): impPos or negPos
              cases hψ' with
              | bot =>
                simp only [temporalApplyOne, tryAllPropRules, applyPropRule, List.map,
                  List.find?, tempAndOf?, tempOrOf?, tempImpOf?, tempNegOf?,
                  RuleResult.isApplicable, Option.getD, reduceIte] at hout
                have hf := hout _ (List.mem_singleton_self _)
                exact absurd hφ_sat ((ih _
                  (by simp only [Formula.complexity] at hle ⊢; omega)
                    (IsPropositional.imp ha (IsPropositional.imp hc (.atom r))) t).2
                  (mem_to_any_neg b t _ hf))
              | atom s =>
                simp only [temporalApplyOne, tryAllPropRules, applyPropRule, List.map,
                  List.find?, tempAndOf?, tempOrOf?, tempImpOf?, tempNegOf?,
                  RuleResult.isApplicable, Option.getD, reduceIte] at hout
                obtain ⟨br, hbr_mem, hbr⟩ := hout
                simp only [List.mem_cons, List.mem_nil_iff, or_false] at hbr_mem
                rcases hbr_mem with rfl | rfl
                · exact absurd hφ_sat ((ih _
                  (by simp only [Formula.complexity] at hle ⊢; omega)
                    (IsPropositional.imp ha (IsPropositional.imp hc (.atom r))) t).2
                    (mem_to_any_neg b t _ (hbr _ (List.mem_singleton_self _))))
                · exact (ih (.atom s)
                  (by simp only [Formula.complexity] at hle ⊢; omega) (.atom s) t).1
                    (mem_to_any_pos b t _ (hbr _ (List.mem_singleton_self _)))
              | imp hψc hψd =>
                simp only [temporalApplyOne, tryAllPropRules, applyPropRule, List.map,
                  List.find?, tempAndOf?, tempOrOf?, tempImpOf?, tempNegOf?,
                  RuleResult.isApplicable, Option.getD, reduceIte] at hout
                obtain ⟨br, hbr_mem, hbr⟩ := hout
                simp only [List.mem_cons, List.mem_nil_iff, or_false] at hbr_mem
                rcases hbr_mem with rfl | rfl
                · exact absurd hφ_sat ((ih _
                  (by simp only [Formula.complexity] at hle ⊢; omega)
                    (IsPropositional.imp ha (IsPropositional.imp hc (.atom r))) t).2
                    (mem_to_any_neg b t _ (hbr _ (List.mem_singleton_self _))))
                · exact (ih _
                  (by simp only [Formula.complexity] at hle ⊢; omega)
                    (IsPropositional.imp hψc hψd) t).1
                    (mem_to_any_pos b t _ (hbr _ (List.mem_singleton_self _)))
            | imp he hf =>
              -- φ' = imp a (imp c (imp e f)): impPos or negPos
              cases hψ' with
              | bot =>
                simp only [temporalApplyOne, tryAllPropRules, applyPropRule, List.map,
                  List.find?, tempAndOf?, tempOrOf?, tempImpOf?, tempNegOf?,
                  RuleResult.isApplicable, Option.getD, reduceIte] at hout
                have hf' := hout _ (List.mem_singleton_self _)
                exact absurd hφ_sat
                  ((ih _
                    (by simp only [Formula.complexity] at hle ⊢; omega)
                      (IsPropositional.imp ha (IsPropositional.imp hc (IsPropositional.imp he hf)))
                      t).2
                    (mem_to_any_neg b t _ hf'))
              | atom s =>
                simp only [temporalApplyOne, tryAllPropRules, applyPropRule, List.map,
                  List.find?, tempAndOf?, tempOrOf?, tempImpOf?, tempNegOf?,
                  RuleResult.isApplicable, Option.getD, reduceIte] at hout
                obtain ⟨br, hbr_mem, hbr⟩ := hout
                simp only [List.mem_cons, List.mem_nil_iff, or_false] at hbr_mem
                rcases hbr_mem with rfl | rfl
                · exact absurd hφ_sat
                    ((ih _
                      (by simp only [Formula.complexity] at hle ⊢; omega)
                        (IsPropositional.imp ha (IsPropositional.imp hc
                          (IsPropositional.imp he hf)))
                        t).2
                      (mem_to_any_neg b t _ (hbr _ (List.mem_singleton_self _))))
                · exact (ih (.atom s)
                  (by simp only [Formula.complexity] at hle ⊢; omega) (.atom s) t).1
                    (mem_to_any_pos b t _ (hbr _ (List.mem_singleton_self _)))
              | imp hψc hψd =>
                simp only [temporalApplyOne, tryAllPropRules, applyPropRule, List.map,
                  List.find?, tempAndOf?, tempOrOf?, tempImpOf?, tempNegOf?,
                  RuleResult.isApplicable, Option.getD, reduceIte] at hout
                obtain ⟨br, hbr_mem, hbr⟩ := hout
                simp only [List.mem_cons, List.mem_nil_iff, or_false] at hbr_mem
                rcases hbr_mem with rfl | rfl
                · exact absurd hφ_sat
                    ((ih _
                      (by simp only [Formula.complexity] at hle ⊢; omega)
                        (IsPropositional.imp ha (IsPropositional.imp hc
                          (IsPropositional.imp he hf)))
                        t).2
                      (mem_to_any_neg b t _ (hbr _ (List.mem_singleton_self _))))
                · exact (ih _
                  (by simp only [Formula.complexity] at hle ⊢; omega)
                    (IsPropositional.imp hψc hψd) t).1
                    (mem_to_any_pos b t _ (hbr _ (List.mem_singleton_self _)))
      · -- F-direction: ¬ Satisfies m t (imp φ' ψ')
        simp only [Satisfies.imp_iff]
        intro hφ_to_ψ
        have hmem := any_neg_mem b t _ hneg
        have hout := hrule _ hmem
        cases hφ' with
        | bot =>
          -- negNeg/impNeg both output T(bot)@t, contradicting openBranch
          cases hψ' with
          | bot =>
              simp only [temporalApplyOne, tryAllPropRules, applyPropRule, List.map,
                List.find?, tempAndOf?, tempOrOf?, tempImpOf?, tempNegOf?,
                RuleResult.isApplicable, Option.getD, reduceIte] at hout
              exact absurd ⟨t, hout _ List.mem_cons_self⟩ (openBranch_noBotPos b ord tracker hopen)
          | atom _ =>
              simp only [temporalApplyOne, tryAllPropRules, applyPropRule, List.map,
                List.find?, tempAndOf?, tempOrOf?, tempImpOf?, tempNegOf?,
                RuleResult.isApplicable, Option.getD, reduceIte] at hout
              exact absurd ⟨t, hout _ List.mem_cons_self⟩ (openBranch_noBotPos b ord tracker hopen)
          | imp _ _ =>
              simp only [temporalApplyOne, tryAllPropRules, applyPropRule, List.map,
                List.find?, tempAndOf?, tempOrOf?, tempImpOf?, tempNegOf?,
                RuleResult.isApplicable, Option.getD, reduceIte] at hout
              exact absurd ⟨t, hout _ List.mem_cons_self⟩ (openBranch_noBotPos b ord tracker hopen)
        | atom p =>
          cases hψ' with
          | bot =>
            -- negNeg fires: linear [T(atom p)@t]
            simp only [temporalApplyOne, tryAllPropRules, applyPropRule, List.map, List.find?,
              tempAndOf?, tempOrOf?, tempImpOf?, tempNegOf?,
              RuleResult.isApplicable, Option.getD, reduceIte] at hout
            have ht_p := hout _ (List.mem_singleton_self _)
            exact hφ_to_ψ ((ih (.atom p)
              (by simp only [Formula.complexity] at hle ⊢; omega)
                (.atom p) t).1 (mem_to_any_pos b t _ ht_p))
          | atom q =>
            -- impNeg fires: linear [T(atom p)@t, F(atom q)@t]
            simp only [temporalApplyOne, tryAllPropRules, applyPropRule, List.map, List.find?,
              tempAndOf?, tempOrOf?, tempImpOf?, tempNegOf?,
              RuleResult.isApplicable, Option.getD, reduceIte] at hout
            simp only [List.forall_mem_cons] at hout
            obtain ⟨ht_p, hf_q, -⟩ := hout
            exact (ih (.atom q) (by simp only [Formula.complexity] at hle ⊢; omega) (.atom q) t).2
              (mem_to_any_neg b t _ hf_q)
              (hφ_to_ψ ((ih (.atom p)
                (by simp only [Formula.complexity] at hle ⊢; omega) (.atom p) t).1
                (mem_to_any_pos b t _ ht_p)))
          | imp hψc hψd =>
            simp only [temporalApplyOne, tryAllPropRules, applyPropRule, List.map, List.find?,
              tempAndOf?, tempOrOf?, tempImpOf?, tempNegOf?,
              RuleResult.isApplicable, Option.getD, reduceIte] at hout
            simp only [List.forall_mem_cons] at hout
            obtain ⟨ht_p, hf_ψ, -⟩ := hout
            exact (ih _
              (by simp only [Formula.complexity] at hle ⊢; omega) (IsPropositional.imp hψc hψd) t).2
              (mem_to_any_neg b t _ hf_ψ)
              (hφ_to_ψ ((ih (.atom p)
                (by simp only [Formula.complexity] at hle ⊢; omega) (.atom p) t).1
                (mem_to_any_pos b t _ ht_p)))
        | imp ha hb =>
          cases hb with
          | bot =>
            -- φ' = imp a bot: orNeg fires: linear [F(a)@t, F(ψ')@t]
            simp only [temporalApplyOne, tryAllPropRules, applyPropRule, List.map, List.find?,
              tempAndOf?, tempOrOf?, tempImpOf?, tempNegOf?,
              RuleResult.isApplicable, Option.getD, reduceIte] at hout
            simp only [List.forall_mem_cons] at hout
            obtain ⟨hf_a, hf_ψ, -⟩ := hout
            exact (ih _ (by simp only [Formula.complexity, IsPropositional.complexity_imp_eq,
              ha, IsPropositional.bot] at hle ⊢; omega) hψ' t).2
              (mem_to_any_neg b t _ hf_ψ)
              (hφ_to_ψ ((ih _ (by simp only [Formula.complexity,
                IsPropositional.complexity_imp_eq, ha, IsPropositional.bot] at hle ⊢; omega) ha
                t).2 (mem_to_any_neg b t _ hf_a)))
          | atom q =>
            -- φ' = imp a (atom q): negNeg (ψ'=bot) or impNeg (ψ'≠bot)
            cases hψ' with
            | bot =>
              simp only [temporalApplyOne, tryAllPropRules, applyPropRule, List.map,
                List.find?, tempAndOf?, tempOrOf?, tempImpOf?, tempNegOf?,
                RuleResult.isApplicable, Option.getD, reduceIte] at hout
              have ht := hout _ (List.mem_singleton_self _)
              exact hφ_to_ψ ((ih _
                (by simp only [Formula.complexity] at hle ⊢; omega)
                  (IsPropositional.imp ha (.atom q)) t).1
                (mem_to_any_pos b t _ ht))
            | atom r =>
              simp only [temporalApplyOne, tryAllPropRules, applyPropRule, List.map,
                List.find?, tempAndOf?, tempOrOf?, tempImpOf?, tempNegOf?,
                RuleResult.isApplicable, Option.getD, reduceIte] at hout
              simp only [List.forall_mem_cons] at hout
              obtain ⟨ht_φ, hf_ψ, -⟩ := hout
              exact (ih (.atom r) (by simp only [Formula.complexity] at hle ⊢; omega) (.atom r) t).2
                (mem_to_any_neg b t _ hf_ψ)
                (hφ_to_ψ ((ih _
                  (by simp only [Formula.complexity] at hle ⊢; omega)
                    (IsPropositional.imp ha (.atom q)) t).1
                  (mem_to_any_pos b t _ ht_φ)))
            | imp hψc hψd =>
              simp only [temporalApplyOne, tryAllPropRules, applyPropRule, List.map,
                List.find?, tempAndOf?, tempOrOf?, tempImpOf?, tempNegOf?,
                RuleResult.isApplicable, Option.getD, reduceIte] at hout
              simp only [List.forall_mem_cons] at hout
              obtain ⟨ht_φ, hf_ψ, -⟩ := hout
              exact (ih _
                (by simp only [Formula.complexity] at hle ⊢; omega)
                  (IsPropositional.imp hψc hψd) t).2
                (mem_to_any_neg b t _ hf_ψ)
                (hφ_to_ψ ((ih _
                  (by simp only [Formula.complexity] at hle ⊢; omega)
                    (IsPropositional.imp ha (.atom q)) t).1
                  (mem_to_any_pos b t _ ht_φ)))
          | imp hc hd =>
            cases hd with
            | bot =>
              -- φ' = imp a (imp c bot): andNeg (ψ'=bot) or impNeg/negNeg (ψ'≠bot)
              cases hψ' with
              | bot =>
                -- andNeg: branching [[F(a)@t], [F(c)@t]]
                simp only [temporalApplyOne, tryAllPropRules, applyPropRule, List.map,
                  List.find?, tempAndOf?, tempOrOf?, tempImpOf?, tempNegOf?,
                  RuleResult.isApplicable, Option.getD, reduceIte] at hout
                obtain ⟨br, hbr_mem, hbr⟩ := hout
                simp only [List.mem_cons, List.mem_nil_iff, or_false] at hbr_mem
                rcases hbr_mem with rfl | rfl
                · have hf_a := hbr _ (List.mem_singleton_self _)
                  exact hφ_to_ψ (fun h_a => absurd h_a ((ih _ (by simp only [Formula.complexity,
                    IsPropositional.complexity_imp_eq, hc, IsPropositional.bot] at hle ⊢; omega)
                    ha t).2 (mem_to_any_neg b t _ hf_a)))
                · have hf_c := hbr _ (List.mem_singleton_self _)
                  exact hφ_to_ψ (fun _ h_c => absurd h_c ((ih _ (by simp only [Formula.complexity,
                    IsPropositional.complexity_imp_eq, hc, IsPropositional.bot] at hle ⊢; omega)
                    hc t).2 (mem_to_any_neg b t _ hf_c)))
              | atom r =>
                simp only [temporalApplyOne, tryAllPropRules, applyPropRule, List.map,
                  List.find?, tempAndOf?, tempOrOf?, tempImpOf?, tempNegOf?,
                  RuleResult.isApplicable, Option.getD, reduceIte] at hout
                simp only [List.forall_mem_cons] at hout
                obtain ⟨ht_φ, hf_ψ, -⟩ := hout
                exact (ih (.atom r)
                  (by simp only [Formula.complexity] at hle ⊢; omega) (.atom r) t).2
                  (mem_to_any_neg b t _ hf_ψ)
                  (hφ_to_ψ ((ih _
                    (by simp only [Formula.complexity] at hle ⊢; omega)
                      (IsPropositional.imp ha (IsPropositional.imp hc .bot)) t).1
                    (mem_to_any_pos b t _ ht_φ)))
              | imp hψc hψd =>
                simp only [temporalApplyOne, tryAllPropRules, applyPropRule, List.map,
                  List.find?, tempAndOf?, tempOrOf?, tempImpOf?, tempNegOf?,
                  RuleResult.isApplicable, Option.getD, reduceIte] at hout
                simp only [List.forall_mem_cons] at hout
                obtain ⟨ht_φ, hf_ψ, -⟩ := hout
                exact (ih _
                  (by simp only [Formula.complexity] at hle ⊢; omega)
                    (IsPropositional.imp hψc hψd) t).2
                  (mem_to_any_neg b t _ hf_ψ)
                  (hφ_to_ψ ((ih _
                    (by simp only [Formula.complexity] at hle ⊢; omega)
                      (IsPropositional.imp ha (IsPropositional.imp hc .bot)) t).1
                    (mem_to_any_pos b t _ ht_φ)))
            | atom r =>
              -- φ' = imp a (imp c (atom r)): negNeg or impNeg
              cases hψ' with
              | bot =>
                simp only [temporalApplyOne, tryAllPropRules, applyPropRule, List.map,
                  List.find?, tempAndOf?, tempOrOf?, tempImpOf?, tempNegOf?,
                  RuleResult.isApplicable, Option.getD, reduceIte] at hout
                have ht := hout _ (List.mem_singleton_self _)
                exact hφ_to_ψ ((ih _
                  (by simp only [Formula.complexity] at hle ⊢; omega)
                    (IsPropositional.imp ha (IsPropositional.imp hc (.atom r))) t).1
                  (mem_to_any_pos b t _ ht))
              | atom s =>
                simp only [temporalApplyOne, tryAllPropRules, applyPropRule, List.map,
                  List.find?, tempAndOf?, tempOrOf?, tempImpOf?, tempNegOf?,
                  RuleResult.isApplicable, Option.getD, reduceIte] at hout
                simp only [List.forall_mem_cons] at hout
                obtain ⟨ht_φ, hf_ψ, -⟩ := hout
                exact (ih (.atom s)
                  (by simp only [Formula.complexity] at hle ⊢; omega) (.atom s) t).2
                  (mem_to_any_neg b t _ hf_ψ)
                  (hφ_to_ψ ((ih _
                    (by simp only [Formula.complexity] at hle ⊢; omega)
                      (IsPropositional.imp ha (IsPropositional.imp hc (.atom r))) t).1
                    (mem_to_any_pos b t _ ht_φ)))
              | imp hψc hψd =>
                simp only [temporalApplyOne, tryAllPropRules, applyPropRule, List.map,
                  List.find?, tempAndOf?, tempOrOf?, tempImpOf?, tempNegOf?,
                  RuleResult.isApplicable, Option.getD, reduceIte] at hout
                simp only [List.forall_mem_cons] at hout
                obtain ⟨ht_φ, hf_ψ, -⟩ := hout
                exact (ih _
                  (by simp only [Formula.complexity] at hle ⊢; omega)
                    (IsPropositional.imp hψc hψd) t).2
                  (mem_to_any_neg b t _ hf_ψ)
                  (hφ_to_ψ ((ih _
                    (by simp only [Formula.complexity] at hle ⊢; omega)
                      (IsPropositional.imp ha (IsPropositional.imp hc (.atom r))) t).1
                    (mem_to_any_pos b t _ ht_φ)))
            | imp he hf =>
              -- φ' = imp a (imp c (imp e f)): negNeg or impNeg
              cases hψ' with
              | bot =>
                simp only [temporalApplyOne, tryAllPropRules, applyPropRule, List.map,
                  List.find?, tempAndOf?, tempOrOf?, tempImpOf?, tempNegOf?,
                  RuleResult.isApplicable, Option.getD, reduceIte] at hout
                have ht := hout _ (List.mem_singleton_self _)
                exact hφ_to_ψ
                  ((ih _
                    (by simp only [Formula.complexity] at hle ⊢; omega)
                      (IsPropositional.imp ha (IsPropositional.imp hc (IsPropositional.imp he hf)))
                      t).1
                    (mem_to_any_pos b t _ ht))
              | atom s =>
                simp only [temporalApplyOne, tryAllPropRules, applyPropRule, List.map,
                  List.find?, tempAndOf?, tempOrOf?, tempImpOf?, tempNegOf?,
                  RuleResult.isApplicable, Option.getD, reduceIte] at hout
                simp only [List.forall_mem_cons] at hout
                obtain ⟨ht_φ, hf_ψ, -⟩ := hout
                exact (ih (.atom s)
                  (by simp only [Formula.complexity] at hle ⊢; omega) (.atom s) t).2
                  (mem_to_any_neg b t _ hf_ψ)
                  (hφ_to_ψ ((ih _
                    (by simp only [Formula.complexity] at hle ⊢; omega)
                      (IsPropositional.imp ha (IsPropositional.imp hc (IsPropositional.imp he hf)))
                      t).1
                    (mem_to_any_pos b t _ ht_φ)))
              | imp hψc hψd =>
                simp only [temporalApplyOne, tryAllPropRules, applyPropRule, List.map,
                  List.find?, tempAndOf?, tempOrOf?, tempImpOf?, tempNegOf?,
                  RuleResult.isApplicable, Option.getD, reduceIte] at hout
                simp only [List.forall_mem_cons] at hout
                obtain ⟨ht_φ, hf_ψ, -⟩ := hout
                exact (ih _
                  (by simp only [Formula.complexity] at hle ⊢; omega)
                    (IsPropositional.imp hψc hψd) t).2
                  (mem_to_any_neg b t _ hf_ψ)
                  (hφ_to_ψ ((ih _
                    (by simp only [Formula.complexity] at hle ⊢; omega)
                      (IsPropositional.imp ha (IsPropositional.imp hc (IsPropositional.imp he hf)))
                      t).1
                    (mem_to_any_pos b t _ ht_φ)))

omit [Hashable Atom] in
/-- Truth lemma for the propositional fragment (atom, ⊥, →) of the temporal tableau:
for a propositional `φ`, every `T(φ)@t` on a temporal Hintikka branch is satisfied in the
extracted model, and every `F(φ)@t` is not. Until/Since are excluded by `IsPropositional`. -/
lemma temporalTruthLemma_propositional
    (b : TBranch Atom) (ord : TimeOrdering) (tracker : EventualityTracker Atom)
    (hH : temporalHintikkaSet b ord tracker)
    (φ : Formula Atom) (hprop : IsPropositional φ) (t : TimeIndex) :
    (b.any (fun sf => sf.sign == .pos && sf.label == t && sf.formula == φ) →
      Satisfies (extractModel b) t φ) ∧
    (b.any (fun sf => sf.sign == .neg && sf.label == t && sf.formula == φ) →
      ¬ Satisfies (extractModel b) t φ) :=
  temporalTruthLemma_propositional_aux b ord tracker hH φ.complexity φ le_rfl hprop t

/-! ### Remaining FMP-Blocked Obligations

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

Order-preservation component: RESOLVED (task 439, task 426 Phase 3). `hInst` is no longer
an assumed hypothesis -- it is the concrete theorem
`Cslib.Logic.Temporal.Tableau.temporalTableau_instantStrict` (`Saturation.lean`), proved by
threading `InstantStrict` through the run-level saturation loop (`mutual`-lifted
`temporalExpandBranches`/`processNext`, single-step preservation, strong induction on fuel +
structural induction on the worklist). Remaining blocker: only the full `temporalTruthLemma`
(FMP-blocked -- Until/Since fulfilment requires PTL's Finite Model Property, not yet
formalized) prevents `openBranch_branchSat` from being stated as a real theorem, since its
`branchSat` witness needs both components simultaneously.

```lean
-- BLOCKED: full temporalTruthLemma requires PTL FMP (Until/Since fulfilment).
-- Order-preservation component is FULLY RESOLVED: D=ℤ, f=ord.instant,
-- hInst=temporalTableau_instantStrict (task 439 / task 426 Phase 3, sorry-free).
--
-- lemma openBranch_branchSat
--     (φ : Formula Atom) (b : TBranch Atom) (ord : TimeOrdering)
--     (tracker : EventualityTracker Atom)
--     (hresult : temporalTableau φ = .openBranch b ord)
--     (hH : temporalHintikkaSet b ord tracker) :
--     branchSat b ord :=
--   ⟨ℤ, inferInstance, inferInstance, extractModelℤ b ord, ord.instant,
--    fun t t' hconstr =>
--      temporalTableau_instantStrict φ b ord hresult t t' hconstr,  -- order-preservation: PROVEN
--    fun sf hmem => temporalTruthLemma … ⟩                          -- truth lemma: BLOCKED (FMP)
```

### Blocked: Completeness Theorem

```lean
-- BLOCKED: depends on openBranch_branchSat.
--
-- lemma temporalTableau_complete (φ : Formula Atom) (h : valid φ) :
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
-- instance instDecidableValid (φ : Formula Atom) : Decidable (valid φ) :=
--   match hresult : temporalTableau φ with
--   | .closed => Decidable.isTrue (temporalTableau_sound hresult)
--   | .openBranch b ord => Decidable.isFalse (openBranch_countermodel hresult)
```

-/

end Cslib.Logic.Temporal.Tableau

end
