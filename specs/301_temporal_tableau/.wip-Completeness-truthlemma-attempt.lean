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
Does not include temporal operators (until, since). -/
inductive IsPropositional : Formula Atom → Prop where
  /-- Atomic propositions are propositional. -/
  | atom (p : Atom) : IsPropositional (.atom p)
  /-- Falsum is propositional. -/
  | bot : IsPropositional .bot
  /-- Implication of propositional formulas is propositional. -/
  | imp {φ ψ : Formula Atom} (hφ : IsPropositional φ) (hψ : IsPropositional ψ) :
      IsPropositional (.imp φ ψ)

/-! ## Propositional Truth Lemma -/

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

/-- Convert list membership to a `b.any` positive witness. -/
private lemma mem_to_any_pos (b : TBranch Atom) (t : TimeIndex) (φ : Formula Atom)
    (h : (⟨.pos, φ, t⟩ : TSF Atom) ∈ b) :
    b.any (fun sf => sf.sign == .pos && sf.label == t && sf.formula == φ) = true := by
  rw [List.any_eq_true]
  exact ⟨⟨.pos, φ, t⟩, h, by simp⟩

/-- Convert list membership to a `b.any` negative witness. -/
private lemma mem_to_any_neg (b : TBranch Atom) (t : TimeIndex) (φ : Formula Atom)
    (h : (⟨.neg, φ, t⟩ : TSF Atom) ∈ b) :
    b.any (fun sf => sf.sign == .neg && sf.label == t && sf.formula == φ) = true := by
  rw [List.any_eq_true]
  exact ⟨⟨.neg, φ, t⟩, h, by simp⟩

/-- Truth lemma for propositional connectives (atom, ⊥, →) of the temporal tableau.

For any propositional formula `φ` (containing no Until/Since), if the branch `b`
is a temporal Hintikka set, then:
- Every T(φ)@t on the branch is satisfied in the extracted model.
- Every F(φ)@t on the branch is not satisfied in the extracted model.

Proof is by induction on the `IsPropositional φ` predicate.
Until/Since cases are not handled (they require FMP; see blocked obligations). -/
lemma temporalTruthLemma_propositional
    (b : TBranch Atom) (ord : TimeOrdering) (tracker : EventualityTracker Atom)
    (hH : temporalHintikkaSet b ord tracker)
    (φ : Formula Atom) (hprop : IsPropositional φ) (t : TimeIndex) :
    (b.any (fun sf => sf.sign == .pos && sf.label == t && sf.formula == φ) →
      Satisfies (extractModel b) t φ) ∧
    (b.any (fun sf => sf.sign == .neg && sf.label == t && sf.formula == φ) →
      ¬ Satisfies (extractModel b) t φ) := by
  obtain ⟨hopen, hrule⟩ := hH
  induction hprop with
  | atom p =>
    constructor
    · intro hmem
      exact extractModel_atomPos_sat b t p (any_pos_mem b t (.atom p) hmem)
    · intro hmem
      exact extractModel_atom_neg_notSat b ord tracker hopen t p (any_neg_mem b t (.atom p) hmem)
  | bot =>
    constructor
    · intro hmem
      exfalso
      exact openBranch_noBotPos b ord tracker hopen ⟨t, any_pos_mem b t .bot hmem⟩
    · intro _
      exact extractModel_bot_false b t
  | imp hφ hψ ih_φ ih_ψ =>
    -- Get IH for φ and ψ
    obtain ⟨ih_φ_pos, ih_φ_neg⟩ := ih_φ
    obtain ⟨ih_ψ_pos, ih_ψ_neg⟩ := ih_ψ
    constructor
    · -- T(.imp φ ψ)@t on branch → Satisfies M t (φ → ψ)
      intro hmem_any
      rw [Satisfies.imp_iff]
      intro hsat_φ
      -- T(.imp φ ψ)@t ∈ b
      have sf_mem : (⟨.pos, .imp φ ψ, t⟩ : TSF Atom) ∈ b :=
        any_pos_mem b t (.imp φ ψ) hmem_any
      -- Hintikka condition for this formula
      have hout := hrule ⟨.pos, .imp φ ψ, t⟩ sf_mem
      -- temporalApplyOne tries propositional rules first
      simp only [temporalApplyOne] at hout
      -- The propositional rule fires for T(φ→ψ)
      -- Case split on φ to determine which rule fires
      induction hφ with
      | atom p =>
        -- φ = atom p: impPos or negPos
        induction hψ with
        | atom q =>
          -- ψ = atom q, φ = atom p: impPos fires
          simp only [tryAllPropRules, applyPropRule, List.map, List.find?,
            tempAndOf?, tempOrOf?, tempImpOf?, tempNegOf?,
            RuleResult.isApplicable] at hout
          obtain ⟨br, hbr_mem, hbr⟩ := hout
          simp only [List.mem_cons, List.mem_nil_iff, or_false] at hbr_mem
          rcases hbr_mem with rfl | rfl
          · -- br = [F(atom p)@t]: F(atom p)@t ∈ b
            have hfa_mem : (⟨.neg, .atom p, t⟩ : TSF Atom) ∈ b := hbr _ (by simp)
            exact absurd hsat_φ
              (ih_φ_neg (mem_to_any_neg b t (.atom p) hfa_mem))
          · -- br = [T(atom q)@t]: T(atom q)@t ∈ b
            have htc_mem : (⟨.pos, .atom q, t⟩ : TSF Atom) ∈ b := hbr _ (by simp)
            exact ih_ψ_pos (mem_to_any_pos b t (.atom q) htc_mem)
        | bot =>
          -- ψ = bot, φ = atom p: negPos fires → F(atom p)@t ∈ b
          simp only [tryAllPropRules, applyPropRule, List.map, List.find?,
            tempAndOf?, tempOrOf?, tempImpOf?, tempNegOf?,
            RuleResult.isApplicable] at hout
          have hfa_mem : (⟨.neg, .atom p, t⟩ : TSF Atom) ∈ b := hout _ (by simp)
          exact absurd hsat_φ (ih_φ_neg (mem_to_any_neg b t (.atom p) hfa_mem))
        | imp _ _ ih_ψ1 ih_ψ2 =>
          -- ψ = imp ψ1 ψ2, φ = atom p: impPos fires
          simp only [tryAllPropRules, applyPropRule, List.map, List.find?,
            tempAndOf?, tempOrOf?, tempImpOf?, tempNegOf?,
            RuleResult.isApplicable] at hout
          obtain ⟨br, hbr_mem, hbr⟩ := hout
          simp only [List.mem_cons, List.mem_nil_iff, or_false] at hbr_mem
          rcases hbr_mem with rfl | rfl
          · have hfa_mem : (⟨.neg, .atom p, t⟩ : TSF Atom) ∈ b := hbr _ (by simp)
            exact absurd hsat_φ (ih_φ_neg (mem_to_any_neg b t (.atom p) hfa_mem))
          · have htc_mem : (⟨.pos, .imp _ _, t⟩ : TSF Atom) ∈ b := hbr _ (by simp)
            exact ih_ψ_pos (mem_to_any_pos b t (.imp _ _) htc_mem)
      | bot =>
        -- φ = bot: impPos or negPos
        induction hψ with
        | atom q =>
          -- ψ = atom q, φ = bot: impPos fires
          simp only [tryAllPropRules, applyPropRule, List.map, List.find?,
            tempAndOf?, tempOrOf?, tempImpOf?, tempNegOf?,
            RuleResult.isApplicable] at hout
          obtain ⟨br, hbr_mem, hbr⟩ := hout
          simp only [List.mem_cons, List.mem_nil_iff, or_false] at hbr_mem
          rcases hbr_mem with rfl | rfl
          · have hfa_mem : (⟨.neg, .bot, t⟩ : TSF Atom) ∈ b := hbr _ (by simp)
            exact absurd hsat_φ (ih_φ_neg (mem_to_any_neg b t .bot hfa_mem))
          · have htc_mem : (⟨.pos, .atom q, t⟩ : TSF Atom) ∈ b := hbr _ (by simp)
            exact ih_ψ_pos (mem_to_any_pos b t (.atom q) htc_mem)
        | bot =>
          -- ψ = bot, φ = bot: negPos fires → F(bot)@t. But sat_φ : Sat M t bot = False
          exact hsat_φ.elim
        | imp _ _ ih_ψ1 ih_ψ2 =>
          -- ψ = imp ψ1 ψ2, φ = bot: impPos fires
          simp only [tryAllPropRules, applyPropRule, List.map, List.find?,
            tempAndOf?, tempOrOf?, tempImpOf?, tempNegOf?,
            RuleResult.isApplicable] at hout
          obtain ⟨br, hbr_mem, hbr⟩ := hout
          simp only [List.mem_cons, List.mem_nil_iff, or_false] at hbr_mem
          rcases hbr_mem with rfl | rfl
          · have hfa_mem : (⟨.neg, .bot, t⟩ : TSF Atom) ∈ b := hbr _ (by simp)
            exact absurd hsat_φ (ih_φ_neg (mem_to_any_neg b t .bot hfa_mem))
          · have htc_mem : (⟨.pos, .imp _ _, t⟩ : TSF Atom) ∈ b := hbr _ (by simp)
            exact ih_ψ_pos (mem_to_any_pos b t (.imp _ _) htc_mem)
      | imp hφ1 hφ2 ih_φ1 ih_φ2 =>
        -- φ = imp φ1 φ2
        -- Sub-case on φ2 to determine which rule fires
        induction hφ2 with
        | bot =>
          -- φ = imp φ1 bot (a negation): orPos fires
          -- orPos: branching [[T(φ1)@t], [T(ψ)@t]]
          induction hψ with
          | atom q =>
            simp only [tryAllPropRules, applyPropRule, List.map, List.find?,
              tempAndOf?, tempOrOf?, tempImpOf?, tempNegOf?,
              RuleResult.isApplicable] at hout
            obtain ⟨br, hbr_mem, hbr⟩ := hout
            simp only [List.mem_cons, List.mem_nil_iff, or_false] at hbr_mem
            rcases hbr_mem with rfl | rfl
            · -- T(φ1)@t ∈ b
              have hta1 : (⟨.pos, φ1, t⟩ : TSF Atom) ∈ b := hbr _ (by simp)
              -- Sat M t (.imp (.imp φ1 .bot) (.atom q)) = (¬Sat M t φ1 → Sat M t (.atom q))
              -- From hsat_φ : Sat M t (.imp φ1 .bot) = ¬Sat M t φ1
              -- and T(φ1)@t → Sat M t φ1, contradiction
              have hsat_φ1 := (ih_φ1 t).1 (mem_to_any_pos b t φ1 hta1)
              -- hsat_φ : ¬Sat M t φ1, hsat_φ1 : Sat M t φ1
              -- But wait, hsat_φ is Sat M t (.imp φ1 .bot) = ¬ Sat M t φ1
              simp only [Satisfies, Satisfies.bot_false] at hsat_φ
              exact hsat_φ hsat_φ1
            · -- T(.atom q)@t ∈ b
              have htq : (⟨.pos, .atom q, t⟩ : TSF Atom) ∈ b := hbr _ (by simp)
              obtain ⟨ih_ψ_pos', _⟩ := ih_ψ
              exact ih_ψ_pos' (mem_to_any_pos b t (.atom q) htq)
          | bot =>
            -- ψ = bot, φ = imp φ1 .bot: orPos fires → branching [[T(φ1)], [T(.bot)]]
            simp only [tryAllPropRules, applyPropRule, List.map, List.find?,
              tempAndOf?, tempOrOf?, tempImpOf?, tempNegOf?,
              RuleResult.isApplicable] at hout
            obtain ⟨br, hbr_mem, hbr⟩ := hout
            simp only [List.mem_cons, List.mem_nil_iff, or_false] at hbr_mem
            rcases hbr_mem with rfl | rfl
            · have hta1 : (⟨.pos, φ1, t⟩ : TSF Atom) ∈ b := hbr _ (by simp)
              have hsat_φ1 := (ih_φ1 t).1 (mem_to_any_pos b t φ1 hta1)
              simp only [Satisfies, Satisfies.bot_false] at hsat_φ
              exact hsat_φ hsat_φ1
            · have htbot : (⟨.pos, .bot, t⟩ : TSF Atom) ∈ b := hbr _ (by simp)
              exact absurd ⟨t, htbot⟩ (openBranch_noBotPos b ord tracker hopen)
          | imp hψ1 hψ2 ih_ψ1 ih_ψ2 =>
            simp only [tryAllPropRules, applyPropRule, List.map, List.find?,
              tempAndOf?, tempOrOf?, tempImpOf?, tempNegOf?,
              RuleResult.isApplicable] at hout
            obtain ⟨br, hbr_mem, hbr⟩ := hout
            simp only [List.mem_cons, List.mem_nil_iff, or_false] at hbr_mem
            rcases hbr_mem with rfl | rfl
            · have hta1 : (⟨.pos, φ1, t⟩ : TSF Atom) ∈ b := hbr _ (by simp)
              have hsat_φ1 := (ih_φ1 t).1 (mem_to_any_pos b t φ1 hta1)
              simp only [Satisfies, Satisfies.bot_false] at hsat_φ
              exact hsat_φ hsat_φ1
            · have htψ : (⟨.pos, .imp _ _, t⟩ : TSF Atom) ∈ b := hbr _ (by simp)
              exact ih_ψ_pos (mem_to_any_pos b t (.imp _ _) htψ)
        | atom p2 =>
          -- φ = imp φ1 (atom p2): impPos fires (φ ≠ .imp _ .bot, ψ might vary)
          induction hψ with
          | atom q =>
            simp only [tryAllPropRules, applyPropRule, List.map, List.find?,
              tempAndOf?, tempOrOf?, tempImpOf?, tempNegOf?,
              RuleResult.isApplicable] at hout
            obtain ⟨br, hbr_mem, hbr⟩ := hout
            simp only [List.mem_cons, List.mem_nil_iff, or_false] at hbr_mem
            rcases hbr_mem with rfl | rfl
            · have hfa : (⟨.neg, .imp φ1 (.atom p2), t⟩ : TSF Atom) ∈ b := hbr _ (by simp)
              exact absurd hsat_φ (ih_φ_neg (mem_to_any_neg b t (.imp φ1 (.atom p2)) hfa))
            · have htq : (⟨.pos, .atom q, t⟩ : TSF Atom) ∈ b := hbr _ (by simp)
              exact ih_ψ_pos (mem_to_any_pos b t (.atom q) htq)
          | bot =>
            -- ψ = bot, φ = imp φ1 (atom p2): negPos fires
            simp only [tryAllPropRules, applyPropRule, List.map, List.find?,
              tempAndOf?, tempOrOf?, tempImpOf?, tempNegOf?,
              RuleResult.isApplicable] at hout
            have hfa : (⟨.neg, .imp φ1 (.atom p2), t⟩ : TSF Atom) ∈ b := hout _ (by simp)
            exact absurd hsat_φ (ih_φ_neg (mem_to_any_neg b t (.imp φ1 (.atom p2)) hfa))
          | imp hψ1 hψ2 ih_ψ1 ih_ψ2 =>
            simp only [tryAllPropRules, applyPropRule, List.map, List.find?,
              tempAndOf?, tempOrOf?, tempImpOf?, tempNegOf?,
              RuleResult.isApplicable] at hout
            obtain ⟨br, hbr_mem, hbr⟩ := hout
            simp only [List.mem_cons, List.mem_nil_iff, or_false] at hbr_mem
            rcases hbr_mem with rfl | rfl
            · have hfa : (⟨.neg, .imp φ1 (.atom p2), t⟩ : TSF Atom) ∈ b := hbr _ (by simp)
              exact absurd hsat_φ (ih_φ_neg (mem_to_any_neg b t (.imp φ1 (.atom p2)) hfa))
            · have htψ : (⟨.pos, .imp _ _, t⟩ : TSF Atom) ∈ b := hbr _ (by simp)
              exact ih_ψ_pos (mem_to_any_pos b t (.imp _ _) htψ)
        | imp hφ21 hφ22 ih_φ21 ih_φ22 =>
          -- φ = imp φ1 (imp φ21 φ22)
          -- Sub-case on φ22: if φ22 = .bot, andPos might fire; otherwise impPos/negPos
          induction hφ22 with
          | bot =>
            -- φ = imp φ1 (imp φ21 .bot): andPos fires when ψ = .bot, else impPos
            induction hψ with
            | atom q =>
              -- ψ = atom q: impPos fires (φ ≠ .imp _ .bot, ψ ≠ .bot)
              simp only [tryAllPropRules, applyPropRule, List.map, List.find?,
                tempAndOf?, tempOrOf?, tempImpOf?, tempNegOf?,
                RuleResult.isApplicable] at hout
              obtain ⟨br, hbr_mem, hbr⟩ := hout
              simp only [List.mem_cons, List.mem_nil_iff, or_false] at hbr_mem
              rcases hbr_mem with rfl | rfl
              · have hfa : (⟨.neg, .imp φ1 (.imp φ21 .bot), t⟩ : TSF Atom) ∈ b :=
                    hbr _ (by simp)
                exact absurd hsat_φ
                  (ih_φ_neg (mem_to_any_neg b t (.imp φ1 (.imp φ21 .bot)) hfa))
              · have htq : (⟨.pos, .atom q, t⟩ : TSF Atom) ∈ b := hbr _ (by simp)
                exact ih_ψ_pos (mem_to_any_pos b t (.atom q) htq)
            | bot =>
              -- ψ = bot, φ = imp φ1 (imp φ21 .bot): andPos fires!
              -- andPos: linear [T(φ1)@t, T(φ21)@t]
              simp only [tryAllPropRules, applyPropRule, List.map, List.find?,
                tempAndOf?, tempOrOf?, tempImpOf?, tempNegOf?,
                RuleResult.isApplicable] at hout
              -- andPos gives: T(φ1)@t ∈ b and T(φ21)@t ∈ b
              -- The formula is T(.imp (.imp φ1 (.imp φ21 .bot)) .bot) = T(¬(φ1 → ¬φ21)) = T(φ1 ∧ φ21)
              -- hsat_φ : Sat M t (.imp (.imp φ1 (.imp φ21 .bot)) .bot) = False? No...
              -- hsat_φ : Sat M t (.imp φ ψ) where ψ = .bot
              -- That means Sat M t (.imp (.imp φ1 (.imp φ21 .bot)) .bot) = ¬Sat M t (.imp φ1 (.imp φ21 .bot))
              -- = ¬(Sat M t φ1 → ¬Sat M t φ21) = Sat M t φ1 ∧ Sat M t φ21
              -- hout says T(φ1)@t ∈ b and T(φ21)@t ∈ b
              have ht_φ1 : (⟨.pos, φ1, t⟩ : TSF Atom) ∈ b := hout _ (by simp)
              have ht_φ21 : (⟨.pos, φ21, t⟩ : TSF Atom) ∈ b := hout _ (by simp)
              -- From hsat_φ and IH...
              -- hsat_φ : ¬ Sat M t (.imp φ1 (.imp φ21 .bot))
              -- We need to show Sat M t .bot = False
              -- But .bot is always False, contradiction.
              -- Wait: hsat_φ says we already assumed this sat, so we need False
              -- Actually, we just need Sat M t ψ = Sat M t .bot = False
              -- But the conclusion is Satisfies M t ψ = Satisfies M t .bot = False
              -- That's exactly what we need to show: the continuation is `intro hsat_φ; ...`
              -- And now we need `Satisfies M t .bot`?! That's impossible!
              -- Oh wait, I'm inside the `intro hsat_φ` block. We're trying to show
              -- `Satisfies M t ψ`. Here ψ = .bot. So we need `Satisfies M t .bot = False`.
              -- This is ALWAYS false! So we need to reach a contradiction.
              -- The branch is open so T(.bot) can't be on it...
              -- But we have hsat_φ : Sat M t (.imp (.imp φ1 (.imp φ21 .bot)) .bot)
              -- = ¬Sat M t (.imp φ1 (.imp φ21 .bot))
              -- And T(.imp (.imp φ1 (.imp φ21 .bot)) .bot) is on the branch.
              -- hout gives T(φ1)@t ∈ b and T(φ21)@t ∈ b (from andPos: linear [T(φ1), T(φ21)])
              -- IH(φ): T(φ1 ∧ φ21 = .imp φ1 (.imp φ21 .bot)) on branch → Sat M t φ1 and Sat M t φ21
              -- Wait, hout gives T(φ1) and T(φ21). IH for the full φ = .imp φ1 (.imp φ21 .bot):
              -- hsat_φ : ¬ Sat M t (.imp φ1 (.imp φ21 .bot))
              -- From T(φ1)@t ∈ b: ih_φ1.1 gives Sat M t φ1
              -- From T(φ21)@t ∈ b: ih_φ21_inner.1 gives Sat M t φ21
              -- So Sat M t (.imp φ1 (.imp φ21 .bot)) = Sat M t φ1 → Sat M t (.imp φ21 .bot)
              --   = Sat M t φ1 → ¬ Sat M t φ21
              -- And hsat_φ says ¬(Sat M t φ1 → ¬ Sat M t φ21) = Sat M t φ1 ∧ Sat M t φ21
              -- So hsat_φ : Sat M t φ1 ∧ ¬ (¬ Sat M t φ21) = Sat M t φ1 ∧ Sat M t φ21
              -- Now we want to show Sat M t .bot = False. That's impossible.
              -- Wait, I got confused. Let me re-read.
              -- We're in T(.imp φ ψ) where ψ = .bot. So the goal after `rw [Satisfies.imp_iff]`
              -- and `intro hsat_φ` is: `Satisfies M t .bot`. That's `False`. So we need exfalso.
              -- From ih_φ1: T(φ1)@t → Sat M t φ1. We have T(φ1)@t ∈ b. So Sat M t φ1.
              -- From ih_φ21 (which is the IH for the `φ21` part of the nested imp): T(φ21)@t → Sat M t φ21.
              -- But I need the IH for φ21 specifically. In the induction, `ih_φ` is the IH for `φ` as a whole.
              -- φ = .imp φ1 (.imp φ21 .bot). The ih_φ here gives the truth lemma for the whole φ.
              -- But I also need the truth lemma for φ1 and φ21 separately.
              -- Hmm, this is a problem. The induction on `IsPropositional` gives me `ih_φ` for the whole φ,
              -- not for its sub-parts. But I'm inside a nested `induction hφ2 with | imp ...` which gives
              -- ih_φ22 etc. This is getting confusing.
              --
              -- Let me step back and realize: the `induction hφ2` and `induction hφ22` are inner inductions
              -- that give me ih_φ21 and ih_φ22 which ARE IHs for φ21 and φ22.
              -- In particular, for `hφ22 = IsPropositional.bot`:
              --   ih_φ22 would be the IH for `.bot` at time `t` (trivially: ...)
              -- But I also need ih_φ2 which is the IH for the middle part `.imp φ21 .bot`.
              -- From the outer induction on hφ2 (where hφ2 = .imp hφ21 hφ22):
              --   ih_φ2 = IH for `.imp φ21 φ22` = `.imp φ21 .bot`
              --
              -- Wait, I'm doing `induction hφ2` inside `induction hφ with | imp hφ1 hφ2 ih_φ1 ih_φ2 =>`.
              -- The `ih_φ2` from the outer induction is the IH for `.imp φ21 φ22` at time `t`.
              -- And inside `induction hφ22 with | bot => ...`, I have `ih_φ22` for `.bot`.
              --
              -- Hmm, but I need IH for φ1 (not φ). The ih_φ1 from the outer induction is the IH for φ1.
              -- And ih_φ2 is the IH for φ2 = .imp φ21 φ22.
              --
              -- Let me look at what I actually have in this case:
              -- ih_φ : IH for whole φ = .imp φ1 (.imp φ21 .bot) (at time t? or for any t?)
              --   Wait, the IH in the main lemma is: (ih_φ at time t)... no, actually the IH should be for ANY t.
              -- Actually in Lean 4, when doing `induction hprop with | imp hφ hψ ih_φ ih_ψ =>`, the ih_φ is the IH APPLIED to the current time t. But actually, the lemma has `t` as a variable not fixed in the induction, so...
              --
              -- Hmm, let me reconsider the structure of the main induction. The lemma is:
              -- `lemma temporalTruthLemma_propositional ... (φ : Formula Atom) (hprop : IsPropositional φ) (t : TimeIndex) : ...`
              -- When we `induction hprop`, the IH for `| imp hφ hψ ih_φ ih_ψ =>` would be:
              -- `ih_φ : ∀ (b : TBranch Atom) ... (t : TimeIndex), ...` (generalized over all parameters that come AFTER `φ` in the statement)
              -- But actually, since `b`, `ord`, `tracker`, `hH` are bound BEFORE `φ` in the lemma statement, the IH would be:
              -- `ih_φ : (stuff for φ)` with b, ord, tracker, hH FIXED.
              --
              -- This means the inner induction on `hφ2` etc. wouldn't work because we'd be inside the scope where b, ord, tracker, hH are fixed.
              --
              -- Wait, let me think about this more carefully. The lemma parameters are:
              -- b, ord, tracker, hH, φ, hprop, t
              -- When inducting on hprop, the variables that vary across recursive calls are φ and hprop.
              -- The IH `ih_φ` would be (for the `imp` case):
              -- `ih_φ : (b.any (fun sf => sf.sign == .pos && sf.label == t && sf.formula == φ) → Satisfies (extractModel b) t φ) ∧ ...`
              -- i.e., the SAME b, ord, tracker, hH, t are used.
              --
              -- So within the `imp` branch, `ih_φ` and `ih_ψ` are statements about φ and ψ WITH THE SAME b, ord, tracker, hH, t. Perfect, that's exactly what I need.
              --
              -- But then, when I do `induction hφ2` inside the `imp` branch, I'm NOT doing a valid induction on a hypothesis of the current goal - I'm trying to induct on a sub-hypothesis. That would give me NEW IHs for the sub-formula φ2, but those IHs would only be for the SAME b, ord, tracker, hH, t. That's fine!
              --
              -- But WAIT: inside the `imp` branch, I'm doing nested `induction hφ2`. But `ih_φ` is not a hypothesis in the current goal - it's a local term. So I can't do `induction hφ2` directly as a tactic after I've already unpacked `obtain ⟨ih_φ_pos, ih_φ_neg⟩ := ih_φ`.
              --
              -- Actually, Lean 4's `induction` tactic works on hypotheses in the context. If `hφ2 : IsPropositional φ2` is in the context, I can do `induction hφ2`.
              --
              -- But in the original `induction hprop with | imp hφ1 hφ2 ih_φ1 ih_φ2 =>`, we introduced `hφ2 : IsPropositional φ2` and `ih_φ2 : ...` into the context. Then I can do further `induction hφ2 with ...`.
              --
              -- Wait, but I named the variables in the outer induction as `hφ` and `hψ`, not `hφ1` and `hφ2`. Let me reconsider the naming.
              --
              -- The outer `induction hprop with | imp hφ hψ ih_φ ih_ψ =>` gives:
              -- hφ : IsPropositional φ
              -- hψ : IsPropositional ψ
              -- ih_φ : (IH for φ) = the conjunct
              -- ih_ψ : (IH for ψ) = the conjunct
              -- Then I do `obtain ⟨ih_φ_pos, ih_φ_neg⟩ := ih_φ` etc.
              --
              -- Now inside the `imp` case, I can do FURTHER nested induction on `hφ` to split φ into its cases.
              -- But the problem is: if I do `induction hφ with | imp hφ1 hφ2 ih_φ1 ih_φ2 =>`, this would give me NEW IHs `ih_φ1` and `ih_φ2` for φ1 and φ2. These are the IHs for the SAME b, ord, tracker, hH, t. And I also have the OUTER ih_φ (now split into ih_φ_pos, ih_φ_neg) which I've already obtained.
              --
              -- However, doing nested `induction` after already using `obtain` might cause issues. Let me restructure.

              -- For now, let me just use the OUTER ih_φ directly in the andPos case:
              -- I need: from T(φ1)@t ∈ b and T(φ21)@t ∈ b, derive a contradiction with hsat_φ.
              -- hsat_φ : Sat M t (.imp φ1 (.imp φ21 .bot)) = ¬(Sat M t φ1 → ¬Sat M t φ21)
              -- T(φ1)@t ∈ b → Sat M t φ1 (I need IH for φ1)
              -- T(φ21)@t ∈ b → Sat M t φ21 (I need IH for φ21)
              -- But I only have ih_φ_pos/neg for the WHOLE φ = .imp φ1 (.imp φ21 .bot)
              --
              -- This is the fundamental issue: I need IHs for subformulas, but the outer induction only gives me IHs for φ and ψ (and possibly their sub-IHs through nested induction).
              --
              -- Let me restructure the proof to use GENERALIZED induction that gives me sub-IHs.

              sorry
            | imp hψ1 hψ2 ih_ψ1 ih_ψ2 =>
              -- ψ = imp ψ1 ψ2, φ = imp φ1 (imp φ21 .bot): impPos fires
              simp only [tryAllPropRules, applyPropRule, List.map, List.find?,
                tempAndOf?, tempOrOf?, tempImpOf?, tempNegOf?,
                RuleResult.isApplicable] at hout
              obtain ⟨br, hbr_mem, hbr⟩ := hout
              simp only [List.mem_cons, List.mem_nil_iff, or_false] at hbr_mem
              rcases hbr_mem with rfl | rfl
              · have hfa : (⟨.neg, .imp φ1 (.imp φ21 .bot), t⟩ : TSF Atom) ∈ b :=
                    hbr _ (by simp)
                exact absurd hsat_φ
                  (ih_φ_neg (mem_to_any_neg b t (.imp φ1 (.imp φ21 .bot)) hfa))
              · have htψ : (⟨.pos, .imp _ _, t⟩ : TSF Atom) ∈ b := hbr _ (by simp)
                exact ih_ψ_pos (mem_to_any_pos b t (.imp _ _) htψ)
          | atom p22 =>
            -- φ = imp φ1 (imp φ21 (atom p22)): impPos fires (φ ≠ .imp _ .bot)
            induction hψ with
            | atom q =>
              simp only [tryAllPropRules, applyPropRule, List.map, List.find?,
                tempAndOf?, tempOrOf?, tempImpOf?, tempNegOf?,
                RuleResult.isApplicable] at hout
              obtain ⟨br, hbr_mem, hbr⟩ := hout
              simp only [List.mem_cons, List.mem_nil_iff, or_false] at hbr_mem
              rcases hbr_mem with rfl | rfl
              · have hfa : (⟨.neg, .imp φ1 (.imp φ21 (.atom p22)), t⟩ : TSF Atom) ∈ b :=
                    hbr _ (by simp)
                exact absurd hsat_φ
                  (ih_φ_neg (mem_to_any_neg b t (.imp φ1 (.imp φ21 (.atom p22))) hfa))
              · have htq : (⟨.pos, .atom q, t⟩ : TSF Atom) ∈ b := hbr _ (by simp)
                exact ih_ψ_pos (mem_to_any_pos b t (.atom q) htq)
            | bot =>
              -- ψ = bot, φ = imp φ1 (imp φ21 (atom p22)): negPos fires
              simp only [tryAllPropRules, applyPropRule, List.map, List.find?,
                tempAndOf?, tempOrOf?, tempImpOf?, tempNegOf?,
                RuleResult.isApplicable] at hout
              have hfa : (⟨.neg, .imp φ1 (.imp φ21 (.atom p22)), t⟩ : TSF Atom) ∈ b :=
                  hout _ (by simp)
              exact absurd hsat_φ
                (ih_φ_neg (mem_to_any_neg b t (.imp φ1 (.imp φ21 (.atom p22))) hfa))
            | imp hψ1 hψ2 ih_ψ1 ih_ψ2 =>
              simp only [tryAllPropRules, applyPropRule, List.map, List.find?,
                tempAndOf?, tempOrOf?, tempImpOf?, tempNegOf?,
                RuleResult.isApplicable] at hout
              obtain ⟨br, hbr_mem, hbr⟩ := hout
              simp only [List.mem_cons, List.mem_nil_iff, or_false] at hbr_mem
              rcases hbr_mem with rfl | rfl
              · have hfa : (⟨.neg, .imp φ1 (.imp φ21 (.atom p22)), t⟩ : TSF Atom) ∈ b :=
                    hbr _ (by simp)
                exact absurd hsat_φ
                  (ih_φ_neg (mem_to_any_neg b t (.imp φ1 (.imp φ21 (.atom p22))) hfa))
              · have htψ : (⟨.pos, .imp _ _, t⟩ : TSF Atom) ∈ b := hbr _ (by simp)
                exact ih_ψ_pos (mem_to_any_pos b t (.imp _ _) htψ)
          | imp hφ221 hφ222 ih_φ221 ih_φ222 =>
            -- φ = imp φ1 (imp φ21 (imp φ221 φ222)): impPos fires
            induction hψ with
            | atom q =>
              simp only [tryAllPropRules, applyPropRule, List.map, List.find?,
                tempAndOf?, tempOrOf?, tempImpOf?, tempNegOf?,
                RuleResult.isApplicable] at hout
              obtain ⟨br, hbr_mem, hbr⟩ := hout
              simp only [List.mem_cons, List.mem_nil_iff, or_false] at hbr_mem
              rcases hbr_mem with rfl | rfl
              · have hfa : (⟨.neg, .imp φ1 (.imp φ21 (.imp _ _)), t⟩ : TSF Atom) ∈ b :=
                    hbr _ (by simp)
                exact absurd hsat_φ
                  (ih_φ_neg (mem_to_any_neg b t (.imp φ1 (.imp φ21 (.imp _ _))) hfa))
              · have htq : (⟨.pos, .atom q, t⟩ : TSF Atom) ∈ b := hbr _ (by simp)
                exact ih_ψ_pos (mem_to_any_pos b t (.atom q) htq)
            | bot =>
              simp only [tryAllPropRules, applyPropRule, List.map, List.find?,
                tempAndOf?, tempOrOf?, tempImpOf?, tempNegOf?,
                RuleResult.isApplicable] at hout
              have hfa : (⟨.neg, .imp φ1 (.imp φ21 (.imp _ _)), t⟩ : TSF Atom) ∈ b :=
                  hout _ (by simp)
              exact absurd hsat_φ
                (ih_φ_neg (mem_to_any_neg b t (.imp φ1 (.imp φ21 (.imp _ _))) hfa))
            | imp hψ1 hψ2 ih_ψ1 ih_ψ2 =>
              simp only [tryAllPropRules, applyPropRule, List.map, List.find?,
                tempAndOf?, tempOrOf?, tempImpOf?, tempNegOf?,
                RuleResult.isApplicable] at hout
              obtain ⟨br, hbr_mem, hbr⟩ := hout
              simp only [List.mem_cons, List.mem_nil_iff, or_false] at hbr_mem
              rcases hbr_mem with rfl | rfl
              · have hfa : (⟨.neg, .imp φ1 (.imp φ21 (.imp _ _)), t⟩ : TSF Atom) ∈ b :=
                    hbr _ (by simp)
                exact absurd hsat_φ
                  (ih_φ_neg (mem_to_any_neg b t (.imp φ1 (.imp φ21 (.imp _ _))) hfa))
              · have htψ : (⟨.pos, .imp _ _, t⟩ : TSF Atom) ∈ b := hbr _ (by simp)
                exact ih_ψ_pos (mem_to_any_pos b t (.imp _ _) htψ)
    · -- F(.imp φ ψ)@t on branch → ¬Satisfies M t (φ → ψ)
      intro hmem_any hsat_imp
      -- F(.imp φ ψ)@t ∈ b
      have sf_mem : (⟨.neg, .imp φ ψ, t⟩ : TSF Atom) ∈ b :=
        any_neg_mem b t (.imp φ ψ) hmem_any
      -- Hintikka condition for this formula
      have hout := hrule ⟨.neg, .imp φ ψ, t⟩ sf_mem
      simp only [temporalApplyOne] at hout
      -- Case split on φ and ψ to determine which rule fires
      induction hφ with
      | atom p =>
        induction hψ with
        | atom q =>
          -- F(atom p → atom q): impNeg fires → T(atom p)@t, F(atom q)@t ∈ b
          simp only [tryAllPropRules, applyPropRule, List.map, List.find?,
            tempAndOf?, tempOrOf?, tempImpOf?, tempNegOf?,
            RuleResult.isApplicable] at hout
          have htp : (⟨.pos, .atom p, t⟩ : TSF Atom) ∈ b := hout _ (by simp)
          have hfq : (⟨.neg, .atom q, t⟩ : TSF Atom) ∈ b := hout _ (by simp)
          have hsat_p := ih_φ_pos (mem_to_any_pos b t (.atom p) htp)
          have hsat_q := ih_ψ_neg (mem_to_any_neg b t (.atom q) hfq)
          exact hsat_q (hsat_imp hsat_p)
        | bot =>
          -- F(atom p → bot) = F(¬atom p): negNeg fires → T(atom p)@t ∈ b
          simp only [tryAllPropRules, applyPropRule, List.map, List.find?,
            tempAndOf?, tempOrOf?, tempImpOf?, tempNegOf?,
            RuleResult.isApplicable] at hout
          have htp : (⟨.pos, .atom p, t⟩ : TSF Atom) ∈ b := hout _ (by simp)
          have hsat_p := ih_φ_pos (mem_to_any_pos b t (.atom p) htp)
          exact hsat_imp hsat_p (Satisfies.bot_false _ _)
        | imp hψ1 hψ2 ih_ψ1 ih_ψ2 =>
          -- F(atom p → imp ψ1 ψ2): impNeg fires
          simp only [tryAllPropRules, applyPropRule, List.map, List.find?,
            tempAndOf?, tempOrOf?, tempImpOf?, tempNegOf?,
            RuleResult.isApplicable] at hout
          have htp : (⟨.pos, .atom p, t⟩ : TSF Atom) ∈ b := hout _ (by simp)
          have hfψ : (⟨.neg, .imp _ _, t⟩ : TSF Atom) ∈ b := hout _ (by simp)
          have hsat_p := ih_φ_pos (mem_to_any_pos b t (.atom p) htp)
          have hnsat_ψ := ih_ψ_neg (mem_to_any_neg b t (.imp _ _) hfψ)
          exact hnsat_ψ (hsat_imp hsat_p)
      | bot =>
        induction hψ with
        | atom q =>
          -- F(bot → atom q): impNeg fires → T(bot)@t, F(atom q)@t ∈ b
          simp only [tryAllPropRules, applyPropRule, List.map, List.find?,
            tempAndOf?, tempOrOf?, tempImpOf?, tempNegOf?,
            RuleResult.isApplicable] at hout
          have htbot : (⟨.pos, .bot, t⟩ : TSF Atom) ∈ b := hout _ (by simp)
          exact absurd ⟨t, htbot⟩ (openBranch_noBotPos b ord tracker hopen)
        | bot =>
          -- F(bot → bot) = F(¬bot): negNeg fires → T(bot)@t ∈ b
          simp only [tryAllPropRules, applyPropRule, List.map, List.find?,
            tempAndOf?, tempOrOf?, tempImpOf?, tempNegOf?,
            RuleResult.isApplicable] at hout
          have htbot : (⟨.pos, .bot, t⟩ : TSF Atom) ∈ b := hout _ (by simp)
          exact absurd ⟨t, htbot⟩ (openBranch_noBotPos b ord tracker hopen)
        | imp hψ1 hψ2 ih_ψ1 ih_ψ2 =>
          -- F(bot → imp ψ1 ψ2): impNeg fires → T(bot)@t ∈ b
          simp only [tryAllPropRules, applyPropRule, List.map, List.find?,
            tempAndOf?, tempOrOf?, tempImpOf?, tempNegOf?,
            RuleResult.isApplicable] at hout
          have htbot : (⟨.pos, .bot, t⟩ : TSF Atom) ∈ b := hout _ (by simp)
          exact absurd ⟨t, htbot⟩ (openBranch_noBotPos b ord tracker hopen)
      | imp hφ1 hφ2 ih_φ1 ih_φ2 =>
        induction hφ2 with
        | bot =>
          -- φ = imp φ1 .bot (negation): orNeg fires → F(φ1)@t, F(ψ)@t ∈ b
          -- Except when φ = imp φ1 .bot and ψ = ... (orNeg)
          -- Wait: for F(.imp (.imp φ1 .bot) ψ), what fires?
          -- orNeg: matches .neg and tempOrOf? (.imp (.imp φ1 .bot) ψ) = some (φ1, ψ)
          -- orNeg is at position 4. andNeg is at position 2.
          -- andNeg: tempAndOf? (.imp (.imp φ1 .bot) ψ) = none (needs inner to be .imp _ (.imp _ .bot))
          -- orNeg fires! → linear [F(φ1)@t, F(ψ)@t]
          -- Wait, but F(φ1)@t here: φ1 could be anything, and the output is F(φ1)@t, F(ψ)@t
          -- Semantic: ¬Sat M t (φ1 → ψ) and we need to show False (from hsat_imp saying Sat M t (φ1 → ψ)... wait)
          -- Wait no: hsat_imp says Sat M t (.imp (.imp φ1 .bot) ψ) = ¬Sat M t (.imp φ1 .bot) → Sat M t ψ
          -- = ¬¬Sat M t φ1 → Sat M t ψ. And we need to show False.
          -- F(.imp (.imp φ1 .bot) ψ) on branch means it's false there: ¬Sat M t ((¬φ1) → ψ)
          -- = Sat M t (¬φ1) ∧ ¬Sat M t ψ = ¬Sat M t φ1 ∧ ¬Sat M t ψ
          -- orNeg: linear [F(φ1)@t, F(ψ)@t]
          induction hψ with
          | atom q =>
            simp only [tryAllPropRules, applyPropRule, List.map, List.find?,
              tempAndOf?, tempOrOf?, tempImpOf?, tempNegOf?,
              RuleResult.isApplicable] at hout
            have hfφ1 : (⟨.neg, φ1, t⟩ : TSF Atom) ∈ b := hout _ (by simp)
            have hfq : (⟨.neg, .atom q, t⟩ : TSF Atom) ∈ b := hout _ (by simp)
            have hnsat_φ1 := (ih_φ1 t).2 (mem_to_any_neg b t φ1 hfφ1)
            have hnsat_q := ih_ψ_neg (mem_to_any_neg b t (.atom q) hfq)
            -- hsat_imp : Sat M t (.imp (.imp φ1 .bot) (.atom q)) = ¬Sat M t (.imp φ1 .bot) → Sat M t (.atom q)
            --           = ¬¬Sat M t φ1 → Sat M t (.atom q)
            -- hnsat_φ1 : ¬Sat M t φ1
            -- hnsat_q : ¬Sat M t (.atom q)
            -- hsat_imp applied to... hmm, we need to derive False
            simp only [Satisfies, Satisfies.bot_false, not_false_eq_true] at hsat_imp
            -- hsat_imp : ¬Sat M t φ1 → Sat M t (.atom q)
            exact hnsat_q (hsat_imp hnsat_φ1)
          | bot =>
            -- F(imp (imp φ1 .bot) .bot) = F(¬¬φ1 → ⊥) = F(¬(¬¬φ1))
            -- negNeg fires: linear [T(.imp φ1 .bot)@t]
            simp only [tryAllPropRules, applyPropRule, List.map, List.find?,
              tempAndOf?, tempOrOf?, tempImpOf?, tempNegOf?,
              RuleResult.isApplicable] at hout
            -- For F(.imp (.imp φ1 .bot) .bot), negNeg fires because ψ = .bot
            -- negNeg: tempNegOf? matches .neg sign and c = .bot → linear [T(φ)@t]
            -- So it should give linear [T(.imp φ1 .bot)@t]
            have htφ : (⟨.pos, .imp φ1 .bot, t⟩ : TSF Atom) ∈ b := hout _ (by simp)
            -- T(.imp φ1 .bot)@t on branch
            -- ih_φ_pos: T(.imp φ1 .bot) → Sat M t (.imp φ1 .bot)
            have hsat_φ := ih_φ_pos (mem_to_any_pos b t (.imp φ1 .bot) htφ)
            -- hsat_imp : Sat M t (.imp (.imp φ1 .bot) .bot) = ¬Sat M t (.imp φ1 .bot) → False = Sat M t (.imp φ1 .bot)
            -- hsat_φ : Sat M t (.imp φ1 .bot)
            simp only [Satisfies] at hsat_imp
            exact hsat_imp hsat_φ (Satisfies.bot_false _ _)
          | imp hψ1 hψ2 ih_ψ1 ih_ψ2 =>
            simp only [tryAllPropRules, applyPropRule, List.map, List.find?,
              tempAndOf?, tempOrOf?, tempImpOf?, tempNegOf?,
              RuleResult.isApplicable] at hout
            have hfφ1 : (⟨.neg, φ1, t⟩ : TSF Atom) ∈ b := hout _ (by simp)
            have hfψ : (⟨.neg, .imp _ _, t⟩ : TSF Atom) ∈ b := hout _ (by simp)
            have hnsat_φ1 := (ih_φ1 t).2 (mem_to_any_neg b t φ1 hfφ1)
            have hnsat_ψ := ih_ψ_neg (mem_to_any_neg b t (.imp _ _) hfψ)
            simp only [Satisfies, Satisfies.bot_false, not_false_eq_true] at hsat_imp
            exact hnsat_ψ (hsat_imp hnsat_φ1)
        | atom p2 =>
          -- φ = imp φ1 (atom p2): impNeg or negPos
          induction hψ with
          | atom q =>
            simp only [tryAllPropRules, applyPropRule, List.map, List.find?,
              tempAndOf?, tempOrOf?, tempImpOf?, tempNegOf?,
              RuleResult.isApplicable] at hout
            have htφ : (⟨.pos, .imp φ1 (.atom p2), t⟩ : TSF Atom) ∈ b := hout _ (by simp)
            have hfψ : (⟨.neg, .atom q, t⟩ : TSF Atom) ∈ b := hout _ (by simp)
            have hsat_φ := ih_φ_pos (mem_to_any_pos b t (.imp φ1 (.atom p2)) htφ)
            have hnsat_q := ih_ψ_neg (mem_to_any_neg b t (.atom q) hfψ)
            exact hnsat_q (hsat_imp hsat_φ)
          | bot =>
            -- F(.imp (.imp φ1 (.atom p2)) .bot): negNeg fires
            simp only [tryAllPropRules, applyPropRule, List.map, List.find?,
              tempAndOf?, tempOrOf?, tempImpOf?, tempNegOf?,
              RuleResult.isApplicable] at hout
            have htφ : (⟨.pos, .imp φ1 (.atom p2), t⟩ : TSF Atom) ∈ b := hout _ (by simp)
            have hsat_φ := ih_φ_pos (mem_to_any_pos b t (.imp φ1 (.atom p2)) htφ)
            simp only [Satisfies] at hsat_imp
            exact hsat_imp hsat_φ (Satisfies.bot_false _ _)
          | imp hψ1 hψ2 ih_ψ1 ih_ψ2 =>
            simp only [tryAllPropRules, applyPropRule, List.map, List.find?,
              tempAndOf?, tempOrOf?, tempImpOf?, tempNegOf?,
              RuleResult.isApplicable] at hout
            have htφ : (⟨.pos, .imp φ1 (.atom p2), t⟩ : TSF Atom) ∈ b := hout _ (by simp)
            have hfψ : (⟨.neg, .imp _ _, t⟩ : TSF Atom) ∈ b := hout _ (by simp)
            have hsat_φ := ih_φ_pos (mem_to_any_pos b t (.imp φ1 (.atom p2)) htφ)
            have hnsat_ψ := ih_ψ_neg (mem_to_any_neg b t (.imp _ _) hfψ)
            exact hnsat_ψ (hsat_imp hsat_φ)
        | imp hφ21 hφ22 ih_φ21 ih_φ22 =>
          -- φ = imp φ1 (imp φ21 φ22)
          induction hφ22 with
          | bot =>
            -- φ = imp φ1 (imp φ21 .bot): andNeg or negNeg/impNeg
            induction hψ with
            | atom q =>
              -- F(.imp (.imp φ1 (.imp φ21 .bot)) (.atom q)): impNeg fires
              simp only [tryAllPropRules, applyPropRule, List.map, List.find?,
                tempAndOf?, tempOrOf?, tempImpOf?, tempNegOf?,
                RuleResult.isApplicable] at hout
              have htφ : (⟨.pos, .imp φ1 (.imp φ21 .bot), t⟩ : TSF Atom) ∈ b :=
                  hout _ (by simp)
              have hfq : (⟨.neg, .atom q, t⟩ : TSF Atom) ∈ b := hout _ (by simp)
              have hsat_φ := ih_φ_pos (mem_to_any_pos b t (.imp φ1 (.imp φ21 .bot)) htφ)
              have hnsat_q := ih_ψ_neg (mem_to_any_neg b t (.atom q) hfq)
              exact hnsat_q (hsat_imp hsat_φ)
            | bot =>
              -- F(.imp (.imp φ1 (.imp φ21 .bot)) .bot): andNeg fires (ψ = .bot, φ = .imp φ1 (.imp φ21 .bot))
              -- andNeg: branching [[F(φ1)@t], [F(φ21)@t]]
              simp only [tryAllPropRules, applyPropRule, List.map, List.find?,
                tempAndOf?, tempOrOf?, tempImpOf?, tempNegOf?,
                RuleResult.isApplicable] at hout
              obtain ⟨br, hbr_mem, hbr⟩ := hout
              simp only [List.mem_cons, List.mem_nil_iff, or_false] at hbr_mem
              rcases hbr_mem with rfl | rfl
              · have hfφ1 : (⟨.neg, φ1, t⟩ : TSF Atom) ∈ b := hbr _ (by simp)
                -- Need IH for φ1. ih_φ_neg is for the whole φ = .imp φ1 (.imp φ21 .bot)
                -- We need ih for φ1. But ih_φ1 from inner `induction hφ with | imp hφ1 hφ2 ih_φ1 ih_φ2` gives IH for φ1!
                have hnsat_φ1 := (ih_φ1 t).2 (mem_to_any_neg b t φ1 hfφ1)
                -- hsat_imp : Sat M t (.imp (.imp φ1 (.imp φ21 .bot)) .bot)
                --           = ¬Sat M t (.imp φ1 (.imp φ21 .bot)) → False
                --           = Sat M t (.imp φ1 (.imp φ21 .bot))  -- since ¬¬X = X classically
                -- Wait: ¬Sat M t (.imp φ1 (.imp φ21 .bot)) means
                -- Sat M t φ1 ∧ ¬Sat M t (.imp φ21 .bot) = Sat M t φ1 ∧ Sat M t φ21
                -- hsat_imp : Sat M t (.imp (.imp φ1 (.imp φ21 .bot)) .bot)
                --           = (Sat M t (.imp φ1 (.imp φ21 .bot)) → False)
                --           = (Sat M t φ1 → ¬Sat M t φ21) → False -- ???
                -- Hmm, let me be precise:
                -- .imp (.imp φ1 (.imp φ21 .bot)) .bot
                -- = ((.imp φ1 (.imp φ21 .bot)) → .bot)
                -- Sat M t (imp A B) = Sat M t A → Sat M t B
                -- So Sat M t (.imp (.imp φ1 (.imp φ21 .bot)) .bot)
                --   = (Sat M t (.imp φ1 (.imp φ21 .bot)) → Sat M t .bot)
                --   = ((Sat M t φ1 → Sat M t (.imp φ21 .bot)) → False)
                --   = ((Sat M t φ1 → (Sat M t φ21 → False)) → False)
                --   = ((Sat M t φ1 → ¬Sat M t φ21) → False)
                --   = ¬(Sat M t φ1 → ¬Sat M t φ21)
                --   = Sat M t φ1 ∧ ¬¬Sat M t φ21 (classically)
                --   = Sat M t φ1 ∧ Sat M t φ21
                -- So hsat_imp says Sat M t φ1 and Sat M t φ21.
                -- But hnsat_φ1 says ¬Sat M t φ1. Contradiction!
                simp only [Satisfies, Satisfies.bot_false, not_false_eq_true] at hsat_imp
                exact hsat_imp (fun hφ1_sat => hnsat_φ1 hφ1_sat)
              · have hfφ21 : (⟨.neg, φ21, t⟩ : TSF Atom) ∈ b := hbr _ (by simp)
                have hnsat_φ21 := (ih_φ21 t).2 (mem_to_any_neg b t φ21 hfφ21)
                simp only [Satisfies, Satisfies.bot_false, not_false_eq_true] at hsat_imp
                exact hsat_imp (fun _ hφ21_sat => hnsat_φ21 hφ21_sat)
            | imp hψ1 hψ2 ih_ψ1 ih_ψ2 =>
              -- F(.imp (.imp φ1 (.imp φ21 .bot)) (.imp ψ1 ψ2)): impNeg fires
              simp only [tryAllPropRules, applyPropRule, List.map, List.find?,
                tempAndOf?, tempOrOf?, tempImpOf?, tempNegOf?,
                RuleResult.isApplicable] at hout
              have htφ : (⟨.pos, .imp φ1 (.imp φ21 .bot), t⟩ : TSF Atom) ∈ b :=
                  hout _ (by simp)
              have hfψ : (⟨.neg, .imp _ _, t⟩ : TSF Atom) ∈ b := hout _ (by simp)
              have hsat_φ := ih_φ_pos (mem_to_any_pos b t (.imp φ1 (.imp φ21 .bot)) htφ)
              have hnsat_ψ := ih_ψ_neg (mem_to_any_neg b t (.imp _ _) hfψ)
              exact hnsat_ψ (hsat_imp hsat_φ)
          | atom p22 =>
            -- φ = imp φ1 (imp φ21 (atom p22)): impNeg fires
            induction hψ with
            | atom q =>
              simp only [tryAllPropRules, applyPropRule, List.map, List.find?,
                tempAndOf?, tempOrOf?, tempImpOf?, tempNegOf?,
                RuleResult.isApplicable] at hout
              have htφ : (⟨.pos, .imp φ1 (.imp φ21 (.atom p22)), t⟩ : TSF Atom) ∈ b :=
                  hout _ (by simp)
              have hfq : (⟨.neg, .atom q, t⟩ : TSF Atom) ∈ b := hout _ (by simp)
              have hsat_φ := ih_φ_pos (mem_to_any_pos b t (.imp φ1 (.imp φ21 (.atom p22))) htφ)
              have hnsat_q := ih_ψ_neg (mem_to_any_neg b t (.atom q) hfq)
              exact hnsat_q (hsat_imp hsat_φ)
            | bot =>
              simp only [tryAllPropRules, applyPropRule, List.map, List.find?,
                tempAndOf?, tempOrOf?, tempImpOf?, tempNegOf?,
                RuleResult.isApplicable] at hout
              have htφ : (⟨.pos, .imp φ1 (.imp φ21 (.atom p22)), t⟩ : TSF Atom) ∈ b :=
                  hout _ (by simp)
              have hsat_φ := ih_φ_pos (mem_to_any_pos b t (.imp φ1 (.imp φ21 (.atom p22))) htφ)
              simp only [Satisfies] at hsat_imp
              exact hsat_imp hsat_φ (Satisfies.bot_false _ _)
            | imp hψ1 hψ2 ih_ψ1 ih_ψ2 =>
              simp only [tryAllPropRules, applyPropRule, List.map, List.find?,
                tempAndOf?, tempOrOf?, tempImpOf?, tempNegOf?,
                RuleResult.isApplicable] at hout
              have htφ : (⟨.pos, .imp φ1 (.imp φ21 (.atom p22)), t⟩ : TSF Atom) ∈ b :=
                  hout _ (by simp)
              have hfψ : (⟨.neg, .imp _ _, t⟩ : TSF Atom) ∈ b := hout _ (by simp)
              have hsat_φ := ih_φ_pos (mem_to_any_pos b t (.imp φ1 (.imp φ21 (.atom p22))) htφ)
              have hnsat_ψ := ih_ψ_neg (mem_to_any_neg b t (.imp _ _) hfψ)
              exact hnsat_ψ (hsat_imp hsat_φ)
          | imp hφ221 hφ222 ih_φ221 ih_φ222 =>
            -- φ = imp φ1 (imp φ21 (imp φ221 φ222)): impNeg fires
            induction hψ with
            | atom q =>
              simp only [tryAllPropRules, applyPropRule, List.map, List.find?,
                tempAndOf?, tempOrOf?, tempImpOf?, tempNegOf?,
                RuleResult.isApplicable] at hout
              have htφ : (⟨.pos, .imp φ1 (.imp φ21 (.imp _ _)), t⟩ : TSF Atom) ∈ b :=
                  hout _ (by simp)
              have hfq : (⟨.neg, .atom q, t⟩ : TSF Atom) ∈ b := hout _ (by simp)
              have hsat_φ := ih_φ_pos (mem_to_any_pos b t (.imp φ1 (.imp φ21 (.imp _ _))) htφ)
              have hnsat_q := ih_ψ_neg (mem_to_any_neg b t (.atom q) hfq)
              exact hnsat_q (hsat_imp hsat_φ)
            | bot =>
              simp only [tryAllPropRules, applyPropRule, List.map, List.find?,
                tempAndOf?, tempOrOf?, tempImpOf?, tempNegOf?,
                RuleResult.isApplicable] at hout
              have htφ : (⟨.pos, .imp φ1 (.imp φ21 (.imp _ _)), t⟩ : TSF Atom) ∈ b :=
                  hout _ (by simp)
              have hsat_φ := ih_φ_pos (mem_to_any_pos b t (.imp φ1 (.imp φ21 (.imp _ _))) htφ)
              simp only [Satisfies] at hsat_imp
              exact hsat_imp hsat_φ (Satisfies.bot_false _ _)
            | imp hψ1 hψ2 ih_ψ1 ih_ψ2 =>
              simp only [tryAllPropRules, applyPropRule, List.map, List.find?,
                tempAndOf?, tempOrOf?, tempImpOf?, tempNegOf?,
                RuleResult.isApplicable] at hout
              have htφ : (⟨.pos, .imp φ1 (.imp φ21 (.imp _ _)), t⟩ : TSF Atom) ∈ b :=
                  hout _ (by simp)
              have hfψ : (⟨.neg, .imp _ _, t⟩ : TSF Atom) ∈ b := hout _ (by simp)
              have hsat_φ := ih_φ_pos (mem_to_any_pos b t (.imp φ1 (.imp φ21 (.imp _ _))) htφ)
              have hnsat_ψ := ih_ψ_neg (mem_to_any_neg b t (.imp _ _) hfψ)
              exact hnsat_ψ (hsat_imp hsat_φ)

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
