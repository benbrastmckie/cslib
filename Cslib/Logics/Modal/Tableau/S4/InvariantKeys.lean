/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Modal.Tableau.S4.Universe
public import Cslib.Logics.Modal.Tableau.S4.BirthKey
public import Cslib.Logics.Modal.Tableau.S4.Guard
public import Cslib.Logics.Modal.Tableau.S4.Driver

/-! # S4 Loop-Checking: `S4LoopInv` Keys-Facing Field Preservation

The six keys-facing `S4LoopInv` field preservation pairs (`keyLowerBd`, `keysInUniverse`,
`keysTotal`, `keysDistinct`, `keysWorldsKnown`, `keysOriginS4`), each proved for both the
bespoke keyed stepper (`modalStepBranchS4Keyed`) and the ordered stepper
(`modalStepBranchS4KeyedOrdered`).

## Why a separate module

The invariant material is split four ways (`InvariantKeys`, `InvariantAcc`, `Invariant`,
`HintikkaInvariant`) rather than kept as one module: a single `Invariant.lean` would be
4,445 lines, larger than every file in `Modal/Tableau/` except `LoopChecking`,
`FrameCompleteness`, and `FrameSoundness`. This is the largest of the four
(~1,725 lines) -- it holds every field whose preservation argument routes through the birth-key
bookkeeping (`BirthKey`/`Guard`'s `keysUpdate_preserves_keysDistinct`) rather than through
accessibility/expansion facts (`InvariantAcc`, Phase 10).

**Research correction 3 of 4**: `successorBirthContent_{boxNeg,diamondPos}_subset_relevantSetFinset`
live here, not in `BirthKey`, despite their `successorBirthContent` name prefix -- they
reference `modalApplyOneS4KeyedMint` and its equation lemmas (`Driver`-layer), and
`keyLowerBd`'s preservation proof consumes them directly. Both remain `private`: the
regenerated dependency graph shows no consumer outside this module.

## Main Results
- `modalStepBranchS4{,KeyedOrdered}_preserves_keyLowerBd`: birth-key lower-bound preservation.
- `modalStepBranchS4{,KeyedOrdered}_preserves_keysInUniverse`: universe-membership preservation.
- `modalStepBranchS4{,KeyedOrdered}_preserves_keysTotal`: totality preservation.
- `modalStepBranchS4{,KeyedOrdered}_preserves_keysDistinct`: distinctness preservation.
- `modalStepBranchS4{,KeyedOrdered}_preserves_keysWorldsKnown`: worlds-known preservation.
- `modalStepBranchS4{Keyed,KeyedOrdered}_preserves_keysOriginS4`: origin-edge preservation.
-/

@[expose] public section

namespace Cslib.Logic.Modal.Tableau

open Cslib.Logic.Tableau Cslib.Logic.Modal

variable {Atom : Type*} [DecidableEq Atom] [Hashable Atom]

omit [Hashable Atom] in
/-- **`keyLowerBd`'s minting case, box-negative shape**: the prospective birth content computed
PRE-step (`successorBirthContent`) is a subset of the freshly-minted world's relevant set
computed POST-step (`relevantSetFinset` over `newForms ++ b`). Consumes the additive keyed
mint's literal box-neg minting payload (`modalApplyOneS4KeyedMint_boxNeg_eq_S4`) via the
`hnewForms` hypothesis (stated in terms of `modalApplyOneS4KeyedMint` rather than the raw
payload literal, so the caller only needs its actual output, not to hand-reconstruct its list
shape) plus the branch-closure witness fact (`hb`/`hsf`, via `modalUniverseS4_mem_formula`/
`modalSubfmls_trans`) that the witness formula `φ` itself lies in `signedSubfmls φ₀`. The two
box-plus disjuncts (`successorBirthContent`'s third/fourth) land inside `boxPlusExtraS4`, which
is why `newForms` must already be the ENRICHED keyed payload -- the raw `modalApplyOne` payload
never contains the boxed transmission (report §4). -/
private lemma successorBirthContent_boxNeg_subset_relevantSetFinset
    (φ₀ : Proposition Atom) (b : List (SignedFormula (Proposition Atom) WorldIndex))
    (acc : Accessibility) (w : WorldIndex) (φ : Proposition Atom)
    (hb : ∀ x ∈ b, x ∈ modalUniverseS4 φ₀)
    (hsf : (⟨.neg, .box φ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b)
    (newForms : List (SignedFormula (Proposition Atom) WorldIndex))
    (hnewForms : (modalApplyOneS4KeyedMint
        (⟨.neg, .box φ, w⟩ : SignedFormula (Proposition Atom) WorldIndex)
        b acc).fst = RuleResult.linear newForms) :
    successorBirthContent φ₀ b .neg φ w ⊆
      relevantSetFinset φ₀ (newForms ++ b) (modalNextWorld b) := by
  rw [congrArg Prod.fst (modalApplyOneS4KeyedMint_boxNeg_eq_S4 b acc φ w)] at hnewForms
  injection hnewForms with hnewForms
  subst hnewForms
  have hφsub : φ ∈ modalSubfmls φ₀ := by
    have h1 : (Proposition.box φ) ∈ modalSubfmls φ₀ := modalUniverseS4_mem_formula (hb _ hsf)
    have h2 : φ ∈ modalSubfmls (Proposition.box φ) :=
      List.mem_cons_of_mem _ (modalSubfmls_self_mem φ)
    exact modalSubfmls_trans h2 h1
  have hwit : ((Sign.neg, φ) : Sign × Proposition Atom) ∈ signedSubfmls φ₀ :=
    mem_signedSubfmls_of_formula_S4 .neg hφsub
  intro p hp
  simp only [successorBirthContent, Finset.mem_insert, Finset.mem_filter] at hp
  rcases hp with rfl | ⟨hpmem, hdisj⟩
  · simp only [relevantSetFinset, Finset.mem_filter]
    refine ⟨hwit, any_beq_of_mem_S4 ?_⟩
    exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
      List.mem_cons_self))
  · simp only [relevantSetFinset, Finset.mem_filter]
    refine ⟨hpmem, any_beq_of_mem_S4 ?_⟩
    rcases hdisj with ⟨hp1, hpb⟩ | ⟨hp1, hpb⟩ | ⟨hp1, hpb⟩ | ⟨hp1, hpb⟩
    · -- box-positive transmission: p.1 = pos, T(□p.2)@w ∈ b
      have hbmem : (⟨.pos, .box p.2, w⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b :=
        mem_of_any_beq_S4 hpb
      have hbp : (p.2, w) ∈ boxPositivesOf b := by
        simp only [boxPositivesOf, List.mem_filterMap]
        exact ⟨⟨.pos, .box p.2, w⟩, hbmem, by simp⟩
      have hdedup : b.any (· == (⟨.pos, p.2, modalNextWorld b⟩ :
          SignedFormula (Proposition Atom) WorldIndex)) = false :=
        modalNextWorld_fresh_beq_S4 b _ rfl
      have htarget : (⟨p.1, p.2, modalNextWorld b⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈
          (boxPositivesOf b).filterMap (fun (ψ, src) =>
            if src == w then
              let sf' : SignedFormula (Proposition Atom) WorldIndex := ⟨.pos, ψ, modalNextWorld b⟩
              if b.any (· == sf') then none else some sf'
            else none) := by
        rw [hp1, List.mem_filterMap]
        exact ⟨(p.2, w), hbp, by simp [hdedup]⟩
      exact List.mem_append_left _ (List.mem_append_left _
        (List.mem_append_left _ (List.mem_cons_of_mem _ htarget)))
    · -- diamond-negative transmission: p.1 = neg, F(◇p.2)@w ∈ b
      have hbmem : (⟨.neg, .diamond p.2, w⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b :=
        mem_of_any_beq_S4 hpb
      have hdedup : b.any (· == (⟨.neg, p.2, modalNextWorld b⟩ :
          SignedFormula (Proposition Atom) WorldIndex)) = false :=
        modalNextWorld_fresh_beq_S4 b _ rfl
      have htarget : (⟨p.1, p.2, modalNextWorld b⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈
          b.filterMap (fun sf' =>
            if sf'.sign == .neg && sf'.label == w then
              match sf'.formula with
              | .diamond ψ =>
                let prop : SignedFormula (Proposition Atom) WorldIndex :=
                  ⟨.neg, ψ, modalNextWorld b⟩
                if b.any (· == prop) then none else some prop
              | _ => none
            else none) := by
        rw [hp1, List.mem_filterMap]
        exact ⟨⟨.neg, .diamond p.2, w⟩, hbmem, by simp [hdedup]⟩
      exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ htarget))
    · -- box-plus positive: p.1 = pos, p.2 = box ψ, T(□ψ)@w ∈ b -- own box-positive, BOXED
      obtain ⟨ψ, hp2, hbmem⟩ := boxPlus_pos_disjunct_elim hpb
      have hbp : (ψ, w) ∈ boxPositivesOf b := by
        simp only [boxPositivesOf, List.mem_filterMap]
        exact ⟨⟨.pos, .box ψ, w⟩, hbmem, by simp⟩
      have hdedup : b.any (· == (⟨.pos, .box ψ, modalNextWorld b⟩ :
          SignedFormula (Proposition Atom) WorldIndex)) = false :=
        modalNextWorld_fresh_beq_S4 b _ rfl
      have htarget : (⟨p.1, p.2, modalNextWorld b⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈
          boxPlusExtraS4 b w := by
        rw [hp1, hp2]
        simp only [boxPlusExtraS4, List.mem_append, List.mem_filterMap]
        exact Or.inl ⟨(ψ, w), hbp, by simp [hdedup]⟩
      exact List.mem_append_left _ (List.mem_append_right _ htarget)
    · -- box-plus negative: p.1 = neg, p.2 = diamond ψ, F(◇ψ)@w ∈ b -- own diamond-negative, BOXED
      obtain ⟨ψ, hp2, hbmem⟩ := boxPlus_neg_disjunct_elim hpb
      have hdedup : b.any (· == (⟨.neg, .diamond ψ, modalNextWorld b⟩ :
          SignedFormula (Proposition Atom) WorldIndex)) = false :=
        modalNextWorld_fresh_beq_S4 b _ rfl
      have htarget : (⟨p.1, p.2, modalNextWorld b⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈
          boxPlusExtraS4 b w := by
        rw [hp1, hp2]
        simp only [boxPlusExtraS4, List.mem_append]
        refine Or.inr ?_
        simp only [List.mem_filterMap]
        exact ⟨⟨.neg, .diamond ψ, w⟩, hbmem, by simp [hdedup]⟩
      exact List.mem_append_left _ (List.mem_append_right _ htarget)

omit [Hashable Atom] in
/-- **`keyLowerBd`'s minting case, diamond-positive shape** (dual of the box-negative case):
the prospective birth content computed PRE-step is a subset of the freshly-minted world's
relevant set computed POST-step. -/
private lemma successorBirthContent_diamondPos_subset_relevantSetFinset
    (φ₀ : Proposition Atom) (b : List (SignedFormula (Proposition Atom) WorldIndex))
    (acc : Accessibility) (w : WorldIndex) (φ : Proposition Atom)
    (hb : ∀ x ∈ b, x ∈ modalUniverseS4 φ₀)
    (hsf : (⟨.pos, .diamond φ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b)
    (newForms : List (SignedFormula (Proposition Atom) WorldIndex))
    (hnewForms : (modalApplyOneS4KeyedMint
        (⟨.pos, .diamond φ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) b acc).fst
        = RuleResult.linear newForms) :
    successorBirthContent φ₀ b .pos φ w ⊆
      relevantSetFinset φ₀ (newForms ++ b) (modalNextWorld b) := by
  rw [congrArg Prod.fst (modalApplyOneS4KeyedMint_diaPos_eq_S4 b acc φ w)] at hnewForms
  injection hnewForms with hnewForms
  subst hnewForms
  have hφsub : φ ∈ modalSubfmls φ₀ := by
    have h1 : (Proposition.diamond φ) ∈ modalSubfmls φ₀ := modalUniverseS4_mem_formula (hb _ hsf)
    have h2 : φ ∈ modalSubfmls (Proposition.diamond φ) :=
      List.mem_cons_of_mem _ (modalSubfmls_self_mem φ)
    exact modalSubfmls_trans h2 h1
  have hwit : ((Sign.pos, φ) : Sign × Proposition Atom) ∈ signedSubfmls φ₀ :=
    mem_signedSubfmls_of_formula_S4 .pos hφsub
  intro p hp
  simp only [successorBirthContent, Finset.mem_insert, Finset.mem_filter] at hp
  rcases hp with rfl | ⟨hpmem, hdisj⟩
  · simp only [relevantSetFinset, Finset.mem_filter]
    refine ⟨hwit, any_beq_of_mem_S4 ?_⟩
    exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
      List.mem_cons_self))
  · simp only [relevantSetFinset, Finset.mem_filter]
    refine ⟨hpmem, any_beq_of_mem_S4 ?_⟩
    rcases hdisj with ⟨hp1, hpb⟩ | ⟨hp1, hpb⟩ | ⟨hp1, hpb⟩ | ⟨hp1, hpb⟩
    · -- box-positive transmission: p.1 = pos, T(□p.2)@w ∈ b
      have hbmem : (⟨.pos, .box p.2, w⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b :=
        mem_of_any_beq_S4 hpb
      have hbp : (p.2, w) ∈ boxPositivesOf b := by
        simp only [boxPositivesOf, List.mem_filterMap]
        exact ⟨⟨.pos, .box p.2, w⟩, hbmem, by simp⟩
      have hdedup : b.any (· == (⟨.pos, p.2, modalNextWorld b⟩ :
          SignedFormula (Proposition Atom) WorldIndex)) = false :=
        modalNextWorld_fresh_beq_S4 b _ rfl
      have htarget : (⟨p.1, p.2, modalNextWorld b⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈
          (boxPositivesOf b).filterMap (fun (ψ, src) =>
            if src == w then
              let sf' : SignedFormula (Proposition Atom) WorldIndex := ⟨.pos, ψ, modalNextWorld b⟩
              if b.any (· == sf') then none else some sf'
            else none) := by
        rw [hp1, List.mem_filterMap]
        exact ⟨(p.2, w), hbp, by simp [hdedup]⟩
      exact List.mem_append_left _ (List.mem_append_left _
        (List.mem_append_left _ (List.mem_cons_of_mem _ htarget)))
    · -- diamond-negative transmission: p.1 = neg, F(◇p.2)@w ∈ b
      have hbmem : (⟨.neg, .diamond p.2, w⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b :=
        mem_of_any_beq_S4 hpb
      have hdedup : b.any (· == (⟨.neg, p.2, modalNextWorld b⟩ :
          SignedFormula (Proposition Atom) WorldIndex)) = false :=
        modalNextWorld_fresh_beq_S4 b _ rfl
      have htarget : (⟨p.1, p.2, modalNextWorld b⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈
          b.filterMap (fun sf' =>
            if sf'.sign == .neg && sf'.label == w then
              match sf'.formula with
              | .diamond ψ =>
                let prop : SignedFormula (Proposition Atom) WorldIndex :=
                  ⟨.neg, ψ, modalNextWorld b⟩
                if b.any (· == prop) then none else some prop
              | _ => none
            else none) := by
        rw [hp1, List.mem_filterMap]
        exact ⟨⟨.neg, .diamond p.2, w⟩, hbmem, by simp [hdedup]⟩
      exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ htarget))
    · -- box-plus positive: p.1 = pos, p.2 = box ψ, T(□ψ)@w ∈ b -- own box-positive, BOXED
      obtain ⟨ψ, hp2, hbmem⟩ := boxPlus_pos_disjunct_elim hpb
      have hbp : (ψ, w) ∈ boxPositivesOf b := by
        simp only [boxPositivesOf, List.mem_filterMap]
        exact ⟨⟨.pos, .box ψ, w⟩, hbmem, by simp⟩
      have hdedup : b.any (· == (⟨.pos, .box ψ, modalNextWorld b⟩ :
          SignedFormula (Proposition Atom) WorldIndex)) = false :=
        modalNextWorld_fresh_beq_S4 b _ rfl
      have htarget : (⟨p.1, p.2, modalNextWorld b⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈
          boxPlusExtraS4 b w := by
        rw [hp1, hp2]
        simp only [boxPlusExtraS4, List.mem_append, List.mem_filterMap]
        exact Or.inl ⟨(ψ, w), hbp, by simp [hdedup]⟩
      exact List.mem_append_left _ (List.mem_append_right _ htarget)
    · -- box-plus negative: p.1 = neg, p.2 = diamond ψ, F(◇ψ)@w ∈ b -- own diamond-negative, BOXED
      obtain ⟨ψ, hp2, hbmem⟩ := boxPlus_neg_disjunct_elim hpb
      have hdedup : b.any (· == (⟨.neg, .diamond ψ, modalNextWorld b⟩ :
          SignedFormula (Proposition Atom) WorldIndex)) = false :=
        modalNextWorld_fresh_beq_S4 b _ rfl
      have htarget : (⟨p.1, p.2, modalNextWorld b⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈
          boxPlusExtraS4 b w := by
        rw [hp1, hp2]
        simp only [boxPlusExtraS4, List.mem_append]
        refine Or.inr ?_
        simp only [List.mem_filterMap]
        exact ⟨⟨.neg, .diamond ψ, w⟩, hbmem, by simp [hdedup]⟩
      exact List.mem_append_left _ (List.mem_append_right _ htarget)

/-! ## Assembling `keyLowerBd`'s Preservation -/

/-- **`keyLowerBd`'s driver-level preservation**: every key
recorded after an S4Keyed step remains a lower bound on its live relevant set, over EVERY
branch the step produces. Assembles `modalStepBranchS4Keyed_branch_superset` (handles every
OLD key uniformly, via `relevantSetFinset_mono`, regardless of which rule fired) with the two
closed minting-content subset lemmas (`successorBirthContent_boxNeg_subset_relevantSetFinset`
/ `_diamondPos_subset_relevantSetFinset`, for the NEW key at the two minting leaves). -/
lemma modalStepBranchS4_preserves_keyLowerBd (φ₀ : Proposition Atom)
    (b e : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (keys : List (WorldIndex × Finset (Sign × Proposition Atom)))
    (newBs newExps : List (List (SignedFormula (Proposition Atom) WorldIndex)))
    (newAcc : Accessibility) (keys' : List (WorldIndex × Finset (Sign × Proposition Atom)))
    (hb : ∀ x ∈ b, x ∈ modalUniverseS4 φ₀)
    (hLB : ∀ w k, (w, k) ∈ keys → k ⊆ relevantSetFinset φ₀ b w)
    (hstep : modalStepBranchS4Keyed φ₀ b e acc keys = some (newBs, newExps, newAcc, keys')) :
    ∀ b' ∈ newBs, ∀ w k, (w, k) ∈ keys' → k ⊆ relevantSetFinset φ₀ b' w := by
  have hsuper := modalStepBranchS4Keyed_branch_superset φ₀ b e acc keys newBs newExps newAcc
    keys' hstep
  have hold : ∀ b' ∈ newBs, ∀ w k, (w, k) ∈ keys → k ⊆ relevantSetFinset φ₀ b' w :=
    fun b' hb' w k hwk => (hLB w k hwk).trans (relevantSetFinset_mono φ₀ b b' w (hsuper b' hb'))
  have hstep0 := hstep
  unfold modalStepBranchS4Keyed at hstep0
  obtain ⟨sf, hsfmem, hsf⟩ := List.exists_of_findSome?_eq_some hstep0
  split_ifs at hsf with hexp
  rcases hpair : modalApplyOneS4Keyed φ₀ keys sf b acc with ⟨result, newAcc0⟩
  rw [hpair] at hsf
  dsimp only at hsf
  have hkeq := modalStepBranchS4Keyed_result_keys_eq result newAcc0 b e sf _ newBs newExps
    newAcc keys' hsf
  intro b' hb' w k hwk
  rw [hkeq] at hwk
  rcases hs : sf.sign with _ | _ <;> rcases hf : sf.formula with _ | _ | _ | _ | _ | ψ | ψ <;>
    simp only [hs, hf] at hwk
  all_goals first
    | exact hold b' hb' w k hwk
    | skip
  case neg.neg.box =>
    have hsfeq : sf = (⟨Sign.neg, .box ψ, sf.label⟩ :
        SignedFormula (Proposition Atom) WorldIndex) := by rw [← hs, ← hf]
    rcases hblock : blockingWorldS4Keyed φ₀ b keys .neg ψ sf.label with _ | wBlock
    · -- unblocked: minting shape, `keys'` gains the new key
      simp only [hblock] at hwk
      simp only [List.mem_append, List.mem_singleton] at hwk
      rcases hwk with hwk | hwk
      · exact hold b' hb' w k hwk
      · have heq2 : modalApplyOneS4Keyed φ₀ keys (⟨Sign.neg, .box ψ, sf.label⟩ :
            SignedFormula (Proposition Atom) WorldIndex) b acc
            = modalApplyOneS4KeyedMint (⟨Sign.neg, .box ψ, sf.label⟩ :
              SignedFormula (Proposition Atom) WorldIndex) b acc :=
          modalApplyOneS4Keyed_boxNeg_unblocked_eq φ₀ b acc keys ψ sf.label hblock
        rw [hsfeq] at hpair
        have hresulteq : result = (modalApplyOneS4KeyedMint (⟨Sign.neg, .box ψ, sf.label⟩ :
            SignedFormula (Proposition Atom) WorldIndex) b acc).fst :=
          congrArg Prod.fst (hpair.symm.trans heq2)
        have hmintKeyed := modalApplyOneS4KeyedMint_boxNeg_eq_S4 b acc ψ sf.label
        rw [hresulteq.trans (congrArg Prod.fst hmintKeyed)] at hsf
        simp only [Option.some.injEq, Prod.mk.injEq] at hsf
        rw [← hsf.1] at hb'
        simp only [List.mem_singleton] at hb'
        have hsfmem' : (⟨Sign.neg, .box ψ, sf.label⟩ :
            SignedFormula (Proposition Atom) WorldIndex) ∈ b := hsfeq ▸ hsfmem
        have hsub := successorBirthContent_boxNeg_subset_relevantSetFinset φ₀ b acc sf.label ψ
          hb hsfmem' _ (congrArg Prod.fst hmintKeyed)
        rw [Prod.mk.injEq] at hwk
        obtain ⟨hweq, hkeq2⟩ := hwk
        subst hweq
        subst hkeq2
        rw [hb']
        exact hsub
    · -- blocked: no new key, old-key argument suffices
      simp only [hblock] at hwk
      exact hold b' hb' w k hwk
  case neg.pos.diamond =>
    have hsfeq : sf = (⟨Sign.pos, .diamond ψ, sf.label⟩ :
        SignedFormula (Proposition Atom) WorldIndex) := by rw [← hs, ← hf]
    rcases hblock : blockingWorldS4Keyed φ₀ b keys .pos ψ sf.label with _ | wBlock
    · -- unblocked: minting shape, `keys'` gains the new key
      simp only [hblock] at hwk
      simp only [List.mem_append, List.mem_singleton] at hwk
      rcases hwk with hwk | hwk
      · exact hold b' hb' w k hwk
      · have heq2 : modalApplyOneS4Keyed φ₀ keys (⟨Sign.pos, .diamond ψ, sf.label⟩ :
            SignedFormula (Proposition Atom) WorldIndex) b acc
            = modalApplyOneS4KeyedMint (⟨Sign.pos, .diamond ψ, sf.label⟩ :
              SignedFormula (Proposition Atom) WorldIndex) b acc :=
          modalApplyOneS4Keyed_diaPos_unblocked_eq φ₀ b acc keys ψ sf.label hblock
        rw [hsfeq] at hpair
        have hresulteq : result = (modalApplyOneS4KeyedMint (⟨Sign.pos, .diamond ψ, sf.label⟩ :
            SignedFormula (Proposition Atom) WorldIndex) b acc).fst :=
          congrArg Prod.fst (hpair.symm.trans heq2)
        have hmintKeyed := modalApplyOneS4KeyedMint_diaPos_eq_S4 b acc ψ sf.label
        rw [hresulteq.trans (congrArg Prod.fst hmintKeyed)] at hsf
        simp only [Option.some.injEq, Prod.mk.injEq] at hsf
        rw [← hsf.1] at hb'
        simp only [List.mem_singleton] at hb'
        have hsfmem' : (⟨Sign.pos, .diamond ψ, sf.label⟩ :
            SignedFormula (Proposition Atom) WorldIndex) ∈ b := hsfeq ▸ hsfmem
        have hsub := successorBirthContent_diamondPos_subset_relevantSetFinset φ₀ b acc sf.label ψ
          hb hsfmem' _ (congrArg Prod.fst hmintKeyed)
        rw [Prod.mk.injEq] at hwk
        obtain ⟨hweq, hkeq2⟩ := hwk
        subst hweq
        subst hkeq2
        rw [hb']
        exact hsub
    · -- blocked: no new key, old-key argument suffices
      simp only [hblock] at hwk
      exact hold b' hb' w k hwk

/-- **`keyLowerBd`'s ordered-driver preservation.** Verbatim transcription of
`modalStepBranchS4_preserves_keyLowerBd` against the ordered stepper: the argument never uses
"`sf` is the first applicable formula in `b`", only "`sf ∈ b`, `sf ∉ e`, and this specific rule
application produced `keys'`" -- exactly what `modalStepBranchS4KeyedOrdered_selected_mem`
supplies. Uses the ordered form of the branch-superset fact
(`modalStepBranchS4KeyedOrdered_branch_superset`) for the OLD-key half of the argument. -/
lemma modalStepBranchS4KeyedOrdered_preserves_keyLowerBd (φ₀ : Proposition Atom)
    (b e : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (keys : List (WorldIndex × Finset (Sign × Proposition Atom)))
    (newBs newExps : List (List (SignedFormula (Proposition Atom) WorldIndex)))
    (newAcc : Accessibility) (keys' : List (WorldIndex × Finset (Sign × Proposition Atom)))
    (hb : ∀ x ∈ b, x ∈ modalUniverseS4 φ₀)
    (hLB : ∀ w k, (w, k) ∈ keys → k ⊆ relevantSetFinset φ₀ b w)
    (hstep : modalStepBranchS4KeyedOrdered φ₀ b e acc keys =
      some (newBs, newExps, newAcc, keys')) :
    ∀ b' ∈ newBs, ∀ w k, (w, k) ∈ keys' → k ⊆ relevantSetFinset φ₀ b' w := by
  have hsuper := modalStepBranchS4KeyedOrdered_branch_superset φ₀ b e acc keys newBs newExps
    newAcc keys' hstep
  have hold : ∀ b' ∈ newBs, ∀ w k, (w, k) ∈ keys → k ⊆ relevantSetFinset φ₀ b' w :=
    fun b' hb' w k hwk => (hLB w k hwk).trans (relevantSetFinset_mono φ₀ b b' w (hsuper b' hb'))
  obtain ⟨sf, hsfmem, hsf_ne, hsf⟩ :=
    modalStepBranchS4KeyedOrdered_selected_mem φ₀ b e acc keys newBs newExps newAcc keys' hstep
  have hany : e.any (· == sf) = false := by
    rw [List.any_eq_false]
    intro x hx heq
    rw [beq_iff_eq] at heq
    subst heq
    exact hsf_ne hx
  unfold modalStepBranchS4KeyedBody at hsf
  rw [if_neg (by simp [hany])] at hsf
  rcases hpair : modalApplyOneS4Keyed φ₀ keys sf b acc with ⟨result, newAcc0⟩
  rw [hpair] at hsf
  dsimp only at hsf
  have hkeq := modalStepBranchS4Keyed_result_keys_eq result newAcc0 b e sf _ newBs newExps
    newAcc keys' hsf
  intro b' hb' w k hwk
  rw [hkeq] at hwk
  rcases hs : sf.sign with _ | _ <;> rcases hf : sf.formula with _ | _ | _ | _ | _ | ψ | ψ <;>
    simp only [hs, hf] at hwk
  all_goals first
    | exact hold b' hb' w k hwk
    | skip
  case neg.box =>
    have hsfeq : sf = (⟨Sign.neg, .box ψ, sf.label⟩ :
        SignedFormula (Proposition Atom) WorldIndex) := by rw [← hs, ← hf]
    rcases hblock : blockingWorldS4Keyed φ₀ b keys .neg ψ sf.label with _ | wBlock
    · -- unblocked: minting shape, `keys'` gains the new key
      simp only [hblock] at hwk
      simp only [List.mem_append, List.mem_singleton] at hwk
      rcases hwk with hwk | hwk
      · exact hold b' hb' w k hwk
      · have heq2 : modalApplyOneS4Keyed φ₀ keys (⟨Sign.neg, .box ψ, sf.label⟩ :
            SignedFormula (Proposition Atom) WorldIndex) b acc
            = modalApplyOneS4KeyedMint (⟨Sign.neg, .box ψ, sf.label⟩ :
              SignedFormula (Proposition Atom) WorldIndex) b acc :=
          modalApplyOneS4Keyed_boxNeg_unblocked_eq φ₀ b acc keys ψ sf.label hblock
        rw [hsfeq] at hpair
        have hresulteq : result = (modalApplyOneS4KeyedMint (⟨Sign.neg, .box ψ, sf.label⟩ :
            SignedFormula (Proposition Atom) WorldIndex) b acc).fst :=
          congrArg Prod.fst (hpair.symm.trans heq2)
        have hmintKeyed := modalApplyOneS4KeyedMint_boxNeg_eq_S4 b acc ψ sf.label
        rw [hresulteq.trans (congrArg Prod.fst hmintKeyed)] at hsf
        simp only [Option.some.injEq, Prod.mk.injEq] at hsf
        rw [← hsf.1] at hb'
        simp only [List.mem_singleton] at hb'
        have hsfmem' : (⟨Sign.neg, .box ψ, sf.label⟩ :
            SignedFormula (Proposition Atom) WorldIndex) ∈ b := hsfeq ▸ hsfmem
        have hsub := successorBirthContent_boxNeg_subset_relevantSetFinset φ₀ b acc sf.label ψ
          hb hsfmem' _ (congrArg Prod.fst hmintKeyed)
        rw [Prod.mk.injEq] at hwk
        obtain ⟨hweq, hkeq2⟩ := hwk
        subst hweq
        subst hkeq2
        rw [hb']
        exact hsub
    · -- blocked: no new key, old-key argument suffices
      simp only [hblock] at hwk
      exact hold b' hb' w k hwk
  case pos.diamond =>
    have hsfeq : sf = (⟨Sign.pos, .diamond ψ, sf.label⟩ :
        SignedFormula (Proposition Atom) WorldIndex) := by rw [← hs, ← hf]
    rcases hblock : blockingWorldS4Keyed φ₀ b keys .pos ψ sf.label with _ | wBlock
    · -- unblocked: minting shape, `keys'` gains the new key
      simp only [hblock] at hwk
      simp only [List.mem_append, List.mem_singleton] at hwk
      rcases hwk with hwk | hwk
      · exact hold b' hb' w k hwk
      · have heq2 : modalApplyOneS4Keyed φ₀ keys (⟨Sign.pos, .diamond ψ, sf.label⟩ :
            SignedFormula (Proposition Atom) WorldIndex) b acc
            = modalApplyOneS4KeyedMint (⟨Sign.pos, .diamond ψ, sf.label⟩ :
              SignedFormula (Proposition Atom) WorldIndex) b acc :=
          modalApplyOneS4Keyed_diaPos_unblocked_eq φ₀ b acc keys ψ sf.label hblock
        rw [hsfeq] at hpair
        have hresulteq : result = (modalApplyOneS4KeyedMint (⟨Sign.pos, .diamond ψ, sf.label⟩ :
            SignedFormula (Proposition Atom) WorldIndex) b acc).fst :=
          congrArg Prod.fst (hpair.symm.trans heq2)
        have hmintKeyed := modalApplyOneS4KeyedMint_diaPos_eq_S4 b acc ψ sf.label
        rw [hresulteq.trans (congrArg Prod.fst hmintKeyed)] at hsf
        simp only [Option.some.injEq, Prod.mk.injEq] at hsf
        rw [← hsf.1] at hb'
        simp only [List.mem_singleton] at hb'
        have hsfmem' : (⟨Sign.pos, .diamond ψ, sf.label⟩ :
            SignedFormula (Proposition Atom) WorldIndex) ∈ b := hsfeq ▸ hsfmem
        have hsub := successorBirthContent_diamondPos_subset_relevantSetFinset φ₀ b acc sf.label ψ
          hb hsfmem' _ (congrArg Prod.fst hmintKeyed)
        rw [Prod.mk.injEq] at hwk
        obtain ⟨hweq, hkeq2⟩ := hwk
        subst hweq
        subst hkeq2
        rw [hb']
        exact hsub
    · -- blocked: no new key, old-key argument suffices
      simp only [hblock] at hwk
      exact hold b' hb' w k hwk

/-- **`keysInUniverse`'s driver-level preservation**: every key
recorded after an S4Keyed step is drawn from `signedSubfmls φ₀`. Unlike `keyLowerBd`, this
obligation is independent of the (possibly several) output branches `newBs` -- it is a fact
about `keys'` alone. Assembled the same way: old keys survive via the `keysInUniverse`
hypothesis directly (`keys ⊆ keys'` always), new keys (the two minting leaves) via
`successorBirthContent_subset_signedSubfmls`, whose witness-formula-membership side
condition is derived exactly as in `successorBirthContent_boxNeg_subset_relevantSetFinset`/
`_diamondPos_subset_relevantSetFinset` above. -/
lemma modalStepBranchS4_preserves_keysInUniverse (φ₀ : Proposition Atom)
    (b e : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (keys : List (WorldIndex × Finset (Sign × Proposition Atom)))
    (newBs newExps : List (List (SignedFormula (Proposition Atom) WorldIndex)))
    (newAcc : Accessibility) (keys' : List (WorldIndex × Finset (Sign × Proposition Atom)))
    (hb : ∀ x ∈ b, x ∈ modalUniverseS4 φ₀)
    (hIU : ∀ w k, (w, k) ∈ keys → k ⊆ signedSubfmls φ₀)
    (hstep : modalStepBranchS4Keyed φ₀ b e acc keys = some (newBs, newExps, newAcc, keys')) :
    ∀ w k, (w, k) ∈ keys' → k ⊆ signedSubfmls φ₀ := by
  have hstep0 := hstep
  unfold modalStepBranchS4Keyed at hstep0
  obtain ⟨sf, hsfmem, hsf⟩ := List.exists_of_findSome?_eq_some hstep0
  split_ifs at hsf with hexp
  rcases hpair : modalApplyOneS4Keyed φ₀ keys sf b acc with ⟨result, newAcc0⟩
  rw [hpair] at hsf
  dsimp only at hsf
  have hkeq := modalStepBranchS4Keyed_result_keys_eq result newAcc0 b e sf _ newBs newExps
    newAcc keys' hsf
  intro w k hwk
  rw [hkeq] at hwk
  rcases hs : sf.sign with _ | _ <;> rcases hf : sf.formula with _ | _ | _ | _ | _ | ψ | ψ <;>
    simp only [hs, hf] at hwk
  all_goals first
    | exact hIU w k hwk
    | skip
  case neg.neg.box =>
    have hsfeq : sf = (⟨Sign.neg, .box ψ, sf.label⟩ :
        SignedFormula (Proposition Atom) WorldIndex) := by rw [← hs, ← hf]
    rcases hblock : blockingWorldS4Keyed φ₀ b keys .neg ψ sf.label with _ | wBlock
    · simp only [hblock] at hwk
      simp only [List.mem_append, List.mem_singleton] at hwk
      rcases hwk with hwk | hwk
      · exact hIU w k hwk
      · have hsfmem' : (⟨Sign.neg, .box ψ, sf.label⟩ :
            SignedFormula (Proposition Atom) WorldIndex) ∈ b := hsfeq ▸ hsfmem
        have hφsub : ψ ∈ modalSubfmls φ₀ := by
          have h1 : (Proposition.box ψ) ∈ modalSubfmls φ₀ :=
            modalUniverseS4_mem_formula (hb _ hsfmem')
          have h2 : ψ ∈ modalSubfmls (Proposition.box ψ) :=
            List.mem_cons_of_mem _ (modalSubfmls_self_mem ψ)
          exact modalSubfmls_trans h2 h1
        rw [Prod.mk.injEq] at hwk
        obtain ⟨-, hkeq2⟩ := hwk
        subst hkeq2
        exact successorBirthContent_subset_signedSubfmls φ₀ b .neg ψ sf.label hφsub
    · simp only [hblock] at hwk
      exact hIU w k hwk
  case neg.pos.diamond =>
    have hsfeq : sf = (⟨Sign.pos, .diamond ψ, sf.label⟩ :
        SignedFormula (Proposition Atom) WorldIndex) := by rw [← hs, ← hf]
    rcases hblock : blockingWorldS4Keyed φ₀ b keys .pos ψ sf.label with _ | wBlock
    · simp only [hblock] at hwk
      simp only [List.mem_append, List.mem_singleton] at hwk
      rcases hwk with hwk | hwk
      · exact hIU w k hwk
      · have hsfmem' : (⟨Sign.pos, .diamond ψ, sf.label⟩ :
            SignedFormula (Proposition Atom) WorldIndex) ∈ b := hsfeq ▸ hsfmem
        have hφsub : ψ ∈ modalSubfmls φ₀ := by
          have h1 : (Proposition.diamond ψ) ∈ modalSubfmls φ₀ :=
            modalUniverseS4_mem_formula (hb _ hsfmem')
          have h2 : ψ ∈ modalSubfmls (Proposition.diamond ψ) :=
            List.mem_cons_of_mem _ (modalSubfmls_self_mem ψ)
          exact modalSubfmls_trans h2 h1
        rw [Prod.mk.injEq] at hwk
        obtain ⟨-, hkeq2⟩ := hwk
        subst hkeq2
        exact successorBirthContent_subset_signedSubfmls φ₀ b .pos ψ sf.label hφsub
    · simp only [hblock] at hwk
      exact hIU w k hwk

/-- **`keysInUniverse`'s ordered-driver preservation.** Verbatim transcription of
`modalStepBranchS4_preserves_keysInUniverse` against the ordered stepper, via
`modalStepBranchS4KeyedOrdered_selected_mem` in place of the direct `findSome?` extraction. -/
lemma modalStepBranchS4KeyedOrdered_preserves_keysInUniverse (φ₀ : Proposition Atom)
    (b e : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (keys : List (WorldIndex × Finset (Sign × Proposition Atom)))
    (newBs newExps : List (List (SignedFormula (Proposition Atom) WorldIndex)))
    (newAcc : Accessibility) (keys' : List (WorldIndex × Finset (Sign × Proposition Atom)))
    (hb : ∀ x ∈ b, x ∈ modalUniverseS4 φ₀)
    (hIU : ∀ w k, (w, k) ∈ keys → k ⊆ signedSubfmls φ₀)
    (hstep : modalStepBranchS4KeyedOrdered φ₀ b e acc keys =
      some (newBs, newExps, newAcc, keys')) :
    ∀ w k, (w, k) ∈ keys' → k ⊆ signedSubfmls φ₀ := by
  obtain ⟨sf, hsfmem, hsf_ne, hsf⟩ :=
    modalStepBranchS4KeyedOrdered_selected_mem φ₀ b e acc keys newBs newExps newAcc keys' hstep
  have hany : e.any (· == sf) = false := by
    rw [List.any_eq_false]
    intro x hx heq
    rw [beq_iff_eq] at heq
    subst heq
    exact hsf_ne hx
  unfold modalStepBranchS4KeyedBody at hsf
  rw [if_neg (by simp [hany])] at hsf
  rcases hpair : modalApplyOneS4Keyed φ₀ keys sf b acc with ⟨result, newAcc0⟩
  rw [hpair] at hsf
  dsimp only at hsf
  have hkeq := modalStepBranchS4Keyed_result_keys_eq result newAcc0 b e sf _ newBs newExps
    newAcc keys' hsf
  intro w k hwk
  rw [hkeq] at hwk
  rcases hs : sf.sign with _ | _ <;> rcases hf : sf.formula with _ | _ | _ | _ | _ | ψ | ψ <;>
    simp only [hs, hf] at hwk
  all_goals first
    | exact hIU w k hwk
    | skip
  case neg.box =>
    have hsfeq : sf = (⟨Sign.neg, .box ψ, sf.label⟩ :
        SignedFormula (Proposition Atom) WorldIndex) := by rw [← hs, ← hf]
    rcases hblock : blockingWorldS4Keyed φ₀ b keys .neg ψ sf.label with _ | wBlock
    · simp only [hblock] at hwk
      simp only [List.mem_append, List.mem_singleton] at hwk
      rcases hwk with hwk | hwk
      · exact hIU w k hwk
      · have hsfmem' : (⟨Sign.neg, .box ψ, sf.label⟩ :
            SignedFormula (Proposition Atom) WorldIndex) ∈ b := hsfeq ▸ hsfmem
        have hφsub : ψ ∈ modalSubfmls φ₀ := by
          have h1 : (Proposition.box ψ) ∈ modalSubfmls φ₀ :=
            modalUniverseS4_mem_formula (hb _ hsfmem')
          have h2 : ψ ∈ modalSubfmls (Proposition.box ψ) :=
            List.mem_cons_of_mem _ (modalSubfmls_self_mem ψ)
          exact modalSubfmls_trans h2 h1
        rw [Prod.mk.injEq] at hwk
        obtain ⟨-, hkeq2⟩ := hwk
        subst hkeq2
        exact successorBirthContent_subset_signedSubfmls φ₀ b .neg ψ sf.label hφsub
    · simp only [hblock] at hwk
      exact hIU w k hwk
  case pos.diamond =>
    have hsfeq : sf = (⟨Sign.pos, .diamond ψ, sf.label⟩ :
        SignedFormula (Proposition Atom) WorldIndex) := by rw [← hs, ← hf]
    rcases hblock : blockingWorldS4Keyed φ₀ b keys .pos ψ sf.label with _ | wBlock
    · simp only [hblock] at hwk
      simp only [List.mem_append, List.mem_singleton] at hwk
      rcases hwk with hwk | hwk
      · exact hIU w k hwk
      · have hsfmem' : (⟨Sign.pos, .diamond ψ, sf.label⟩ :
            SignedFormula (Proposition Atom) WorldIndex) ∈ b := hsfeq ▸ hsfmem
        have hφsub : ψ ∈ modalSubfmls φ₀ := by
          have h1 : (Proposition.diamond ψ) ∈ modalSubfmls φ₀ :=
            modalUniverseS4_mem_formula (hb _ hsfmem')
          have h2 : ψ ∈ modalSubfmls (Proposition.diamond ψ) :=
            List.mem_cons_of_mem _ (modalSubfmls_self_mem ψ)
          exact modalSubfmls_trans h2 h1
        rw [Prod.mk.injEq] at hwk
        obtain ⟨-, hkeq2⟩ := hwk
        subst hkeq2
        exact successorBirthContent_subset_signedSubfmls φ₀ b .pos ψ sf.label hφsub
    · simp only [hblock] at hwk
      exact hIU w k hwk

/-! ## Assembling `keysTotal`'s Preservation -/

/-- **`keysTotal`'s driver-level preservation** (the crux): every
known world after an S4Keyed step has a recorded key. Assembled by a top-level split on whether
`sf` is one of the two minting shapes: at the 2 minting shapes, the newly-minted world's label
is exactly `modalNextWorld b` (`mintGroup_label_eq_freshWorld`), which `keys'` gains an entry
for by construction; at the other 12 shapes, `modalApplyOneS4Keyed_nonMint_known_S4` shows no
label beyond `modalKnownWorlds b` is ever introduced, so the new-known-world case never
actually arises there and old keys (`keys ⊆ keys'`, `modalStepBranchS4Keyed_keys_subset`)
suffice. -/
lemma modalStepBranchS4_preserves_keysTotal (φ₀ : Proposition Atom)
    (b e : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (keys : List (WorldIndex × Finset (Sign × Proposition Atom)))
    (newBs newExps : List (List (SignedFormula (Proposition Atom) WorldIndex)))
    (newAcc : Accessibility) (keys' : List (WorldIndex × Finset (Sign × Proposition Atom)))
    (hknown : accTargetsKnown b acc)
    (hKT : ∀ w ∈ modalKnownWorlds b, ∃ k, (w, k) ∈ keys)
    (hstep : modalStepBranchS4Keyed φ₀ b e acc keys = some (newBs, newExps, newAcc, keys')) :
    ∀ b' ∈ newBs, ∀ w ∈ modalKnownWorlds b', ∃ k, (w, k) ∈ keys' := by
  have hkeysub := modalStepBranchS4Keyed_keys_subset φ₀ b e acc keys newBs newExps newAcc keys'
    hstep
  have hold : ∀ w ∈ modalKnownWorlds b, ∃ k, (w, k) ∈ keys' :=
    fun w hw => (hKT w hw).imp (fun k hk => hkeysub hk)
  have hstep0 := hstep
  unfold modalStepBranchS4Keyed at hstep0
  obtain ⟨sf, hsfmem, hsf⟩ := List.exists_of_findSome?_eq_some hstep0
  split_ifs at hsf with hexp
  rcases hpair : modalApplyOneS4Keyed φ₀ keys sf b acc with ⟨result, newAcc0⟩
  rw [hpair] at hsf
  dsimp only at hsf
  have hkeq := modalStepBranchS4Keyed_result_keys_eq result newAcc0 b e sf _ newBs newExps
    newAcc keys' hsf
  by_cases hmint : (sf.sign = .neg ∧ ∃ φ, sf.formula = .box φ) ∨
      (sf.sign = .pos ∧ ∃ φ, sf.formula = .diamond φ)
  · rcases hmint with ⟨hs, ψ, hf⟩ | ⟨hs, ψ, hf⟩
    · have hsfeq : sf = (⟨Sign.neg, .box ψ, sf.label⟩ :
          SignedFormula (Proposition Atom) WorldIndex) := by rw [← hs, ← hf]
      rcases hblock : blockingWorldS4Keyed φ₀ b keys .neg ψ sf.label with _ | wBlock
      · have heq2 : modalApplyOneS4Keyed φ₀ keys (⟨Sign.neg, .box ψ, sf.label⟩ :
            SignedFormula (Proposition Atom) WorldIndex) b acc
            = modalApplyOneS4KeyedMint (⟨Sign.neg, .box ψ, sf.label⟩ :
              SignedFormula (Proposition Atom) WorldIndex) b acc :=
          modalApplyOneS4Keyed_boxNeg_unblocked_eq φ₀ b acc keys ψ sf.label hblock
        rw [hsfeq] at hpair
        have hresulteq : result = (modalApplyOneS4KeyedMint (⟨Sign.neg, .box ψ, sf.label⟩ :
            SignedFormula (Proposition Atom) WorldIndex) b acc).fst :=
          congrArg Prod.fst (hpair.symm.trans heq2)
        have hmintKeyed := modalApplyOneS4KeyedMint_boxNeg_eq_S4 b acc ψ sf.label
        have hresulteq2 := hresulteq.trans (congrArg Prod.fst hmintKeyed)
        have hlabel := mintGroup_label_eq_freshWorld b sf.label .neg ψ
        have hlabelExtra := boxPlusExtraS4_label_eq_freshWorld b sf.label
        have hkeq2 : keys' = keys ++
            [(modalNextWorld b, successorBirthContent φ₀ b .neg ψ sf.label)] := by
          rw [hkeq]; simp only [hs, hf, hblock]
        intro b' hb' w hw
        rw [hresulteq2] at hsf
        simp only [Option.some.injEq, Prod.mk.injEq] at hsf
        rw [← hsf.1] at hb'
        simp only [List.mem_singleton] at hb'
        subst hb'
        rw [mem_modalKnownWorlds] at hw
        obtain ⟨sf', hsf', rfl⟩ := hw
        rcases List.mem_append.mp hsf' with hsf'new | hsf'old
        · rcases List.mem_append.mp hsf'new with hsf'raw | hsf'extra
          · have hlabeleq := hlabel sf' hsf'raw
            rw [hlabeleq, hkeq2]
            exact ⟨successorBirthContent φ₀ b .neg ψ sf.label,
              List.mem_append_right _ (List.mem_singleton_self _)⟩
          · have hlabeleq := hlabelExtra sf' hsf'extra
            rw [hlabeleq, hkeq2]
            exact ⟨successorBirthContent φ₀ b .neg ψ sf.label,
              List.mem_append_right _ (List.mem_singleton_self _)⟩
        · have hwk : sf'.label ∈ modalKnownWorlds b := by
            rw [mem_modalKnownWorlds]; exact ⟨sf', hsf'old, rfl⟩
          exact hold sf'.label hwk
      · have hkeq2 : keys' = keys := by rw [hkeq]; simp only [hs, hf, hblock]
        have heq2 : modalApplyOneS4Keyed φ₀ keys (⟨Sign.neg, .box ψ, sf.label⟩ :
            SignedFormula (Proposition Atom) WorldIndex) b acc
            = (.linear [], acc.addEdge sf.label wBlock) :=
          modalApplyOneS4Keyed_boxNeg_blocked_eq φ₀ b acc keys ψ sf.label wBlock hblock
        rw [hsfeq] at hpair
        have hresulteq : result = RuleResult.linear [] :=
          congrArg Prod.fst (hpair.symm.trans heq2)
        intro b' hb' w hw
        rw [hresulteq] at hsf
        simp only [Option.some.injEq, Prod.mk.injEq] at hsf
        rw [← hsf.1] at hb'
        simp only [List.mem_singleton] at hb'
        subst hb'
        exact hold w hw
    · have hsfeq : sf = (⟨Sign.pos, .diamond ψ, sf.label⟩ :
          SignedFormula (Proposition Atom) WorldIndex) := by rw [← hs, ← hf]
      rcases hblock : blockingWorldS4Keyed φ₀ b keys .pos ψ sf.label with _ | wBlock
      · have heq2 : modalApplyOneS4Keyed φ₀ keys (⟨Sign.pos, .diamond ψ, sf.label⟩ :
            SignedFormula (Proposition Atom) WorldIndex) b acc
            = modalApplyOneS4KeyedMint (⟨Sign.pos, .diamond ψ, sf.label⟩ :
              SignedFormula (Proposition Atom) WorldIndex) b acc :=
          modalApplyOneS4Keyed_diaPos_unblocked_eq φ₀ b acc keys ψ sf.label hblock
        rw [hsfeq] at hpair
        have hresulteq : result = (modalApplyOneS4KeyedMint (⟨Sign.pos, .diamond ψ, sf.label⟩ :
            SignedFormula (Proposition Atom) WorldIndex) b acc).fst :=
          congrArg Prod.fst (hpair.symm.trans heq2)
        have hmintKeyed := modalApplyOneS4KeyedMint_diaPos_eq_S4 b acc ψ sf.label
        have hresulteq2 := hresulteq.trans (congrArg Prod.fst hmintKeyed)
        have hlabel := mintGroup_label_eq_freshWorld b sf.label .pos ψ
        have hlabelExtra := boxPlusExtraS4_label_eq_freshWorld b sf.label
        have hkeq2 : keys' = keys ++
            [(modalNextWorld b, successorBirthContent φ₀ b .pos ψ sf.label)] := by
          rw [hkeq]; simp only [hs, hf, hblock]
        intro b' hb' w hw
        rw [hresulteq2] at hsf
        simp only [Option.some.injEq, Prod.mk.injEq] at hsf
        rw [← hsf.1] at hb'
        simp only [List.mem_singleton] at hb'
        subst hb'
        rw [mem_modalKnownWorlds] at hw
        obtain ⟨sf', hsf', rfl⟩ := hw
        rcases List.mem_append.mp hsf' with hsf'new | hsf'old
        · rcases List.mem_append.mp hsf'new with hsf'raw | hsf'extra
          · have hlabeleq := hlabel sf' hsf'raw
            rw [hlabeleq, hkeq2]
            exact ⟨successorBirthContent φ₀ b .pos ψ sf.label,
              List.mem_append_right _ (List.mem_singleton_self _)⟩
          · have hlabeleq := hlabelExtra sf' hsf'extra
            rw [hlabeleq, hkeq2]
            exact ⟨successorBirthContent φ₀ b .pos ψ sf.label,
              List.mem_append_right _ (List.mem_singleton_self _)⟩
        · have hwk : sf'.label ∈ modalKnownWorlds b := by
            rw [mem_modalKnownWorlds]; exact ⟨sf', hsf'old, rfl⟩
          exact hold sf'.label hwk
      · have hkeq2 : keys' = keys := by rw [hkeq]; simp only [hs, hf, hblock]
        have heq2 : modalApplyOneS4Keyed φ₀ keys (⟨Sign.pos, .diamond ψ, sf.label⟩ :
            SignedFormula (Proposition Atom) WorldIndex) b acc
            = (.linear [], acc.addEdge sf.label wBlock) :=
          modalApplyOneS4Keyed_diaPos_blocked_eq φ₀ b acc keys ψ sf.label wBlock hblock
        rw [hsfeq] at hpair
        have hresulteq : result = RuleResult.linear [] :=
          congrArg Prod.fst (hpair.symm.trans heq2)
        intro b' hb' w hw
        rw [hresulteq] at hsf
        simp only [Option.some.injEq, Prod.mk.injEq] at hsf
        rw [← hsf.1] at hb'
        simp only [List.mem_singleton] at hb'
        subst hb'
        exact hold w hw
  · have hnbd : ¬ (sf.sign = .neg ∧ ∃ φ, sf.formula = .box φ) ∧
        ¬ (sf.sign = .pos ∧ ∃ φ, sf.formula = .diamond φ) :=
      ⟨fun hc => hmint (Or.inl hc), fun hc => hmint (Or.inr hc)⟩
    have hnm := modalApplyOneS4Keyed_nonMint_known_S4 φ₀ keys sf b acc hsfmem hknown hnbd
    rw [hpair] at hnm
    dsimp only at hnm
    intro b' hb' w hw
    have hwb : w ∈ modalKnownWorlds b := by
      rcases hres : result with lf | brs | lf | -
      · rw [hres] at hsf hnm
        simp only [Option.some.injEq, Prod.mk.injEq] at hsf
        rw [← hsf.1] at hb'
        simp only [List.mem_singleton] at hb'
        subst hb'
        rw [mem_modalKnownWorlds] at hw
        obtain ⟨sf', hsf', rfl⟩ := hw
        rcases List.mem_append.mp hsf' with hsf' | hsf'
        · exact hnm sf' hsf'
        · rw [mem_modalKnownWorlds]; exact ⟨sf', hsf', rfl⟩
      · rw [hres] at hsf hnm
        simp only [Option.some.injEq, Prod.mk.injEq] at hsf
        rw [← hsf.1] at hb'
        obtain ⟨br, hbr, rfl⟩ := List.mem_map.mp hb'
        rw [mem_modalKnownWorlds] at hw
        obtain ⟨sf', hsf', rfl⟩ := hw
        rcases List.mem_append.mp hsf' with hsf' | hsf'
        · exact hnm sf' (List.mem_flatten.mpr ⟨br, hbr, hsf'⟩)
        · rw [mem_modalKnownWorlds]; exact ⟨sf', hsf', rfl⟩
      · rw [hres] at hsf hnm
        simp only [Option.some.injEq, Prod.mk.injEq] at hsf
        rw [← hsf.1] at hb'
        simp only [List.mem_singleton] at hb'
        subst hb'
        rw [mem_modalKnownWorlds] at hw
        obtain ⟨sf', hsf', rfl⟩ := hw
        rcases List.mem_append.mp hsf' with hsf' | hsf'
        · exact hnm sf' hsf'
        · rw [mem_modalKnownWorlds]; exact ⟨sf', hsf', rfl⟩
      · rw [hres] at hsf; simp at hsf
    exact hold w hwb

/-- **`keysTotal`'s ordered-driver preservation.** Verbatim transcription of
`modalStepBranchS4_preserves_keysTotal` against the ordered stepper: the top-level
minting/non-minting split, the `mintGroup_label_eq_freshWorld` argument at the two minting
shapes, and `modalApplyOneS4Keyed_nonMint_known_S4` at the other twelve all consume only
"`sf ∈ b`, this rule application produced `keys'`" -- never "`sf` is the first applicable
formula" -- so the argument transfers unchanged once fed
`modalStepBranchS4KeyedOrdered_selected_mem` in place of the direct `findSome?` extraction. -/
lemma modalStepBranchS4KeyedOrdered_preserves_keysTotal (φ₀ : Proposition Atom)
    (b e : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (keys : List (WorldIndex × Finset (Sign × Proposition Atom)))
    (newBs newExps : List (List (SignedFormula (Proposition Atom) WorldIndex)))
    (newAcc : Accessibility) (keys' : List (WorldIndex × Finset (Sign × Proposition Atom)))
    (hknown : accTargetsKnown b acc)
    (hKT : ∀ w ∈ modalKnownWorlds b, ∃ k, (w, k) ∈ keys)
    (hstep : modalStepBranchS4KeyedOrdered φ₀ b e acc keys =
      some (newBs, newExps, newAcc, keys')) :
    ∀ b' ∈ newBs, ∀ w ∈ modalKnownWorlds b', ∃ k, (w, k) ∈ keys' := by
  have hkeysub := modalStepBranchS4KeyedOrdered_keys_subset φ₀ b e acc keys newBs newExps newAcc
    keys' hstep
  have hold : ∀ w ∈ modalKnownWorlds b, ∃ k, (w, k) ∈ keys' :=
    fun w hw => (hKT w hw).imp (fun k hk => hkeysub hk)
  obtain ⟨sf, hsfmem, hsf_ne, hsf⟩ :=
    modalStepBranchS4KeyedOrdered_selected_mem φ₀ b e acc keys newBs newExps newAcc keys' hstep
  have hany : e.any (· == sf) = false := by
    rw [List.any_eq_false]
    intro x hx heq
    rw [beq_iff_eq] at heq
    subst heq
    exact hsf_ne hx
  unfold modalStepBranchS4KeyedBody at hsf
  rw [if_neg (by simp [hany])] at hsf
  rcases hpair : modalApplyOneS4Keyed φ₀ keys sf b acc with ⟨result, newAcc0⟩
  rw [hpair] at hsf
  dsimp only at hsf
  have hkeq := modalStepBranchS4Keyed_result_keys_eq result newAcc0 b e sf _ newBs newExps
    newAcc keys' hsf
  by_cases hmint : (sf.sign = .neg ∧ ∃ φ, sf.formula = .box φ) ∨
      (sf.sign = .pos ∧ ∃ φ, sf.formula = .diamond φ)
  · rcases hmint with ⟨hs, ψ, hf⟩ | ⟨hs, ψ, hf⟩
    · have hsfeq : sf = (⟨Sign.neg, .box ψ, sf.label⟩ :
          SignedFormula (Proposition Atom) WorldIndex) := by rw [← hs, ← hf]
      rcases hblock : blockingWorldS4Keyed φ₀ b keys .neg ψ sf.label with _ | wBlock
      · have heq2 : modalApplyOneS4Keyed φ₀ keys (⟨Sign.neg, .box ψ, sf.label⟩ :
            SignedFormula (Proposition Atom) WorldIndex) b acc
            = modalApplyOneS4KeyedMint (⟨Sign.neg, .box ψ, sf.label⟩ :
              SignedFormula (Proposition Atom) WorldIndex) b acc :=
          modalApplyOneS4Keyed_boxNeg_unblocked_eq φ₀ b acc keys ψ sf.label hblock
        rw [hsfeq] at hpair
        have hresulteq : result = (modalApplyOneS4KeyedMint (⟨Sign.neg, .box ψ, sf.label⟩ :
            SignedFormula (Proposition Atom) WorldIndex) b acc).fst :=
          congrArg Prod.fst (hpair.symm.trans heq2)
        have hmintKeyed := modalApplyOneS4KeyedMint_boxNeg_eq_S4 b acc ψ sf.label
        have hresulteq2 := hresulteq.trans (congrArg Prod.fst hmintKeyed)
        have hlabel := mintGroup_label_eq_freshWorld b sf.label .neg ψ
        have hlabelExtra := boxPlusExtraS4_label_eq_freshWorld b sf.label
        have hkeq2 : keys' = keys ++
            [(modalNextWorld b, successorBirthContent φ₀ b .neg ψ sf.label)] := by
          rw [hkeq]; simp only [hs, hf, hblock]
        intro b' hb' w hw
        rw [hresulteq2] at hsf
        simp only [Option.some.injEq, Prod.mk.injEq] at hsf
        rw [← hsf.1] at hb'
        simp only [List.mem_singleton] at hb'
        subst hb'
        rw [mem_modalKnownWorlds] at hw
        obtain ⟨sf', hsf', rfl⟩ := hw
        rcases List.mem_append.mp hsf' with hsf'new | hsf'old
        · rcases List.mem_append.mp hsf'new with hsf'raw | hsf'extra
          · have hlabeleq := hlabel sf' hsf'raw
            rw [hlabeleq, hkeq2]
            exact ⟨successorBirthContent φ₀ b .neg ψ sf.label,
              List.mem_append_right _ (List.mem_singleton_self _)⟩
          · have hlabeleq := hlabelExtra sf' hsf'extra
            rw [hlabeleq, hkeq2]
            exact ⟨successorBirthContent φ₀ b .neg ψ sf.label,
              List.mem_append_right _ (List.mem_singleton_self _)⟩
        · have hwk : sf'.label ∈ modalKnownWorlds b := by
            rw [mem_modalKnownWorlds]; exact ⟨sf', hsf'old, rfl⟩
          exact hold sf'.label hwk
      · have hkeq2 : keys' = keys := by rw [hkeq]; simp only [hs, hf, hblock]
        have heq2 : modalApplyOneS4Keyed φ₀ keys (⟨Sign.neg, .box ψ, sf.label⟩ :
            SignedFormula (Proposition Atom) WorldIndex) b acc
            = (.linear [], acc.addEdge sf.label wBlock) :=
          modalApplyOneS4Keyed_boxNeg_blocked_eq φ₀ b acc keys ψ sf.label wBlock hblock
        rw [hsfeq] at hpair
        have hresulteq : result = RuleResult.linear [] :=
          congrArg Prod.fst (hpair.symm.trans heq2)
        intro b' hb' w hw
        rw [hresulteq] at hsf
        simp only [Option.some.injEq, Prod.mk.injEq] at hsf
        rw [← hsf.1] at hb'
        simp only [List.mem_singleton] at hb'
        subst hb'
        exact hold w hw
    · have hsfeq : sf = (⟨Sign.pos, .diamond ψ, sf.label⟩ :
          SignedFormula (Proposition Atom) WorldIndex) := by rw [← hs, ← hf]
      rcases hblock : blockingWorldS4Keyed φ₀ b keys .pos ψ sf.label with _ | wBlock
      · have heq2 : modalApplyOneS4Keyed φ₀ keys (⟨Sign.pos, .diamond ψ, sf.label⟩ :
            SignedFormula (Proposition Atom) WorldIndex) b acc
            = modalApplyOneS4KeyedMint (⟨Sign.pos, .diamond ψ, sf.label⟩ :
              SignedFormula (Proposition Atom) WorldIndex) b acc :=
          modalApplyOneS4Keyed_diaPos_unblocked_eq φ₀ b acc keys ψ sf.label hblock
        rw [hsfeq] at hpair
        have hresulteq : result = (modalApplyOneS4KeyedMint (⟨Sign.pos, .diamond ψ, sf.label⟩ :
            SignedFormula (Proposition Atom) WorldIndex) b acc).fst :=
          congrArg Prod.fst (hpair.symm.trans heq2)
        have hmintKeyed := modalApplyOneS4KeyedMint_diaPos_eq_S4 b acc ψ sf.label
        have hresulteq2 := hresulteq.trans (congrArg Prod.fst hmintKeyed)
        have hlabel := mintGroup_label_eq_freshWorld b sf.label .pos ψ
        have hlabelExtra := boxPlusExtraS4_label_eq_freshWorld b sf.label
        have hkeq2 : keys' = keys ++
            [(modalNextWorld b, successorBirthContent φ₀ b .pos ψ sf.label)] := by
          rw [hkeq]; simp only [hs, hf, hblock]
        intro b' hb' w hw
        rw [hresulteq2] at hsf
        simp only [Option.some.injEq, Prod.mk.injEq] at hsf
        rw [← hsf.1] at hb'
        simp only [List.mem_singleton] at hb'
        subst hb'
        rw [mem_modalKnownWorlds] at hw
        obtain ⟨sf', hsf', rfl⟩ := hw
        rcases List.mem_append.mp hsf' with hsf'new | hsf'old
        · rcases List.mem_append.mp hsf'new with hsf'raw | hsf'extra
          · have hlabeleq := hlabel sf' hsf'raw
            rw [hlabeleq, hkeq2]
            exact ⟨successorBirthContent φ₀ b .pos ψ sf.label,
              List.mem_append_right _ (List.mem_singleton_self _)⟩
          · have hlabeleq := hlabelExtra sf' hsf'extra
            rw [hlabeleq, hkeq2]
            exact ⟨successorBirthContent φ₀ b .pos ψ sf.label,
              List.mem_append_right _ (List.mem_singleton_self _)⟩
        · have hwk : sf'.label ∈ modalKnownWorlds b := by
            rw [mem_modalKnownWorlds]; exact ⟨sf', hsf'old, rfl⟩
          exact hold sf'.label hwk
      · have hkeq2 : keys' = keys := by rw [hkeq]; simp only [hs, hf, hblock]
        have heq2 : modalApplyOneS4Keyed φ₀ keys (⟨Sign.pos, .diamond ψ, sf.label⟩ :
            SignedFormula (Proposition Atom) WorldIndex) b acc
            = (.linear [], acc.addEdge sf.label wBlock) :=
          modalApplyOneS4Keyed_diaPos_blocked_eq φ₀ b acc keys ψ sf.label wBlock hblock
        rw [hsfeq] at hpair
        have hresulteq : result = RuleResult.linear [] :=
          congrArg Prod.fst (hpair.symm.trans heq2)
        intro b' hb' w hw
        rw [hresulteq] at hsf
        simp only [Option.some.injEq, Prod.mk.injEq] at hsf
        rw [← hsf.1] at hb'
        simp only [List.mem_singleton] at hb'
        subst hb'
        exact hold w hw
  · have hnbd : ¬ (sf.sign = .neg ∧ ∃ φ, sf.formula = .box φ) ∧
        ¬ (sf.sign = .pos ∧ ∃ φ, sf.formula = .diamond φ) :=
      ⟨fun hc => hmint (Or.inl hc), fun hc => hmint (Or.inr hc)⟩
    have hnm := modalApplyOneS4Keyed_nonMint_known_S4 φ₀ keys sf b acc hsfmem hknown hnbd
    rw [hpair] at hnm
    dsimp only at hnm
    intro b' hb' w hw
    have hwb : w ∈ modalKnownWorlds b := by
      rcases hres : result with lf | brs | lf | -
      · rw [hres] at hsf hnm
        simp only [Option.some.injEq, Prod.mk.injEq] at hsf
        rw [← hsf.1] at hb'
        simp only [List.mem_singleton] at hb'
        subst hb'
        rw [mem_modalKnownWorlds] at hw
        obtain ⟨sf', hsf', rfl⟩ := hw
        rcases List.mem_append.mp hsf' with hsf' | hsf'
        · exact hnm sf' hsf'
        · rw [mem_modalKnownWorlds]; exact ⟨sf', hsf', rfl⟩
      · rw [hres] at hsf hnm
        simp only [Option.some.injEq, Prod.mk.injEq] at hsf
        rw [← hsf.1] at hb'
        obtain ⟨br, hbr, rfl⟩ := List.mem_map.mp hb'
        rw [mem_modalKnownWorlds] at hw
        obtain ⟨sf', hsf', rfl⟩ := hw
        rcases List.mem_append.mp hsf' with hsf' | hsf'
        · exact hnm sf' (List.mem_flatten.mpr ⟨br, hbr, hsf'⟩)
        · rw [mem_modalKnownWorlds]; exact ⟨sf', hsf', rfl⟩
      · rw [hres] at hsf hnm
        simp only [Option.some.injEq, Prod.mk.injEq] at hsf
        rw [← hsf.1] at hb'
        simp only [List.mem_singleton] at hb'
        subst hb'
        rw [mem_modalKnownWorlds] at hw
        obtain ⟨sf', hsf', rfl⟩ := hw
        rcases List.mem_append.mp hsf' with hsf' | hsf'
        · exact hnm sf' hsf'
        · rw [mem_modalKnownWorlds]; exact ⟨sf', hsf', rfl⟩
      · rw [hres] at hsf; simp at hsf
    exact hold w hwb

/-- **`keysDistinct`'s driver-level preservation**: every pair of
distinctly-labeled keys recorded after an S4Keyed step remains distinct-keyed. Assembled the
same way as `keyLowerBd`/`keysInUniverse`/`keysTotal`: a `sf.sign`/`sf.formula` case split via
`modalStepBranchS4Keyed_result_keys_eq`, 12 leaves trivial (`keys' = keys`), the 2 minting
leaves reduce to exactly `keysUpdate_preserves_keysDistinct`'s own match shape. -/
lemma modalStepBranchS4_preserves_keysDistinct (φ₀ : Proposition Atom)
    (b e : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (keys : List (WorldIndex × Finset (Sign × Proposition Atom)))
    (newBs newExps : List (List (SignedFormula (Proposition Atom) WorldIndex)))
    (newAcc : Accessibility) (keys' : List (WorldIndex × Finset (Sign × Proposition Atom)))
    (hKD : ∀ w1 w2 k1 k2, (w1, k1) ∈ keys → (w2, k2) ∈ keys → w1 ≠ w2 → k1 ≠ k2)
    (hstep : modalStepBranchS4Keyed φ₀ b e acc keys = some (newBs, newExps, newAcc, keys')) :
    ∀ w1 w2 k1 k2, (w1, k1) ∈ keys' → (w2, k2) ∈ keys' → w1 ≠ w2 → k1 ≠ k2 := by
  have hstep0 := hstep
  unfold modalStepBranchS4Keyed at hstep0
  obtain ⟨sf, -, hsf⟩ := List.exists_of_findSome?_eq_some hstep0
  split_ifs at hsf with hexp
  rcases hpair : modalApplyOneS4Keyed φ₀ keys sf b acc with ⟨result, newAcc0⟩
  rw [hpair] at hsf
  dsimp only at hsf
  have hkeq := modalStepBranchS4Keyed_result_keys_eq result newAcc0 b e sf _ newBs newExps
    newAcc keys' hsf
  intro w1 w2 k1 k2 h1 h2 hne
  rw [hkeq] at h1 h2
  rcases hs : sf.sign with _ | _ <;> rcases hf : sf.formula with _ | _ | _ | _ | _ | ψ | ψ <;>
    simp only [hs, hf] at h1 h2
  all_goals first
    | exact hKD w1 w2 k1 k2 h1 h2 hne
    | skip
  case neg.neg.box =>
    exact keysUpdate_preserves_keysDistinct φ₀ b keys .neg ψ sf.label hKD w1 w2 k1 k2 h1 h2 hne
  case neg.pos.diamond =>
    exact keysUpdate_preserves_keysDistinct φ₀ b keys .pos ψ sf.label hKD w1 w2 k1 k2 h1 h2 hne

/-- **`keysDistinct`'s ordered-driver preservation (escalation-trigger sub-lemma).**
Identical statement and proof shape to `modalStepBranchS4_preserves_keysDistinct`, transcribed
against the ordered stepper via `modalStepBranchS4KeyedOrdered_selected_mem` in place of the
direct `findSome?` extraction from `modalStepBranchS4Keyed`. The plan flags this sub-lemma as the
escalation trigger: if it required ANY weakening of `keysUpdate_preserves_keysDistinct`, that
would contradict the plan's central claim that reordering only changes *timing*, never producing
a duplicate key. It does not need any such weakening -- the argument is verbatim
selection-independent, since `modalStepBranchS4Keyed_result_keys_eq` and
`keysUpdate_preserves_keysDistinct` only ever consume "some formula `sf` fired, producing this
key list", never "`sf` is the first such formula in `b`". -/
lemma modalStepBranchS4KeyedOrdered_preserves_keysDistinct (φ₀ : Proposition Atom)
    (b e : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (keys : List (WorldIndex × Finset (Sign × Proposition Atom)))
    (newBs newExps : List (List (SignedFormula (Proposition Atom) WorldIndex)))
    (newAcc : Accessibility) (keys' : List (WorldIndex × Finset (Sign × Proposition Atom)))
    (hKD : ∀ w1 w2 k1 k2, (w1, k1) ∈ keys → (w2, k2) ∈ keys → w1 ≠ w2 → k1 ≠ k2)
    (hstep : modalStepBranchS4KeyedOrdered φ₀ b e acc keys =
      some (newBs, newExps, newAcc, keys')) :
    ∀ w1 w2 k1 k2, (w1, k1) ∈ keys' → (w2, k2) ∈ keys' → w1 ≠ w2 → k1 ≠ k2 := by
  obtain ⟨sf, hsfmem, hsf_ne, hsf⟩ :=
    modalStepBranchS4KeyedOrdered_selected_mem φ₀ b e acc keys newBs newExps newAcc keys' hstep
  have hany : e.any (· == sf) = false := by
    rw [List.any_eq_false]
    intro x hx heq
    rw [beq_iff_eq] at heq
    subst heq
    exact hsf_ne hx
  unfold modalStepBranchS4KeyedBody at hsf
  rw [if_neg (by simp [hany])] at hsf
  rcases hpair : modalApplyOneS4Keyed φ₀ keys sf b acc with ⟨result, newAcc0⟩
  rw [hpair] at hsf
  dsimp only at hsf
  have hkeq := modalStepBranchS4Keyed_result_keys_eq result newAcc0 b e sf _ newBs newExps
    newAcc keys' hsf
  intro w1 w2 k1 k2 h1 h2 hne
  rw [hkeq] at h1 h2
  rcases hs : sf.sign with _ | _ <;> rcases hf : sf.formula with _ | _ | _ | _ | _ | ψ | ψ <;>
    simp only [hs, hf] at h1 h2
  all_goals first
    | exact hKD w1 w2 k1 k2 h1 h2 hne
    | skip
  case neg.box =>
    exact keysUpdate_preserves_keysDistinct φ₀ b keys .neg ψ sf.label hKD w1 w2 k1 k2 h1 h2 hne
  case pos.diamond =>
    exact keysUpdate_preserves_keysDistinct φ₀ b keys .pos ψ sf.label hKD w1 w2 k1 k2 h1 h2 hne

/-- **`keysWorldsKnown`, a proof-internal auxiliary invariant** (not an `S4LoopInv` field: adding
one would reopen the already-finalized struct design): every RECORDED key's world is
already a known world of the branch. Not literally implied by any single `S4LoopInv` field
(`keysTotal` only gives the converse direction), but true by construction -- `keys` only ever
gains an entry `(modalNextWorld b, ...)` in the SAME step that mints the branch formula carrying
that exact label, so the keyed world is known from the moment its key is recorded onward. Needed
by `accFresh`/`accKnown`'s preservation, whose guard-BLOCKED minting sub-case adds an edge to
`blockingWorldS4Keyed`'s result `wBlock` -- a RECORDED-key world, not necessarily K's usual
"freshly-minted" witness, so the standard `hFreshLocal`-style dichotomy (nonempty `.linear`
headed by the fresh witness) does not apply; `wBlock ∈ modalKnownWorlds b` is what closes the
gap instead. Threaded as an extra hypothesis/conclusion alongside `S4LoopInv` at every call site
(including the final assembly), exactly like `RuleApplicationSpec`-style raw hypotheses
elsewhere in this development. -/
lemma modalStepBranchS4_preserves_keysWorldsKnown (φ₀ : Proposition Atom)
    (b e : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (keys : List (WorldIndex × Finset (Sign × Proposition Atom)))
    (newBs newExps : List (List (SignedFormula (Proposition Atom) WorldIndex)))
    (newAcc : Accessibility) (keys' : List (WorldIndex × Finset (Sign × Proposition Atom)))
    (hKW : ∀ w k, (w, k) ∈ keys → w ∈ modalKnownWorlds b)
    (hstep : modalStepBranchS4Keyed φ₀ b e acc keys = some (newBs, newExps, newAcc, keys')) :
    ∀ b' ∈ newBs, ∀ w k, (w, k) ∈ keys' → w ∈ modalKnownWorlds b' := by
  have hsuper := modalStepBranchS4Keyed_branch_superset φ₀ b e acc keys newBs newExps newAcc
    keys' hstep
  have hold : ∀ b' ∈ newBs, ∀ w k, (w, k) ∈ keys → w ∈ modalKnownWorlds b' := by
    intro b' hb' w k hwk
    obtain ⟨sf', hsf', hlab⟩ := (mem_modalKnownWorlds b w).mp (hKW w k hwk)
    exact (mem_modalKnownWorlds b' w).mpr ⟨sf', hsuper b' hb' sf' hsf', hlab⟩
  have hstep0 := hstep
  unfold modalStepBranchS4Keyed at hstep0
  obtain ⟨sf, hsfmem, hsf⟩ := List.exists_of_findSome?_eq_some hstep0
  split_ifs at hsf with hexp
  rcases hpair : modalApplyOneS4Keyed φ₀ keys sf b acc with ⟨result, newAcc0⟩
  rw [hpair] at hsf
  dsimp only at hsf
  have hkeq := modalStepBranchS4Keyed_result_keys_eq result newAcc0 b e sf _ newBs newExps
    newAcc keys' hsf
  intro b' hb' w k hwk
  rw [hkeq] at hwk
  rcases hs : sf.sign with _ | _ <;> rcases hf : sf.formula with _ | _ | _ | _ | _ | ψ | ψ <;>
    simp only [hs, hf] at hwk
  all_goals first
    | exact hold b' hb' w k hwk
    | skip
  case neg.neg.box =>
    have hsfeq : sf = (⟨Sign.neg, .box ψ, sf.label⟩ :
        SignedFormula (Proposition Atom) WorldIndex) := by rw [← hs, ← hf]
    rcases hblock : blockingWorldS4Keyed φ₀ b keys .neg ψ sf.label with _ | wBlock
    · simp only [hblock] at hwk
      simp only [List.mem_append, List.mem_singleton] at hwk
      rcases hwk with hwk | hwk
      · exact hold b' hb' w k hwk
      · rw [Prod.mk.injEq] at hwk
        obtain ⟨hweq, -⟩ := hwk
        subst hweq
        have heq2 : modalApplyOneS4Keyed φ₀ keys (⟨Sign.neg, .box ψ, sf.label⟩ :
            SignedFormula (Proposition Atom) WorldIndex) b acc
            = modalApplyOneS4KeyedMint (⟨Sign.neg, .box ψ, sf.label⟩ :
              SignedFormula (Proposition Atom) WorldIndex) b acc :=
          modalApplyOneS4Keyed_boxNeg_unblocked_eq φ₀ b acc keys ψ sf.label hblock
        rw [hsfeq] at hpair
        have hresulteq : result = (modalApplyOneS4KeyedMint (⟨Sign.neg, .box ψ, sf.label⟩ :
            SignedFormula (Proposition Atom) WorldIndex) b acc).fst :=
          congrArg Prod.fst (hpair.symm.trans heq2)
        have hresulteq2 := hresulteq.trans
          (congrArg Prod.fst (modalApplyOneS4KeyedMint_boxNeg_eq_S4 b acc ψ sf.label))
        rw [hresulteq2] at hsf
        simp only [Option.some.injEq, Prod.mk.injEq] at hsf
        rw [← hsf.1] at hb'
        simp only [List.mem_singleton] at hb'
        subst hb'
        rw [mem_modalKnownWorlds]
        exact ⟨⟨.neg, ψ, modalNextWorld b⟩,
          List.mem_append_left _ (List.mem_append_left _ List.mem_cons_self), rfl⟩
    · simp only [hblock] at hwk
      exact hold b' hb' w k hwk
  case neg.pos.diamond =>
    have hsfeq : sf = (⟨Sign.pos, .diamond ψ, sf.label⟩ :
        SignedFormula (Proposition Atom) WorldIndex) := by rw [← hs, ← hf]
    rcases hblock : blockingWorldS4Keyed φ₀ b keys .pos ψ sf.label with _ | wBlock
    · simp only [hblock] at hwk
      simp only [List.mem_append, List.mem_singleton] at hwk
      rcases hwk with hwk | hwk
      · exact hold b' hb' w k hwk
      · rw [Prod.mk.injEq] at hwk
        obtain ⟨hweq, -⟩ := hwk
        subst hweq
        have heq2 : modalApplyOneS4Keyed φ₀ keys (⟨Sign.pos, .diamond ψ, sf.label⟩ :
            SignedFormula (Proposition Atom) WorldIndex) b acc
            = modalApplyOneS4KeyedMint (⟨Sign.pos, .diamond ψ, sf.label⟩ :
              SignedFormula (Proposition Atom) WorldIndex) b acc :=
          modalApplyOneS4Keyed_diaPos_unblocked_eq φ₀ b acc keys ψ sf.label hblock
        rw [hsfeq] at hpair
        have hresulteq : result = (modalApplyOneS4KeyedMint (⟨Sign.pos, .diamond ψ, sf.label⟩ :
            SignedFormula (Proposition Atom) WorldIndex) b acc).fst :=
          congrArg Prod.fst (hpair.symm.trans heq2)
        have hresulteq2 := hresulteq.trans
          (congrArg Prod.fst (modalApplyOneS4KeyedMint_diaPos_eq_S4 b acc ψ sf.label))
        rw [hresulteq2] at hsf
        simp only [Option.some.injEq, Prod.mk.injEq] at hsf
        rw [← hsf.1] at hb'
        simp only [List.mem_singleton] at hb'
        subst hb'
        rw [mem_modalKnownWorlds]
        exact ⟨⟨.pos, ψ, modalNextWorld b⟩,
          List.mem_append_left _ (List.mem_append_left _ List.mem_cons_self), rfl⟩
    · simp only [hblock] at hwk
      exact hold b' hb' w k hwk

/-- **`keysWorldsKnown`'s ordered-driver preservation.** Verbatim transcription of
`modalStepBranchS4_preserves_keysWorldsKnown` against the ordered stepper, via
`modalStepBranchS4KeyedOrdered_selected_mem`/`modalStepBranchS4KeyedOrdered_branch_superset` in
place of their unordered counterparts. -/
lemma modalStepBranchS4KeyedOrdered_preserves_keysWorldsKnown (φ₀ : Proposition Atom)
    (b e : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (keys : List (WorldIndex × Finset (Sign × Proposition Atom)))
    (newBs newExps : List (List (SignedFormula (Proposition Atom) WorldIndex)))
    (newAcc : Accessibility) (keys' : List (WorldIndex × Finset (Sign × Proposition Atom)))
    (hKW : ∀ w k, (w, k) ∈ keys → w ∈ modalKnownWorlds b)
    (hstep : modalStepBranchS4KeyedOrdered φ₀ b e acc keys =
      some (newBs, newExps, newAcc, keys')) :
    ∀ b' ∈ newBs, ∀ w k, (w, k) ∈ keys' → w ∈ modalKnownWorlds b' := by
  have hsuper := modalStepBranchS4KeyedOrdered_branch_superset φ₀ b e acc keys newBs newExps
    newAcc keys' hstep
  have hold : ∀ b' ∈ newBs, ∀ w k, (w, k) ∈ keys → w ∈ modalKnownWorlds b' := by
    intro b' hb' w k hwk
    obtain ⟨sf', hsf', hlab⟩ := (mem_modalKnownWorlds b w).mp (hKW w k hwk)
    exact (mem_modalKnownWorlds b' w).mpr ⟨sf', hsuper b' hb' sf' hsf', hlab⟩
  obtain ⟨sf, hsfmem, hsf_ne, hsf⟩ :=
    modalStepBranchS4KeyedOrdered_selected_mem φ₀ b e acc keys newBs newExps newAcc keys' hstep
  have hany : e.any (· == sf) = false := by
    rw [List.any_eq_false]
    intro x hx heq
    rw [beq_iff_eq] at heq
    subst heq
    exact hsf_ne hx
  unfold modalStepBranchS4KeyedBody at hsf
  rw [if_neg (by simp [hany])] at hsf
  rcases hpair : modalApplyOneS4Keyed φ₀ keys sf b acc with ⟨result, newAcc0⟩
  rw [hpair] at hsf
  dsimp only at hsf
  have hkeq := modalStepBranchS4Keyed_result_keys_eq result newAcc0 b e sf _ newBs newExps
    newAcc keys' hsf
  intro b' hb' w k hwk
  rw [hkeq] at hwk
  rcases hs : sf.sign with _ | _ <;> rcases hf : sf.formula with _ | _ | _ | _ | _ | ψ | ψ <;>
    simp only [hs, hf] at hwk
  all_goals first
    | exact hold b' hb' w k hwk
    | skip
  case neg.box =>
    have hsfeq : sf = (⟨Sign.neg, .box ψ, sf.label⟩ :
        SignedFormula (Proposition Atom) WorldIndex) := by rw [← hs, ← hf]
    rcases hblock : blockingWorldS4Keyed φ₀ b keys .neg ψ sf.label with _ | wBlock
    · simp only [hblock] at hwk
      simp only [List.mem_append, List.mem_singleton] at hwk
      rcases hwk with hwk | hwk
      · exact hold b' hb' w k hwk
      · rw [Prod.mk.injEq] at hwk
        obtain ⟨hweq, -⟩ := hwk
        subst hweq
        have heq2 : modalApplyOneS4Keyed φ₀ keys (⟨Sign.neg, .box ψ, sf.label⟩ :
            SignedFormula (Proposition Atom) WorldIndex) b acc
            = modalApplyOneS4KeyedMint (⟨Sign.neg, .box ψ, sf.label⟩ :
              SignedFormula (Proposition Atom) WorldIndex) b acc :=
          modalApplyOneS4Keyed_boxNeg_unblocked_eq φ₀ b acc keys ψ sf.label hblock
        rw [hsfeq] at hpair
        have hresulteq : result = (modalApplyOneS4KeyedMint (⟨Sign.neg, .box ψ, sf.label⟩ :
            SignedFormula (Proposition Atom) WorldIndex) b acc).fst :=
          congrArg Prod.fst (hpair.symm.trans heq2)
        have hresulteq2 := hresulteq.trans
          (congrArg Prod.fst (modalApplyOneS4KeyedMint_boxNeg_eq_S4 b acc ψ sf.label))
        rw [hresulteq2] at hsf
        simp only [Option.some.injEq, Prod.mk.injEq] at hsf
        rw [← hsf.1] at hb'
        simp only [List.mem_singleton] at hb'
        subst hb'
        rw [mem_modalKnownWorlds]
        exact ⟨⟨.neg, ψ, modalNextWorld b⟩,
          List.mem_append_left _ (List.mem_append_left _ List.mem_cons_self), rfl⟩
    · simp only [hblock] at hwk
      exact hold b' hb' w k hwk
  case pos.diamond =>
    have hsfeq : sf = (⟨Sign.pos, .diamond ψ, sf.label⟩ :
        SignedFormula (Proposition Atom) WorldIndex) := by rw [← hs, ← hf]
    rcases hblock : blockingWorldS4Keyed φ₀ b keys .pos ψ sf.label with _ | wBlock
    · simp only [hblock] at hwk
      simp only [List.mem_append, List.mem_singleton] at hwk
      rcases hwk with hwk | hwk
      · exact hold b' hb' w k hwk
      · rw [Prod.mk.injEq] at hwk
        obtain ⟨hweq, -⟩ := hwk
        subst hweq
        have heq2 : modalApplyOneS4Keyed φ₀ keys (⟨Sign.pos, .diamond ψ, sf.label⟩ :
            SignedFormula (Proposition Atom) WorldIndex) b acc
            = modalApplyOneS4KeyedMint (⟨Sign.pos, .diamond ψ, sf.label⟩ :
              SignedFormula (Proposition Atom) WorldIndex) b acc :=
          modalApplyOneS4Keyed_diaPos_unblocked_eq φ₀ b acc keys ψ sf.label hblock
        rw [hsfeq] at hpair
        have hresulteq : result = (modalApplyOneS4KeyedMint (⟨Sign.pos, .diamond ψ, sf.label⟩ :
            SignedFormula (Proposition Atom) WorldIndex) b acc).fst :=
          congrArg Prod.fst (hpair.symm.trans heq2)
        have hresulteq2 := hresulteq.trans
          (congrArg Prod.fst (modalApplyOneS4KeyedMint_diaPos_eq_S4 b acc ψ sf.label))
        rw [hresulteq2] at hsf
        simp only [Option.some.injEq, Prod.mk.injEq] at hsf
        rw [← hsf.1] at hb'
        simp only [List.mem_singleton] at hb'
        subst hb'
        rw [mem_modalKnownWorlds]
        exact ⟨⟨.pos, ψ, modalNextWorld b⟩,
          List.mem_append_left _ (List.mem_append_left _ List.mem_cons_self), rfl⟩
    · simp only [hblock] at hwk
      exact hold b' hb' w k hwk

/-! ### Origin-Edge Invariant — Step Preservation

`keysOriginS4` (defined above, alongside its entry and monotonicity lemmas) survives a single
`modalStepBranchS4Keyed`/`modalStepBranchS4KeyedOrdered` step, over every branch produced.
Mirrors `keysWorldsKnown`'s preservation shape (proof-internal auxiliary, threaded as an extra
hypothesis/conclusion, never an `S4LoopInv` field): twelve of the fourteen `sf.sign`/
`sf.formula` shapes are free -- `modalApplyOneS4Keyed_nonMint_snd_eq_acc` gives `newAcc = acc`
outright and the `keys'`-defining match falls to its `_, _ => keys` catch-all -- so
`keysOriginS4_mono_branch`/`_mono_acc` alone close them. The blocked-mint sub-case adds an edge
but no key, closed the same way via a direct `Accessibility.addEdge`/`hasEdge` unfolding. Only
the unblocked-mint sub-case establishes a genuinely new key, by construction: the new entry is
`(modalNextWorld b, successorBirthContent φ₀ b s φ v)`, born together with the freshly-added
edge `v → modalNextWorld b`, so `u := v` and the witness pair is `(s, φ)` itself -- exactly the
`insert (s, φ) (...)` head of `successorBirthContent`. -/

/-- **`keysOriginS4`'s single-step preservation.** -/
lemma modalStepBranchS4Keyed_preserves_keysOriginS4 (φ₀ : Proposition Atom)
    (b e : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (keys : List (WorldIndex × Finset (Sign × Proposition Atom)))
    (newBs newExps : List (List (SignedFormula (Proposition Atom) WorldIndex)))
    (newAcc : Accessibility) (keys' : List (WorldIndex × Finset (Sign × Proposition Atom)))
    (haK : accTargetsKnown b acc)
    (hKO : keysOriginS4 b acc keys)
    (hstep : modalStepBranchS4Keyed φ₀ b e acc keys = some (newBs, newExps, newAcc, keys')) :
    ∀ b' ∈ newBs, keysOriginS4 b' newAcc keys' := by
  have hsuper := modalStepBranchS4Keyed_branch_superset φ₀ b e acc keys newBs newExps newAcc
    keys' hstep
  have hstep0 := hstep
  unfold modalStepBranchS4Keyed at hstep0
  obtain ⟨sf, hsfmem, hsf⟩ := List.exists_of_findSome?_eq_some hstep0
  split_ifs at hsf with hexp
  rcases hpair : modalApplyOneS4Keyed φ₀ keys sf b acc with ⟨result, newAcc0⟩
  by_cases hmint : (sf.sign = .neg ∧ ∃ φ, sf.formula = .box φ) ∨
      (sf.sign = .pos ∧ ∃ φ, sf.formula = .diamond φ)
  · rcases hmint with ⟨hs, ψ, hf⟩ | ⟨hs, ψ, hf⟩
    · -- box-negative minting shape
      have hsfeq : sf = (⟨Sign.neg, .box ψ, sf.label⟩ :
          SignedFormula (Proposition Atom) WorldIndex) := by rw [← hs, ← hf]
      rw [hsfeq] at hsf hpair
      rw [hpair] at hsf
      dsimp only at hsf
      rcases hblock : blockingWorldS4Keyed φ₀ b keys .neg ψ sf.label with _ | wBlock
      · -- unblocked: establishes the new key
        obtain ⟨hwsnd, rest, hwfst⟩ := modalApplyOneS4KeyedMint_boxNeg_witness b acc ψ sf.label
        have hAOeq := modalApplyOneS4Keyed_boxNeg_unblocked_eq φ₀ b acc keys ψ sf.label hblock
        rw [hblock] at hsf
        have hresulteq : result = RuleResult.linear
            ((⟨.neg, ψ, modalNextWorld b⟩ : SignedFormula (Proposition Atom) WorldIndex) ::
              rest) := (congrArg Prod.fst (hpair.symm.trans hAOeq)).trans hwfst
        have hnewAcc0eq : newAcc0 = acc.addEdge sf.label (modalNextWorld b) := by
          have hsndeq := congrArg Prod.snd (hpair.symm.trans hAOeq)
          rwa [hwsnd] at hsndeq
        have haccsub : ∀ u w, acc.hasEdge u w = true → newAcc0.hasEdge u w = true := by
          intro u w h
          rw [hnewAcc0eq]
          simp only [Accessibility.hasEdge, Accessibility.addEdge, List.any_cons] at h ⊢
          simp [h]
        rw [hresulteq] at hsf
        simp only [Option.some.injEq, Prod.mk.injEq] at hsf
        obtain ⟨hnewBs, -, hnewAcc, hnewKeys⟩ := hsf
        intro b' hb'
        have hb'_mem := hb'
        rw [← hnewBs] at hb'
        simp only [List.mem_singleton] at hb'
        subst hb'
        subst hnewAcc
        rw [← hnewKeys]
        have hold := keysOriginS4_mono_acc _ acc newAcc0 keys haccsub
          (keysOriginS4_mono_branch b _ acc keys (hsuper _ hb'_mem) hKO)
        intro w k hmem
        rcases List.mem_append.mp hmem with hmemold | hmemnew
        · exact hold w k hmemold
        · simp only [List.mem_singleton, Prod.mk.injEq] at hmemnew
          obtain ⟨rfl, rfl⟩ := hmemnew
          refine Or.inr ⟨sf.label, .neg, ψ, ?_, ?_, ?_⟩
          · rw [hnewAcc0eq]
            simp only [Accessibility.hasEdge, Accessibility.addEdge, List.any_cons]
            simp
          · intro ψ' hψ'
            simp only [successorBirthContent, Finset.mem_insert, Finset.mem_filter] at hψ'
            rcases hψ' with heq | ⟨-, hdisj⟩
            · exact absurd heq (by simp)
            · rcases hdisj with ⟨-, hbany⟩ | ⟨hcon, -⟩ | ⟨-, hbpb⟩ | ⟨hcon, -⟩
              · exact Or.inr (Or.inl (List.mem_append_right _ (mem_of_any_beq_S4 hbany)))
              · exact absurd hcon (by simp)
              · obtain ⟨χ, hχ, hbmem⟩ := boxPlus_pos_disjunct_elim hbpb
                exact Or.inr (Or.inr ⟨χ, hχ, List.mem_append_right _ hbmem⟩)
              · exact absurd hcon (by simp)
          · intro ψ' hψ'
            simp only [successorBirthContent, Finset.mem_insert, Finset.mem_filter] at hψ'
            rcases hψ' with heq | ⟨-, hdisj⟩
            · exact Or.inl heq.symm
            · rcases hdisj with ⟨hcon, -⟩ | ⟨-, hbany⟩ | ⟨hcon, -⟩ | ⟨-, hbpb⟩
              · exact absurd hcon (by simp)
              · exact Or.inr (Or.inl (List.mem_append_right _ (mem_of_any_beq_S4 hbany)))
              · exact absurd hcon (by simp)
              · obtain ⟨χ, hχ, hdmem⟩ := boxPlus_neg_disjunct_elim hbpb
                exact Or.inr (Or.inr ⟨χ, hχ, List.mem_append_right _ hdmem⟩)
      · -- blocked: keys unchanged, edge added
        have hAOeq := modalApplyOneS4Keyed_boxNeg_blocked_eq φ₀ b acc keys ψ sf.label wBlock
          hblock
        rw [hblock] at hsf
        have hresulteq : result = RuleResult.linear [] :=
          congrArg Prod.fst (hpair.symm.trans hAOeq)
        have hnewAcc0eq : newAcc0 = acc.addEdge sf.label wBlock :=
          congrArg Prod.snd (hpair.symm.trans hAOeq)
        have haccsub : ∀ u w, acc.hasEdge u w = true → newAcc0.hasEdge u w = true := by
          intro u w h
          rw [hnewAcc0eq]
          simp only [Accessibility.hasEdge, Accessibility.addEdge, List.any_cons] at h ⊢
          simp [h]
        rw [hresulteq] at hsf
        simp only [List.nil_append, Option.some.injEq, Prod.mk.injEq] at hsf
        obtain ⟨hnewBs, -, hnewAcc, hnewKeys⟩ := hsf
        intro b' hb'
        have hb'_mem := hb'
        rw [← hnewBs] at hb'
        simp only [List.mem_singleton] at hb'
        symm at hb'
        subst hb'
        subst hnewAcc
        rw [← hnewKeys]
        exact keysOriginS4_mono_acc _ acc newAcc0 keys haccsub
          (keysOriginS4_mono_branch b _ acc keys (hsuper _ hb'_mem) hKO)
    · -- diamond-positive minting shape (symmetric)
      have hsfeq : sf = (⟨Sign.pos, .diamond ψ, sf.label⟩ :
          SignedFormula (Proposition Atom) WorldIndex) := by rw [← hs, ← hf]
      rw [hsfeq] at hsf hpair
      rw [hpair] at hsf
      dsimp only at hsf
      rcases hblock : blockingWorldS4Keyed φ₀ b keys .pos ψ sf.label with _ | wBlock
      · -- unblocked: establishes the new key
        obtain ⟨hwsnd, rest, hwfst⟩ := modalApplyOneS4KeyedMint_diaPos_witness b acc ψ sf.label
        have hAOeq := modalApplyOneS4Keyed_diaPos_unblocked_eq φ₀ b acc keys ψ sf.label hblock
        rw [hblock] at hsf
        have hresulteq : result = RuleResult.linear
            ((⟨.pos, ψ, modalNextWorld b⟩ : SignedFormula (Proposition Atom) WorldIndex) ::
              rest) := (congrArg Prod.fst (hpair.symm.trans hAOeq)).trans hwfst
        have hnewAcc0eq : newAcc0 = acc.addEdge sf.label (modalNextWorld b) := by
          have hsndeq := congrArg Prod.snd (hpair.symm.trans hAOeq)
          rwa [hwsnd] at hsndeq
        have haccsub : ∀ u w, acc.hasEdge u w = true → newAcc0.hasEdge u w = true := by
          intro u w h
          rw [hnewAcc0eq]
          simp only [Accessibility.hasEdge, Accessibility.addEdge, List.any_cons] at h ⊢
          simp [h]
        rw [hresulteq] at hsf
        simp only [Option.some.injEq, Prod.mk.injEq] at hsf
        obtain ⟨hnewBs, -, hnewAcc, hnewKeys⟩ := hsf
        intro b' hb'
        have hb'_mem := hb'
        rw [← hnewBs] at hb'
        simp only [List.mem_singleton] at hb'
        subst hb'
        subst hnewAcc
        rw [← hnewKeys]
        have hold := keysOriginS4_mono_acc _ acc newAcc0 keys haccsub
          (keysOriginS4_mono_branch b _ acc keys (hsuper _ hb'_mem) hKO)
        intro w k hmem
        rcases List.mem_append.mp hmem with hmemold | hmemnew
        · exact hold w k hmemold
        · simp only [List.mem_singleton, Prod.mk.injEq] at hmemnew
          obtain ⟨rfl, rfl⟩ := hmemnew
          refine Or.inr ⟨sf.label, .pos, ψ, ?_, ?_, ?_⟩
          · rw [hnewAcc0eq]
            simp only [Accessibility.hasEdge, Accessibility.addEdge, List.any_cons]
            simp
          · intro ψ' hψ'
            simp only [successorBirthContent, Finset.mem_insert, Finset.mem_filter] at hψ'
            rcases hψ' with heq | ⟨-, hdisj⟩
            · exact Or.inl heq.symm
            · rcases hdisj with ⟨-, hbany⟩ | ⟨hcon, -⟩ | ⟨-, hbpb⟩ | ⟨hcon, -⟩
              · exact Or.inr (Or.inl (List.mem_append_right _ (mem_of_any_beq_S4 hbany)))
              · exact absurd hcon (by simp)
              · obtain ⟨χ, hχ, hbmem⟩ := boxPlus_pos_disjunct_elim hbpb
                exact Or.inr (Or.inr ⟨χ, hχ, List.mem_append_right _ hbmem⟩)
              · exact absurd hcon (by simp)
          · intro ψ' hψ'
            simp only [successorBirthContent, Finset.mem_insert, Finset.mem_filter] at hψ'
            rcases hψ' with heq | ⟨-, hdisj⟩
            · exact absurd heq (by simp)
            · rcases hdisj with ⟨hcon, -⟩ | ⟨-, hbany⟩ | ⟨hcon, -⟩ | ⟨-, hbpb⟩
              · exact absurd hcon (by simp)
              · exact Or.inr (Or.inl (List.mem_append_right _ (mem_of_any_beq_S4 hbany)))
              · exact absurd hcon (by simp)
              · obtain ⟨χ, hχ, hdmem⟩ := boxPlus_neg_disjunct_elim hbpb
                exact Or.inr (Or.inr ⟨χ, hχ, List.mem_append_right _ hdmem⟩)
      · -- blocked: keys unchanged, edge added
        have hAOeq := modalApplyOneS4Keyed_diaPos_blocked_eq φ₀ b acc keys ψ sf.label wBlock
          hblock
        rw [hblock] at hsf
        have hresulteq : result = RuleResult.linear [] :=
          congrArg Prod.fst (hpair.symm.trans hAOeq)
        have hnewAcc0eq : newAcc0 = acc.addEdge sf.label wBlock :=
          congrArg Prod.snd (hpair.symm.trans hAOeq)
        have haccsub : ∀ u w, acc.hasEdge u w = true → newAcc0.hasEdge u w = true := by
          intro u w h
          rw [hnewAcc0eq]
          simp only [Accessibility.hasEdge, Accessibility.addEdge, List.any_cons] at h ⊢
          simp [h]
        rw [hresulteq] at hsf
        simp only [List.nil_append, Option.some.injEq, Prod.mk.injEq] at hsf
        obtain ⟨hnewBs, -, hnewAcc, hnewKeys⟩ := hsf
        intro b' hb'
        have hb'_mem := hb'
        rw [← hnewBs] at hb'
        simp only [List.mem_singleton] at hb'
        symm at hb'
        subst hb'
        subst hnewAcc
        rw [← hnewKeys]
        exact keysOriginS4_mono_acc _ acc newAcc0 keys haccsub
          (keysOriginS4_mono_branch b _ acc keys (hsuper _ hb'_mem) hKO)
  · -- non-mint: keys' = keys, newAcc = newAcc0 = acc, regardless of which of the 12 shapes fired
    rw [hpair] at hsf
    dsimp only at hsf
    have hnbd : ¬ (sf.sign = .neg ∧ ∃ φ, sf.formula = .box φ) ∧
        ¬ (sf.sign = .pos ∧ ∃ φ, sf.formula = .diamond φ) :=
      ⟨fun hc => hmint (Or.inl hc), fun hc => hmint (Or.inr hc)⟩
    have hnewAcc0eq : newAcc0 = acc :=
      (congrArg Prod.snd hpair).symm.trans
        (modalApplyOneS4Keyed_nonMint_snd_eq_acc φ₀ keys sf b acc hsfmem haK hnbd)
    have haccsub : ∀ u w, acc.hasEdge u w = true → newAcc0.hasEdge u w = true := by
      rw [hnewAcc0eq]; exact fun u w h => h
    have hold : ∀ b' ∈ newBs, keysOriginS4 b' newAcc0 keys := fun b' hb' =>
      keysOriginS4_mono_acc b' acc newAcc0 keys haccsub
        (keysOriginS4_mono_branch b b' acc keys (hsuper b' hb') hKO)
    have hkeq0 := modalStepBranchS4Keyed_result_keys_eq result newAcc0 b e sf _ newBs newExps
      newAcc keys' hsf
    have haccEq := modalStepBranchS4Keyed_result_acc_eq result newAcc0 b e sf _ newBs newExps
      newAcc keys' hsf
    have hkeq : keys' = keys := by
      rw [hkeq0]
      rcases hs : sf.sign with _ | _ <;>
        rcases hf : sf.formula with _ | _ | _ | _ | _ | ψ | ψ <;> dsimp only [hs, hf]
      · exact absurd ⟨hs, ψ, hf⟩ hnbd.2
      · exact absurd ⟨hs, ψ, hf⟩ hnbd.1
    intro b' hb'
    rw [haccEq, hkeq]
    exact hold b' hb'

/-- **`keysOriginS4`'s ordered-driver preservation.** Verbatim transcription of
`modalStepBranchS4Keyed_preserves_keysOriginS4` against the ordered stepper, via
`modalStepBranchS4KeyedOrdered_selected_mem`/`modalStepBranchS4KeyedOrdered_branch_superset` in
place of their unordered counterparts. -/
lemma modalStepBranchS4KeyedOrdered_preserves_keysOriginS4 (φ₀ : Proposition Atom)
    (b e : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (keys : List (WorldIndex × Finset (Sign × Proposition Atom)))
    (newBs newExps : List (List (SignedFormula (Proposition Atom) WorldIndex)))
    (newAcc : Accessibility) (keys' : List (WorldIndex × Finset (Sign × Proposition Atom)))
    (haK : accTargetsKnown b acc)
    (hKO : keysOriginS4 b acc keys)
    (hstep : modalStepBranchS4KeyedOrdered φ₀ b e acc keys =
      some (newBs, newExps, newAcc, keys')) :
    ∀ b' ∈ newBs, keysOriginS4 b' newAcc keys' := by
  have hsuper := modalStepBranchS4KeyedOrdered_branch_superset φ₀ b e acc keys newBs newExps
    newAcc keys' hstep
  obtain ⟨sf, hsfmem, hsf_ne, hsf⟩ :=
    modalStepBranchS4KeyedOrdered_selected_mem φ₀ b e acc keys newBs newExps newAcc keys' hstep
  have hany : e.any (· == sf) = false := by
    rw [List.any_eq_false]
    intro x hx heq
    rw [beq_iff_eq] at heq
    subst heq
    exact hsf_ne hx
  unfold modalStepBranchS4KeyedBody at hsf
  rw [if_neg (by simp [hany])] at hsf
  rcases hpair : modalApplyOneS4Keyed φ₀ keys sf b acc with ⟨result, newAcc0⟩
  by_cases hmint : (sf.sign = .neg ∧ ∃ φ, sf.formula = .box φ) ∨
      (sf.sign = .pos ∧ ∃ φ, sf.formula = .diamond φ)
  · rcases hmint with ⟨hs, ψ, hf⟩ | ⟨hs, ψ, hf⟩
    · -- box-negative minting shape
      have hsfeq : sf = (⟨Sign.neg, .box ψ, sf.label⟩ :
          SignedFormula (Proposition Atom) WorldIndex) := by rw [← hs, ← hf]
      rw [hsfeq] at hsf hpair
      rw [hpair] at hsf
      dsimp only at hsf
      rw [hsfeq] at hsfmem
      rcases hblock : blockingWorldS4Keyed φ₀ b keys .neg ψ sf.label with _ | wBlock
      · -- unblocked: establishes the new key
        obtain ⟨hwsnd, rest, hwfst⟩ := modalApplyOneS4KeyedMint_boxNeg_witness b acc ψ sf.label
        have hAOeq := modalApplyOneS4Keyed_boxNeg_unblocked_eq φ₀ b acc keys ψ sf.label hblock
        rw [hblock] at hsf
        have hresulteq : result = RuleResult.linear
            ((⟨.neg, ψ, modalNextWorld b⟩ : SignedFormula (Proposition Atom) WorldIndex) ::
              rest) := (congrArg Prod.fst (hpair.symm.trans hAOeq)).trans hwfst
        have hnewAcc0eq : newAcc0 = acc.addEdge sf.label (modalNextWorld b) := by
          have hsndeq := congrArg Prod.snd (hpair.symm.trans hAOeq)
          rwa [hwsnd] at hsndeq
        have haccsub : ∀ u w, acc.hasEdge u w = true → newAcc0.hasEdge u w = true := by
          intro u w h
          rw [hnewAcc0eq]
          simp only [Accessibility.hasEdge, Accessibility.addEdge, List.any_cons] at h ⊢
          simp [h]
        rw [hresulteq] at hsf
        simp only [Option.some.injEq, Prod.mk.injEq] at hsf
        obtain ⟨hnewBs, -, hnewAcc, hnewKeys⟩ := hsf
        intro b' hb'
        have hb'_mem := hb'
        rw [← hnewBs] at hb'
        simp only [List.mem_singleton] at hb'
        subst hb'
        subst hnewAcc
        rw [← hnewKeys]
        have hold := keysOriginS4_mono_acc _ acc newAcc0 keys haccsub
          (keysOriginS4_mono_branch b _ acc keys (hsuper _ hb'_mem) hKO)
        intro w k hmem
        rcases List.mem_append.mp hmem with hmemold | hmemnew
        · exact hold w k hmemold
        · simp only [List.mem_singleton, Prod.mk.injEq] at hmemnew
          obtain ⟨rfl, rfl⟩ := hmemnew
          refine Or.inr ⟨sf.label, .neg, ψ, ?_, ?_, ?_⟩
          · rw [hnewAcc0eq]
            simp only [Accessibility.hasEdge, Accessibility.addEdge, List.any_cons]
            simp
          · intro ψ' hψ'
            simp only [successorBirthContent, Finset.mem_insert, Finset.mem_filter] at hψ'
            rcases hψ' with heq | ⟨-, hdisj⟩
            · exact absurd heq (by simp)
            · rcases hdisj with ⟨-, hbany⟩ | ⟨hcon, -⟩ | ⟨-, hbpb⟩ | ⟨hcon, -⟩
              · exact Or.inr (Or.inl (List.mem_append_right _ (mem_of_any_beq_S4 hbany)))
              · exact absurd hcon (by simp)
              · obtain ⟨χ, hχ, hbmem⟩ := boxPlus_pos_disjunct_elim hbpb
                exact Or.inr (Or.inr ⟨χ, hχ, List.mem_append_right _ hbmem⟩)
              · exact absurd hcon (by simp)
          · intro ψ' hψ'
            simp only [successorBirthContent, Finset.mem_insert, Finset.mem_filter] at hψ'
            rcases hψ' with heq | ⟨-, hdisj⟩
            · exact Or.inl heq.symm
            · rcases hdisj with ⟨hcon, -⟩ | ⟨-, hbany⟩ | ⟨hcon, -⟩ | ⟨-, hbpb⟩
              · exact absurd hcon (by simp)
              · exact Or.inr (Or.inl (List.mem_append_right _ (mem_of_any_beq_S4 hbany)))
              · exact absurd hcon (by simp)
              · obtain ⟨χ, hχ, hdmem⟩ := boxPlus_neg_disjunct_elim hbpb
                exact Or.inr (Or.inr ⟨χ, hχ, List.mem_append_right _ hdmem⟩)
      · -- blocked: keys unchanged, edge added
        have hAOeq := modalApplyOneS4Keyed_boxNeg_blocked_eq φ₀ b acc keys ψ sf.label wBlock
          hblock
        rw [hblock] at hsf
        have hresulteq : result = RuleResult.linear [] :=
          congrArg Prod.fst (hpair.symm.trans hAOeq)
        have hnewAcc0eq : newAcc0 = acc.addEdge sf.label wBlock :=
          congrArg Prod.snd (hpair.symm.trans hAOeq)
        have haccsub : ∀ u w, acc.hasEdge u w = true → newAcc0.hasEdge u w = true := by
          intro u w h
          rw [hnewAcc0eq]
          simp only [Accessibility.hasEdge, Accessibility.addEdge, List.any_cons] at h ⊢
          simp [h]
        rw [hresulteq] at hsf
        simp only [List.nil_append, Option.some.injEq, Prod.mk.injEq] at hsf
        obtain ⟨hnewBs, -, hnewAcc, hnewKeys⟩ := hsf
        intro b' hb'
        have hb'_mem := hb'
        rw [← hnewBs] at hb'
        simp only [List.mem_singleton] at hb'
        symm at hb'
        subst hb'
        subst hnewAcc
        rw [← hnewKeys]
        exact keysOriginS4_mono_acc _ acc newAcc0 keys haccsub
          (keysOriginS4_mono_branch b _ acc keys (hsuper _ hb'_mem) hKO)
    · -- diamond-positive minting shape (symmetric)
      have hsfeq : sf = (⟨Sign.pos, .diamond ψ, sf.label⟩ :
          SignedFormula (Proposition Atom) WorldIndex) := by rw [← hs, ← hf]
      rw [hsfeq] at hsf hpair
      rw [hpair] at hsf
      dsimp only at hsf
      rw [hsfeq] at hsfmem
      rcases hblock : blockingWorldS4Keyed φ₀ b keys .pos ψ sf.label with _ | wBlock
      · -- unblocked: establishes the new key
        obtain ⟨hwsnd, rest, hwfst⟩ := modalApplyOneS4KeyedMint_diaPos_witness b acc ψ sf.label
        have hAOeq := modalApplyOneS4Keyed_diaPos_unblocked_eq φ₀ b acc keys ψ sf.label hblock
        rw [hblock] at hsf
        have hresulteq : result = RuleResult.linear
            ((⟨.pos, ψ, modalNextWorld b⟩ : SignedFormula (Proposition Atom) WorldIndex) ::
              rest) := (congrArg Prod.fst (hpair.symm.trans hAOeq)).trans hwfst
        have hnewAcc0eq : newAcc0 = acc.addEdge sf.label (modalNextWorld b) := by
          have hsndeq := congrArg Prod.snd (hpair.symm.trans hAOeq)
          rwa [hwsnd] at hsndeq
        have haccsub : ∀ u w, acc.hasEdge u w = true → newAcc0.hasEdge u w = true := by
          intro u w h
          rw [hnewAcc0eq]
          simp only [Accessibility.hasEdge, Accessibility.addEdge, List.any_cons] at h ⊢
          simp [h]
        rw [hresulteq] at hsf
        simp only [Option.some.injEq, Prod.mk.injEq] at hsf
        obtain ⟨hnewBs, -, hnewAcc, hnewKeys⟩ := hsf
        intro b' hb'
        have hb'_mem := hb'
        rw [← hnewBs] at hb'
        simp only [List.mem_singleton] at hb'
        subst hb'
        subst hnewAcc
        rw [← hnewKeys]
        have hold := keysOriginS4_mono_acc _ acc newAcc0 keys haccsub
          (keysOriginS4_mono_branch b _ acc keys (hsuper _ hb'_mem) hKO)
        intro w k hmem
        rcases List.mem_append.mp hmem with hmemold | hmemnew
        · exact hold w k hmemold
        · simp only [List.mem_singleton, Prod.mk.injEq] at hmemnew
          obtain ⟨rfl, rfl⟩ := hmemnew
          refine Or.inr ⟨sf.label, .pos, ψ, ?_, ?_, ?_⟩
          · rw [hnewAcc0eq]
            simp only [Accessibility.hasEdge, Accessibility.addEdge, List.any_cons]
            simp
          · intro ψ' hψ'
            simp only [successorBirthContent, Finset.mem_insert, Finset.mem_filter] at hψ'
            rcases hψ' with heq | ⟨-, hdisj⟩
            · exact Or.inl heq.symm
            · rcases hdisj with ⟨-, hbany⟩ | ⟨hcon, -⟩ | ⟨-, hbpb⟩ | ⟨hcon, -⟩
              · exact Or.inr (Or.inl (List.mem_append_right _ (mem_of_any_beq_S4 hbany)))
              · exact absurd hcon (by simp)
              · obtain ⟨χ, hχ, hbmem⟩ := boxPlus_pos_disjunct_elim hbpb
                exact Or.inr (Or.inr ⟨χ, hχ, List.mem_append_right _ hbmem⟩)
              · exact absurd hcon (by simp)
          · intro ψ' hψ'
            simp only [successorBirthContent, Finset.mem_insert, Finset.mem_filter] at hψ'
            rcases hψ' with heq | ⟨-, hdisj⟩
            · exact absurd heq (by simp)
            · rcases hdisj with ⟨hcon, -⟩ | ⟨-, hbany⟩ | ⟨hcon, -⟩ | ⟨-, hbpb⟩
              · exact absurd hcon (by simp)
              · exact Or.inr (Or.inl (List.mem_append_right _ (mem_of_any_beq_S4 hbany)))
              · exact absurd hcon (by simp)
              · obtain ⟨χ, hχ, hdmem⟩ := boxPlus_neg_disjunct_elim hbpb
                exact Or.inr (Or.inr ⟨χ, hχ, List.mem_append_right _ hdmem⟩)
      · -- blocked: keys unchanged, edge added
        have hAOeq := modalApplyOneS4Keyed_diaPos_blocked_eq φ₀ b acc keys ψ sf.label wBlock
          hblock
        rw [hblock] at hsf
        have hresulteq : result = RuleResult.linear [] :=
          congrArg Prod.fst (hpair.symm.trans hAOeq)
        have hnewAcc0eq : newAcc0 = acc.addEdge sf.label wBlock :=
          congrArg Prod.snd (hpair.symm.trans hAOeq)
        have haccsub : ∀ u w, acc.hasEdge u w = true → newAcc0.hasEdge u w = true := by
          intro u w h
          rw [hnewAcc0eq]
          simp only [Accessibility.hasEdge, Accessibility.addEdge, List.any_cons] at h ⊢
          simp [h]
        rw [hresulteq] at hsf
        simp only [List.nil_append, Option.some.injEq, Prod.mk.injEq] at hsf
        obtain ⟨hnewBs, -, hnewAcc, hnewKeys⟩ := hsf
        intro b' hb'
        have hb'_mem := hb'
        rw [← hnewBs] at hb'
        simp only [List.mem_singleton] at hb'
        symm at hb'
        subst hb'
        subst hnewAcc
        rw [← hnewKeys]
        exact keysOriginS4_mono_acc _ acc newAcc0 keys haccsub
          (keysOriginS4_mono_branch b _ acc keys (hsuper _ hb'_mem) hKO)
  · -- non-mint: keys' = keys, newAcc = newAcc0 = acc, regardless of which of the 12 shapes fired
    rw [hpair] at hsf
    dsimp only at hsf
    have hnbd : ¬ (sf.sign = .neg ∧ ∃ φ, sf.formula = .box φ) ∧
        ¬ (sf.sign = .pos ∧ ∃ φ, sf.formula = .diamond φ) :=
      ⟨fun hc => hmint (Or.inl hc), fun hc => hmint (Or.inr hc)⟩
    have hnewAcc0eq : newAcc0 = acc :=
      (congrArg Prod.snd hpair).symm.trans
        (modalApplyOneS4Keyed_nonMint_snd_eq_acc φ₀ keys sf b acc hsfmem haK hnbd)
    have haccsub : ∀ u w, acc.hasEdge u w = true → newAcc0.hasEdge u w = true := by
      rw [hnewAcc0eq]; exact fun u w h => h
    have hold : ∀ b' ∈ newBs, keysOriginS4 b' newAcc0 keys := fun b' hb' =>
      keysOriginS4_mono_acc b' acc newAcc0 keys haccsub
        (keysOriginS4_mono_branch b b' acc keys (hsuper b' hb') hKO)
    have hkeq0 := modalStepBranchS4Keyed_result_keys_eq result newAcc0 b e sf _ newBs newExps
      newAcc keys' hsf
    have haccEq := modalStepBranchS4Keyed_result_acc_eq result newAcc0 b e sf _ newBs newExps
      newAcc keys' hsf
    have hkeq : keys' = keys := by
      rw [hkeq0]
      rcases hs : sf.sign with _ | _ <;>
        rcases hf : sf.formula with _ | _ | _ | _ | _ | ψ | ψ <;> dsimp only [hs, hf]
      · exact absurd ⟨hs, ψ, hf⟩ hnbd.2
      · exact absurd ⟨hs, ψ, hf⟩ hnbd.1
    intro b' hb'
    rw [haccEq, hkeq]
    exact hold b' hb'


end Cslib.Logic.Modal.Tableau

end
