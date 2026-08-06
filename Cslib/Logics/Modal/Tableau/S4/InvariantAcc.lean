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

/-! # S4 Loop-Checking: `S4LoopInv` Accessibility/Expansion Field Preservation

The accessibility/expansion-facing `S4LoopInv` field preservation pairs (`eNodup`, `accFresh`,
`accKnown`), world contiguity (`worldsContiguousS4`) and its preservation, and the pigeonhole
world bound (`modalKnownWorlds_length_le_worldBoundS4`, `modalStepBranchS4_worldBound`).

## Why a separate module

The invariant material is split four ways (`InvariantKeys`, `InvariantAcc`, `Invariant`,
`HintikkaInvariant`) rather than kept as one module; see `InvariantKeys.lean`'s docstring for
the full rationale. This module holds every field whose preservation argument routes through
accessibility/expansion facts rather than the birth-key bookkeeping.

`LoopChecking.lean`'s retained termination-measure block consumes
`modalStepBranchS4_worldBound` and `worldsContiguousS4` directly, so both must be public at
module scope (they already are). `accFreshInv_append_S4` remains `private`: the regenerated
dependency graph shows no consumer outside this module.

## Main Definitions
- `worldsContiguousS4`: the world-contiguity predicate.

## Main Results
- `modalStepBranchS4{,KeyedOrdered}_preserves_eNodup`: expanded-set no-duplicates preservation.
- `modalStepBranchS4{,KeyedOrdered}_preserves_accFresh`: accessibility-freshness preservation.
- `modalStepBranchS4{,KeyedOrdered}_preserves_accKnown`: accessibility-known-worlds preservation.
- `modalStepBranchS4{,KeyedOrdered}_preserves_worldsContiguousS4`: contiguity preservation.
- `modalKnownWorlds_length_le_worldBoundS4`, `modalStepBranchS4_worldBound`: the pigeonhole
  world-count bound the termination measure consumes.
-/

@[expose] public section

namespace Cslib.Logic.Modal.Tableau

open Cslib.Logic.Tableau Cslib.Logic.Modal

variable {Atom : Type*} [DecidableEq Atom] [Hashable Atom]

/-- **`eNodup`'s driver-level preservation**: `modalStepBranchS4Keyed` preserves `Nodup`-ness of
the expanded set `e`, exactly like the generic `modalStepBranch_preserves_expandedNodup_gen`
(`FmpMeasure.lean`) -- fully rule-agnostic, only the top-level `RuleResult` constructor shape
matters, `keys`/`keys'` never enter the argument. Direct case split on `result` (not routed
through the generic lemma, since `modalStepBranchS4Keyed` returns a 4-tuple with `keys'` bolted
on rather than literally being `modalStepBranchGen (modalApplyOneS4Keyed φ₀ keys)`). -/
lemma modalStepBranchS4_preserves_eNodup (φ₀ : Proposition Atom)
    (b e : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (keys : List (WorldIndex × Finset (Sign × Proposition Atom)))
    (newBs newExps : List (List (SignedFormula (Proposition Atom) WorldIndex)))
    (newAcc : Accessibility) (keys' : List (WorldIndex × Finset (Sign × Proposition Atom)))
    (hstep : modalStepBranchS4Keyed φ₀ b e acc keys = some (newBs, newExps, newAcc, keys'))
    (hnodup : e.Nodup) :
    ∀ e' ∈ newExps, e'.Nodup := by
  unfold modalStepBranchS4Keyed at hstep
  obtain ⟨sf, -, hsf⟩ := List.exists_of_findSome?_eq_some hstep
  split_ifs at hsf with hexp
  have hsfnotmem : sf ∉ e := by
    intro hmem
    exact hexp (by simp only [List.any_eq_true]; exact ⟨sf, hmem, by simp⟩)
  rcases hpair : modalApplyOneS4Keyed φ₀ keys sf b acc with ⟨result, newAcc0⟩
  rw [hpair] at hsf
  dsimp only at hsf
  rcases hres : result with nf | brs | nf | -
  · rw [hres] at hsf
    simp only [Option.some.injEq, Prod.mk.injEq] at hsf
    obtain ⟨-, rfl, -, -⟩ := hsf
    intro e' he'
    simp only [List.mem_singleton] at he'
    subst he'
    exact List.Nodup.append hnodup (List.nodup_singleton sf)
      (fun a ha hmem => by simp only [List.mem_singleton] at hmem; exact hsfnotmem (hmem ▸ ha))
  · rw [hres] at hsf
    simp only [Option.some.injEq, Prod.mk.injEq] at hsf
    obtain ⟨-, rfl, -, -⟩ := hsf
    intro e' he'
    obtain ⟨x, -, rfl⟩ := List.mem_map.mp he'
    exact List.Nodup.append hnodup (List.nodup_singleton sf)
      (fun a ha hmem => by simp only [List.mem_singleton] at hmem; exact hsfnotmem (hmem ▸ ha))
  · rw [hres] at hsf
    simp only [Option.some.injEq, Prod.mk.injEq] at hsf
    obtain ⟨-, rfl, -, -⟩ := hsf
    intro e' he'
    simp only [List.mem_singleton] at he'
    subst he'
    exact hnodup
  · rw [hres] at hsf; simp at hsf

/-- **`eNodup`'s ordered-driver preservation.** Verbatim transcription of
`modalStepBranchS4_preserves_eNodup`: fully rule-agnostic (only the top-level `RuleResult`
constructor shape matters), so the selected formula's identity plays no role beyond `sf ∉ e`,
which `modalStepBranchS4KeyedOrdered_selected_mem` supplies directly. -/
lemma modalStepBranchS4KeyedOrdered_preserves_eNodup (φ₀ : Proposition Atom)
    (b e : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (keys : List (WorldIndex × Finset (Sign × Proposition Atom)))
    (newBs newExps : List (List (SignedFormula (Proposition Atom) WorldIndex)))
    (newAcc : Accessibility) (keys' : List (WorldIndex × Finset (Sign × Proposition Atom)))
    (hstep : modalStepBranchS4KeyedOrdered φ₀ b e acc keys =
      some (newBs, newExps, newAcc, keys'))
    (hnodup : e.Nodup) :
    ∀ e' ∈ newExps, e'.Nodup := by
  obtain ⟨sf, hsfmem, hsfnotmem, hsf⟩ :=
    modalStepBranchS4KeyedOrdered_selected_mem φ₀ b e acc keys newBs newExps newAcc keys' hstep
  have hany : e.any (· == sf) = false := by
    rw [List.any_eq_false]
    intro x hx heq
    rw [beq_iff_eq] at heq
    subst heq
    exact hsfnotmem hx
  unfold modalStepBranchS4KeyedBody at hsf
  rw [if_neg (by simp [hany])] at hsf
  rcases hpair : modalApplyOneS4Keyed φ₀ keys sf b acc with ⟨result, newAcc0⟩
  rw [hpair] at hsf
  dsimp only at hsf
  rcases hres : result with nf | brs | nf | -
  · rw [hres] at hsf
    simp only [Option.some.injEq, Prod.mk.injEq] at hsf
    obtain ⟨-, rfl, -, -⟩ := hsf
    intro e' he'
    simp only [List.mem_singleton] at he'
    subst he'
    exact List.Nodup.append hnodup (List.nodup_singleton sf)
      (fun a ha hmem => by simp only [List.mem_singleton] at hmem; exact hsfnotmem (hmem ▸ ha))
  · rw [hres] at hsf
    simp only [Option.some.injEq, Prod.mk.injEq] at hsf
    obtain ⟨-, rfl, -, -⟩ := hsf
    intro e' he'
    obtain ⟨x, -, rfl⟩ := List.mem_map.mp he'
    exact List.Nodup.append hnodup (List.nodup_singleton sf)
      (fun a ha hmem => by simp only [List.mem_singleton] at hmem; exact hsfnotmem (hmem ▸ ha))
  · rw [hres] at hsf
    simp only [Option.some.injEq, Prod.mk.injEq] at hsf
    obtain ⟨-, rfl, -, -⟩ := hsf
    intro e' he'
    simp only [List.mem_singleton] at he'
    subst he'
    exact hnodup
  · rw [hres] at hsf; simp at hsf

omit [DecidableEq Atom] [Hashable Atom] in
/-- Local re-derivation of `Soundness.lean`'s `private lemma accFreshInv_append` (unavailable
across files): prepending formulas to a branch preserves `accFreshInv`. -/
private lemma accFreshInv_append_S4
    {b : List (SignedFormula (Proposition Atom) WorldIndex)} {acc : Accessibility}
    (hInv : accFreshInv b acc)
    (xs : List (SignedFormula (Proposition Atom) WorldIndex)) :
    accFreshInv (xs ++ b) acc := by
  intro w w' hedge
  obtain ⟨hw, hw'⟩ := hInv w w' hedge
  exact ⟨Nat.lt_of_lt_of_le hw (modalNextWorld_le_append xs b),
         Nat.lt_of_lt_of_le hw' (modalNextWorld_le_append xs b)⟩

/-- **`accFresh`'s driver-level preservation**: the per-branch freshness invariant `accFreshInv`
survives an S4Keyed step. At the 12 non-minting shapes, `acc` is unchanged
(`modalApplyOneS4Keyed_nonMint_snd_eq_acc`) and every produced branch is a prepend of `b`, so
`accFreshInv_append_S4` carries the invariant forward directly. At the 2 minting shapes'
UNBLOCKED sub-case, `modalApplyOneS4Keyed` reduces to plain K's `modalApplyOne`, whose unique new
edge targets the genuinely fresh witness `modalNextWorld b` -- the standard K freshness argument
applies. At the BLOCKED sub-case the new edge targets `wBlock` instead -- NOT necessarily fresh,
so `keysWorldsKnown` (`wBlock ∈ modalKnownWorlds b`, hence `wBlock < modalNextWorld b` via
`modalNextWorld_gt`) is what bounds it, in place of the standard freshness argument. -/
lemma modalStepBranchS4_preserves_accFresh (φ₀ : Proposition Atom)
    (b e : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (keys : List (WorldIndex × Finset (Sign × Proposition Atom)))
    (newBs newExps : List (List (SignedFormula (Proposition Atom) WorldIndex)))
    (newAcc : Accessibility) (keys' : List (WorldIndex × Finset (Sign × Proposition Atom)))
    (hknown : accTargetsKnown b acc)
    (hKW : ∀ w k, (w, k) ∈ keys → w ∈ modalKnownWorlds b)
    (hFresh : accFreshInv b acc)
    (hstep : modalStepBranchS4Keyed φ₀ b e acc keys = some (newBs, newExps, newAcc, keys')) :
    ∀ b' ∈ newBs, accFreshInv b' newAcc := by
  have hstep0 := hstep
  unfold modalStepBranchS4Keyed at hstep0
  obtain ⟨sf, hsfmem, hsf⟩ := List.exists_of_findSome?_eq_some hstep0
  split_ifs at hsf with hexp
  rcases hpair : modalApplyOneS4Keyed φ₀ keys sf b acc with ⟨result, newAcc0⟩
  rw [hpair] at hsf
  dsimp only at hsf
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
        have hpaireq : (result, newAcc0) = modalApplyOneS4KeyedMint (⟨Sign.neg, .box ψ, sf.label⟩ :
            SignedFormula (Proposition Atom) WorldIndex) b acc := hpair.symm.trans heq2
        have hresulteq : result = (modalApplyOneS4KeyedMint (⟨Sign.neg, .box ψ, sf.label⟩ :
            SignedFormula (Proposition Atom) WorldIndex) b acc).fst :=
          congrArg Prod.fst hpaireq
        have haccnew0 : newAcc0 = (modalApplyOneS4KeyedMint (⟨Sign.neg, .box ψ, sf.label⟩ :
            SignedFormula (Proposition Atom) WorldIndex) b acc).snd :=
          congrArg Prod.snd hpaireq
        have hmintfst2 := hresulteq.trans
          (congrArg Prod.fst (modalApplyOneS4KeyedMint_boxNeg_eq_S4 b acc ψ sf.label))
        have hsndeq := haccnew0.trans
          (congrArg Prod.snd (modalApplyOneS4KeyedMint_boxNeg_eq_S4 b acc ψ sf.label))
        rw [hmintfst2] at hsf
        simp only [Option.some.injEq, Prod.mk.injEq] at hsf
        obtain ⟨rfl, -, hacceq3, -⟩ := hsf
        intro b' hb'
        simp only [List.mem_singleton] at hb'
        subst hb'
        rw [← hacceq3, hsndeq]
        intro w w' hedge
        rcases hasEdge_addEdge_cases hedge with ⟨rfl, rfl⟩ | hold
        · exact ⟨Nat.lt_of_lt_of_le (modalNextWorld_gt b sf hsfmem)
              (modalNextWorld_le_append _ b),
            modalNextWorld_gt _ (⟨.neg, ψ, modalNextWorld b⟩ :
                SignedFormula (Proposition Atom) WorldIndex)
              (List.mem_append_left _ (List.mem_append_left _ List.mem_cons_self))⟩
        · obtain ⟨ha, ha'⟩ := hFresh w w' hold
          exact ⟨Nat.lt_of_lt_of_le ha (modalNextWorld_le_append _ b),
            Nat.lt_of_lt_of_le ha' (modalNextWorld_le_append _ b)⟩
      · have heq2 : modalApplyOneS4Keyed φ₀ keys (⟨Sign.neg, .box ψ, sf.label⟩ :
            SignedFormula (Proposition Atom) WorldIndex) b acc
            = (.linear [], acc.addEdge sf.label wBlock) :=
          modalApplyOneS4Keyed_boxNeg_blocked_eq φ₀ b acc keys ψ sf.label wBlock hblock
        rw [hsfeq] at hpair
        have hpaireq : (result, newAcc0) = (RuleResult.linear [], acc.addEdge sf.label wBlock) :=
          hpair.symm.trans heq2
        have hreseq : result = RuleResult.linear [] := congrArg Prod.fst hpaireq
        have hacceq : newAcc0 = acc.addEdge sf.label wBlock := congrArg Prod.snd hpaireq
        rw [hreseq, hacceq] at hsf
        simp only [Option.some.injEq, Prod.mk.injEq] at hsf
        obtain ⟨rfl, -, rfl, -⟩ := hsf
        intro b' hb'
        simp only [List.mem_singleton] at hb'
        subst b'
        intro w w' hedge
        rcases hasEdge_addEdge_cases hedge with ⟨rfl, rfl⟩ | hold
        · refine ⟨modalNextWorld_gt b sf hsfmem, ?_⟩
          obtain ⟨sf'', hsf''mem, hsf''lab⟩ := (mem_modalKnownWorlds b w').mp
            (hKW w' _ (blockingWorldS4Keyed_eq_birthContent φ₀ b keys .neg ψ sf.label w'
              hblock))
          exact hsf''lab ▸ modalNextWorld_gt b sf'' hsf''mem
        · exact hFresh w w' hold
    · have hsfeq : sf = (⟨Sign.pos, .diamond ψ, sf.label⟩ :
          SignedFormula (Proposition Atom) WorldIndex) := by rw [← hs, ← hf]
      rcases hblock : blockingWorldS4Keyed φ₀ b keys .pos ψ sf.label with _ | wBlock
      · have heq2 : modalApplyOneS4Keyed φ₀ keys (⟨Sign.pos, .diamond ψ, sf.label⟩ :
            SignedFormula (Proposition Atom) WorldIndex) b acc
            = modalApplyOneS4KeyedMint (⟨Sign.pos, .diamond ψ, sf.label⟩ :
              SignedFormula (Proposition Atom) WorldIndex) b acc :=
          modalApplyOneS4Keyed_diaPos_unblocked_eq φ₀ b acc keys ψ sf.label hblock
        rw [hsfeq] at hpair
        have hpaireq : (result, newAcc0) =
            modalApplyOneS4KeyedMint (⟨Sign.pos, .diamond ψ, sf.label⟩ :
              SignedFormula (Proposition Atom) WorldIndex) b acc := hpair.symm.trans heq2
        have hresulteq : result = (modalApplyOneS4KeyedMint (⟨Sign.pos, .diamond ψ, sf.label⟩ :
            SignedFormula (Proposition Atom) WorldIndex) b acc).fst :=
          congrArg Prod.fst hpaireq
        have haccnew0 : newAcc0 = (modalApplyOneS4KeyedMint (⟨Sign.pos, .diamond ψ, sf.label⟩ :
            SignedFormula (Proposition Atom) WorldIndex) b acc).snd :=
          congrArg Prod.snd hpaireq
        have hmintfst2 := hresulteq.trans
          (congrArg Prod.fst (modalApplyOneS4KeyedMint_diaPos_eq_S4 b acc ψ sf.label))
        have hsndeq := haccnew0.trans
          (congrArg Prod.snd (modalApplyOneS4KeyedMint_diaPos_eq_S4 b acc ψ sf.label))
        rw [hmintfst2] at hsf
        simp only [Option.some.injEq, Prod.mk.injEq] at hsf
        obtain ⟨rfl, -, hacceq3, -⟩ := hsf
        intro b' hb'
        simp only [List.mem_singleton] at hb'
        subst hb'
        rw [← hacceq3, hsndeq]
        intro w w' hedge
        rcases hasEdge_addEdge_cases hedge with ⟨rfl, rfl⟩ | hold
        · exact ⟨Nat.lt_of_lt_of_le (modalNextWorld_gt b sf hsfmem)
              (modalNextWorld_le_append _ b),
            modalNextWorld_gt _ (⟨.pos, ψ, modalNextWorld b⟩ :
                SignedFormula (Proposition Atom) WorldIndex)
              (List.mem_append_left _ (List.mem_append_left _ List.mem_cons_self))⟩
        · obtain ⟨ha, ha'⟩ := hFresh w w' hold
          exact ⟨Nat.lt_of_lt_of_le ha (modalNextWorld_le_append _ b),
            Nat.lt_of_lt_of_le ha' (modalNextWorld_le_append _ b)⟩
      · have heq2 : modalApplyOneS4Keyed φ₀ keys (⟨Sign.pos, .diamond ψ, sf.label⟩ :
            SignedFormula (Proposition Atom) WorldIndex) b acc
            = (.linear [], acc.addEdge sf.label wBlock) :=
          modalApplyOneS4Keyed_diaPos_blocked_eq φ₀ b acc keys ψ sf.label wBlock hblock
        rw [hsfeq] at hpair
        have hpaireq : (result, newAcc0) = (RuleResult.linear [], acc.addEdge sf.label wBlock) :=
          hpair.symm.trans heq2
        have hreseq : result = RuleResult.linear [] := congrArg Prod.fst hpaireq
        have hacceq : newAcc0 = acc.addEdge sf.label wBlock := congrArg Prod.snd hpaireq
        rw [hreseq, hacceq] at hsf
        simp only [Option.some.injEq, Prod.mk.injEq] at hsf
        obtain ⟨rfl, -, rfl, -⟩ := hsf
        intro b' hb'
        simp only [List.mem_singleton] at hb'
        subst b'
        intro w w' hedge
        rcases hasEdge_addEdge_cases hedge with ⟨rfl, rfl⟩ | hold
        · refine ⟨modalNextWorld_gt b sf hsfmem, ?_⟩
          obtain ⟨sf'', hsf''mem, hsf''lab⟩ := (mem_modalKnownWorlds b w').mp
            (hKW w' _ (blockingWorldS4Keyed_eq_birthContent φ₀ b keys .pos ψ sf.label w'
              hblock))
          exact hsf''lab ▸ modalNextWorld_gt b sf'' hsf''mem
        · exact hFresh w w' hold
  · have hnbd : ¬ (sf.sign = .neg ∧ ∃ φ, sf.formula = .box φ) ∧
        ¬ (sf.sign = .pos ∧ ∃ φ, sf.formula = .diamond φ) :=
      ⟨fun hc => hmint (Or.inl hc), fun hc => hmint (Or.inr hc)⟩
    have haccunchanged : newAcc0 = acc := by
      have hthis := modalApplyOneS4Keyed_nonMint_snd_eq_acc φ₀ keys sf b acc hsfmem hknown hnbd
      rw [hpair] at hthis
      exact hthis
    subst haccunchanged
    rcases hres : result with nf | brs | nf | -
    · rw [hres] at hsf
      simp only [Option.some.injEq, Prod.mk.injEq] at hsf
      obtain ⟨rfl, -, rfl, -⟩ := hsf
      intro b' hb'
      simp only [List.mem_singleton] at hb'
      subst hb'
      exact accFreshInv_append_S4 hFresh nf
    · rw [hres] at hsf
      simp only [Option.some.injEq, Prod.mk.injEq] at hsf
      obtain ⟨rfl, -, rfl, -⟩ := hsf
      intro b' hb'
      obtain ⟨x, -, rfl⟩ := List.mem_map.mp hb'
      exact accFreshInv_append_S4 hFresh x
    · rw [hres] at hsf
      simp only [Option.some.injEq, Prod.mk.injEq] at hsf
      obtain ⟨rfl, -, rfl, -⟩ := hsf
      intro b' hb'
      simp only [List.mem_singleton] at hb'
      subst hb'
      exact accFreshInv_append_S4 hFresh nf
    · rw [hres] at hsf; simp at hsf

/-- **`accFresh`'s ordered-driver preservation.** Verbatim transcription of
`modalStepBranchS4_preserves_accFresh` against the ordered stepper, via
`modalStepBranchS4KeyedOrdered_selected_mem` in place of the direct `findSome?` extraction; the
three-regime case split (non-minting / minting-unblocked / minting-blocked) and its
`keysWorldsKnown` dependency at the blocked sub-case are otherwise unchanged. -/
lemma modalStepBranchS4KeyedOrdered_preserves_accFresh (φ₀ : Proposition Atom)
    (b e : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (keys : List (WorldIndex × Finset (Sign × Proposition Atom)))
    (newBs newExps : List (List (SignedFormula (Proposition Atom) WorldIndex)))
    (newAcc : Accessibility) (keys' : List (WorldIndex × Finset (Sign × Proposition Atom)))
    (hknown : accTargetsKnown b acc)
    (hKW : ∀ w k, (w, k) ∈ keys → w ∈ modalKnownWorlds b)
    (hFresh : accFreshInv b acc)
    (hstep : modalStepBranchS4KeyedOrdered φ₀ b e acc keys =
      some (newBs, newExps, newAcc, keys')) :
    ∀ b' ∈ newBs, accFreshInv b' newAcc := by
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
        have hpaireq : (result, newAcc0) = modalApplyOneS4KeyedMint (⟨Sign.neg, .box ψ, sf.label⟩ :
            SignedFormula (Proposition Atom) WorldIndex) b acc := hpair.symm.trans heq2
        have hresulteq : result = (modalApplyOneS4KeyedMint (⟨Sign.neg, .box ψ, sf.label⟩ :
            SignedFormula (Proposition Atom) WorldIndex) b acc).fst :=
          congrArg Prod.fst hpaireq
        have haccnew0 : newAcc0 = (modalApplyOneS4KeyedMint (⟨Sign.neg, .box ψ, sf.label⟩ :
            SignedFormula (Proposition Atom) WorldIndex) b acc).snd :=
          congrArg Prod.snd hpaireq
        have hmintfst2 := hresulteq.trans
          (congrArg Prod.fst (modalApplyOneS4KeyedMint_boxNeg_eq_S4 b acc ψ sf.label))
        have hsndeq := haccnew0.trans
          (congrArg Prod.snd (modalApplyOneS4KeyedMint_boxNeg_eq_S4 b acc ψ sf.label))
        rw [hmintfst2] at hsf
        simp only [Option.some.injEq, Prod.mk.injEq] at hsf
        obtain ⟨rfl, -, hacceq3, -⟩ := hsf
        intro b' hb'
        simp only [List.mem_singleton] at hb'
        subst hb'
        rw [← hacceq3, hsndeq]
        intro w w' hedge
        rcases hasEdge_addEdge_cases hedge with ⟨rfl, rfl⟩ | hold
        · exact ⟨Nat.lt_of_lt_of_le (modalNextWorld_gt b sf hsfmem)
              (modalNextWorld_le_append _ b),
            modalNextWorld_gt _ (⟨.neg, ψ, modalNextWorld b⟩ :
                SignedFormula (Proposition Atom) WorldIndex)
              (List.mem_append_left _ (List.mem_append_left _ List.mem_cons_self))⟩
        · obtain ⟨ha, ha'⟩ := hFresh w w' hold
          exact ⟨Nat.lt_of_lt_of_le ha (modalNextWorld_le_append _ b),
            Nat.lt_of_lt_of_le ha' (modalNextWorld_le_append _ b)⟩
      · have heq2 : modalApplyOneS4Keyed φ₀ keys (⟨Sign.neg, .box ψ, sf.label⟩ :
            SignedFormula (Proposition Atom) WorldIndex) b acc
            = (.linear [], acc.addEdge sf.label wBlock) :=
          modalApplyOneS4Keyed_boxNeg_blocked_eq φ₀ b acc keys ψ sf.label wBlock hblock
        rw [hsfeq] at hpair
        have hpaireq : (result, newAcc0) = (RuleResult.linear [], acc.addEdge sf.label wBlock) :=
          hpair.symm.trans heq2
        have hreseq : result = RuleResult.linear [] := congrArg Prod.fst hpaireq
        have hacceq : newAcc0 = acc.addEdge sf.label wBlock := congrArg Prod.snd hpaireq
        rw [hreseq, hacceq] at hsf
        simp only [Option.some.injEq, Prod.mk.injEq] at hsf
        obtain ⟨rfl, -, rfl, -⟩ := hsf
        intro b' hb'
        simp only [List.mem_singleton] at hb'
        subst b'
        intro w w' hedge
        rcases hasEdge_addEdge_cases hedge with ⟨rfl, rfl⟩ | hold
        · refine ⟨modalNextWorld_gt b sf hsfmem, ?_⟩
          obtain ⟨sf'', hsf''mem, hsf''lab⟩ := (mem_modalKnownWorlds b w').mp
            (hKW w' _ (blockingWorldS4Keyed_eq_birthContent φ₀ b keys .neg ψ sf.label w'
              hblock))
          exact hsf''lab ▸ modalNextWorld_gt b sf'' hsf''mem
        · exact hFresh w w' hold
    · have hsfeq : sf = (⟨Sign.pos, .diamond ψ, sf.label⟩ :
          SignedFormula (Proposition Atom) WorldIndex) := by rw [← hs, ← hf]
      rcases hblock : blockingWorldS4Keyed φ₀ b keys .pos ψ sf.label with _ | wBlock
      · have heq2 : modalApplyOneS4Keyed φ₀ keys (⟨Sign.pos, .diamond ψ, sf.label⟩ :
            SignedFormula (Proposition Atom) WorldIndex) b acc
            = modalApplyOneS4KeyedMint (⟨Sign.pos, .diamond ψ, sf.label⟩ :
              SignedFormula (Proposition Atom) WorldIndex) b acc :=
          modalApplyOneS4Keyed_diaPos_unblocked_eq φ₀ b acc keys ψ sf.label hblock
        rw [hsfeq] at hpair
        have hpaireq : (result, newAcc0) =
            modalApplyOneS4KeyedMint (⟨Sign.pos, .diamond ψ, sf.label⟩ :
              SignedFormula (Proposition Atom) WorldIndex) b acc := hpair.symm.trans heq2
        have hresulteq : result = (modalApplyOneS4KeyedMint (⟨Sign.pos, .diamond ψ, sf.label⟩ :
            SignedFormula (Proposition Atom) WorldIndex) b acc).fst :=
          congrArg Prod.fst hpaireq
        have haccnew0 : newAcc0 = (modalApplyOneS4KeyedMint (⟨Sign.pos, .diamond ψ, sf.label⟩ :
            SignedFormula (Proposition Atom) WorldIndex) b acc).snd :=
          congrArg Prod.snd hpaireq
        have hmintfst2 := hresulteq.trans
          (congrArg Prod.fst (modalApplyOneS4KeyedMint_diaPos_eq_S4 b acc ψ sf.label))
        have hsndeq := haccnew0.trans
          (congrArg Prod.snd (modalApplyOneS4KeyedMint_diaPos_eq_S4 b acc ψ sf.label))
        rw [hmintfst2] at hsf
        simp only [Option.some.injEq, Prod.mk.injEq] at hsf
        obtain ⟨rfl, -, hacceq3, -⟩ := hsf
        intro b' hb'
        simp only [List.mem_singleton] at hb'
        subst hb'
        rw [← hacceq3, hsndeq]
        intro w w' hedge
        rcases hasEdge_addEdge_cases hedge with ⟨rfl, rfl⟩ | hold
        · exact ⟨Nat.lt_of_lt_of_le (modalNextWorld_gt b sf hsfmem)
              (modalNextWorld_le_append _ b),
            modalNextWorld_gt _ (⟨.pos, ψ, modalNextWorld b⟩ :
                SignedFormula (Proposition Atom) WorldIndex)
              (List.mem_append_left _ (List.mem_append_left _ List.mem_cons_self))⟩
        · obtain ⟨ha, ha'⟩ := hFresh w w' hold
          exact ⟨Nat.lt_of_lt_of_le ha (modalNextWorld_le_append _ b),
            Nat.lt_of_lt_of_le ha' (modalNextWorld_le_append _ b)⟩
      · have heq2 : modalApplyOneS4Keyed φ₀ keys (⟨Sign.pos, .diamond ψ, sf.label⟩ :
            SignedFormula (Proposition Atom) WorldIndex) b acc
            = (.linear [], acc.addEdge sf.label wBlock) :=
          modalApplyOneS4Keyed_diaPos_blocked_eq φ₀ b acc keys ψ sf.label wBlock hblock
        rw [hsfeq] at hpair
        have hpaireq : (result, newAcc0) = (RuleResult.linear [], acc.addEdge sf.label wBlock) :=
          hpair.symm.trans heq2
        have hreseq : result = RuleResult.linear [] := congrArg Prod.fst hpaireq
        have hacceq : newAcc0 = acc.addEdge sf.label wBlock := congrArg Prod.snd hpaireq
        rw [hreseq, hacceq] at hsf
        simp only [Option.some.injEq, Prod.mk.injEq] at hsf
        obtain ⟨rfl, -, rfl, -⟩ := hsf
        intro b' hb'
        simp only [List.mem_singleton] at hb'
        subst b'
        intro w w' hedge
        rcases hasEdge_addEdge_cases hedge with ⟨rfl, rfl⟩ | hold
        · refine ⟨modalNextWorld_gt b sf hsfmem, ?_⟩
          obtain ⟨sf'', hsf''mem, hsf''lab⟩ := (mem_modalKnownWorlds b w').mp
            (hKW w' _ (blockingWorldS4Keyed_eq_birthContent φ₀ b keys .pos ψ sf.label w'
              hblock))
          exact hsf''lab ▸ modalNextWorld_gt b sf'' hsf''mem
        · exact hFresh w w' hold
  · have hnbd : ¬ (sf.sign = .neg ∧ ∃ φ, sf.formula = .box φ) ∧
        ¬ (sf.sign = .pos ∧ ∃ φ, sf.formula = .diamond φ) :=
      ⟨fun hc => hmint (Or.inl hc), fun hc => hmint (Or.inr hc)⟩
    have haccunchanged : newAcc0 = acc := by
      have hthis := modalApplyOneS4Keyed_nonMint_snd_eq_acc φ₀ keys sf b acc hsfmem hknown hnbd
      rw [hpair] at hthis
      exact hthis
    subst haccunchanged
    rcases hres : result with nf | brs | nf | -
    · rw [hres] at hsf
      simp only [Option.some.injEq, Prod.mk.injEq] at hsf
      obtain ⟨rfl, -, rfl, -⟩ := hsf
      intro b' hb'
      simp only [List.mem_singleton] at hb'
      subst hb'
      exact accFreshInv_append_S4 hFresh nf
    · rw [hres] at hsf
      simp only [Option.some.injEq, Prod.mk.injEq] at hsf
      obtain ⟨rfl, -, rfl, -⟩ := hsf
      intro b' hb'
      obtain ⟨x, -, rfl⟩ := List.mem_map.mp hb'
      exact accFreshInv_append_S4 hFresh x
    · rw [hres] at hsf
      simp only [Option.some.injEq, Prod.mk.injEq] at hsf
      obtain ⟨rfl, -, rfl, -⟩ := hsf
      intro b' hb'
      simp only [List.mem_singleton] at hb'
      subst hb'
      exact accFreshInv_append_S4 hFresh nf
    · rw [hres] at hsf; simp at hsf

/-- **`accKnown`'s driver-level preservation**: every `acc`-edge target stays a known branch
world across an S4Keyed step. Mirrors `accFresh`'s case split exactly (same three regimes,
same `keysWorldsKnown` dependency at the BLOCKED sub-case), but concludes membership in
`modalKnownWorlds b'` rather than a numeric bound, via `modalKnownWorlds_mono_append` to lift
old facts across a branch prepend. -/
lemma modalStepBranchS4_preserves_accKnown (φ₀ : Proposition Atom)
    (b e : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (keys : List (WorldIndex × Finset (Sign × Proposition Atom)))
    (newBs newExps : List (List (SignedFormula (Proposition Atom) WorldIndex)))
    (newAcc : Accessibility) (keys' : List (WorldIndex × Finset (Sign × Proposition Atom)))
    (hknown : accTargetsKnown b acc)
    (hKW : ∀ w k, (w, k) ∈ keys → w ∈ modalKnownWorlds b)
    (hstep : modalStepBranchS4Keyed φ₀ b e acc keys = some (newBs, newExps, newAcc, keys')) :
    ∀ b' ∈ newBs, accTargetsKnown b' newAcc := by
  have hstep0 := hstep
  unfold modalStepBranchS4Keyed at hstep0
  obtain ⟨sf, hsfmem, hsf⟩ := List.exists_of_findSome?_eq_some hstep0
  split_ifs at hsf with hexp
  rcases hpair : modalApplyOneS4Keyed φ₀ keys sf b acc with ⟨result, newAcc0⟩
  rw [hpair] at hsf
  dsimp only at hsf
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
        have hpaireq : (result, newAcc0) = modalApplyOneS4KeyedMint (⟨Sign.neg, .box ψ, sf.label⟩ :
            SignedFormula (Proposition Atom) WorldIndex) b acc := hpair.symm.trans heq2
        have hresulteq : result = (modalApplyOneS4KeyedMint (⟨Sign.neg, .box ψ, sf.label⟩ :
            SignedFormula (Proposition Atom) WorldIndex) b acc).fst :=
          congrArg Prod.fst hpaireq
        have haccnew0 : newAcc0 = (modalApplyOneS4KeyedMint (⟨Sign.neg, .box ψ, sf.label⟩ :
            SignedFormula (Proposition Atom) WorldIndex) b acc).snd :=
          congrArg Prod.snd hpaireq
        have hmintfst2 := hresulteq.trans
          (congrArg Prod.fst (modalApplyOneS4KeyedMint_boxNeg_eq_S4 b acc ψ sf.label))
        have hsndeq := haccnew0.trans
          (congrArg Prod.snd (modalApplyOneS4KeyedMint_boxNeg_eq_S4 b acc ψ sf.label))
        rw [hmintfst2] at hsf
        simp only [Option.some.injEq, Prod.mk.injEq] at hsf
        obtain ⟨rfl, -, hacceq3, -⟩ := hsf
        intro b' hb'
        simp only [List.mem_singleton] at hb'
        subst hb'
        rw [← hacceq3, hsndeq]
        intro w w' hedge
        rcases hasEdge_addEdge_cases hedge with ⟨rfl, rfl⟩ | hold
        · rw [mem_modalKnownWorlds]
          exact ⟨⟨.neg, ψ, modalNextWorld b⟩,
            List.mem_append_left _ (List.mem_append_left _ List.mem_cons_self), rfl⟩
        · exact modalKnownWorlds_mono_append _ b _ (hknown w w' hold)
      · have heq2 : modalApplyOneS4Keyed φ₀ keys (⟨Sign.neg, .box ψ, sf.label⟩ :
            SignedFormula (Proposition Atom) WorldIndex) b acc
            = (.linear [], acc.addEdge sf.label wBlock) :=
          modalApplyOneS4Keyed_boxNeg_blocked_eq φ₀ b acc keys ψ sf.label wBlock hblock
        rw [hsfeq] at hpair
        have hpaireq : (result, newAcc0) = (RuleResult.linear [], acc.addEdge sf.label wBlock) :=
          hpair.symm.trans heq2
        have hreseq : result = RuleResult.linear [] := congrArg Prod.fst hpaireq
        have hacceq : newAcc0 = acc.addEdge sf.label wBlock := congrArg Prod.snd hpaireq
        rw [hreseq, hacceq] at hsf
        simp only [Option.some.injEq, Prod.mk.injEq] at hsf
        obtain ⟨rfl, -, rfl, -⟩ := hsf
        intro b' hb'
        simp only [List.mem_singleton] at hb'
        subst b'
        intro w w' hedge
        rcases hasEdge_addEdge_cases hedge with ⟨rfl, rfl⟩ | hold
        · exact hKW w' _ (blockingWorldS4Keyed_eq_birthContent φ₀ b keys .neg ψ sf.label w'
            hblock)
        · exact hknown w w' hold
    · have hsfeq : sf = (⟨Sign.pos, .diamond ψ, sf.label⟩ :
          SignedFormula (Proposition Atom) WorldIndex) := by rw [← hs, ← hf]
      rcases hblock : blockingWorldS4Keyed φ₀ b keys .pos ψ sf.label with _ | wBlock
      · have heq2 : modalApplyOneS4Keyed φ₀ keys (⟨Sign.pos, .diamond ψ, sf.label⟩ :
            SignedFormula (Proposition Atom) WorldIndex) b acc
            = modalApplyOneS4KeyedMint (⟨Sign.pos, .diamond ψ, sf.label⟩ :
              SignedFormula (Proposition Atom) WorldIndex) b acc :=
          modalApplyOneS4Keyed_diaPos_unblocked_eq φ₀ b acc keys ψ sf.label hblock
        rw [hsfeq] at hpair
        have hpaireq : (result, newAcc0) =
            modalApplyOneS4KeyedMint (⟨Sign.pos, .diamond ψ, sf.label⟩ :
              SignedFormula (Proposition Atom) WorldIndex) b acc := hpair.symm.trans heq2
        have hresulteq : result = (modalApplyOneS4KeyedMint (⟨Sign.pos, .diamond ψ, sf.label⟩ :
            SignedFormula (Proposition Atom) WorldIndex) b acc).fst :=
          congrArg Prod.fst hpaireq
        have haccnew0 : newAcc0 = (modalApplyOneS4KeyedMint (⟨Sign.pos, .diamond ψ, sf.label⟩ :
            SignedFormula (Proposition Atom) WorldIndex) b acc).snd :=
          congrArg Prod.snd hpaireq
        have hmintfst2 := hresulteq.trans
          (congrArg Prod.fst (modalApplyOneS4KeyedMint_diaPos_eq_S4 b acc ψ sf.label))
        have hsndeq := haccnew0.trans
          (congrArg Prod.snd (modalApplyOneS4KeyedMint_diaPos_eq_S4 b acc ψ sf.label))
        rw [hmintfst2] at hsf
        simp only [Option.some.injEq, Prod.mk.injEq] at hsf
        obtain ⟨rfl, -, hacceq3, -⟩ := hsf
        intro b' hb'
        simp only [List.mem_singleton] at hb'
        subst hb'
        rw [← hacceq3, hsndeq]
        intro w w' hedge
        rcases hasEdge_addEdge_cases hedge with ⟨rfl, rfl⟩ | hold
        · rw [mem_modalKnownWorlds]
          exact ⟨⟨.pos, ψ, modalNextWorld b⟩,
            List.mem_append_left _ (List.mem_append_left _ List.mem_cons_self), rfl⟩
        · exact modalKnownWorlds_mono_append _ b _ (hknown w w' hold)
      · have heq2 : modalApplyOneS4Keyed φ₀ keys (⟨Sign.pos, .diamond ψ, sf.label⟩ :
            SignedFormula (Proposition Atom) WorldIndex) b acc
            = (.linear [], acc.addEdge sf.label wBlock) :=
          modalApplyOneS4Keyed_diaPos_blocked_eq φ₀ b acc keys ψ sf.label wBlock hblock
        rw [hsfeq] at hpair
        have hpaireq : (result, newAcc0) = (RuleResult.linear [], acc.addEdge sf.label wBlock) :=
          hpair.symm.trans heq2
        have hreseq : result = RuleResult.linear [] := congrArg Prod.fst hpaireq
        have hacceq : newAcc0 = acc.addEdge sf.label wBlock := congrArg Prod.snd hpaireq
        rw [hreseq, hacceq] at hsf
        simp only [Option.some.injEq, Prod.mk.injEq] at hsf
        obtain ⟨rfl, -, rfl, -⟩ := hsf
        intro b' hb'
        simp only [List.mem_singleton] at hb'
        subst b'
        intro w w' hedge
        rcases hasEdge_addEdge_cases hedge with ⟨rfl, rfl⟩ | hold
        · exact hKW w' _ (blockingWorldS4Keyed_eq_birthContent φ₀ b keys .pos ψ sf.label w'
            hblock)
        · exact hknown w w' hold
  · have hnbd : ¬ (sf.sign = .neg ∧ ∃ φ, sf.formula = .box φ) ∧
        ¬ (sf.sign = .pos ∧ ∃ φ, sf.formula = .diamond φ) :=
      ⟨fun hc => hmint (Or.inl hc), fun hc => hmint (Or.inr hc)⟩
    have haccunchanged : newAcc0 = acc := by
      have hthis := modalApplyOneS4Keyed_nonMint_snd_eq_acc φ₀ keys sf b acc hsfmem hknown hnbd
      rw [hpair] at hthis
      exact hthis
    subst haccunchanged
    rcases hres : result with nf | brs | nf | -
    · rw [hres] at hsf
      simp only [Option.some.injEq, Prod.mk.injEq] at hsf
      obtain ⟨rfl, -, rfl, -⟩ := hsf
      intro b' hb'
      simp only [List.mem_singleton] at hb'
      subst hb'
      intro w w' hedge
      exact modalKnownWorlds_mono_append _ b _ (hknown w w' hedge)
    · rw [hres] at hsf
      simp only [Option.some.injEq, Prod.mk.injEq] at hsf
      obtain ⟨rfl, -, rfl, -⟩ := hsf
      intro b' hb'
      obtain ⟨x, -, rfl⟩ := List.mem_map.mp hb'
      intro w w' hedge
      exact modalKnownWorlds_mono_append _ b _ (hknown w w' hedge)
    · rw [hres] at hsf
      simp only [Option.some.injEq, Prod.mk.injEq] at hsf
      obtain ⟨rfl, -, rfl, -⟩ := hsf
      intro b' hb'
      simp only [List.mem_singleton] at hb'
      subst hb'
      intro w w' hedge
      exact modalKnownWorlds_mono_append _ b _ (hknown w w' hedge)
    · rw [hres] at hsf; simp at hsf

/-- **`accKnown`'s ordered-driver preservation.** Verbatim transcription of
`modalStepBranchS4_preserves_accKnown` against the ordered stepper, via
`modalStepBranchS4KeyedOrdered_selected_mem` in place of the direct `findSome?` extraction; the
three-regime case split mirrors `accFresh`'s exactly, as in the unordered original. -/
lemma modalStepBranchS4KeyedOrdered_preserves_accKnown (φ₀ : Proposition Atom)
    (b e : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (keys : List (WorldIndex × Finset (Sign × Proposition Atom)))
    (newBs newExps : List (List (SignedFormula (Proposition Atom) WorldIndex)))
    (newAcc : Accessibility) (keys' : List (WorldIndex × Finset (Sign × Proposition Atom)))
    (hknown : accTargetsKnown b acc)
    (hKW : ∀ w k, (w, k) ∈ keys → w ∈ modalKnownWorlds b)
    (hstep : modalStepBranchS4KeyedOrdered φ₀ b e acc keys =
      some (newBs, newExps, newAcc, keys')) :
    ∀ b' ∈ newBs, accTargetsKnown b' newAcc := by
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
        have hpaireq : (result, newAcc0) = modalApplyOneS4KeyedMint (⟨Sign.neg, .box ψ, sf.label⟩ :
            SignedFormula (Proposition Atom) WorldIndex) b acc := hpair.symm.trans heq2
        have hresulteq : result = (modalApplyOneS4KeyedMint (⟨Sign.neg, .box ψ, sf.label⟩ :
            SignedFormula (Proposition Atom) WorldIndex) b acc).fst :=
          congrArg Prod.fst hpaireq
        have haccnew0 : newAcc0 = (modalApplyOneS4KeyedMint (⟨Sign.neg, .box ψ, sf.label⟩ :
            SignedFormula (Proposition Atom) WorldIndex) b acc).snd :=
          congrArg Prod.snd hpaireq
        have hmintfst2 := hresulteq.trans
          (congrArg Prod.fst (modalApplyOneS4KeyedMint_boxNeg_eq_S4 b acc ψ sf.label))
        have hsndeq := haccnew0.trans
          (congrArg Prod.snd (modalApplyOneS4KeyedMint_boxNeg_eq_S4 b acc ψ sf.label))
        rw [hmintfst2] at hsf
        simp only [Option.some.injEq, Prod.mk.injEq] at hsf
        obtain ⟨rfl, -, hacceq3, -⟩ := hsf
        intro b' hb'
        simp only [List.mem_singleton] at hb'
        subst hb'
        rw [← hacceq3, hsndeq]
        intro w w' hedge
        rcases hasEdge_addEdge_cases hedge with ⟨rfl, rfl⟩ | hold
        · rw [mem_modalKnownWorlds]
          exact ⟨⟨.neg, ψ, modalNextWorld b⟩,
            List.mem_append_left _ (List.mem_append_left _ List.mem_cons_self), rfl⟩
        · exact modalKnownWorlds_mono_append _ b _ (hknown w w' hold)
      · have heq2 : modalApplyOneS4Keyed φ₀ keys (⟨Sign.neg, .box ψ, sf.label⟩ :
            SignedFormula (Proposition Atom) WorldIndex) b acc
            = (.linear [], acc.addEdge sf.label wBlock) :=
          modalApplyOneS4Keyed_boxNeg_blocked_eq φ₀ b acc keys ψ sf.label wBlock hblock
        rw [hsfeq] at hpair
        have hpaireq : (result, newAcc0) = (RuleResult.linear [], acc.addEdge sf.label wBlock) :=
          hpair.symm.trans heq2
        have hreseq : result = RuleResult.linear [] := congrArg Prod.fst hpaireq
        have hacceq : newAcc0 = acc.addEdge sf.label wBlock := congrArg Prod.snd hpaireq
        rw [hreseq, hacceq] at hsf
        simp only [Option.some.injEq, Prod.mk.injEq] at hsf
        obtain ⟨rfl, -, rfl, -⟩ := hsf
        intro b' hb'
        simp only [List.mem_singleton] at hb'
        subst b'
        intro w w' hedge
        rcases hasEdge_addEdge_cases hedge with ⟨rfl, rfl⟩ | hold
        · exact hKW w' _ (blockingWorldS4Keyed_eq_birthContent φ₀ b keys .neg ψ sf.label w'
            hblock)
        · exact hknown w w' hold
    · have hsfeq : sf = (⟨Sign.pos, .diamond ψ, sf.label⟩ :
          SignedFormula (Proposition Atom) WorldIndex) := by rw [← hs, ← hf]
      rcases hblock : blockingWorldS4Keyed φ₀ b keys .pos ψ sf.label with _ | wBlock
      · have heq2 : modalApplyOneS4Keyed φ₀ keys (⟨Sign.pos, .diamond ψ, sf.label⟩ :
            SignedFormula (Proposition Atom) WorldIndex) b acc
            = modalApplyOneS4KeyedMint (⟨Sign.pos, .diamond ψ, sf.label⟩ :
              SignedFormula (Proposition Atom) WorldIndex) b acc :=
          modalApplyOneS4Keyed_diaPos_unblocked_eq φ₀ b acc keys ψ sf.label hblock
        rw [hsfeq] at hpair
        have hpaireq : (result, newAcc0) =
            modalApplyOneS4KeyedMint (⟨Sign.pos, .diamond ψ, sf.label⟩ :
              SignedFormula (Proposition Atom) WorldIndex) b acc := hpair.symm.trans heq2
        have hresulteq : result = (modalApplyOneS4KeyedMint (⟨Sign.pos, .diamond ψ, sf.label⟩ :
            SignedFormula (Proposition Atom) WorldIndex) b acc).fst :=
          congrArg Prod.fst hpaireq
        have haccnew0 : newAcc0 = (modalApplyOneS4KeyedMint (⟨Sign.pos, .diamond ψ, sf.label⟩ :
            SignedFormula (Proposition Atom) WorldIndex) b acc).snd :=
          congrArg Prod.snd hpaireq
        have hmintfst2 := hresulteq.trans
          (congrArg Prod.fst (modalApplyOneS4KeyedMint_diaPos_eq_S4 b acc ψ sf.label))
        have hsndeq := haccnew0.trans
          (congrArg Prod.snd (modalApplyOneS4KeyedMint_diaPos_eq_S4 b acc ψ sf.label))
        rw [hmintfst2] at hsf
        simp only [Option.some.injEq, Prod.mk.injEq] at hsf
        obtain ⟨rfl, -, hacceq3, -⟩ := hsf
        intro b' hb'
        simp only [List.mem_singleton] at hb'
        subst hb'
        rw [← hacceq3, hsndeq]
        intro w w' hedge
        rcases hasEdge_addEdge_cases hedge with ⟨rfl, rfl⟩ | hold
        · rw [mem_modalKnownWorlds]
          exact ⟨⟨.pos, ψ, modalNextWorld b⟩,
            List.mem_append_left _ (List.mem_append_left _ List.mem_cons_self), rfl⟩
        · exact modalKnownWorlds_mono_append _ b _ (hknown w w' hold)
      · have heq2 : modalApplyOneS4Keyed φ₀ keys (⟨Sign.pos, .diamond ψ, sf.label⟩ :
            SignedFormula (Proposition Atom) WorldIndex) b acc
            = (.linear [], acc.addEdge sf.label wBlock) :=
          modalApplyOneS4Keyed_diaPos_blocked_eq φ₀ b acc keys ψ sf.label wBlock hblock
        rw [hsfeq] at hpair
        have hpaireq : (result, newAcc0) = (RuleResult.linear [], acc.addEdge sf.label wBlock) :=
          hpair.symm.trans heq2
        have hreseq : result = RuleResult.linear [] := congrArg Prod.fst hpaireq
        have hacceq : newAcc0 = acc.addEdge sf.label wBlock := congrArg Prod.snd hpaireq
        rw [hreseq, hacceq] at hsf
        simp only [Option.some.injEq, Prod.mk.injEq] at hsf
        obtain ⟨rfl, -, rfl, -⟩ := hsf
        intro b' hb'
        simp only [List.mem_singleton] at hb'
        subst b'
        intro w w' hedge
        rcases hasEdge_addEdge_cases hedge with ⟨rfl, rfl⟩ | hold
        · exact hKW w' _ (blockingWorldS4Keyed_eq_birthContent φ₀ b keys .pos ψ sf.label w'
            hblock)
        · exact hknown w w' hold
  · have hnbd : ¬ (sf.sign = .neg ∧ ∃ φ, sf.formula = .box φ) ∧
        ¬ (sf.sign = .pos ∧ ∃ φ, sf.formula = .diamond φ) :=
      ⟨fun hc => hmint (Or.inl hc), fun hc => hmint (Or.inr hc)⟩
    have haccunchanged : newAcc0 = acc := by
      have hthis := modalApplyOneS4Keyed_nonMint_snd_eq_acc φ₀ keys sf b acc hsfmem hknown hnbd
      rw [hpair] at hthis
      exact hthis
    subst haccunchanged
    rcases hres : result with nf | brs | nf | -
    · rw [hres] at hsf
      simp only [Option.some.injEq, Prod.mk.injEq] at hsf
      obtain ⟨rfl, -, rfl, -⟩ := hsf
      intro b' hb'
      simp only [List.mem_singleton] at hb'
      subst hb'
      intro w w' hedge
      exact modalKnownWorlds_mono_append _ b _ (hknown w w' hedge)
    · rw [hres] at hsf
      simp only [Option.some.injEq, Prod.mk.injEq] at hsf
      obtain ⟨rfl, -, rfl, -⟩ := hsf
      intro b' hb'
      obtain ⟨x, -, rfl⟩ := List.mem_map.mp hb'
      intro w w' hedge
      exact modalKnownWorlds_mono_append _ b _ (hknown w w' hedge)
    · rw [hres] at hsf
      simp only [Option.some.injEq, Prod.mk.injEq] at hsf
      obtain ⟨rfl, -, rfl, -⟩ := hsf
      intro b' hb'
      simp only [List.mem_singleton] at hb'
      subst hb'
      intro w w' hedge
      exact modalKnownWorlds_mono_append _ b _ (hknown w w' hedge)
    · rw [hres] at hsf; simp at hsf

/-! ## Pigeonhole World Bound -/

/-- **Proof-internal auxiliary invariant**: the known worlds of a branch
form the contiguous range `{0, ..., modalMaxWorld b}` -- not an `S4LoopInv` field (would reopen
the finalized struct design), threaded as an extra hypothesis/conclusion alongside the
struct at every call site, exactly like `keysWorldsKnown`. Holds by construction: the driver
only ever mints the SINGLE next integer `modalNextWorld b = modalMaxWorld b + 1`, never skipping
a label -- this is the "worlds are consecutive from 0" fact `modalStepBranchS4_worldBound`
converts a pigeonhole *length* bound into a STRICT `modalMaxWorld` bound with. -/
def worldsContiguousS4 (b : List (SignedFormula (Proposition Atom) WorldIndex)) : Prop :=
  ∀ w, w ≤ modalMaxWorld b → w ∈ modalKnownWorlds b

/-- `worldsContiguousS4`'s driver-level preservation: mirrors `keysWorldsKnown`'s assembly shape
(top split on minting vs. non-minting, reusing `modalStepBranchS4Keyed_branch_superset` for the
"old worlds carry over" half). At the 12 non-minting shapes, every emitted formula's label is
already a known world of `b` (`modalApplyOneS4Keyed_nonMint_known_S4`), so `modalMaxWorld`
cannot grow. At the 2 minting UNBLOCKED shapes, every emitted formula's label is exactly
`modalNextWorld b` (`mintGroup_label_eq_freshWorld`), so `modalMaxWorld` grows by exactly the
one new label, which is directly known via the witness formula's own membership. At the BLOCKED
sub-case, `result = .linear []` so the branch is unchanged. -/
lemma modalStepBranchS4_preserves_worldsContiguousS4 (φ₀ : Proposition Atom)
    (b e : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (keys : List (WorldIndex × Finset (Sign × Proposition Atom)))
    (newBs newExps : List (List (SignedFormula (Proposition Atom) WorldIndex)))
    (newAcc : Accessibility) (keys' : List (WorldIndex × Finset (Sign × Proposition Atom)))
    (hWC : worldsContiguousS4 b) (hknown : accTargetsKnown b acc)
    (hstep : modalStepBranchS4Keyed φ₀ b e acc keys = some (newBs, newExps, newAcc, keys')) :
    ∀ b' ∈ newBs, worldsContiguousS4 b' := by
  have hsuper := modalStepBranchS4Keyed_branch_superset φ₀ b e acc keys newBs newExps newAcc
    keys' hstep
  have hold : ∀ b' ∈ newBs, ∀ w ≤ modalMaxWorld b, w ∈ modalKnownWorlds b' := by
    intro b' hb' w hw
    obtain ⟨sf', hsf'mem, hlab⟩ := (mem_modalKnownWorlds b w).mp (hWC w hw)
    exact (mem_modalKnownWorlds b' w).mpr ⟨sf', hsuper b' hb' sf' hsf'mem, hlab⟩
  have hstep0 := hstep
  unfold modalStepBranchS4Keyed at hstep0
  obtain ⟨sf, hsfmem, hsf⟩ := List.exists_of_findSome?_eq_some hstep0
  split_ifs at hsf with hexp
  rcases hpair : modalApplyOneS4Keyed φ₀ keys sf b acc with ⟨result, newAcc0⟩
  rw [hpair] at hsf
  dsimp only at hsf
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
        have hresulteq2 := hresulteq.trans
          (congrArg Prod.fst (modalApplyOneS4KeyedMint_boxNeg_eq_S4 b acc ψ sf.label))
        have hlabel := mintGroup_label_eq_freshWorld b sf.label .neg ψ
        have hlabelExtra := boxPlusExtraS4_label_eq_freshWorld b sf.label
        rw [hresulteq2] at hsf
        simp only [Option.some.injEq, Prod.mk.injEq] at hsf
        intro b' hb'
        rw [← hsf.1] at hb'
        simp only [List.mem_singleton] at hb'
        subst hb'
        intro w hw
        have hle : w ≤ modalNextWorld b := le_trans hw (by
          apply modalMaxWorld_le_of_forall_label_le
          intro sf'' hsf''
          rcases List.mem_append.mp hsf'' with hnew | holdmem
          · rcases List.mem_append.mp hnew with hraw | hextra
            · rw [hlabel sf'' hraw]
            · rw [hlabelExtra sf'' hextra]
          · exact le_of_lt (lt_of_le_of_lt (label_le_modalMaxWorld holdmem)
              (Nat.lt_succ_self _)))
        have hwle : w ≤ modalMaxWorld b ∨ w = modalNextWorld b := by
          have hnw : modalNextWorld b = modalMaxWorld b + 1 := rfl
          rw [hnw] at hle
          rcases Nat.le_add_one_iff.mp hle with hcase | hcase
          · exact Or.inl hcase
          · exact Or.inr (hcase.trans hnw.symm)
        rcases hwle with hwle | rfl
        · exact hold _ (by rw [← hsf.1]; exact List.mem_singleton_self _) w hwle
        · rw [mem_modalKnownWorlds]
          exact ⟨⟨.neg, ψ, modalNextWorld b⟩,
            List.mem_append_left _ (List.mem_append_left _ List.mem_cons_self), rfl⟩
      · have heq2 : modalApplyOneS4Keyed φ₀ keys (⟨Sign.neg, .box ψ, sf.label⟩ :
            SignedFormula (Proposition Atom) WorldIndex) b acc
            = (.linear [], acc.addEdge sf.label wBlock) :=
          modalApplyOneS4Keyed_boxNeg_blocked_eq φ₀ b acc keys ψ sf.label wBlock hblock
        rw [hsfeq] at hpair
        have hresulteq : result = RuleResult.linear [] :=
          congrArg Prod.fst (hpair.symm.trans heq2)
        intro b' hb'
        rw [hresulteq] at hsf
        simp only [Option.some.injEq, Prod.mk.injEq] at hsf
        rw [← hsf.1] at hb'
        simp only [List.mem_singleton] at hb'
        subst hb'
        intro w hw
        exact hold _ (by rw [← hsf.1]; exact List.mem_singleton_self _) w hw
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
        have hresulteq2 := hresulteq.trans
          (congrArg Prod.fst (modalApplyOneS4KeyedMint_diaPos_eq_S4 b acc ψ sf.label))
        have hlabel := mintGroup_label_eq_freshWorld b sf.label .pos ψ
        have hlabelExtra := boxPlusExtraS4_label_eq_freshWorld b sf.label
        rw [hresulteq2] at hsf
        simp only [Option.some.injEq, Prod.mk.injEq] at hsf
        intro b' hb'
        rw [← hsf.1] at hb'
        simp only [List.mem_singleton] at hb'
        subst hb'
        intro w hw
        have hle : w ≤ modalNextWorld b := le_trans hw (by
          apply modalMaxWorld_le_of_forall_label_le
          intro sf'' hsf''
          rcases List.mem_append.mp hsf'' with hnew | holdmem
          · rcases List.mem_append.mp hnew with hraw | hextra
            · rw [hlabel sf'' hraw]
            · rw [hlabelExtra sf'' hextra]
          · exact le_of_lt (lt_of_le_of_lt (label_le_modalMaxWorld holdmem)
              (Nat.lt_succ_self _)))
        have hwle : w ≤ modalMaxWorld b ∨ w = modalNextWorld b := by
          have hnw : modalNextWorld b = modalMaxWorld b + 1 := rfl
          rw [hnw] at hle
          rcases Nat.le_add_one_iff.mp hle with hcase | hcase
          · exact Or.inl hcase
          · exact Or.inr (hcase.trans hnw.symm)
        rcases hwle with hwle | rfl
        · exact hold _ (by rw [← hsf.1]; exact List.mem_singleton_self _) w hwle
        · rw [mem_modalKnownWorlds]
          exact ⟨⟨.pos, ψ, modalNextWorld b⟩,
            List.mem_append_left _ (List.mem_append_left _ List.mem_cons_self), rfl⟩
      · have heq2 : modalApplyOneS4Keyed φ₀ keys (⟨Sign.pos, .diamond ψ, sf.label⟩ :
            SignedFormula (Proposition Atom) WorldIndex) b acc
            = (.linear [], acc.addEdge sf.label wBlock) :=
          modalApplyOneS4Keyed_diaPos_blocked_eq φ₀ b acc keys ψ sf.label wBlock hblock
        rw [hsfeq] at hpair
        have hresulteq : result = RuleResult.linear [] :=
          congrArg Prod.fst (hpair.symm.trans heq2)
        intro b' hb'
        rw [hresulteq] at hsf
        simp only [Option.some.injEq, Prod.mk.injEq] at hsf
        rw [← hsf.1] at hb'
        simp only [List.mem_singleton] at hb'
        subst hb'
        intro w hw
        exact hold _ (by rw [← hsf.1]; exact List.mem_singleton_self _) w hw
  · have hnbd : ¬ (sf.sign = .neg ∧ ∃ φ, sf.formula = .box φ) ∧
        ¬ (sf.sign = .pos ∧ ∃ φ, sf.formula = .diamond φ) :=
      ⟨fun hc => hmint (Or.inl hc), fun hc => hmint (Or.inr hc)⟩
    have hnm := modalApplyOneS4Keyed_nonMint_known_S4 φ₀ keys sf b acc hsfmem hknown hnbd
    rw [hpair] at hnm
    dsimp only at hnm
    intro b' hb'
    have hmaxle : modalMaxWorld b' ≤ modalMaxWorld b := by
      rcases hres : result with lf | brs | lf | -
      · rw [hres] at hsf hnm
        simp only [Option.some.injEq, Prod.mk.injEq] at hsf
        rw [← hsf.1] at hb'
        simp only [List.mem_singleton] at hb'
        subst hb'
        apply modalMaxWorld_le_of_forall_label_le
        intro sf'' hsf''
        rcases List.mem_append.mp hsf'' with hnew | holdmem
        · obtain ⟨sf3, hsf3mem, hsf3lab⟩ :=
            (mem_modalKnownWorlds b sf''.label).mp (hnm sf'' hnew)
          rw [← hsf3lab]
          exact label_le_modalMaxWorld hsf3mem
        · exact label_le_modalMaxWorld holdmem
      · rw [hres] at hsf hnm
        simp only [Option.some.injEq, Prod.mk.injEq] at hsf
        rw [← hsf.1] at hb'
        obtain ⟨br, hbr, rfl⟩ := List.mem_map.mp hb'
        apply modalMaxWorld_le_of_forall_label_le
        intro sf'' hsf''
        rcases List.mem_append.mp hsf'' with hnew | holdmem
        · obtain ⟨sf3, hsf3mem, hsf3lab⟩ := (mem_modalKnownWorlds b sf''.label).mp
            (hnm sf'' (List.mem_flatten.mpr ⟨br, hbr, hnew⟩))
          rw [← hsf3lab]
          exact label_le_modalMaxWorld hsf3mem
        · exact label_le_modalMaxWorld holdmem
      · rw [hres] at hsf hnm
        simp only [Option.some.injEq, Prod.mk.injEq] at hsf
        rw [← hsf.1] at hb'
        simp only [List.mem_singleton] at hb'
        subst hb'
        apply modalMaxWorld_le_of_forall_label_le
        intro sf'' hsf''
        rcases List.mem_append.mp hsf'' with hnew | holdmem
        · obtain ⟨sf3, hsf3mem, hsf3lab⟩ :=
            (mem_modalKnownWorlds b sf''.label).mp (hnm sf'' hnew)
          rw [← hsf3lab]
          exact label_le_modalMaxWorld hsf3mem
        · exact label_le_modalMaxWorld holdmem
      · rw [hres] at hsf; simp at hsf
    intro w hw
    exact hold b' hb' w (le_trans hw hmaxle)

/-- **`worldsContiguousS4`'s ordered-driver preservation.** Verbatim transcription of
`modalStepBranchS4_preserves_worldsContiguousS4` against the ordered stepper, via
`modalStepBranchS4KeyedOrdered_selected_mem`/`modalStepBranchS4KeyedOrdered_branch_superset` in
place of their unordered counterparts; the top-level minting/non-minting split and its
sub-arguments are otherwise unchanged. -/
lemma modalStepBranchS4KeyedOrdered_preserves_worldsContiguousS4 (φ₀ : Proposition Atom)
    (b e : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (keys : List (WorldIndex × Finset (Sign × Proposition Atom)))
    (newBs newExps : List (List (SignedFormula (Proposition Atom) WorldIndex)))
    (newAcc : Accessibility) (keys' : List (WorldIndex × Finset (Sign × Proposition Atom)))
    (hWC : worldsContiguousS4 b) (hknown : accTargetsKnown b acc)
    (hstep : modalStepBranchS4KeyedOrdered φ₀ b e acc keys =
      some (newBs, newExps, newAcc, keys')) :
    ∀ b' ∈ newBs, worldsContiguousS4 b' := by
  have hsuper := modalStepBranchS4KeyedOrdered_branch_superset φ₀ b e acc keys newBs newExps
    newAcc keys' hstep
  have hold : ∀ b' ∈ newBs, ∀ w ≤ modalMaxWorld b, w ∈ modalKnownWorlds b' := by
    intro b' hb' w hw
    obtain ⟨sf', hsf'mem, hlab⟩ := (mem_modalKnownWorlds b w).mp (hWC w hw)
    exact (mem_modalKnownWorlds b' w).mpr ⟨sf', hsuper b' hb' sf' hsf'mem, hlab⟩
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
        have hresulteq2 := hresulteq.trans
          (congrArg Prod.fst (modalApplyOneS4KeyedMint_boxNeg_eq_S4 b acc ψ sf.label))
        have hlabel := mintGroup_label_eq_freshWorld b sf.label .neg ψ
        have hlabelExtra := boxPlusExtraS4_label_eq_freshWorld b sf.label
        rw [hresulteq2] at hsf
        simp only [Option.some.injEq, Prod.mk.injEq] at hsf
        intro b' hb'
        rw [← hsf.1] at hb'
        simp only [List.mem_singleton] at hb'
        subst hb'
        intro w hw
        have hle : w ≤ modalNextWorld b := le_trans hw (by
          apply modalMaxWorld_le_of_forall_label_le
          intro sf'' hsf''
          rcases List.mem_append.mp hsf'' with hnew | holdmem
          · rcases List.mem_append.mp hnew with hraw | hextra
            · rw [hlabel sf'' hraw]
            · rw [hlabelExtra sf'' hextra]
          · exact le_of_lt (lt_of_le_of_lt (label_le_modalMaxWorld holdmem)
              (Nat.lt_succ_self _)))
        have hwle : w ≤ modalMaxWorld b ∨ w = modalNextWorld b := by
          have hnw : modalNextWorld b = modalMaxWorld b + 1 := rfl
          rw [hnw] at hle
          rcases Nat.le_add_one_iff.mp hle with hcase | hcase
          · exact Or.inl hcase
          · exact Or.inr (hcase.trans hnw.symm)
        rcases hwle with hwle | rfl
        · exact hold _ (by rw [← hsf.1]; exact List.mem_singleton_self _) w hwle
        · rw [mem_modalKnownWorlds]
          exact ⟨⟨.neg, ψ, modalNextWorld b⟩,
            List.mem_append_left _ (List.mem_append_left _ List.mem_cons_self), rfl⟩
      · have heq2 : modalApplyOneS4Keyed φ₀ keys (⟨Sign.neg, .box ψ, sf.label⟩ :
            SignedFormula (Proposition Atom) WorldIndex) b acc
            = (.linear [], acc.addEdge sf.label wBlock) :=
          modalApplyOneS4Keyed_boxNeg_blocked_eq φ₀ b acc keys ψ sf.label wBlock hblock
        rw [hsfeq] at hpair
        have hresulteq : result = RuleResult.linear [] :=
          congrArg Prod.fst (hpair.symm.trans heq2)
        intro b' hb'
        rw [hresulteq] at hsf
        simp only [Option.some.injEq, Prod.mk.injEq] at hsf
        rw [← hsf.1] at hb'
        simp only [List.mem_singleton] at hb'
        subst hb'
        intro w hw
        exact hold _ (by rw [← hsf.1]; exact List.mem_singleton_self _) w hw
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
        have hresulteq2 := hresulteq.trans
          (congrArg Prod.fst (modalApplyOneS4KeyedMint_diaPos_eq_S4 b acc ψ sf.label))
        have hlabel := mintGroup_label_eq_freshWorld b sf.label .pos ψ
        have hlabelExtra := boxPlusExtraS4_label_eq_freshWorld b sf.label
        rw [hresulteq2] at hsf
        simp only [Option.some.injEq, Prod.mk.injEq] at hsf
        intro b' hb'
        rw [← hsf.1] at hb'
        simp only [List.mem_singleton] at hb'
        subst hb'
        intro w hw
        have hle : w ≤ modalNextWorld b := le_trans hw (by
          apply modalMaxWorld_le_of_forall_label_le
          intro sf'' hsf''
          rcases List.mem_append.mp hsf'' with hnew | holdmem
          · rcases List.mem_append.mp hnew with hraw | hextra
            · rw [hlabel sf'' hraw]
            · rw [hlabelExtra sf'' hextra]
          · exact le_of_lt (lt_of_le_of_lt (label_le_modalMaxWorld holdmem)
              (Nat.lt_succ_self _)))
        have hwle : w ≤ modalMaxWorld b ∨ w = modalNextWorld b := by
          have hnw : modalNextWorld b = modalMaxWorld b + 1 := rfl
          rw [hnw] at hle
          rcases Nat.le_add_one_iff.mp hle with hcase | hcase
          · exact Or.inl hcase
          · exact Or.inr (hcase.trans hnw.symm)
        rcases hwle with hwle | rfl
        · exact hold _ (by rw [← hsf.1]; exact List.mem_singleton_self _) w hwle
        · rw [mem_modalKnownWorlds]
          exact ⟨⟨.pos, ψ, modalNextWorld b⟩,
            List.mem_append_left _ (List.mem_append_left _ List.mem_cons_self), rfl⟩
      · have heq2 : modalApplyOneS4Keyed φ₀ keys (⟨Sign.pos, .diamond ψ, sf.label⟩ :
            SignedFormula (Proposition Atom) WorldIndex) b acc
            = (.linear [], acc.addEdge sf.label wBlock) :=
          modalApplyOneS4Keyed_diaPos_blocked_eq φ₀ b acc keys ψ sf.label wBlock hblock
        rw [hsfeq] at hpair
        have hresulteq : result = RuleResult.linear [] :=
          congrArg Prod.fst (hpair.symm.trans heq2)
        intro b' hb'
        rw [hresulteq] at hsf
        simp only [Option.some.injEq, Prod.mk.injEq] at hsf
        rw [← hsf.1] at hb'
        simp only [List.mem_singleton] at hb'
        subst hb'
        intro w hw
        exact hold _ (by rw [← hsf.1]; exact List.mem_singleton_self _) w hw
  · have hnbd : ¬ (sf.sign = .neg ∧ ∃ φ, sf.formula = .box φ) ∧
        ¬ (sf.sign = .pos ∧ ∃ φ, sf.formula = .diamond φ) :=
      ⟨fun hc => hmint (Or.inl hc), fun hc => hmint (Or.inr hc)⟩
    have hnm := modalApplyOneS4Keyed_nonMint_known_S4 φ₀ keys sf b acc hsfmem hknown hnbd
    rw [hpair] at hnm
    dsimp only at hnm
    intro b' hb'
    have hmaxle : modalMaxWorld b' ≤ modalMaxWorld b := by
      rcases hres : result with lf | brs | lf | -
      · rw [hres] at hsf hnm
        simp only [Option.some.injEq, Prod.mk.injEq] at hsf
        rw [← hsf.1] at hb'
        simp only [List.mem_singleton] at hb'
        subst hb'
        apply modalMaxWorld_le_of_forall_label_le
        intro sf'' hsf''
        rcases List.mem_append.mp hsf'' with hnew | holdmem
        · obtain ⟨sf3, hsf3mem, hsf3lab⟩ :=
            (mem_modalKnownWorlds b sf''.label).mp (hnm sf'' hnew)
          rw [← hsf3lab]
          exact label_le_modalMaxWorld hsf3mem
        · exact label_le_modalMaxWorld holdmem
      · rw [hres] at hsf hnm
        simp only [Option.some.injEq, Prod.mk.injEq] at hsf
        rw [← hsf.1] at hb'
        obtain ⟨br, hbr, rfl⟩ := List.mem_map.mp hb'
        apply modalMaxWorld_le_of_forall_label_le
        intro sf'' hsf''
        rcases List.mem_append.mp hsf'' with hnew | holdmem
        · obtain ⟨sf3, hsf3mem, hsf3lab⟩ := (mem_modalKnownWorlds b sf''.label).mp
            (hnm sf'' (List.mem_flatten.mpr ⟨br, hbr, hnew⟩))
          rw [← hsf3lab]
          exact label_le_modalMaxWorld hsf3mem
        · exact label_le_modalMaxWorld holdmem
      · rw [hres] at hsf hnm
        simp only [Option.some.injEq, Prod.mk.injEq] at hsf
        rw [← hsf.1] at hb'
        simp only [List.mem_singleton] at hb'
        subst hb'
        apply modalMaxWorld_le_of_forall_label_le
        intro sf'' hsf''
        rcases List.mem_append.mp hsf'' with hnew | holdmem
        · obtain ⟨sf3, hsf3mem, hsf3lab⟩ :=
            (mem_modalKnownWorlds b sf''.label).mp (hnm sf'' hnew)
          rw [← hsf3lab]
          exact label_le_modalMaxWorld hsf3mem
        · exact label_le_modalMaxWorld holdmem
      · rw [hres] at hsf; simp at hsf
    intro w hw
    exact hold b' hb' w (le_trans hw hmaxle)

omit [Hashable Atom] in
/-- **The pigeonhole cardinality bound**: the number of known worlds of a branch is
bounded by `modalWorldBoundS4 φ₀`. Injects known worlds into `keys` via `keysTotal`, injectivity
via `keysDistinct`, codomain bound via `keysInUniverse` + `signedSubfmls_powerset_card_le`,
cardinality via `Finset.card_le_card_of_injOn`. -/
lemma modalKnownWorlds_length_le_worldBoundS4 (φ₀ : Proposition Atom)
    (b : List (SignedFormula (Proposition Atom) WorldIndex))
    (keys : List (WorldIndex × Finset (Sign × Proposition Atom)))
    (hKT : ∀ w ∈ modalKnownWorlds b, ∃ k, (w, k) ∈ keys)
    (hKD : ∀ w1 w2 k1 k2, (w1, k1) ∈ keys → (w2, k2) ∈ keys → w1 ≠ w2 → k1 ≠ k2)
    (hKI : ∀ w k, (w, k) ∈ keys → k ⊆ signedSubfmls φ₀) :
    (modalKnownWorlds b).length ≤ modalWorldBoundS4 φ₀ := by
  classical
  set f : WorldIndex → Finset (Sign × Proposition Atom) :=
    fun w => if hw : w ∈ modalKnownWorlds b then (hKT w hw).choose else ∅ with hf
  have hmapsto : ∀ w ∈ (modalKnownWorlds b).toFinset, f w ∈ (signedSubfmls φ₀).powerset := by
    intro w hw
    rw [List.mem_toFinset] at hw
    simp only [hf, dif_pos hw]
    rw [Finset.mem_powerset]
    exact hKI w _ (hKT w hw).choose_spec
  have hinj : Set.InjOn f (modalKnownWorlds b).toFinset := by
    intro w1 hw1 w2 hw2 heq
    simp only [Finset.mem_coe, List.mem_toFinset] at hw1 hw2
    by_contra hne
    have hk1 : (w1, f w1) ∈ keys := by
      simp only [hf, dif_pos hw1]; exact (hKT w1 hw1).choose_spec
    have hk2 : (w2, f w2) ∈ keys := by
      simp only [hf, dif_pos hw2]; exact (hKT w2 hw2).choose_spec
    exact (hKD w1 w2 (f w1) (f w2) hk1 hk2 hne) heq
  have hcard := Finset.card_le_card_of_injOn f hmapsto hinj
  rw [List.toFinset_card_of_nodup (modalKnownWorlds_nodup b)] at hcard
  calc (modalKnownWorlds b).length ≤ (signedSubfmls φ₀).powerset.card := hcard
    _ ≤ modalWorldBoundS4 φ₀ := signedSubfmls_powerset_card_le φ₀

omit [Hashable Atom] in
/-- **`modalStepBranchS4_worldBound`**: the
STRICT world bound `modalMaxWorld b < modalWorldBoundS4 φ₀`, the deliverable that makes any
fresh mint's label (`modalNextWorld b = modalMaxWorld b + 1`) stay within `modalWorldBoundS4`'s
fixed range. Combines the pigeonhole length bound
(`modalKnownWorlds_length_le_worldBoundS4`) with the density fact `worldsContiguousS4` provides:
`{0, ..., modalMaxWorld b} ⊆ modalKnownWorlds b`, so `modalMaxWorld b + 1 ≤
(modalKnownWorlds b).length ≤ modalWorldBoundS4 φ₀`. -/
lemma modalStepBranchS4_worldBound (φ₀ : Proposition Atom)
    (b : List (SignedFormula (Proposition Atom) WorldIndex))
    (keys : List (WorldIndex × Finset (Sign × Proposition Atom)))
    (hWC : worldsContiguousS4 b)
    (hKT : ∀ w ∈ modalKnownWorlds b, ∃ k, (w, k) ∈ keys)
    (hKD : ∀ w1 w2 k1 k2, (w1, k1) ∈ keys → (w2, k2) ∈ keys → w1 ≠ w2 → k1 ≠ k2)
    (hKI : ∀ w k, (w, k) ∈ keys → k ⊆ signedSubfmls φ₀) :
    modalMaxWorld b < modalWorldBoundS4 φ₀ := by
  have hlen := modalKnownWorlds_length_le_worldBoundS4 φ₀ b keys hKT hKD hKI
  have hsub : (List.range (modalMaxWorld b + 1)).toFinset ⊆ (modalKnownWorlds b).toFinset := by
    intro w hw
    rw [List.mem_toFinset, List.mem_range] at hw
    rw [List.mem_toFinset]
    exact hWC w (Nat.lt_succ_iff.mp hw)
  have hcard := Finset.card_le_card hsub
  rw [List.toFinset_card_of_nodup List.nodup_range,
      List.toFinset_card_of_nodup (modalKnownWorlds_nodup b), List.length_range] at hcard
  calc modalMaxWorld b < modalMaxWorld b + 1 := Nat.lt_succ_self _
    _ ≤ (modalKnownWorlds b).length := hcard
    _ ≤ modalWorldBoundS4 φ₀ := hlen

end Cslib.Logic.Modal.Tableau

end
