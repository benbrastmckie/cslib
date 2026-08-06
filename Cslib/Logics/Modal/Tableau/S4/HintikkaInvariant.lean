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
public import Cslib.Logics.Modal.Tableau.S4.Hintikka
public import Cslib.Logics.Modal.Tableau.S4.InvariantAcc
public import Cslib.Logics.Modal.Tableau.S4.Invariant

/-! # S4 Loop-Checking: Keyed-Hintikka and Ordered-Fuel Invariants

The keyed-Hintikka invariant `S4KeyedHintikkaInv` (bridging `S4LoopInv` to
`modalS4Saturated`-hood at a settled ordered-stepper state) and the ordered-fuel invariant
`S4OrderedFuelInv`, together with their preservation theorems.

## Why a separate module

This is the top `S4/` module: it imports `Hintikka`, `InvariantAcc`, and `Invariant`, and
nothing else in the cluster imports it. `S4KeyedHintikkaInv` is stated in terms of both
`S4LoopInv` (`Invariant`) and `modalS4Saturated`/settledness (`Hintikka`), so it can only be
declared once both are available -- it is the natural final layer.

## Main Definitions
- `S4KeyedHintikkaInv`: the keyed-Hintikka invariant bridging `S4LoopInv` to
  `modalS4Saturated`-hood at a settled state.
- `S4OrderedFuelInv`: the ordered-stepper fuel invariant.

## Main Results
- `S4KeyedHintikkaInv_weaken`: weakening under a stronger settledness hypothesis.
- `modalS4Saturated_of_ordered_settled`: the ordered stepper reaches `modalS4Saturated`-hood once
  settled.
- `S4KeyedHintikkaInv_append`: append-stability (kept `private`; no cross-module consumer).
- `modalStepBranchS4Keyed_preserves_S4KeyedHintikkaInv`,
  `modalStepBranchS4KeyedOrdered_preserves_S4KeyedHintikkaInv`: per-step preservation for the
  bespoke and ordered steppers.
- `modalStepBranchS4KeyedOrdered_preserves_S4OrderedFuelInv`: ordered-fuel invariant
  preservation.
-/

@[expose] public section

namespace Cslib.Logic.Modal.Tableau

open Cslib.Logic.Tableau Cslib.Logic.Modal

variable {Atom : Type*} [DecidableEq Atom] [Hashable Atom]

/-! ## Keys-Threaded Hintikka-Tracking Invariant Bundle

The bespoke keys-threaded analogue of the `ModalLoopInvHintikka` bundle
(`CompletenessLoop.lean:293-325`), for `modalApplyOneS4Keyed φ₀ keys`. The frozen `S4LoopInv`
structure (defined above in this file) already carries the universe-closure/keys-bookkeeping
conjuncts (`bClosure`/`eClosure`/`eNodup`/`accFresh`/`accKnown`), so this bundle carries ONLY
the five Hintikka-specific conjuncts
(`hintikkaInv`/`eBoxOnlyNeg`/`eBoxNegWitness`/`eDiamondOnlyPos`/`eDiamondPosWitness`), threaded
alongside `S4LoopInv` as a separate ambient hypothesis at each call site rather than duplicating
its fields. -/

/-- **Keys-threaded Hintikka-tracking invariant bundle** for `modalApplyOneS4Keyed φ₀ keys`: the
bespoke analogue of `ModalLoopInvHintikka`'s five Hintikka-specific conjuncts
(`CompletenessLoop.lean:310-325`), carrying ONLY those five fields. The universe-closure/
keys-bookkeeping conjuncts already live in the frozen `S4LoopInv` structure (defined above in this
file) and are threaded as a separate ambient hypothesis at each call site rather than duplicated
here. -/
structure S4KeyedHintikkaInv (φ₀ : Proposition Atom)
    (b e : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (keys : List (WorldIndex × Finset (Sign × Proposition Atom))) : Prop where
  /-- Every already-expanded formula's Hintikka witness obligation is already met on `b`. -/
  hintikkaInv : ∀ sf ∈ e,
    modalHintikkaClauseGen (modalApplyOneS4Keyed φ₀ keys) sf.sign sf.formula sf.label b acc
  /-- Every box-shaped formula in the expanded set `e` has sign `.neg`. -/
  eBoxOnlyNeg : ∀ sf ∈ e, ∀ ψ, sf.formula = .box ψ → sf.sign = .neg
  /-- Every `boxNeg`-shaped formula already has a witness successor on the branch. -/
  eBoxNegWitness : ∀ sf ∈ e, ∀ (ψ : Proposition Atom) (w : WorldIndex),
    sf = (⟨.neg, .box ψ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) →
    ∃ w', acc.hasEdge w w' = true ∧
      (⟨.neg, ψ, w'⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b
  /-- Every diamond-shaped formula in the expanded set `e` has sign `.pos`. -/
  eDiamondOnlyPos : ∀ sf ∈ e, ∀ ψ, sf.formula = .diamond ψ → sf.sign = .pos
  /-- Every `diamondPos`-shaped formula already has a witness successor on the branch. -/
  eDiamondPosWitness : ∀ sf ∈ e, ∀ (ψ : Proposition Atom) (w : WorldIndex),
    sf = (⟨.pos, .diamond ψ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) →
    ∃ w', acc.hasEdge w w' = true ∧
      (⟨.pos, ψ, w'⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b

/-- **`S4KeyedHintikkaInv` weakens across branch/accessibility growth** at a FIXED expanded set
`e`: this discharges the Hintikka-tracking invariant's monotonicity obligations directly --
`hintikkaInv` transports via the branch/`acc`-independence of non-box/diamond shapes
(`modalHintikkaClauseGen_lift` fed `modalApplyOneS4Keyed_fst_eq_of_not_box`; box/diamond
shapes are vacuously `True` on both sides), and the two witness-existence fields are permanent
once recorded since `acc`/`b` only grow (`hbsub`/`haccsub`). `eBoxOnlyNeg`/`eDiamondOnlyPos`
mention no `b`/`acc` at all and transport unchanged. This is the building block the
single-step-preservation lemma below composes against the OLD `e`'s facts lifted to the post-step
`(b', acc')`. -/
lemma S4KeyedHintikkaInv_weaken (φ₀ : Proposition Atom)
    (b b' e : List (SignedFormula (Proposition Atom) WorldIndex)) (acc acc' : Accessibility)
    (keys : List (WorldIndex × Finset (Sign × Proposition Atom)))
    (hbsub : b ⊆ b')
    (haccsub : ∀ w w', acc.hasEdge w w' = true → acc'.hasEdge w w' = true)
    (hinv : S4KeyedHintikkaInv φ₀ b e acc keys) :
    S4KeyedHintikkaInv φ₀ b' e acc' keys := by
  refine ⟨?_, hinv.eBoxOnlyNeg, ?_, hinv.eDiamondOnlyPos, ?_⟩
  · intro sf hsf
    exact modalHintikkaClauseGen_lift (modalApplyOneS4Keyed φ₀ keys)
      (modalApplyOneS4Keyed_fst_eq_of_not_box φ₀ keys) sf.sign sf.formula sf.label b b' acc acc'
      hbsub (hinv.hintikkaInv sf hsf)
  · intro sf hsf ψ w hsfeq
    obtain ⟨w', hedge, hwit⟩ := hinv.eBoxNegWitness sf hsf ψ w hsfeq
    exact ⟨w', haccsub w w' hedge, hbsub hwit⟩
  · intro sf hsf ψ w hsfeq
    obtain ⟨w', hedge, hwit⟩ := hinv.eDiamondPosWitness sf hsf ψ w hsfeq
    exact ⟨w', haccsub w w' hedge, hbsub hwit⟩

/-! ## GATE B -- `modalS4Saturated` at a Settled Ordered-Stepper State

Determines whether `modalS4Saturated φ₀ b acc` is available at an INTERMEDIATE ordered-stepper
state -- specifically a settled state (`modalNonMintCandidates φ₀ keys b e acc = []`) where a
blocked step is about to fire. Gate B **PASSES at its cheapest**: the gate lemma closes
sorry-free from `hsettled` + `hHI` + a per-shape keyed/unkeyed congruence argument alone (in the
same spirit as `hintikka_congr_S4`), with no additional invariant field needed. See
`#### Phase 2 Verdict` in `plans/07_canonical-witness-truth-lemma.md`
(`specs/553_s4_loop_guard_soundness_reachability_restriction/`) for the full write-up.

The apparent gap the plan flagged -- `S4KeyedHintikkaInv.hintikkaInv`'s use of
`modalHintikkaClauseGen`, which is vacuous at EVERY box/diamond-shaped formula regardless of
sign, seemingly supplies nothing for the box-positive/diamond-negative (T-self/4-rule) shapes a
member of `e` might have -- turns out not to arise: `S4KeyedHintikkaInv.eBoxOnlyNeg`/
`eDiamondOnlyPos` already force any box/diamond-shaped member of `e` to be exactly one of the two
MINTING shapes (`.neg,.box`/`.pos,.diamond`), which the non-mint-shape hypothesis in scope here
already excludes. So a non-mint-shaped `sf ∈ e` is never box/diamond-shaped at all, and
`hintikkaInv`'s clause gives genuine (non-vacuous) content there, matching `modalS4Saturated`'s
own requirement exactly once the keyed/unkeyed congruence is applied. -/

lemma modalS4Saturated_of_ordered_settled (φ₀ : Proposition Atom)
    (b e : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (keys : List (WorldIndex × Finset (Sign × Proposition Atom)))
    (hsettled : modalNonMintCandidates φ₀ keys b e acc = [])
    (hHI : S4KeyedHintikkaInv φ₀ b e acc keys) :
    modalS4Saturated φ₀ b acc := by
  intro sf hsfmem
  by_cases hms : modalMintShape sf = true
  · unfold modalMintShape at hms
    rcases hsg : sf.sign with _ | _ <;> rcases hfm : sf.formula with _|_|_|_|_|φ|φ <;> simp_all
  · have hnb : ¬ (sf.sign = .neg ∧ ∃ φ, sf.formula = .box φ) ∧
        ¬ (sf.sign = .pos ∧ ∃ φ, sf.formula = .diamond φ) := by
      simp only [Bool.not_eq_true] at hms
      rcases hsg : sf.sign with _ | _ <;> rcases hfm : sf.formula with _|_|_|_|_|φ|φ <;>
        simp_all [modalMintShape]
    by_cases he : sf ∈ e
    · -- `sf ∈ e`: `eBoxOnlyNeg`/`eDiamondOnlyPos` rule out `sf` being box/diamond-shaped at
      -- all, once the two mint shapes are already excluded by `hnb` -- a box-shaped member of
      -- `e` is forced `.neg` (mint-shaped), a diamond-shaped member is forced `.pos`
      -- (mint-shaped), and `hnb` excludes both. So `sf` is a genuinely non-modal shape here,
      -- where `modalHintikkaClauseGen`'s vacuity at box/diamond formulas does not apply and
      -- `hHI.hintikkaInv` supplies real content.
      have heq1 : modalApplyOneS4Keyed φ₀ keys sf b acc = modalApplyOneS4 φ₀ sf b acc := by
        unfold modalApplyOneS4Keyed
        rcases hsg : sf.sign with _ | _ <;> rcases hfm : sf.formula with _|_|_|_|_|φ|φ <;>
          simp_all
      have hclause := hHI.hintikkaInv sf he
      unfold modalHintikkaClauseGen at hclause
      rw [heq1] at hclause
      simp only
      rcases hsg : sf.sign with _ | _ <;> rcases hfm : sf.formula with _|_|_|_|_|φ|φ <;>
        simp only [hfm] at hclause ⊢ <;>
        first
          | trivial
          | exact hclause
          | (exact absurd (hHI.eBoxOnlyNeg sf he _ hfm) (by simp [hsg]))
          | (exact absurd (hHI.eDiamondOnlyPos sf he _ hfm) (by simp [hsg]))
    · have hdisj := (modalNonMintCandidates_eq_nil_iff φ₀ keys b e acc).mp hsettled sf hsfmem
      have hnotapp : (modalApplyOneS4Keyed φ₀ keys sf b acc).1 = .notApplicable := by
        rcases hdisj with hms' | hex | hnotapp'
        · exact absurd hms' hms
        · exact absurd hex he
        · exact hnotapp'
      have heq1 : modalApplyOneS4Keyed φ₀ keys sf b acc = modalApplyOneS4 φ₀ sf b acc := by
        unfold modalApplyOneS4Keyed
        rcases hsg : sf.sign with _ | _ <;> rcases hfm : sf.formula with _|_|_|_|_|φ|φ <;>
          simp_all
      rw [heq1] at hnotapp
      simp only
      rcases hsg : sf.sign with _ | _ <;> rcases hfm : sf.formula with _|_|_|_|_|φ|φ <;>
        simp_all

/-! ## The `red` Channel: General Infrastructure Retained Post-Gate-B

Route (3) (`Massacci2000` Technique 8.2, subtractive blocking; see this task's plan
`specs/553_s4_loop_guard_soundness_reachability_restriction/plans/
04_subtractive-blocking-red-channel.md`) proposed moving the redirect a blocked minting step
would otherwise justify OUT of `acc` (the soundness-tracked structure) and into a separate,
completeness-only channel `red`, with a bifurcated Hintikka predicate (`modalHintikkaSetS4Sub`)
substituting `accWithReds acc red` for `acc` in the witness/forward-cone conjuncts only.

**Route (3) is dead** (see `plans/04_subtractive-blocking-red-channel.md`):
Decision Gate B refuted the cone-extension lemma the bifurcated predicate's forward-cone
conjuncts require, because the free transfer below (`blockedRedirect_unwrapped_boxPos_mem`/
`blockedRedirect_unwrapped_diaNeg_mem`) yields only an *unwrapped* branch fact at the redirect
target, and unwrapped facts have no persistence mechanism in this tableau's Hintikka apparatus.
`modalHintikkaSetS4Sub`, `modalHintikkaSetS4Sub_saturated`, and `S4KeyedSubHintikkaInv` were
removed as part of the post-Gate-B triage (see plan v4's `#### Post-Gate-B Triage` note); the
route (1) truth-lemma successor plan does not use the `red` channel at all.

What remains below is genuinely route-independent: `Reds` and `accWithReds` are a plain
"accessibility plus a recorded extra-edge list" packaging with no route-specific content, and
`hasEdge_accWithReds_iff` / `reflTransGen_accWithReds_first_red` are general `simp`/path-
decomposition bridges over that packaging. They are retained as minimal support for those two
bridges and for the two sorry-free, standard-axioms-only free-transfer lemmas
(`blockedRedirect_unwrapped_boxPos_mem`/`blockedRedirect_unwrapped_diaNeg_mem`), which route (1)
may reuse. -/

/-- **Assembly helper**: given the OLD `e`'s bundle already transported to the post-step
`(b', acc')` at the OLD `keys` (`S4KeyedHintikkaInv_weaken`), plus the just-selected formula
`sf`'s own five per-field facts at the post-step `keys'`, assemble the full bundle at
`e ++ [sf]`. The old-`e` facts are lifted from `keys` to `keys'` via
`modalHintikkaClauseGen_S4Keyed_keys_indep` (only `hintikkaInv` mentions `keys`; the other four
fields do not reference `apply`/`keys` at all). -/
private lemma S4KeyedHintikkaInv_append (φ₀ : Proposition Atom)
    (b' e : List (SignedFormula (Proposition Atom) WorldIndex)) (acc' : Accessibility)
    (keys keys' : List (WorldIndex × Finset (Sign × Proposition Atom)))
    (sf : SignedFormula (Proposition Atom) WorldIndex)
    (hweak : S4KeyedHintikkaInv φ₀ b' e acc' keys)
    (hnew_hintikka : modalHintikkaClauseGen (modalApplyOneS4Keyed φ₀ keys') sf.sign sf.formula
      sf.label b' acc')
    (hnew_boxOnlyNeg : ∀ ψ, sf.formula = .box ψ → sf.sign = .neg)
    (hnew_diaOnlyPos : ∀ ψ, sf.formula = .diamond ψ → sf.sign = .pos)
    (hnew_boxNegWitness : ∀ (ψ : Proposition Atom) (w : WorldIndex),
      sf = (⟨.neg, .box ψ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) →
      ∃ w', acc'.hasEdge w w' = true ∧
        (⟨.neg, ψ, w'⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b')
    (hnew_diaPosWitness : ∀ (ψ : Proposition Atom) (w : WorldIndex),
      sf = (⟨.pos, .diamond ψ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) →
      ∃ w', acc'.hasEdge w w' = true ∧
        (⟨.pos, ψ, w'⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b') :
    S4KeyedHintikkaInv φ₀ b' (e ++ [sf]) acc' keys' := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro sf' hsf'
    rcases List.mem_append.mp hsf' with hold | hnewmem
    · rw [← modalHintikkaClauseGen_S4Keyed_keys_indep φ₀ keys keys' sf'.sign sf'.formula
        sf'.label b' acc']
      exact hweak.hintikkaInv sf' hold
    · simp only [List.mem_singleton] at hnewmem
      subst hnewmem
      exact hnew_hintikka
  · intro sf' hsf' ψ hform
    rcases List.mem_append.mp hsf' with hold | hnewmem
    · exact hweak.eBoxOnlyNeg sf' hold ψ hform
    · simp only [List.mem_singleton] at hnewmem
      subst hnewmem
      exact hnew_boxOnlyNeg ψ hform
  · intro sf' hsf' ψ w hsfeq
    rcases List.mem_append.mp hsf' with hold | hnewmem
    · exact hweak.eBoxNegWitness sf' hold ψ w hsfeq
    · simp only [List.mem_singleton] at hnewmem
      subst hnewmem
      exact hnew_boxNegWitness ψ w hsfeq
  · intro sf' hsf' ψ hform
    rcases List.mem_append.mp hsf' with hold | hnewmem
    · exact hweak.eDiamondOnlyPos sf' hold ψ hform
    · simp only [List.mem_singleton] at hnewmem
      subst hnewmem
      exact hnew_diaOnlyPos ψ hform
  · intro sf' hsf' ψ w hsfeq
    rcases List.mem_append.mp hsf' with hold | hnewmem
    · exact hweak.eDiamondPosWitness sf' hold ψ w hsfeq
    · simp only [List.mem_singleton] at hnewmem
      subst hnewmem
      exact hnew_diaPosWitness ψ w hsfeq

/-- **Single-step preservation of `S4KeyedHintikkaInv`**: every
`modalStepBranchS4Keyed` step preserves the keys-threaded Hintikka-tracking invariant bundle,
given the ambient frozen `S4LoopInv` structure (defined above in this file, consumed for
`keyLowerBd`'s blocked-witness argument).
Mirrors `modalStepBranchS4_preserves_bClosure`'s case-split shape (mint-unblocked / mint-blocked
/ non-mint), composing `S4KeyedHintikkaInv_weaken` (old `e`'s facts lifted across
branch/`acc` growth) with `S4KeyedHintikkaInv_append`'s per-field assembly for the just-selected
formula: an unblocked mint discharges its witness via K's own `modalApplyOne_boxNeg_witness`/
`_diamondPos_witness`; a blocked redirect discharges it via
`modalStepBranchS4Keyed_blocked_witness_mem` (this file, above). -/
theorem modalStepBranchS4Keyed_preserves_S4KeyedHintikkaInv (φ₀ : Proposition Atom)
    (b e : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (keys : List (WorldIndex × Finset (Sign × Proposition Atom)))
    (newBs newExps : List (List (SignedFormula (Proposition Atom) WorldIndex)))
    (newAcc : Accessibility) (keys' : List (WorldIndex × Finset (Sign × Proposition Atom)))
    (hLoopInv : S4LoopInv φ₀ b e acc keys)
    (hHinv : S4KeyedHintikkaInv φ₀ b e acc keys)
    (hstep : modalStepBranchS4Keyed φ₀ b e acc keys = some (newBs, newExps, newAcc, keys')) :
    ∀ b' ∈ newBs, ∀ e' ∈ newExps, S4KeyedHintikkaInv φ₀ b' e' newAcc keys' := by
  have hstep0 := hstep
  unfold modalStepBranchS4Keyed at hstep0
  obtain ⟨sf, hsfmem, hsf⟩ := List.exists_of_findSome?_eq_some hstep0
  split_ifs at hsf with hexp
  rcases hpair : modalApplyOneS4Keyed φ₀ keys sf b acc with ⟨result, newAcc0⟩
  have haccsub : ∀ w w', acc.hasEdge w w' = true → newAcc0.hasEdge w w' = true := by
    intro w w' h
    have hmono := modalApplyOneS4Keyed_hasEdge_mono φ₀ keys sf b acc h
    rwa [hpair] at hmono
  by_cases hmint : (sf.sign = .neg ∧ ∃ φ, sf.formula = .box φ) ∨
      (sf.sign = .pos ∧ ∃ φ, sf.formula = .diamond φ)
  · rcases hmint with ⟨hs, ψ, hf⟩ | ⟨hs, ψ, hf⟩
    · -- neg + box: the boxNeg minting shape.
      have hsfeq : sf = (⟨Sign.neg, .box ψ, sf.label⟩ :
          SignedFormula (Proposition Atom) WorldIndex) := by rw [← hs, ← hf]
      rw [hsfeq] at hsf hpair
      rw [hpair] at hsf
      dsimp only at hsf
      rw [hsfeq] at hsfmem
      rcases hblock : blockingWorldS4Keyed φ₀ b keys .neg ψ sf.label with _ | wBlock
      · -- unblocked: fresh witness world, standard K minting facts transfer.
        obtain ⟨hwsnd, rest, hwfst⟩ := modalApplyOneS4KeyedMint_boxNeg_witness b acc ψ sf.label
        have hAOeq := modalApplyOneS4Keyed_boxNeg_unblocked_eq φ₀ b acc keys ψ sf.label hblock
        rw [hblock] at hsf
        have hresulteq : result = RuleResult.linear
            ((⟨.neg, ψ, modalNextWorld b⟩ : SignedFormula (Proposition Atom) WorldIndex) ::
              rest) := (congrArg Prod.fst (hpair.symm.trans hAOeq)).trans hwfst
        have hnewAcc0eq : newAcc0 = acc.addEdge sf.label (modalNextWorld b) := by
          have hsndeq := congrArg Prod.snd (hpair.symm.trans hAOeq)
          rwa [hwsnd] at hsndeq
        rw [hresulteq] at hsf
        simp only [Option.some.injEq, Prod.mk.injEq] at hsf
        obtain ⟨hnewBs, hnewExps, hnewAcc, -⟩ := hsf
        intro b' hb' e' he'
        rw [← hnewBs] at hb'; simp only [List.mem_singleton] at hb'
        rw [← hnewExps] at he'; simp only [List.mem_singleton] at he'
        subst hb'; subst he'; subst hnewAcc
        have hbsub : ∀ x ∈ b, x ∈
            ((⟨.neg, ψ, modalNextWorld b⟩ : SignedFormula (Proposition Atom) WorldIndex) ::
              rest) ++ b := fun x hx => List.mem_append_right _ hx
        have hweak := S4KeyedHintikkaInv_weaken φ₀ b
          (((⟨.neg, ψ, modalNextWorld b⟩ : SignedFormula (Proposition Atom) WorldIndex) ::
            rest) ++ b) e acc newAcc0 keys hbsub haccsub hHinv
        have hedge : newAcc0.hasEdge sf.label (modalNextWorld b) = true := by
          rw [hnewAcc0eq]; simp [Accessibility.hasEdge, Accessibility.addEdge]
        refine S4KeyedHintikkaInv_append φ₀ _ e newAcc0 keys keys'
          (⟨.neg, .box ψ, sf.label⟩ : SignedFormula (Proposition Atom) WorldIndex) hweak
          ?_ ?_ ?_ ?_ ?_
        · simp [modalHintikkaClauseGen]
        · intro ψ' _; rfl
        · intro ψ' hform; exact absurd hform (by simp)
        · intro ψ' w hsfeq2
          simp only [SignedFormula.mk.injEq, Proposition.box.injEq] at hsfeq2
          obtain ⟨-, hψeq, hweq⟩ := hsfeq2
          subst hψeq; subst hweq
          exact ⟨modalNextWorld b, hedge, List.mem_append_left _ List.mem_cons_self⟩
        · intro ψ' w hsfeq2
          simp only [SignedFormula.mk.injEq] at hsfeq2
          exact absurd hsfeq2.1 (by simp)
      · -- blocked: redirect to `wBlock`, witness already on the branch.
        have hAOeq := modalApplyOneS4Keyed_boxNeg_blocked_eq φ₀ b acc keys ψ sf.label wBlock
          hblock
        rw [hblock] at hsf
        have hresulteq : result = RuleResult.linear [] :=
          congrArg Prod.fst (hpair.symm.trans hAOeq)
        have hnewAcc0eq : newAcc0 = acc.addEdge sf.label wBlock :=
          congrArg Prod.snd (hpair.symm.trans hAOeq)
        rw [hresulteq] at hsf
        simp only [List.nil_append, Option.some.injEq, Prod.mk.injEq] at hsf
        obtain ⟨hnewBs, hnewExps, hnewAcc, hnewKeys⟩ := hsf
        intro b' hb' e' he'
        rw [← hnewBs] at hb'; simp only [List.mem_singleton] at hb'
        rw [← hnewExps] at he'; simp only [List.mem_singleton] at he'
        rw [hb', he']
        subst hnewAcc; subst hnewKeys
        have hbsub : ∀ x ∈ b, x ∈ b := fun x hx => hx
        have hweak := S4KeyedHintikkaInv_weaken φ₀ b b e acc newAcc0 keys hbsub haccsub hHinv
        have hedge : newAcc0.hasEdge sf.label wBlock = true := by
          rw [hnewAcc0eq]; simp [Accessibility.hasEdge, Accessibility.addEdge]
        have hwitmem := modalStepBranchS4Keyed_blocked_witness_mem φ₀ b keys .neg ψ sf.label
          wBlock hLoopInv.keyLowerBd hblock
        refine S4KeyedHintikkaInv_append φ₀ b e newAcc0 keys keys
          (⟨.neg, .box ψ, sf.label⟩ : SignedFormula (Proposition Atom) WorldIndex) hweak
          ?_ ?_ ?_ ?_ ?_
        · simp [modalHintikkaClauseGen]
        · intro ψ' _; rfl
        · intro ψ' hform; exact absurd hform (by simp)
        · intro ψ' w hsfeq2
          simp only [SignedFormula.mk.injEq, Proposition.box.injEq] at hsfeq2
          obtain ⟨-, hψeq, hweq⟩ := hsfeq2
          subst hψeq; subst hweq
          exact ⟨wBlock, hedge, hwitmem⟩
        · intro ψ' w hsfeq2
          simp only [SignedFormula.mk.injEq] at hsfeq2
          exact absurd hsfeq2.1 (by simp)
    · -- pos + diamond: the diamondPos minting shape, symmetric to neg + box above.
      have hsfeq : sf = (⟨Sign.pos, .diamond ψ, sf.label⟩ :
          SignedFormula (Proposition Atom) WorldIndex) := by rw [← hs, ← hf]
      rw [hsfeq] at hsf hpair
      rw [hpair] at hsf
      dsimp only at hsf
      rw [hsfeq] at hsfmem
      rcases hblock : blockingWorldS4Keyed φ₀ b keys .pos ψ sf.label with _ | wBlock
      · -- unblocked: fresh witness world.
        obtain ⟨hwsnd, rest, hwfst⟩ := modalApplyOneS4KeyedMint_diaPos_witness b acc ψ sf.label
        have hAOeq := modalApplyOneS4Keyed_diaPos_unblocked_eq φ₀ b acc keys ψ sf.label hblock
        rw [hblock] at hsf
        have hresulteq : result = RuleResult.linear
            ((⟨.pos, ψ, modalNextWorld b⟩ : SignedFormula (Proposition Atom) WorldIndex) ::
              rest) := (congrArg Prod.fst (hpair.symm.trans hAOeq)).trans hwfst
        have hnewAcc0eq : newAcc0 = acc.addEdge sf.label (modalNextWorld b) := by
          have hsndeq := congrArg Prod.snd (hpair.symm.trans hAOeq)
          rwa [hwsnd] at hsndeq
        rw [hresulteq] at hsf
        simp only [Option.some.injEq, Prod.mk.injEq] at hsf
        obtain ⟨hnewBs, hnewExps, hnewAcc, -⟩ := hsf
        intro b' hb' e' he'
        rw [← hnewBs] at hb'; simp only [List.mem_singleton] at hb'
        rw [← hnewExps] at he'; simp only [List.mem_singleton] at he'
        subst hb'; subst he'; subst hnewAcc
        have hbsub : ∀ x ∈ b, x ∈
            ((⟨.pos, ψ, modalNextWorld b⟩ : SignedFormula (Proposition Atom) WorldIndex) ::
              rest) ++ b := fun x hx => List.mem_append_right _ hx
        have hweak := S4KeyedHintikkaInv_weaken φ₀ b
          (((⟨.pos, ψ, modalNextWorld b⟩ : SignedFormula (Proposition Atom) WorldIndex) ::
            rest) ++ b) e acc newAcc0 keys hbsub haccsub hHinv
        have hedge : newAcc0.hasEdge sf.label (modalNextWorld b) = true := by
          rw [hnewAcc0eq]; simp [Accessibility.hasEdge, Accessibility.addEdge]
        refine S4KeyedHintikkaInv_append φ₀ _ e newAcc0 keys keys'
          (⟨.pos, .diamond ψ, sf.label⟩ : SignedFormula (Proposition Atom) WorldIndex) hweak
          ?_ ?_ ?_ ?_ ?_
        · simp [modalHintikkaClauseGen]
        · intro ψ' hform; exact absurd hform (by simp)
        · intro ψ' _; rfl
        · intro ψ' w hsfeq2
          simp only [SignedFormula.mk.injEq] at hsfeq2
          exact absurd hsfeq2.1 (by simp)
        · intro ψ' w hsfeq2
          simp only [SignedFormula.mk.injEq, Proposition.diamond.injEq] at hsfeq2
          obtain ⟨-, hψeq, hweq⟩ := hsfeq2
          subst hψeq; subst hweq
          exact ⟨modalNextWorld b, hedge, List.mem_append_left _ List.mem_cons_self⟩
      · -- blocked: redirect to `wBlock`.
        have hAOeq := modalApplyOneS4Keyed_diaPos_blocked_eq φ₀ b acc keys ψ sf.label wBlock
          hblock
        rw [hblock] at hsf
        have hresulteq : result = RuleResult.linear [] :=
          congrArg Prod.fst (hpair.symm.trans hAOeq)
        have hnewAcc0eq : newAcc0 = acc.addEdge sf.label wBlock :=
          congrArg Prod.snd (hpair.symm.trans hAOeq)
        rw [hresulteq] at hsf
        simp only [List.nil_append, Option.some.injEq, Prod.mk.injEq] at hsf
        obtain ⟨hnewBs, hnewExps, hnewAcc, hnewKeys⟩ := hsf
        intro b' hb' e' he'
        rw [← hnewBs] at hb'; simp only [List.mem_singleton] at hb'
        rw [← hnewExps] at he'; simp only [List.mem_singleton] at he'
        rw [hb', he']
        subst hnewAcc; subst hnewKeys
        have hbsub : ∀ x ∈ b, x ∈ b := fun x hx => hx
        have hweak := S4KeyedHintikkaInv_weaken φ₀ b b e acc newAcc0 keys hbsub haccsub hHinv
        have hedge : newAcc0.hasEdge sf.label wBlock = true := by
          rw [hnewAcc0eq]; simp [Accessibility.hasEdge, Accessibility.addEdge]
        have hwitmem := modalStepBranchS4Keyed_blocked_witness_mem φ₀ b keys .pos ψ sf.label
          wBlock hLoopInv.keyLowerBd hblock
        refine S4KeyedHintikkaInv_append φ₀ b e newAcc0 keys keys
          (⟨.pos, .diamond ψ, sf.label⟩ : SignedFormula (Proposition Atom) WorldIndex) hweak
          ?_ ?_ ?_ ?_ ?_
        · simp [modalHintikkaClauseGen]
        · intro ψ' hform; exact absurd hform (by simp)
        · intro ψ' _; rfl
        · intro ψ' w hsfeq2
          simp only [SignedFormula.mk.injEq] at hsfeq2
          exact absurd hsfeq2.1 (by simp)
        · intro ψ' w hsfeq2
          simp only [SignedFormula.mk.injEq, Proposition.diamond.injEq] at hsfeq2
          obtain ⟨-, hψeq, hweq⟩ := hsfeq2
          subst hψeq; subst hweq
          exact ⟨wBlock, hedge, hwitmem⟩
  · -- non-mint: `sf` is neither the boxNeg nor the diaPos minting shape, so `keys' = keys`
    -- (the `keys'`-defining match falls to its `_, _` catch-all). `result` is
    -- `.persistent`/`.linear`/`.branching` for a purely propositional or T/4-persistent `sf`;
    -- `.notApplicable` is excluded since `findSome?` only returns `some` there.
    have hnbd : ¬ (sf.sign = .neg ∧ ∃ φ, sf.formula = .box φ) ∧
        ¬ (sf.sign = .pos ∧ ∃ φ, sf.formula = .diamond φ) :=
      ⟨fun hc => hmint (Or.inl hc), fun hc => hmint (Or.inr hc)⟩
    rw [hpair] at hsf
    dsimp only at hsf
    by_cases hmint2 : (sf.sign = .pos ∧ ∃ φ, sf.formula = .box φ) ∨
        (sf.sign = .neg ∧ ∃ φ, sf.formula = .diamond φ)
    · -- pos-box / neg-diamond: always persistent/notApplicable (never linear/branching).
      have hne := modalApplyOneS4Keyed_boxPos_diaNeg_not_expanding φ₀ keys sf b acc hsfmem
        hLoopInv.accKnown hmint2
      rw [hpair] at hne
      dsimp only at hne
      rcases hres : result with lf | brs | lf | _
      · exact absurd hres (by rw [hres] at hne; rcases hne with h | ⟨_, h⟩ <;> simp_all)
      · exact absurd hres (by rw [hres] at hne; rcases hne with h | ⟨_, h⟩ <;> simp_all)
      · rw [hres] at hsf
        simp only [Option.some.injEq, Prod.mk.injEq] at hsf
        obtain ⟨hnewBs, hnewExps, hnewAcc, hnewKeys⟩ := hsf
        have hkeq : keys' = keys := by
          rw [← hnewKeys]
          rcases hs : sf.sign with _ | _ <;>
            rcases hf : sf.formula with _ | _ | _ | _ | _ | ψ | ψ <;> dsimp only [hs, hf]
          · exact absurd ⟨hs, ψ, hf⟩ hnbd.2
          · exact absurd ⟨hs, ψ, hf⟩ hnbd.1
        intro b' hb' e' he'
        rw [← hnewBs] at hb'; simp only [List.mem_singleton] at hb'
        rw [← hnewExps] at he'; simp only [List.mem_singleton] at he'
        subst hb'; rw [he', hkeq]; subst hnewAcc
        have hbsub : ∀ x ∈ b, x ∈ lf ++ b := fun x hx => List.mem_append_right _ hx
        exact S4KeyedHintikkaInv_weaken φ₀ b (lf ++ b) e acc newAcc0 keys hbsub haccsub hHinv
      · exact absurd hres (by rw [hres] at hne; rcases hne with h | ⟨_, h⟩ <;> simp_all)
    · -- genuinely propositional: `sf.formula` is neither box- nor diamond-shaped at all.
      have hnbd2 : ¬ (sf.sign = .pos ∧ ∃ φ, sf.formula = .box φ) ∧
          ¬ (sf.sign = .neg ∧ ∃ φ, sf.formula = .diamond φ) :=
        ⟨fun hc => hmint2 (Or.inl hc), fun hc => hmint2 (Or.inr hc)⟩
      have hnb : ∀ ψ, sf.formula ≠ .box ψ := by
        intro ψ hform
        rcases hs : sf.sign with _ | _
        · exact hnbd2.1 ⟨hs, ψ, hform⟩
        · exact hnbd.1 ⟨hs, ψ, hform⟩
      have hnd : ∀ ψ, sf.formula ≠ .diamond ψ := by
        intro ψ hform
        rcases hs : sf.sign with _ | _
        · exact hnbd.2 ⟨hs, ψ, hform⟩
        · exact hnbd2.2 ⟨hs, ψ, hform⟩
      rcases hres : result with lf | brs | lf | _
      · -- linear (propositional rule, e.g. and/or/imp)
        rw [hres] at hsf
        simp only [Option.some.injEq, Prod.mk.injEq] at hsf
        obtain ⟨hnewBs, hnewExps, hnewAcc, hnewKeys⟩ := hsf
        have hkeq : keys' = keys := by
          rw [← hnewKeys]
          rcases hs : sf.sign with _ | _ <;>
            rcases hf : sf.formula with _ | _ | _ | _ | _ | ψ | ψ <;> dsimp only [hs, hf]
          · exact absurd ⟨hs, ψ, hf⟩ hnbd.2
          · exact absurd ⟨hs, ψ, hf⟩ hnbd.1
        intro b' hb' e' he'
        rw [← hnewBs] at hb'; simp only [List.mem_singleton] at hb'
        rw [← hnewExps] at he'; simp only [List.mem_singleton] at he'
        subst hb'; subst he'; subst hnewAcc; rw [hkeq]
        have hbsub : ∀ x ∈ b, x ∈ lf ++ b := fun x hx => List.mem_append_right _ hx
        have hweak := S4KeyedHintikkaInv_weaken φ₀ b (lf ++ b) e acc newAcc0 keys hbsub haccsub
          hHinv
        have hinveq : (modalApplyOneS4Keyed φ₀ keys
            (⟨sf.sign, sf.formula, sf.label⟩ : SignedFormula (Proposition Atom) WorldIndex)
            (lf ++ b) newAcc0).1 = RuleResult.linear lf := by
          rw [← modalApplyOneS4Keyed_fst_eq_of_not_box φ₀ keys sf.sign sf.formula sf.label
            hnb hnd b (lf ++ b) acc newAcc0]
          rw [← hres]; exact congrArg Prod.fst hpair
        refine S4KeyedHintikkaInv_append φ₀ (lf ++ b) e newAcc0 keys keys sf hweak ?_
          (fun ψ' hform => absurd hform (hnb ψ')) (fun ψ' hform => absurd hform (hnd ψ'))
          (fun ψ' w hsfeq2 => absurd (congrArg SignedFormula.formula hsfeq2) (hnb ψ'))
          (fun ψ' w hsfeq2 => absurd (congrArg SignedFormula.formula hsfeq2) (hnd ψ'))
        unfold modalHintikkaClauseGen
        rcases hff : sf.formula with p | _ | ⟨a, c⟩ | ⟨x, y⟩ | ⟨x, y⟩ | ψ | ψ
        · rw [hff] at hinveq; rw [hinveq]; exact fun x hx => List.mem_append_left _ hx
        · rw [hff] at hinveq; rw [hinveq]; exact fun x hx => List.mem_append_left _ hx
        · rw [hff] at hinveq; rw [hinveq]; exact fun x hx => List.mem_append_left _ hx
        · rw [hff] at hinveq; rw [hinveq]; exact fun x hx => List.mem_append_left _ hx
        · rw [hff] at hinveq; rw [hinveq]; exact fun x hx => List.mem_append_left _ hx
        · exact absurd hff (hnb ψ)
        · exact absurd hff (hnd ψ)
      · -- branching (propositional or-rule)
        rw [hres] at hsf
        simp only [Option.some.injEq, Prod.mk.injEq] at hsf
        obtain ⟨hnewBs, hnewExps, hnewAcc, hnewKeys⟩ := hsf
        have hkeq : keys' = keys := by
          rw [← hnewKeys]
          rcases hs : sf.sign with _ | _ <;>
            rcases hf : sf.formula with _ | _ | _ | _ | _ | ψ | ψ <;> dsimp only [hs, hf]
          · exact absurd ⟨hs, ψ, hf⟩ hnbd.2
          · exact absurd ⟨hs, ψ, hf⟩ hnbd.1
        intro b' hb' e' he'
        rw [← hnewBs] at hb'
        obtain ⟨br, hbrmem, rfl⟩ := List.mem_map.mp hb'
        rw [← hnewExps] at he'
        obtain ⟨br', hbr'mem, he'eq⟩ := List.mem_map.mp he'
        subst hnewAcc; rw [hkeq]
        have hbsub : ∀ x ∈ b, x ∈ br ++ b := fun x hx => List.mem_append_right _ hx
        have hweak := S4KeyedHintikkaInv_weaken φ₀ b (br ++ b) e acc newAcc0 keys hbsub haccsub
          hHinv
        have hinveq : (modalApplyOneS4Keyed φ₀ keys
            (⟨sf.sign, sf.formula, sf.label⟩ : SignedFormula (Proposition Atom) WorldIndex)
            (br ++ b) newAcc0).1 = RuleResult.branching brs := by
          rw [← modalApplyOneS4Keyed_fst_eq_of_not_box φ₀ keys sf.sign sf.formula sf.label
            hnb hnd b (br ++ b) acc newAcc0]
          rw [← hres]; exact congrArg Prod.fst hpair
        rw [← he'eq]
        refine S4KeyedHintikkaInv_append φ₀ (br ++ b) e newAcc0 keys keys sf hweak ?_
          (fun ψ' hform => absurd hform (hnb ψ')) (fun ψ' hform => absurd hform (hnd ψ'))
          (fun ψ' w hsfeq2 => absurd (congrArg SignedFormula.formula hsfeq2) (hnb ψ'))
          (fun ψ' w hsfeq2 => absurd (congrArg SignedFormula.formula hsfeq2) (hnd ψ'))
        unfold modalHintikkaClauseGen
        rcases hff : sf.formula with p | _ | ⟨a, c⟩ | ⟨x, y⟩ | ⟨x, y⟩ | ψ | ψ
        · rw [hff] at hinveq; rw [hinveq]
          exact ⟨br, hbrmem, fun x hx => List.mem_append_left _ hx⟩
        · rw [hff] at hinveq; rw [hinveq]
          exact ⟨br, hbrmem, fun x hx => List.mem_append_left _ hx⟩
        · rw [hff] at hinveq; rw [hinveq]
          exact ⟨br, hbrmem, fun x hx => List.mem_append_left _ hx⟩
        · rw [hff] at hinveq; rw [hinveq]
          exact ⟨br, hbrmem, fun x hx => List.mem_append_left _ hx⟩
        · rw [hff] at hinveq; rw [hinveq]
          exact ⟨br, hbrmem, fun x hx => List.mem_append_left _ hx⟩
        · exact absurd hff (hnb ψ)
        · exact absurd hff (hnd ψ)
      · -- persistent (no change to `e`)
        rw [hres] at hsf
        simp only [Option.some.injEq, Prod.mk.injEq] at hsf
        obtain ⟨hnewBs, hnewExps, hnewAcc, hnewKeys⟩ := hsf
        have hkeq : keys' = keys := by
          rw [← hnewKeys]
          rcases hs : sf.sign with _ | _ <;>
            rcases hf : sf.formula with _ | _ | _ | _ | _ | ψ | ψ <;> dsimp only [hs, hf]
          · exact absurd ⟨hs, ψ, hf⟩ hnbd.2
          · exact absurd ⟨hs, ψ, hf⟩ hnbd.1
        intro b' hb' e' he'
        rw [← hnewBs] at hb'; simp only [List.mem_singleton] at hb'
        rw [← hnewExps] at he'; simp only [List.mem_singleton] at he'
        subst hb'; rw [he', hkeq]; subst hnewAcc
        have hbsub : ∀ x ∈ b, x ∈ lf ++ b := fun x hx => List.mem_append_right _ hx
        exact S4KeyedHintikkaInv_weaken φ₀ b (lf ++ b) e acc newAcc0 keys hbsub haccsub hHinv
      · -- notApplicable: impossible, `findSome?` only returns `some` when applicable.
        rw [hres] at hsf; simp at hsf

/-- **`S4KeyedHintikkaInv` preservation for the ordered driver.** Every
`modalStepBranchS4KeyedOrdered` step preserves the keys-threaded Hintikka-tracking invariant
bundle, given the ambient frozen `S4LoopInv` structure. Ports
`modalStepBranchS4Keyed_preserves_S4KeyedHintikkaInv` (above) to the ordered driver via
`modalStepBranchS4KeyedOrdered_cases`: the settled-fallback branch reduces to a literal call of
`modalStepBranchS4Keyed`, so it is discharged by the unordered theorem directly with no new
content; the primary-scan-hit branch selects a NON-MINT candidate
(`modalMintShape sf = false`, `modalNonMintCandidates`'s own predicate), so it is confined to the
unordered proof's own "non-mint" case (its final `by_cases hmint2` branch), restated here against
the shared body `modalStepBranchS4KeyedBody` in place of the bare `findSome?` extraction -- the
SAME per-formula mechanics (`modalStepBranchS4Keyed_eq_findSome_body` confirms the two traversals
share this body verbatim), just reached via a different selection route. No mint case ever arises
in the primary-scan-hit branch, so it needs none of the unordered proof's mint-shape content. -/
theorem modalStepBranchS4KeyedOrdered_preserves_S4KeyedHintikkaInv (φ₀ : Proposition Atom)
    (b e : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (keys : List (WorldIndex × Finset (Sign × Proposition Atom)))
    (newBs newExps : List (List (SignedFormula (Proposition Atom) WorldIndex)))
    (newAcc : Accessibility) (keys' : List (WorldIndex × Finset (Sign × Proposition Atom)))
    (hLoopInv : S4LoopInv φ₀ b e acc keys)
    (hHinv : S4KeyedHintikkaInv φ₀ b e acc keys)
    (hstep : modalStepBranchS4KeyedOrdered φ₀ b e acc keys =
      some (newBs, newExps, newAcc, keys')) :
    ∀ b' ∈ newBs, ∀ e' ∈ newExps, S4KeyedHintikkaInv φ₀ b' e' newAcc keys' := by
  rcases modalStepBranchS4KeyedOrdered_cases φ₀ b e acc keys newBs newExps newAcc keys' hstep with
    ⟨sf, hcand, hbody⟩ | ⟨-, hfallback⟩
  · -- Primary-scan hit: `sf` is non-mint-shaped (by `modalNonMintCandidates`'s own predicate).
    have hsfmemb := modalNonMintCandidates_subset φ₀ keys b e acc hcand
    have hsfnote := modalNonMintCandidates_not_mem_expanded φ₀ keys b e acc sf hcand
    have hmintapp : modalMintShape sf = false ∧
        (modalApplyOneS4Keyed φ₀ keys sf b acc).1.isApplicable = true := by
      unfold modalNonMintCandidates at hcand
      have hpred := (List.mem_filter.mp hcand).2
      simp only [Bool.and_eq_true, Bool.not_eq_true'] at hpred
      exact ⟨hpred.1.1, hpred.2⟩
    obtain ⟨hmshape, -⟩ := hmintapp
    have hnbd : ¬ (sf.sign = .neg ∧ ∃ φ, sf.formula = .box φ) ∧
        ¬ (sf.sign = .pos ∧ ∃ φ, sf.formula = .diamond φ) := by
      refine ⟨?_, ?_⟩
      · rintro ⟨hs, φ, hf⟩
        exact absurd hmshape (by simp [modalMintShape, hs, hf])
      · rintro ⟨hs, φ, hf⟩
        exact absurd hmshape (by simp [modalMintShape, hs, hf])
    have hany : e.any (· == sf) = false := by
      rw [List.any_eq_false]
      intro x hx heq
      rw [beq_iff_eq] at heq
      subst heq
      exact hsfnote hx
    unfold modalStepBranchS4KeyedBody at hbody
    rw [if_neg (by simp [hany])] at hbody
    rcases hpair : modalApplyOneS4Keyed φ₀ keys sf b acc with ⟨result, newAcc0⟩
    rw [hpair] at hbody
    dsimp only at hbody
    have haccsub : ∀ w w', acc.hasEdge w w' = true → newAcc0.hasEdge w w' = true := by
      intro w w' h
      have hmono := modalApplyOneS4Keyed_hasEdge_mono φ₀ keys sf b acc h
      rwa [hpair] at hmono
    by_cases hmint2 : (sf.sign = .pos ∧ ∃ φ, sf.formula = .box φ) ∨
        (sf.sign = .neg ∧ ∃ φ, sf.formula = .diamond φ)
    · -- pos-box / neg-diamond: always persistent (never linear/branching).
      have hne := modalApplyOneS4Keyed_boxPos_diaNeg_not_expanding φ₀ keys sf b acc hsfmemb
        hLoopInv.accKnown hmint2
      rw [hpair] at hne
      dsimp only at hne
      rcases hres : result with lf | brs | lf | _
      · exact absurd hres (by rw [hres] at hne; rcases hne with h | ⟨_, h⟩ <;> simp_all)
      · exact absurd hres (by rw [hres] at hne; rcases hne with h | ⟨_, h⟩ <;> simp_all)
      · rw [hres] at hbody
        simp only [Option.some.injEq, Prod.mk.injEq] at hbody
        obtain ⟨hnewBs, hnewExps, hnewAcc, hnewKeys⟩ := hbody
        have hkeq : keys' = keys := by
          rw [← hnewKeys]
          rcases hs : sf.sign with _ | _ <;>
            rcases hf : sf.formula with _ | _ | _ | _ | _ | ψ | ψ <;> dsimp only [hs, hf]
          · exact absurd ⟨hs, ψ, hf⟩ hnbd.2
          · exact absurd ⟨hs, ψ, hf⟩ hnbd.1
        intro b' hb' e' he'
        rw [← hnewBs] at hb'; simp only [List.mem_singleton] at hb'
        rw [← hnewExps] at he'; simp only [List.mem_singleton] at he'
        subst hb'; rw [he', hkeq]; subst hnewAcc
        have hbsub : ∀ x ∈ b, x ∈ lf ++ b := fun x hx => List.mem_append_right _ hx
        exact S4KeyedHintikkaInv_weaken φ₀ b (lf ++ b) e acc newAcc0 keys hbsub haccsub hHinv
      · exact absurd hres (by rw [hres] at hne; rcases hne with h | ⟨_, h⟩ <;> simp_all)
    · -- genuinely propositional: `sf.formula` is neither box- nor diamond-shaped at all.
      have hnbd2 : ¬ (sf.sign = .pos ∧ ∃ φ, sf.formula = .box φ) ∧
          ¬ (sf.sign = .neg ∧ ∃ φ, sf.formula = .diamond φ) :=
        ⟨fun hc => hmint2 (Or.inl hc), fun hc => hmint2 (Or.inr hc)⟩
      have hnb : ∀ ψ, sf.formula ≠ .box ψ := by
        intro ψ hform
        rcases hs : sf.sign with _ | _
        · exact hnbd2.1 ⟨hs, ψ, hform⟩
        · exact hnbd.1 ⟨hs, ψ, hform⟩
      have hnd : ∀ ψ, sf.formula ≠ .diamond ψ := by
        intro ψ hform
        rcases hs : sf.sign with _ | _
        · exact hnbd.2 ⟨hs, ψ, hform⟩
        · exact hnbd2.2 ⟨hs, ψ, hform⟩
      rcases hres : result with lf | brs | lf | _
      · -- linear (propositional rule, e.g. and/or/imp)
        rw [hres] at hbody
        simp only [Option.some.injEq, Prod.mk.injEq] at hbody
        obtain ⟨hnewBs, hnewExps, hnewAcc, hnewKeys⟩ := hbody
        have hkeq : keys' = keys := by
          rw [← hnewKeys]
          rcases hs : sf.sign with _ | _ <;>
            rcases hf : sf.formula with _ | _ | _ | _ | _ | ψ | ψ <;> dsimp only [hs, hf]
          · exact absurd ⟨hs, ψ, hf⟩ hnbd.2
          · exact absurd ⟨hs, ψ, hf⟩ hnbd.1
        intro b' hb' e' he'
        rw [← hnewBs] at hb'; simp only [List.mem_singleton] at hb'
        rw [← hnewExps] at he'; simp only [List.mem_singleton] at he'
        subst hb'; subst he'; subst hnewAcc; rw [hkeq]
        have hbsub : ∀ x ∈ b, x ∈ lf ++ b := fun x hx => List.mem_append_right _ hx
        have hweak := S4KeyedHintikkaInv_weaken φ₀ b (lf ++ b) e acc newAcc0 keys hbsub haccsub
          hHinv
        have hinveq : (modalApplyOneS4Keyed φ₀ keys
            (⟨sf.sign, sf.formula, sf.label⟩ : SignedFormula (Proposition Atom) WorldIndex)
            (lf ++ b) newAcc0).1 = RuleResult.linear lf := by
          rw [← modalApplyOneS4Keyed_fst_eq_of_not_box φ₀ keys sf.sign sf.formula sf.label
            hnb hnd b (lf ++ b) acc newAcc0]
          rw [← hres]; exact congrArg Prod.fst hpair
        refine S4KeyedHintikkaInv_append φ₀ (lf ++ b) e newAcc0 keys keys sf hweak ?_
          (fun ψ' hform => absurd hform (hnb ψ')) (fun ψ' hform => absurd hform (hnd ψ'))
          (fun ψ' w hsfeq2 => absurd (congrArg SignedFormula.formula hsfeq2) (hnb ψ'))
          (fun ψ' w hsfeq2 => absurd (congrArg SignedFormula.formula hsfeq2) (hnd ψ'))
        unfold modalHintikkaClauseGen
        rcases hff : sf.formula with p | _ | ⟨a, c⟩ | ⟨x, y⟩ | ⟨x, y⟩ | ψ | ψ
        · rw [hff] at hinveq; rw [hinveq]; exact fun x hx => List.mem_append_left _ hx
        · rw [hff] at hinveq; rw [hinveq]; exact fun x hx => List.mem_append_left _ hx
        · rw [hff] at hinveq; rw [hinveq]; exact fun x hx => List.mem_append_left _ hx
        · rw [hff] at hinveq; rw [hinveq]; exact fun x hx => List.mem_append_left _ hx
        · rw [hff] at hinveq; rw [hinveq]; exact fun x hx => List.mem_append_left _ hx
        · exact absurd hff (hnb ψ)
        · exact absurd hff (hnd ψ)
      · -- branching (propositional or-rule)
        rw [hres] at hbody
        simp only [Option.some.injEq, Prod.mk.injEq] at hbody
        obtain ⟨hnewBs, hnewExps, hnewAcc, hnewKeys⟩ := hbody
        have hkeq : keys' = keys := by
          rw [← hnewKeys]
          rcases hs : sf.sign with _ | _ <;>
            rcases hf : sf.formula with _ | _ | _ | _ | _ | ψ | ψ <;> dsimp only [hs, hf]
          · exact absurd ⟨hs, ψ, hf⟩ hnbd.2
          · exact absurd ⟨hs, ψ, hf⟩ hnbd.1
        intro b' hb' e' he'
        rw [← hnewBs] at hb'
        obtain ⟨br, hbrmem, rfl⟩ := List.mem_map.mp hb'
        rw [← hnewExps] at he'
        obtain ⟨br', hbr'mem, he'eq⟩ := List.mem_map.mp he'
        subst hnewAcc; rw [hkeq]
        have hbsub : ∀ x ∈ b, x ∈ br ++ b := fun x hx => List.mem_append_right _ hx
        have hweak := S4KeyedHintikkaInv_weaken φ₀ b (br ++ b) e acc newAcc0 keys hbsub haccsub
          hHinv
        have hinveq : (modalApplyOneS4Keyed φ₀ keys
            (⟨sf.sign, sf.formula, sf.label⟩ : SignedFormula (Proposition Atom) WorldIndex)
            (br ++ b) newAcc0).1 = RuleResult.branching brs := by
          rw [← modalApplyOneS4Keyed_fst_eq_of_not_box φ₀ keys sf.sign sf.formula sf.label
            hnb hnd b (br ++ b) acc newAcc0]
          rw [← hres]; exact congrArg Prod.fst hpair
        rw [← he'eq]
        refine S4KeyedHintikkaInv_append φ₀ (br ++ b) e newAcc0 keys keys sf hweak ?_
          (fun ψ' hform => absurd hform (hnb ψ')) (fun ψ' hform => absurd hform (hnd ψ'))
          (fun ψ' w hsfeq2 => absurd (congrArg SignedFormula.formula hsfeq2) (hnb ψ'))
          (fun ψ' w hsfeq2 => absurd (congrArg SignedFormula.formula hsfeq2) (hnd ψ'))
        unfold modalHintikkaClauseGen
        rcases hff : sf.formula with p | _ | ⟨a, c⟩ | ⟨x, y⟩ | ⟨x, y⟩ | ψ | ψ
        · rw [hff] at hinveq; rw [hinveq]
          exact ⟨br, hbrmem, fun x hx => List.mem_append_left _ hx⟩
        · rw [hff] at hinveq; rw [hinveq]
          exact ⟨br, hbrmem, fun x hx => List.mem_append_left _ hx⟩
        · rw [hff] at hinveq; rw [hinveq]
          exact ⟨br, hbrmem, fun x hx => List.mem_append_left _ hx⟩
        · rw [hff] at hinveq; rw [hinveq]
          exact ⟨br, hbrmem, fun x hx => List.mem_append_left _ hx⟩
        · rw [hff] at hinveq; rw [hinveq]
          exact ⟨br, hbrmem, fun x hx => List.mem_append_left _ hx⟩
        · exact absurd hff (hnb ψ)
        · exact absurd hff (hnd ψ)
      · -- persistent (no change to `e`)
        rw [hres] at hbody
        simp only [Option.some.injEq, Prod.mk.injEq] at hbody
        obtain ⟨hnewBs, hnewExps, hnewAcc, hnewKeys⟩ := hbody
        have hkeq : keys' = keys := by
          rw [← hnewKeys]
          rcases hs : sf.sign with _ | _ <;>
            rcases hf : sf.formula with _ | _ | _ | _ | _ | ψ | ψ <;> dsimp only [hs, hf]
          · exact absurd ⟨hs, ψ, hf⟩ hnbd.2
          · exact absurd ⟨hs, ψ, hf⟩ hnbd.1
        intro b' hb' e' he'
        rw [← hnewBs] at hb'; simp only [List.mem_singleton] at hb'
        rw [← hnewExps] at he'; simp only [List.mem_singleton] at he'
        subst hb'; rw [he', hkeq]; subst hnewAcc
        have hbsub : ∀ x ∈ b, x ∈ lf ++ b := fun x hx => List.mem_append_right _ hx
        exact S4KeyedHintikkaInv_weaken φ₀ b (lf ++ b) e acc newAcc0 keys hbsub haccsub hHinv
      · -- notApplicable: impossible, `findSome?` only returns `some` when applicable.
        rw [hres] at hbody; simp at hbody
  · exact modalStepBranchS4Keyed_preserves_S4KeyedHintikkaInv φ₀ b e acc keys newBs newExps
      newAcc keys' hLoopInv hHinv hfallback

/-- **The combined structural invariant bundle Phase 9's fuel induction threads.** Everything
`modalStepBranchS4KeyedOrdered_preserves_S4LoopInv` and
`modalStepBranchS4KeyedOrdered_preserves_S4KeyedHintikkaInv` jointly need as ambient state,
packaged as one `Prop` so a single `List.Forall₂`-style relation carries all of it through the
outer fuel induction, mirroring how `S5SoundInv` (`FrameSoundness.lean`) bundles
`accFreshInv ∧ accReachableInv ∧ accTargetsKnown` for the S5 assembly. -/
def S4OrderedFuelInv (φ₀ : Proposition Atom)
    (b e : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (keys : List (WorldIndex × Finset (Sign × Proposition Atom))) : Prop :=
  S4LoopInv φ₀ b e acc keys ∧ S4KeyedHintikkaInv φ₀ b e acc keys ∧
  (∀ w k, (w, k) ∈ keys → w ∈ modalKnownWorlds b) ∧ worldsContiguousS4 b ∧
  keysOriginS4 b acc keys

/-- Every `modalStepBranchS4KeyedOrdered` step preserves the combined `S4OrderedFuelInv` bundle,
for every child branch/expanded-set pair. Direct assembly of
`modalStepBranchS4KeyedOrdered_preserves_S4LoopInv` (supplies four of the five conjuncts) and
`modalStepBranchS4KeyedOrdered_preserves_S4KeyedHintikkaInv` (the fifth) -- no independent proof
content of its own. -/
theorem modalStepBranchS4KeyedOrdered_preserves_S4OrderedFuelInv (φ₀ : Proposition Atom)
    (b e : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (keys : List (WorldIndex × Finset (Sign × Proposition Atom)))
    (newBs newExps : List (List (SignedFormula (Proposition Atom) WorldIndex)))
    (newAcc : Accessibility) (keys' : List (WorldIndex × Finset (Sign × Proposition Atom)))
    (hinv : S4OrderedFuelInv φ₀ b e acc keys)
    (hstep : modalStepBranchS4KeyedOrdered φ₀ b e acc keys =
      some (newBs, newExps, newAcc, keys')) :
    ∀ b' ∈ newBs, ∀ e' ∈ newExps, S4OrderedFuelInv φ₀ b' e' newAcc keys' := by
  obtain ⟨hLoop, hH, hKW, hWC, hKO⟩ := hinv
  have hL := modalStepBranchS4KeyedOrdered_preserves_S4LoopInv φ₀ b e acc keys newBs newExps
    newAcc keys' hLoop hKW hWC hKO hstep
  have hHi := modalStepBranchS4KeyedOrdered_preserves_S4KeyedHintikkaInv φ₀ b e acc keys newBs
    newExps newAcc keys' hLoop hH hstep
  intro b' hb' e' he'
  exact ⟨hL.1 b' hb' e' he', hHi b' hb' e' he', hL.2.1 b' hb', hL.2.2.1 b' hb', hL.2.2.2 b' hb'⟩

end Cslib.Logic.Modal.Tableau

end
