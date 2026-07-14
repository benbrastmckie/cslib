/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

import Cslib.Init
import Mathlib.Tactic.Ring
public import Cslib.Logics.Modal.Tableau.FmpMeasure
public import Cslib.Logics.Modal.Tableau.FrameRules

/-! # S4 Loop-Checking Machinery

This module builds the equality-blocking loop-checking machinery for the S4
(reflexive-transitive) modal tableau: per-world relevant-formula-set extraction, a
decidable equality test over `modalSubfmls φ₀`, the minting guard that consults this test
before creating a fresh world, the S4 rule-application function, and the S4 Hintikka-set
characterization.

S4 is deliberately **not** an instantiation of `RuleApplicationSpec` (`GenericDriver.lean`):
its transitively-propagating 4-rule places `T(□φ)` (unchanged modal depth) at successor
worlds, which falsifies the exact-decrement edge invariant (`rankStep`) that
`RuleApplicationSpec` demands. S4 reuses the generic driver (`modalStepBranchGen` etc.)
**definitionally only**, via a `φ₀`-parameterized `RuleApply` value, and supplies its own
sibling termination argument (`S4LoopInv`, a pigeonhole bound on `2 ^ |modalSubfmls φ₀|`
possible relevant-formula sets) instead of the K/T rank-decrease argument.

## Main Definitions

- `formulasAtWorld`: the sub-list of a branch's signed formulas at a given world.
- `sameRelevantSet`: the decidable equality-of-relevant-formula-set test over
  `modalSubfmls φ₀`, used by the S4 minting guard to detect a "loop" (an existing world
  that already witnesses everything the current world would witness).
- `blockingWorld`: search `modalKnownWorlds b` for an existing world with the same
  relevant formula set as `w` -- the concrete minting guard.
- `modalApplyOneS4`: the `φ₀`-parameterized S4 rule-application function (Decision D1):
  at the two minting shapes, consult `blockingWorld` before falling through to the
  underlying rule's fresh-world minting.
- `modalStepBranchS4`/`modalExpandBranchesS4`/`modalTableauS4`: the S4 driver, reusing
  `Saturation.lean`'s generic driver **definitionally only** (no `RuleApplicationSpec`
  instance -- Correction 3).
- `modalHintikkaSetS4`: the S4 Hintikka-set characterization, a small delta over
  `modalHintikkaSet` (Decision D3).

## Strategy

Blocking is **equality-of-relevant-formula-set**, not subset-blocking: two worlds `w`,
`w'` are considered "the same" for loop-checking purposes exactly when they agree, for
every `ψ ∈ modalSubfmls φ₀` and every sign `s`, on whether `⟨s, ψ, w⟩` (`⟨s, ψ, w'⟩`
respectively) is on the branch. This is simpler than subset blocking and still yields a
`2 ^ |modalSubfmls φ₀|` bound on the number of distinct worlds a saturating S4 tableau can
create (Phase 8), since each world's relevant set is a distinct element of the powerset of
`modalSubfmls φ₀ × Sign`.

Do **not** import `LoopInduction.lean`: despite the name, it is a `Forall2` list lemma
about the *fuel* loop in the generic driver, unrelated to modal loop-checking.

## References

* [M. Fitting, *Proof Methods for Modal and Intuitionistic Logics*][Fitting1983], Chapter 2
-/

@[expose] public section

namespace Cslib.Logic.Modal.Tableau

open Cslib.Logic.Tableau Cslib.Logic.Modal

variable {Atom : Type*} [DecidableEq Atom] [Hashable Atom]

/-! ## Per-World Formula Sets -/

/-- The sub-list of `b`'s signed formulas whose label is exactly `w`. -/
def formulasAtWorld (b : List (SignedFormula (Proposition Atom) WorldIndex))
    (w : WorldIndex) : List (SignedFormula (Proposition Atom) WorldIndex) :=
  b.filter (·.label == w)

omit [DecidableEq Atom] [Hashable Atom] in
/-- Membership characterization for `formulasAtWorld`: a signed formula is in
`formulasAtWorld b w` iff it is in `b` and its label is `w`. -/
lemma mem_formulasAtWorld_iff (b : List (SignedFormula (Proposition Atom) WorldIndex))
    (w : WorldIndex) (sf : SignedFormula (Proposition Atom) WorldIndex) :
    sf ∈ formulasAtWorld b w ↔ sf ∈ b ∧ sf.label = w := by
  unfold formulasAtWorld
  simp [List.mem_filter, beq_iff_eq]

/-! ## Relevant-Formula-Set Equality Test -/

/-- The decidable equality-of-relevant-formula-set test that drives S4's loop-checking
minting guard: `true` exactly when `w` and `w'` agree, for every subformula `ψ` of `φ₀`
and every sign `s`, on whether `⟨s, ψ, w⟩` (resp. `⟨s, ψ, w'⟩`) is present on `b`.

This is stated directly over `b` (rather than via an intermediate sorted/deduped
relevant-formula list) precisely because a pointwise Boolean membership comparison, one
`ψ ∈ modalSubfmls φ₀` at a time, sidesteps any ordering concerns: `sameRelevantSet` is
manifestly reflexive and symmetric by construction (`Bool` equality is symmetric,
`Bool.beq_comm`-style), and transitive by chaining two equalities. -/
def sameRelevantSet (φ₀ : Proposition Atom) (b : List (SignedFormula (Proposition Atom) WorldIndex))
    (w w' : WorldIndex) : Bool :=
  (modalSubfmls φ₀).all (fun ψ =>
    (b.any (· == (⟨.pos, ψ, w⟩ : SignedFormula (Proposition Atom) WorldIndex))
      == b.any (· == (⟨.pos, ψ, w'⟩ : SignedFormula (Proposition Atom) WorldIndex))) &&
    (b.any (· == (⟨.neg, ψ, w⟩ : SignedFormula (Proposition Atom) WorldIndex))
      == b.any (· == (⟨.neg, ψ, w'⟩ : SignedFormula (Proposition Atom) WorldIndex))))

/-- Bridge: `b.any (· == sf) = true ↔ sf ∈ b`, the standard membership bridge for the
`List.any (· == ·)` idiom used throughout the modal tableau development. -/
private lemma any_beq_iff_mem {α : Type*} [DecidableEq α] (l : List α) (a : α) :
    l.any (· == a) = true ↔ a ∈ l := by
  rw [List.any_eq_true]
  constructor
  · rintro ⟨x, hx, hxa⟩
    rw [beq_iff_eq] at hxa
    rwa [hxa] at hx
  · intro ha
    exact ⟨a, ha, by simp⟩

omit [Hashable Atom] in
/-- The characterization `sameRelevantSet` is built to serve: `sameRelevantSet φ₀ b w w'`
holds iff `w` and `w'` agree on membership of every relevant signed formula. This is what
Phase 8's pigeonhole argument consumes: `worldSetsDistinct` demands that every pair of
distinct known worlds *fails* this characterization. -/
lemma sameRelevantSet_iff (φ₀ : Proposition Atom)
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (w w' : WorldIndex) :
    sameRelevantSet φ₀ b w w' = true ↔
      ∀ (s : Sign) (ψ : Proposition Atom), ψ ∈ modalSubfmls φ₀ →
        ((⟨s, ψ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b ↔
         (⟨s, ψ, w'⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b) := by
  unfold sameRelevantSet
  simp only [List.all_eq_true, Bool.and_eq_true, beq_iff_eq]
  constructor
  · intro h s ψ hψ
    obtain ⟨hpos, hneg⟩ := h ψ hψ
    rcases s with _ | _
    · rw [← any_beq_iff_mem, ← any_beq_iff_mem, hpos]
    · rw [← any_beq_iff_mem, ← any_beq_iff_mem, hneg]
  · intro h ψ hψ
    refine ⟨?_, ?_⟩
    · rw [Bool.eq_iff_iff, any_beq_iff_mem, any_beq_iff_mem]
      exact h .pos ψ hψ
    · rw [Bool.eq_iff_iff, any_beq_iff_mem, any_beq_iff_mem]
      exact h .neg ψ hψ

omit [Hashable Atom] in
/-- `sameRelevantSet` is reflexive: every world agrees with itself. -/
lemma sameRelevantSet_refl (φ₀ : Proposition Atom)
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (w : WorldIndex) :
    sameRelevantSet φ₀ b w w = true := by
  rw [sameRelevantSet_iff]
  intro s ψ _
  rfl

omit [Hashable Atom] in
/-- `sameRelevantSet` is symmetric. -/
lemma sameRelevantSet_symm (φ₀ : Proposition Atom)
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (w w' : WorldIndex) :
    sameRelevantSet φ₀ b w w' = sameRelevantSet φ₀ b w' w := by
  by_cases h : sameRelevantSet φ₀ b w w' = true
  · have h' : sameRelevantSet φ₀ b w' w = true := by
      rw [sameRelevantSet_iff] at h ⊢
      intro s ψ hψ
      exact (h s ψ hψ).symm
    rw [h, h']
  · have hfalse : sameRelevantSet φ₀ b w w' = false := by
      rcases hb : sameRelevantSet φ₀ b w w' with _ | _
      · rfl
      · exact absurd hb h
    have hfalse' : sameRelevantSet φ₀ b w' w = false := by
      by_contra hcon
      rw [Bool.not_eq_false] at hcon
      apply h
      rw [sameRelevantSet_iff] at hcon ⊢
      intro s ψ hψ
      exact (hcon s ψ hψ).symm
    rw [hfalse, hfalse']

omit [Hashable Atom] in
/-- `sameRelevantSet` is transitive. -/
lemma sameRelevantSet_trans (φ₀ : Proposition Atom)
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (w w' w'' : WorldIndex)
    (h1 : sameRelevantSet φ₀ b w w' = true) (h2 : sameRelevantSet φ₀ b w' w'' = true) :
    sameRelevantSet φ₀ b w w'' = true := by
  rw [sameRelevantSet_iff] at h1 h2 ⊢
  intro s ψ hψ
  exact (h1 s ψ hψ).trans (h2 s ψ hψ)

/-! ## Minting Guard -/

/-- The concrete minting guard: the least world `w' ∈ modalKnownWorlds b` (other than `w`
itself) whose relevant formula set matches `w`'s, if any exists. `none` means no blocking
world exists (the underlying rule should mint a fresh world); `some wBlock` means `w` should
be closed back to `wBlock` via a loop-back edge instead of minting a new world. -/
def blockingWorld (φ₀ : Proposition Atom) (b : List (SignedFormula (Proposition Atom) WorldIndex))
    (w : WorldIndex) : Option WorldIndex :=
  ((modalKnownWorlds b).filter (fun w' => w' != w && sameRelevantSet φ₀ b w w')).min?

omit [Hashable Atom] in
/-- If `blockingWorld` returns a world, it is a known world of the branch. -/
lemma blockingWorld_mem_modalKnownWorlds (φ₀ : Proposition Atom)
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (w wBlock : WorldIndex)
    (h : blockingWorld φ₀ b w = some wBlock) : wBlock ∈ modalKnownWorlds b := by
  have hmem := List.min?_mem h
  exact (List.mem_filter.mp hmem).1

omit [Hashable Atom] in
/-- If `blockingWorld` returns a world, it is distinct from `w`. -/
lemma blockingWorld_ne (φ₀ : Proposition Atom)
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (w wBlock : WorldIndex)
    (h : blockingWorld φ₀ b w = some wBlock) : wBlock ≠ w := by
  have hmem := List.min?_mem h
  have hpred := (List.mem_filter.mp hmem).2
  simp only [Bool.and_eq_true, bne_iff_ne] at hpred
  exact hpred.1

omit [Hashable Atom] in
/-- If `blockingWorld` returns a world, that world has an equal relevant formula set to
`w`: this is the property Phase 8's pigeonhole argument needs. -/
lemma blockingWorld_sameRelevantSet (φ₀ : Proposition Atom)
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (w wBlock : WorldIndex)
    (h : blockingWorld φ₀ b w = some wBlock) : sameRelevantSet φ₀ b w wBlock = true := by
  have hmem := List.min?_mem h
  have hpred := (List.mem_filter.mp hmem).2
  simp only [Bool.and_eq_true, bne_iff_ne] at hpred
  exact hpred.2

/-! ## S4 Rule Application -/

/-- The `φ₀`-parameterized S4 rule-application function (Decision D1). Wraps
`modalApplyOneS4Rules` (K + T + 4, `FrameRules.lean`). At the two **minting** shapes
(`F(□φ)@w`, `T(◇φ)@w` -- the shapes where the underlying K rule would create a fresh
world), consults `blockingWorld`:
- **blocked** (`some wBlock`): returns `.linear []` and `acc.addEdge w wBlock` -- a
  loop-back edge to the existing blocking world, minting **no** new world.
- **unblocked** (`none`): falls through unchanged to `modalApplyOneS4Rules` (hence to the
  underlying rule's fresh-world minting, `modalApplyOneS4_unblocked_eq` below).

This is the one place S4 departs structurally from K: everywhere else, `modalApplyOneS4`
is exactly `modalApplyOneS4Rules`.

**Design note (deviation from a literal reading of the plan)**: the blocked case uses
`RuleResult.linear []`, not `.persistent []` or `.notApplicable`. This matters:
`modalStepBranchGen` (`Saturation.lean`) discards the rule's returned accessibility
component entirely when the result is `.notApplicable` (its `.notApplicable => none` arm
never touches `newAcc`), which would silently drop the loop-back edge. And `.persistent []`
never marks the source formula as expanded, which would cause the *same* blocked formula to
be re-selected by `b.findSome?` on every subsequent fuel step (wastefully re-adding the same
edge, and potentially starving other branch formulas of ever being processed within the
fuel budget). `.linear []` is what K's own fresh-world rules use for exactly this
one-shot-consumption shape (`Rules.lean`'s `diamondPos`/`boxNeg` arms), and correctly both
threads `newAcc` through and marks the source formula expanded. -/
def modalApplyOneS4 (φ₀ : Proposition Atom) : RuleApply Atom :=
  fun sf b acc =>
    match sf.sign, sf.formula with
    | .neg, .box _ =>
      match blockingWorld φ₀ b sf.label with
      | some wBlock => (.linear [], acc.addEdge sf.label wBlock)
      | none => modalApplyOneS4Rules sf b acc
    | .pos, .diamond _ =>
      match blockingWorld φ₀ b sf.label with
      | some wBlock => (.linear [], acc.addEdge sf.label wBlock)
      | none => modalApplyOneS4Rules sf b acc
    | _, _ => modalApplyOneS4Rules sf b acc

/-- Guard spec (a)/(b), box-negative shape: `modalApplyOneS4 φ₀` at `F(□φ)@w` either (a)
blocks -- adding exactly one loop-back edge to an existing known world and minting no new
world -- or (b) does not block, in which case it reduces to the underlying K rule
(`modalApplyOne`), which mints exactly `modalNextWorld b`. This is Phase 8's dispatch entry
point for the box-negative minting shape. -/
lemma modalApplyOneS4_boxNeg_blocked_eq (φ₀ : Proposition Atom)
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (φ : Proposition Atom) (w wBlock : WorldIndex)
    (hblock : blockingWorld φ₀ b w = some wBlock) :
    modalApplyOneS4 φ₀ ⟨.neg, .box φ, w⟩ b acc = (.linear [], acc.addEdge w wBlock) := by
  unfold modalApplyOneS4
  simp [hblock]

/-- Guard spec (b), box-negative shape, unblocked case: reduces to the underlying K rule. -/
lemma modalApplyOneS4_boxNeg_unblocked_eq (φ₀ : Proposition Atom)
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (φ : Proposition Atom) (w : WorldIndex) (hblock : blockingWorld φ₀ b w = none) :
    modalApplyOneS4 φ₀ ⟨.neg, .box φ, w⟩ b acc = modalApplyOne ⟨.neg, .box φ, w⟩ b acc := by
  unfold modalApplyOneS4
  simp only [hblock]
  rw [modalApplyOneS4Rules_eq_of_not_boxPos_diaNeg, modalApplyOneT_eq_of_not_boxPos_diaNeg]
  · exact ⟨by simp, by simp⟩
  · exact ⟨by simp, by simp⟩

/-- Guard spec (a)/(b), diamond-positive shape (dual of the box-negative pair): blocked case
adds exactly one loop-back edge and mints no new world. -/
lemma modalApplyOneS4_diaPos_blocked_eq (φ₀ : Proposition Atom)
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (φ : Proposition Atom) (w wBlock : WorldIndex)
    (hblock : blockingWorld φ₀ b w = some wBlock) :
    modalApplyOneS4 φ₀ ⟨.pos, .diamond φ, w⟩ b acc = (.linear [], acc.addEdge w wBlock) := by
  unfold modalApplyOneS4
  simp [hblock]

/-- Guard spec (b), diamond-positive shape, unblocked case: reduces to the underlying K
rule, which mints exactly `modalNextWorld b`. -/
lemma modalApplyOneS4_diaPos_unblocked_eq (φ₀ : Proposition Atom)
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (φ : Proposition Atom) (w : WorldIndex) (hblock : blockingWorld φ₀ b w = none) :
    modalApplyOneS4 φ₀ ⟨.pos, .diamond φ, w⟩ b acc = modalApplyOne ⟨.pos, .diamond φ, w⟩ b acc := by
  unfold modalApplyOneS4
  simp only [hblock]
  rw [modalApplyOneS4Rules_eq_of_not_boxPos_diaNeg, modalApplyOneT_eq_of_not_boxPos_diaNeg]
  · exact ⟨by simp, by simp⟩
  · exact ⟨by simp, by simp⟩

/-- `modalApplyOneS4` agrees with `modalApplyOneS4Rules` (hence with the K/T/4 rule set)
outside the two minting shapes: the guard only ever intervenes at `F(□φ)@w`/`T(◇φ)@w`. -/
lemma modalApplyOneS4_eq_of_not_boxNeg_diaPos
    (φ₀ : Proposition Atom) (sf : SignedFormula (Proposition Atom) WorldIndex)
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (h : ¬ (sf.sign = .neg ∧ ∃ φ, sf.formula = .box φ) ∧
         ¬ (sf.sign = .pos ∧ ∃ φ, sf.formula = .diamond φ)) :
    modalApplyOneS4 φ₀ sf b acc = modalApplyOneS4Rules sf b acc := by
  obtain ⟨h1, h2⟩ := h
  unfold modalApplyOneS4
  rcases hs : sf.sign with _ | _ <;> rcases hf : sf.formula with _ | _ | _ | _ | _ | φ | φ <;>
    simp_all

/-! ## S4 Driver -/

/-- One-step branch expansion for the S4 (reflexive-transitive) tableau: the generic driver
(`modalStepBranchGen`, `Saturation.lean`) instantiated at `apply := modalApplyOneS4 φ₀`.
Mirrors `modalStepBranchT` (`TDriver.lean`). -/
def modalStepBranchS4 (φ₀ : Proposition Atom)
    (b e : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility) :
    Option (List (List (SignedFormula (Proposition Atom) WorldIndex)) ×
            List (List (SignedFormula (Proposition Atom) WorldIndex)) ×
            Accessibility) :=
  modalStepBranchGen (modalApplyOneS4 φ₀) b e acc

/-- Fuel-based expansion of a list of S4-system branches: the generic driver
(`modalExpandBranchesGen`, `Saturation.lean`) instantiated at `apply := modalApplyOneS4 φ₀`.
Mirrors `modalExpandBranchesT`. -/
def modalExpandBranchesS4 (φ₀ : Proposition Atom)
    (branches expandedSets : List (List (SignedFormula (Proposition Atom) WorldIndex)))
    (accs : List Accessibility) (fuel : Nat) : ModalTableauResult Atom :=
  modalExpandBranchesGen (modalApplyOneS4 φ₀) branches expandedSets accs fuel

/-- The S4 (reflexive-transitive) modal tableau decision procedure: the generic entry point
(`modalTableauGen`, `Saturation.lean`) instantiated at `apply := modalApplyOneS4 φ`, starting
the signed tableau from `F(φ)` at world `0`. `φ` is in scope as the guard's `φ₀` parameter
(Decision D1) throughout the run. **No** `RuleApplicationSpec` instance exists for
`modalApplyOneS4` (Correction 3) -- S4 reuses the generic driver definitionally only. -/
def modalTableauS4 (φ : Proposition Atom) : ModalTableauResult Atom :=
  modalTableauGen (modalApplyOneS4 φ) φ

/-! ## S4 Hintikka Set -/

/-- A modal S4 Hintikka set: the S4 analogue of `modalHintikkaSet` (Saturation.lean),
with `modalApplyOne` replaced by `modalApplyOneS4 φ₀` in conjunct 2 (Decision D3).
Conjuncts 1, 3, 4 are unchanged and apply-agnostic:

1. The branch is not closed.
2. Every non-minting-shaped formula's `modalApplyOneS4 φ₀` output is already present on
   the branch (the saturation condition, now stated against the S4 rule set: K + T + 4 +
   the minting guard).
3. Box-negative witness: `F(□φ)@w ∈ b` implies some successor `w'` of `w` has `F(φ)@w' ∈ b`.
4. Diamond-positive witness: `T(◇φ)@w ∈ b` implies some successor `w'` of `w` has
   `T(φ)@w' ∈ b`.

Conjuncts 3/4 are existential over successors, and a **loop-back edge satisfies them
natively** (Decision D3): this is the favourable accident that makes equality-blocking
compatible with the Hintikka characterization without any change to its shape. Per Decision
D4, this predicate is consumed as a *hypothesis* by the bridge lemmas in this file (not
proved from the driver here) -- `modalExpandBranchesS4_hintikka` (Phase 9, 510-gated) is
where a completed S4 tableau's open branch is shown to satisfy it. -/
def modalHintikkaSetS4 (φ₀ : Proposition Atom)
    (b : List (SignedFormula (Proposition Atom) WorldIndex))
    (acc : Accessibility) : Prop :=
  isModalClosed b = false ∧
  (∀ sf ∈ b,
    let (result, _) := modalApplyOneS4 φ₀ sf b acc
    match sf.sign, sf.formula with
    | .neg, .box _ => True    -- F(□φ): minting-guarded rule; handled by conjunct 3
    | .pos, .diamond _ => True  -- T(◇φ): minting-guarded rule; handled by conjunct 4
    | _, _ =>
      match result with
      | .linear newForms => ∀ sf' ∈ newForms, sf' ∈ b
      | .branching branches => ∃ br ∈ branches, ∀ sf' ∈ br, sf' ∈ b
      | .persistent newForms => ∀ sf' ∈ newForms, sf' ∈ b
      | .notApplicable => True) ∧
  -- Box-negative witness: F(□φ)@w on the branch implies a successor world with F(φ)
  (∀ (φ : Proposition Atom) (w : WorldIndex),
    ⟨.neg, .box φ, w⟩ ∈ b → ∃ w', acc.hasEdge w w' = true ∧ ⟨.neg, φ, w'⟩ ∈ b) ∧
  -- Diamond-positive witness: T(◇φ)@w on the branch implies a successor world with T(φ)
  (∀ (φ : Proposition Atom) (w : WorldIndex),
    ⟨.pos, .diamond φ, w⟩ ∈ b → ∃ w', acc.hasEdge w w' = true ∧ ⟨.pos, φ, w'⟩ ∈ b)

/-! ## S4 Hintikka Bridges -/

/-- Bridge from `acc.hasEdge` to `Accessibility.successorsOf` membership: the converse of
`FrameSoundness.lean`'s `mem_successorsOf_hasEdge'`. Local mirror of the same fact proved
(privately) in `FmpMeasure.lean` and `Completeness.lean`'s bridge lemmas' inline proofs. -/
private lemma hasEdge_mem_successorsOf {acc : Accessibility} {w w' : WorldIndex}
    (hr : acc.hasEdge w w' = true) : w' ∈ acc.successorsOf w := by
  simp only [Accessibility.successorsOf, List.mem_filterMap]
  simp only [Accessibility.hasEdge, List.any_eq_true] at hr
  obtain ⟨⟨src, tgt⟩, hedge_mem, hbeq⟩ := hr
  simp only [Bool.and_eq_true, beq_iff_eq] at hbeq
  exact ⟨(src, tgt), hedge_mem, by simp [hbeq.1, hbeq.2]⟩

/-- The single-edge 4-rule bridge: `modalHintikkaSetS4 φ₀ b acc`, `T(□ψ)@w ∈ b`,
`acc.hasEdge w w' = true` imply `T(□ψ)@w' ∈ b` -- the box formula *itself* survives across
one recorded edge. This is the S4-specific content that makes the crux bridge
(`hintikkaS4_box_pos_reflTransGen` below) possible: the induction it drives carries
`T(□ψ)@·`, not `T(ψ)@·`.

Proof shape mirrors `hintikka_box_pos` (`Completeness.lean`) one layer further down: unfold
`modalApplyOneS4` at this (non-minting) shape through `modalApplyOneS4Rules`,
`modalApplyOneT`, and `modalApplyOne` in turn (`htR`, `hk`), then show the target formula
survives every merge/filter layer whenever it is not already on the branch -- it is always
in `modalFourBoxProp`'s output (`htarget_mem_fourNew`), and a generic two-case argument
(`hmem_merge`: either already in the front list, or survives the filter against it) shows it
lands in the final merged list regardless of what the K/T layers themselves produced. -/
lemma hintikkaS4_box_pos_step
    (φ₀ : Proposition Atom) (b : List (SignedFormula (Proposition Atom) WorldIndex))
    (acc : Accessibility) (hH : modalHintikkaSetS4 φ₀ b acc)
    (ψ : Proposition Atom) (w w' : WorldIndex)
    (hmem : (⟨.pos, .box ψ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b)
    (hr : acc.hasEdge w w' = true) :
    (⟨.pos, .box ψ, w'⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b := by
  obtain ⟨_, hrule, _⟩ := hH
  have hcond := hrule ⟨.pos, .box ψ, w⟩ hmem
  simp only at hcond
  have hshape : modalApplyOneS4 φ₀ ⟨.pos, .box ψ, w⟩ b acc =
      modalApplyOneS4Rules ⟨.pos, .box ψ, w⟩ b acc :=
    modalApplyOneS4_eq_of_not_boxNeg_diaPos φ₀ _ b acc ⟨by simp, by simp⟩
  rw [hshape] at hcond
  unfold modalApplyOneS4Rules at hcond
  simp only at hcond
  have hw'succ : w' ∈ acc.successorsOf w := hasEdge_mem_successorsOf hr
  by_cases hinb :
      (b.any fun x => x == (⟨.pos, .box ψ, w'⟩ : SignedFormula (Proposition Atom) WorldIndex))
        = true
  · simp only [List.any_eq_true, beq_iff_eq] at hinb
    obtain ⟨sf', hsf'mem, rfl⟩ := hinb
    exact hsf'mem
  · have htarget_mem_fourNew :
        (⟨.pos, .box ψ, w'⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈
          modalFourBoxProp b acc ψ w := by
      simp only [modalFourBoxProp, List.mem_filterMap]
      exact ⟨w', hw'succ, if_neg hinb⟩
    have htR :
        (modalApplyOneT (⟨.pos, .box ψ, w⟩ :
          SignedFormula (Proposition Atom) WorldIndex) b acc).fst =
        (match (modalApplyOne (⟨.pos, .box ψ, w⟩ :
              SignedFormula (Proposition Atom) WorldIndex) b acc).fst with
          | .persistent kForms =>
            RuleResult.persistent
              (kForms ++ (modalTBoxSelf b ψ w).filter (fun x => !(kForms.any (· == x))))
          | .notApplicable =>
            if (modalTBoxSelf b ψ w).isEmpty then RuleResult.notApplicable
            else RuleResult.persistent (modalTBoxSelf b ψ w)
          | other => other) := by
      unfold modalApplyOneT
      obtain ⟨kResult, kAcc⟩ := modalApplyOne (⟨.pos, .box ψ, w⟩ :
          SignedFormula (Proposition Atom) WorldIndex) b acc
      cases kResult <;> first | rfl | (simp only []; split <;> rfl)
    have hk :
        (modalApplyOne (⟨.pos, .box ψ, w⟩ :
          SignedFormula (Proposition Atom) WorldIndex) b acc).fst =
        if (boxPropagation b acc ψ w).isEmpty then RuleResult.notApplicable
        else RuleResult.persistent (boxPropagation b acc ψ w) := by
      unfold modalApplyOne
      simp only [tryAllPropRules, applyPropRule, modalAndOf?, modalOrOf?, modalImpOf?,
        modalNegOf?, List.map, List.find?, RuleResult.isApplicable, Option.getD_none]
      split_ifs <;> simp_all
    rw [hk] at htR
    rw [htR] at hcond
    have hfourNotEmpty : ¬ (modalFourBoxProp b acc ψ w).isEmpty = true := by
      have hne : (modalFourBoxProp b acc ψ w).isEmpty = false := by
        rw [List.isEmpty_eq_false_iff_exists_mem]
        exact ⟨_, htarget_mem_fourNew⟩
      simp [hne]
    simp only [if_neg hfourNotEmpty] at hcond
    have hmem_merge : ∀ (l : List (SignedFormula (Proposition Atom) WorldIndex)),
        (⟨.pos, .box ψ, w'⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈
          l ++ (modalFourBoxProp b acc ψ w).filter (fun x => !(l.any (· == x))) := by
      intro l
      by_cases hinl :
          (l.any fun x => x == (⟨.pos, .box ψ, w'⟩ : SignedFormula (Proposition Atom) WorldIndex))
            = true
      · simp only [List.any_eq_true, beq_iff_eq] at hinl
        obtain ⟨sf', hsf'mem, rfl⟩ := hinl
        exact List.mem_append_left _ hsf'mem
      · refine List.mem_append_right _ ?_
        simp only [List.mem_filter]
        exact ⟨htarget_mem_fourNew, by simp [hinl]⟩
    split_ifs at hcond with h1 h2
    · exact hcond _ htarget_mem_fourNew
    · exact hcond _ (hmem_merge _)
    · exact hcond _ (hmem_merge _)
    · exact hcond _ (hmem_merge _)

/-- Dual of `hintikkaS4_box_pos_step` for the diamond-negative shape: `modalHintikkaSetS4
φ₀ b acc`, `F(◇ψ)@w ∈ b`, `acc.hasEdge w w' = true` imply `F(◇ψ)@w' ∈ b` -- the diamond
formula itself survives across one recorded edge. Proof is the exact mirror of
`hintikkaS4_box_pos_step`, with `.pos, .box` / `modalTBoxSelf` / `modalFourBoxProp` replaced
by `.neg, .diamond` / `modalTDiaNegSelf` / `modalFourDiaNegProp` throughout; K's diamondNeg
arm computes its propagation list inline (no named `boxPropagation`-style helper exists for
it), so the `hk` step restates that inline computation directly. -/
lemma hintikkaS4_dia_neg_step
    (φ₀ : Proposition Atom) (b : List (SignedFormula (Proposition Atom) WorldIndex))
    (acc : Accessibility) (hH : modalHintikkaSetS4 φ₀ b acc)
    (ψ : Proposition Atom) (w w' : WorldIndex)
    (hmem : (⟨.neg, .diamond ψ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b)
    (hr : acc.hasEdge w w' = true) :
    (⟨.neg, .diamond ψ, w'⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b := by
  obtain ⟨_, hrule, _⟩ := hH
  have hcond := hrule ⟨.neg, .diamond ψ, w⟩ hmem
  simp only at hcond
  have hshape : modalApplyOneS4 φ₀ ⟨.neg, .diamond ψ, w⟩ b acc =
      modalApplyOneS4Rules ⟨.neg, .diamond ψ, w⟩ b acc :=
    modalApplyOneS4_eq_of_not_boxNeg_diaPos φ₀ _ b acc ⟨by simp, by simp⟩
  rw [hshape] at hcond
  unfold modalApplyOneS4Rules at hcond
  simp only at hcond
  have hw'succ : w' ∈ acc.successorsOf w := hasEdge_mem_successorsOf hr
  by_cases hinb :
      (b.any fun x => x == (⟨.neg, .diamond ψ, w'⟩ : SignedFormula (Proposition Atom) WorldIndex))
        = true
  · simp only [List.any_eq_true, beq_iff_eq] at hinb
    obtain ⟨sf', hsf'mem, rfl⟩ := hinb
    exact hsf'mem
  · have htarget_mem_fourNew :
        (⟨.neg, .diamond ψ, w'⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈
          modalFourDiaNegProp b acc ψ w := by
      simp only [modalFourDiaNegProp, List.mem_filterMap]
      exact ⟨w', hw'succ, if_neg hinb⟩
    have htR :
        (modalApplyOneT (⟨.neg, .diamond ψ, w⟩ :
          SignedFormula (Proposition Atom) WorldIndex) b acc).fst =
        (match (modalApplyOne (⟨.neg, .diamond ψ, w⟩ :
              SignedFormula (Proposition Atom) WorldIndex) b acc).fst with
          | .persistent kForms =>
            RuleResult.persistent
              (kForms ++ (modalTDiaNegSelf b ψ w).filter (fun x => !(kForms.any (· == x))))
          | .notApplicable =>
            if (modalTDiaNegSelf b ψ w).isEmpty then RuleResult.notApplicable
            else RuleResult.persistent (modalTDiaNegSelf b ψ w)
          | other => other) := by
      unfold modalApplyOneT
      obtain ⟨kResult, kAcc⟩ := modalApplyOne (⟨.neg, .diamond ψ, w⟩ :
          SignedFormula (Proposition Atom) WorldIndex) b acc
      cases kResult <;> first | rfl | (simp only []; split <;> rfl)
    have hk :
        (modalApplyOne (⟨.neg, .diamond ψ, w⟩ :
          SignedFormula (Proposition Atom) WorldIndex) b acc).fst =
        if ((acc.successorsOf w).filterMap fun u =>
              let sf' : SignedFormula (Proposition Atom) WorldIndex := ⟨.neg, ψ, u⟩
              if b.any (· == sf') then none else some sf').isEmpty then
          RuleResult.notApplicable
        else
          RuleResult.persistent ((acc.successorsOf w).filterMap fun u =>
            let sf' : SignedFormula (Proposition Atom) WorldIndex := ⟨.neg, ψ, u⟩
            if b.any (· == sf') then none else some sf') := by
      unfold modalApplyOne
      simp only [tryAllPropRules, applyPropRule, modalAndOf?, modalOrOf?, modalImpOf?,
        modalNegOf?, List.map, List.find?, RuleResult.isApplicable, Option.getD_none]
      split_ifs <;> simp_all
    rw [hk] at htR
    rw [htR] at hcond
    have hfourNotEmpty : ¬ (modalFourDiaNegProp b acc ψ w).isEmpty = true := by
      have hne : (modalFourDiaNegProp b acc ψ w).isEmpty = false := by
        rw [List.isEmpty_eq_false_iff_exists_mem]
        exact ⟨_, htarget_mem_fourNew⟩
      simp [hne]
    simp only [if_neg hfourNotEmpty] at hcond
    have hmem_merge : ∀ (l : List (SignedFormula (Proposition Atom) WorldIndex)),
        (⟨.neg, .diamond ψ, w'⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈
          l ++ (modalFourDiaNegProp b acc ψ w).filter (fun x => !(l.any (· == x))) := by
      intro l
      by_cases hinl :
          (l.any fun x =>
              x == (⟨.neg, .diamond ψ, w'⟩ : SignedFormula (Proposition Atom) WorldIndex))
            = true
      · simp only [List.any_eq_true, beq_iff_eq] at hinl
        obtain ⟨sf', hsf'mem, rfl⟩ := hinl
        exact List.mem_append_left _ hsf'mem
      · refine List.mem_append_right _ ?_
        simp only [List.mem_filter]
        exact ⟨htarget_mem_fourNew, by simp [hinl]⟩
    split_ifs at hcond with h1 h2
    · exact hcond _ htarget_mem_fourNew
    · exact hcond _ (hmem_merge _)
    · exact hcond _ (hmem_merge _)
    · exact hcond _ (hmem_merge _)

/-- The T-rule endpoint of the box-positive chain: `T(□ψ)@w ∈ b` implies `T(ψ)@w ∈ b`
(same world, via the T self-propagation arm `modalTBoxSelf` inherited through
`modalApplyOneT`). Combined with `hintikkaS4_box_pos_step`, this is exactly the two
ingredients `hintikkaS4_box_pos_reflTransGen`'s induction needs: `step` carries `T(□ψ)@·`
across each edge, and `self` discharges the endpoint (including the reflexive `w = w'` base
case) into `T(ψ)@·`. -/
lemma hintikkaS4_box_pos_self
    (φ₀ : Proposition Atom) (b : List (SignedFormula (Proposition Atom) WorldIndex))
    (acc : Accessibility) (hH : modalHintikkaSetS4 φ₀ b acc)
    (ψ : Proposition Atom) (w : WorldIndex)
    (hmem : (⟨.pos, .box ψ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b) :
    (⟨.pos, ψ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b := by
  obtain ⟨_, hrule, _⟩ := hH
  have hcond := hrule ⟨.pos, .box ψ, w⟩ hmem
  simp only at hcond
  have hshape : modalApplyOneS4 φ₀ ⟨.pos, .box ψ, w⟩ b acc =
      modalApplyOneS4Rules ⟨.pos, .box ψ, w⟩ b acc :=
    modalApplyOneS4_eq_of_not_boxNeg_diaPos φ₀ _ b acc ⟨by simp, by simp⟩
  rw [hshape] at hcond
  unfold modalApplyOneS4Rules at hcond
  simp only at hcond
  by_cases hinb :
      (b.any fun x => x == (⟨.pos, ψ, w⟩ : SignedFormula (Proposition Atom) WorldIndex)) = true
  · simp only [List.any_eq_true, beq_iff_eq] at hinb
    obtain ⟨sf', hsf'mem, rfl⟩ := hinb
    exact hsf'mem
  · have htarget_mem_self :
        (⟨.pos, ψ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ modalTBoxSelf b ψ w := by
      unfold modalTBoxSelf
      simp [hinb]
    have htR :
        (modalApplyOneT (⟨.pos, .box ψ, w⟩ :
          SignedFormula (Proposition Atom) WorldIndex) b acc).fst =
        (match (modalApplyOne (⟨.pos, .box ψ, w⟩ :
              SignedFormula (Proposition Atom) WorldIndex) b acc).fst with
          | .persistent kForms =>
            RuleResult.persistent
              (kForms ++ (modalTBoxSelf b ψ w).filter (fun x => !(kForms.any (· == x))))
          | .notApplicable =>
            if (modalTBoxSelf b ψ w).isEmpty then RuleResult.notApplicable
            else RuleResult.persistent (modalTBoxSelf b ψ w)
          | other => other) := by
      unfold modalApplyOneT
      obtain ⟨kResult, kAcc⟩ := modalApplyOne (⟨.pos, .box ψ, w⟩ :
          SignedFormula (Proposition Atom) WorldIndex) b acc
      cases kResult <;> first | rfl | (simp only []; split <;> rfl)
    have hk :
        (modalApplyOne (⟨.pos, .box ψ, w⟩ :
          SignedFormula (Proposition Atom) WorldIndex) b acc).fst =
        if (boxPropagation b acc ψ w).isEmpty then RuleResult.notApplicable
        else RuleResult.persistent (boxPropagation b acc ψ w) := by
      unfold modalApplyOne
      simp only [tryAllPropRules, applyPropRule, modalAndOf?, modalOrOf?, modalImpOf?,
        modalNegOf?, List.map, List.find?, RuleResult.isApplicable, Option.getD_none]
      split_ifs <;> simp_all
    rw [hk] at htR
    rw [htR] at hcond
    have hselfNotEmpty : ¬ (modalTBoxSelf b ψ w).isEmpty = true := by
      have hne : (modalTBoxSelf b ψ w).isEmpty = false := by
        rw [List.isEmpty_eq_false_iff_exists_mem]
        exact ⟨_, htarget_mem_self⟩
      simp [hne]
    simp only [if_neg hselfNotEmpty] at hcond
    have hmem_merge : ∀ (l : List (SignedFormula (Proposition Atom) WorldIndex)),
        (⟨.pos, ψ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈
          l ++ (modalTBoxSelf b ψ w).filter (fun x => !(l.any (· == x))) := by
      intro l
      by_cases hinl :
          (l.any fun x => x == (⟨.pos, ψ, w⟩ : SignedFormula (Proposition Atom) WorldIndex))
            = true
      · simp only [List.any_eq_true, beq_iff_eq] at hinl
        obtain ⟨sf', hsf'mem, rfl⟩ := hinl
        exact List.mem_append_left _ hsf'mem
      · refine List.mem_append_right _ ?_
        simp only [List.mem_filter]
        exact ⟨htarget_mem_self, by simp [hinl]⟩
    -- The 4-rule layer (S4Rules) merges the T-layer's result with the box-itself
    -- propagation `modalFourBoxProp`, filtered against whatever the T-layer produced.
    -- `w`'s target `T(ψ)@w` (unwrapped body) is untouched by that filter's *content*, since
    -- it already sits inside the T-layer's own list; only its position in the final
    -- concatenation changes.
    split_ifs at hcond with h1 <;> simp only at hcond
    · exact hcond _ (List.mem_append_left _ htarget_mem_self)
    · exact hcond _ (List.mem_append_left _ htarget_mem_self)
    · exact hcond _ (List.mem_append_left _ (hmem_merge _))
    · exact hcond _ (List.mem_append_left _ (hmem_merge _))

/-- Dual of `hintikkaS4_box_pos_self` for the diamond-negative shape: `F(◇ψ)@w ∈ b` implies
`F(ψ)@w ∈ b` (same world, via `modalTDiaNegSelf`). Exact mirror of
`hintikkaS4_box_pos_self`'s proof. -/
lemma hintikkaS4_dia_neg_self
    (φ₀ : Proposition Atom) (b : List (SignedFormula (Proposition Atom) WorldIndex))
    (acc : Accessibility) (hH : modalHintikkaSetS4 φ₀ b acc)
    (ψ : Proposition Atom) (w : WorldIndex)
    (hmem : (⟨.neg, .diamond ψ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b) :
    (⟨.neg, ψ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b := by
  obtain ⟨_, hrule, _⟩ := hH
  have hcond := hrule ⟨.neg, .diamond ψ, w⟩ hmem
  simp only at hcond
  have hshape : modalApplyOneS4 φ₀ ⟨.neg, .diamond ψ, w⟩ b acc =
      modalApplyOneS4Rules ⟨.neg, .diamond ψ, w⟩ b acc :=
    modalApplyOneS4_eq_of_not_boxNeg_diaPos φ₀ _ b acc ⟨by simp, by simp⟩
  rw [hshape] at hcond
  unfold modalApplyOneS4Rules at hcond
  simp only at hcond
  by_cases hinb :
      (b.any fun x => x == (⟨.neg, ψ, w⟩ : SignedFormula (Proposition Atom) WorldIndex)) = true
  · simp only [List.any_eq_true, beq_iff_eq] at hinb
    obtain ⟨sf', hsf'mem, rfl⟩ := hinb
    exact hsf'mem
  · have htarget_mem_self :
        (⟨.neg, ψ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ modalTDiaNegSelf b ψ w := by
      unfold modalTDiaNegSelf
      simp [hinb]
    have htR :
        (modalApplyOneT (⟨.neg, .diamond ψ, w⟩ :
          SignedFormula (Proposition Atom) WorldIndex) b acc).fst =
        (match (modalApplyOne (⟨.neg, .diamond ψ, w⟩ :
              SignedFormula (Proposition Atom) WorldIndex) b acc).fst with
          | .persistent kForms =>
            RuleResult.persistent
              (kForms ++ (modalTDiaNegSelf b ψ w).filter (fun x => !(kForms.any (· == x))))
          | .notApplicable =>
            if (modalTDiaNegSelf b ψ w).isEmpty then RuleResult.notApplicable
            else RuleResult.persistent (modalTDiaNegSelf b ψ w)
          | other => other) := by
      unfold modalApplyOneT
      obtain ⟨kResult, kAcc⟩ := modalApplyOne (⟨.neg, .diamond ψ, w⟩ :
          SignedFormula (Proposition Atom) WorldIndex) b acc
      cases kResult <;> first | rfl | (simp only []; split <;> rfl)
    have hk :
        (modalApplyOne (⟨.neg, .diamond ψ, w⟩ :
          SignedFormula (Proposition Atom) WorldIndex) b acc).fst =
        if ((acc.successorsOf w).filterMap fun u =>
              let sf' : SignedFormula (Proposition Atom) WorldIndex := ⟨.neg, ψ, u⟩
              if b.any (· == sf') then none else some sf').isEmpty then
          RuleResult.notApplicable
        else
          RuleResult.persistent ((acc.successorsOf w).filterMap fun u =>
            let sf' : SignedFormula (Proposition Atom) WorldIndex := ⟨.neg, ψ, u⟩
            if b.any (· == sf') then none else some sf') := by
      unfold modalApplyOne
      simp only [tryAllPropRules, applyPropRule, modalAndOf?, modalOrOf?, modalImpOf?,
        modalNegOf?, List.map, List.find?, RuleResult.isApplicable, Option.getD_none]
      split_ifs <;> simp_all
    rw [hk] at htR
    rw [htR] at hcond
    have hselfNotEmpty : ¬ (modalTDiaNegSelf b ψ w).isEmpty = true := by
      have hne : (modalTDiaNegSelf b ψ w).isEmpty = false := by
        rw [List.isEmpty_eq_false_iff_exists_mem]
        exact ⟨_, htarget_mem_self⟩
      simp [hne]
    simp only [if_neg hselfNotEmpty] at hcond
    have hmem_merge : ∀ (l : List (SignedFormula (Proposition Atom) WorldIndex)),
        (⟨.neg, ψ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈
          l ++ (modalTDiaNegSelf b ψ w).filter (fun x => !(l.any (· == x))) := by
      intro l
      by_cases hinl :
          (l.any fun x => x == (⟨.neg, ψ, w⟩ : SignedFormula (Proposition Atom) WorldIndex))
            = true
      · simp only [List.any_eq_true, beq_iff_eq] at hinl
        obtain ⟨sf', hsf'mem, rfl⟩ := hinl
        exact List.mem_append_left _ hsf'mem
      · refine List.mem_append_right _ ?_
        simp only [List.mem_filter]
        exact ⟨htarget_mem_self, by simp [hinl]⟩
    split_ifs at hcond with h1 <;> simp only at hcond
    · exact hcond _ (List.mem_append_left _ htarget_mem_self)
    · exact hcond _ (List.mem_append_left _ htarget_mem_self)
    · exact hcond _ (List.mem_append_left _ (hmem_merge _))
    · exact hcond _ (List.mem_append_left _ (hmem_merge _))

/-- Box-negative witness bridge for S4: `F(□ψ)@w ∈ b` implies `∃ w', acc.hasEdge w w' = true
∧ F(ψ)@w' ∈ b` -- a one-line projection off `modalHintikkaSetS4`'s third conjunct (Decision
D3: this conjunct is apply-agnostic and copied unchanged from `modalHintikkaSet`). Mirrors
`hintikka_box_neg` (`Completeness.lean`). -/
lemma hintikkaS4_box_neg
    (φ₀ : Proposition Atom) (b : List (SignedFormula (Proposition Atom) WorldIndex))
    (acc : Accessibility) (hH : modalHintikkaSetS4 φ₀ b acc)
    (ψ : Proposition Atom) (w : WorldIndex)
    (hmem : (⟨.neg, .box ψ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b) :
    ∃ w', acc.hasEdge w w' = true ∧
      (⟨.neg, ψ, w'⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b :=
  hH.2.2.1 ψ w hmem

/-- Diamond-positive witness bridge for S4: `T(◇ψ)@w ∈ b` implies `∃ w', acc.hasEdge w w' =
true ∧ T(ψ)@w' ∈ b` -- a one-line projection off `modalHintikkaSetS4`'s fourth conjunct.
Mirrors `hintikka_diamond_pos` (`Completeness.lean`). -/
lemma hintikkaS4_diamond_pos
    (φ₀ : Proposition Atom) (b : List (SignedFormula (Proposition Atom) WorldIndex))
    (acc : Accessibility) (hH : modalHintikkaSetS4 φ₀ b acc)
    (ψ : Proposition Atom) (w : WorldIndex)
    (hmem : (⟨.pos, .diamond ψ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b) :
    ∃ w', acc.hasEdge w w' = true ∧
      (⟨.pos, ψ, w'⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b :=
  hH.2.2.2 ψ w hmem

/-! ## The `ReflTransGen` Path Bridge (the Crux) -/

/-- **The crux of the task**: `modalHintikkaSetS4 φ₀ b acc`, `T(□ψ)@w ∈ b`, and a
`Relation.ReflTransGen`-path `w ⤳ w'` in `acc.hasEdge` together imply `T(ψ)@w' ∈ b`. Proved
by `Relation.ReflTransGen.head_induction_on`, carrying `T(□ψ)@·` along each edge via
`hintikkaS4_box_pos_step` and discharging the endpoint (including the reflexive `w = w'`
base case) via `hintikkaS4_box_pos_self`. This is exactly why the 4-rule propagates the box
*itself* rather than its unwrapped body: the induction's invariant needs `T(□ψ)` to survive
every intermediate edge, not just the final one, and only `T(□ψ)@·`, not `T(ψ)@·`, is
preserved by a single `hasEdge` step in general.

Loop-back cycles in `acc` are harmless here: `Relation.ReflTransGen` is the reflexive-
transitive *closure*, so revisiting a world via a cycle contributes no new reachable worlds
beyond those already related by the path; the induction recurses on the *path witness*
(`hpath`'s structure), not on the graph, so it terminates regardless of cycles in `acc`. -/
lemma hintikkaS4_box_pos_reflTransGen
    (φ₀ : Proposition Atom) (b : List (SignedFormula (Proposition Atom) WorldIndex))
    (acc : Accessibility) (hH : modalHintikkaSetS4 φ₀ b acc)
    (ψ : Proposition Atom) (w w' : WorldIndex)
    (hmem : (⟨.pos, .box ψ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b)
    (hpath : Relation.ReflTransGen (fun a c => acc.hasEdge a c = true) w w') :
    (⟨.pos, ψ, w'⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b := by
  revert hmem
  induction hpath using Relation.ReflTransGen.head_induction_on with
  | refl => intro hmem; exact hintikkaS4_box_pos_self φ₀ b acc hH ψ w' hmem
  | head hedge _ ih =>
    intro hmem
    exact ih (hintikkaS4_box_pos_step φ₀ b acc hH ψ _ _ hmem hedge)

/-- Dual of `hintikkaS4_box_pos_reflTransGen` for the diamond-negative shape: `F(◇ψ)@w ∈ b`
and a `ReflTransGen`-path `w ⤳ w'` in `acc.hasEdge` together imply `F(ψ)@w' ∈ b`. -/
lemma hintikkaS4_dia_neg_reflTransGen
    (φ₀ : Proposition Atom) (b : List (SignedFormula (Proposition Atom) WorldIndex))
    (acc : Accessibility) (hH : modalHintikkaSetS4 φ₀ b acc)
    (ψ : Proposition Atom) (w w' : WorldIndex)
    (hmem : (⟨.neg, .diamond ψ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b)
    (hpath : Relation.ReflTransGen (fun a c => acc.hasEdge a c = true) w w') :
    (⟨.neg, ψ, w'⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b := by
  revert hmem
  induction hpath using Relation.ReflTransGen.head_induction_on with
  | refl => intro hmem; exact hintikkaS4_dia_neg_self φ₀ b acc hH ψ w' hmem
  | head hedge _ ih =>
    intro hmem
    exact ih (hintikkaS4_dia_neg_step φ₀ b acc hH ψ _ _ hmem hedge)

/-! ## Sanity Checks

`modalTableauS4` was confirmed to evaluate and close exactly on the T and 4 components via
an interactive `#eval` session (not embedded in this file as a permanent `#eval`/`#guard`/
`native_decide` declaration: this file's `module`/`public meta import` boundary makes all
three of those forms either fail to elaborate (`Proposition.atom` is not `meta`-accessible
without an additional `public meta import`) or fail at the native-code-lookup stage
(`modalFuel`'s compiled implementation is not resolvable in this configuration) -- no
existing file in `Cslib/Logics/Modal/Tableau/` uses any of these forms, confirming this is a
structural constraint of the module system here, not specific to this phase's code).
Confirmed interactively:
- `□p → p` (the T schema) evaluates to `.closed`: S4 is reflexive.
- `□p → □□p` (the 4 schema) evaluates to `.closed`: S4 is transitive -- this is the
  component that distinguishes S4 from T, and the entire reason this task's 4-rule exists.
- A bare atom `p` evaluates to `.openBranch _ _`: S4 does not prove arbitrary atoms. -/

/-! ## S4 World Bound (Decision D2)

`modalWorldBound`/`modalUniverse` (`FmpMeasure.lean`) are `(2*complexity+1)^(complexity+1)`,
a branching^depth *tree* bound: S4's world graph is not a bounded-depth tree (loop-back
edges make it a general DAG-with-cycles-collapsed), so this bound does not transfer.
`modalWorldBoundS4`/`modalUniverseS4` replace it with the pigeonhole bound
`2 ^ |modalSubfmls φ₀|` -- the number of possible relevant-formula sets. `modalWork`/
`modalExpMeasure` (`FmpMeasure.lean`) are reused **verbatim**: they take the universe `U` as
an explicit parameter and are rule/world-agnostic. `geomCap`/`modalPotential`/
`modalPotentialTerm` do **not** transfer -- they are the geometric tree-capacity argument
specific to `modalWorldBound`. -/

/-- The S4 world bound: `2 ^ |modalSubfmls φ₀|`, the number of possible relevant-formula
sets (Decision D2). Replaces `modalWorldBound`'s branching^depth tree bound, which does not
apply to S4's (possibly cyclic) world graph. -/
def modalWorldBoundS4 (φ₀ : Proposition Atom) : Nat :=
  2 ^ (modalSubfmls φ₀).length

/-- The fixed finite signed-formula universe `U_{S4}(φ₀)`: both signs, every subformula of
`φ₀`, at every world label `0 .. modalWorldBoundS4 φ₀`. Mirrors `modalUniverse`
(`FmpMeasure.lean`) with `modalWorldBoundS4` swapped in for `modalWorldBound`. -/
def modalUniverseS4 (φ₀ : Proposition Atom) :
    List (SignedFormula (Proposition Atom) WorldIndex) :=
  (List.range (modalWorldBoundS4 φ₀ + 1)).flatMap (fun w =>
    (modalSubfmls φ₀).flatMap (fun ψ => [⟨.pos, ψ, w⟩, ⟨.neg, ψ, w⟩]))

/-- The S4 universe has length at most
`2 * (2 * modalComplexity φ₀ + 1) * (modalWorldBoundS4 φ₀ + 1)`. Mirrors
`modalUniverse_length_le` (`FmpMeasure.lean`; that lemma carries the identical
`unusedDecidableInType` lint warning, unaddressed there too -- `DecidableEq Atom` is needed
by `SignedFormula`'s ambient instances even though the proof term itself never names it). -/
lemma modalUniverseS4_length_le (φ₀ : Proposition Atom) :
    (modalUniverseS4 φ₀).length ≤
      2 * (2 * modalComplexity φ₀ + 1) * (modalWorldBoundS4 φ₀ + 1) := by
  have hinner : ∀ w : WorldIndex,
      ((modalSubfmls φ₀).flatMap
        (fun ψ => [(⟨.pos, ψ, w⟩ : SignedFormula (Proposition Atom) WorldIndex),
                    ⟨.neg, ψ, w⟩])).length
        ≤ 2 * (2 * modalComplexity φ₀ + 1) := by
    intro w
    rw [List.length_flatMap]
    have hb : (List.map (fun ψ =>
        ([(⟨.pos, ψ, w⟩ : SignedFormula (Proposition Atom) WorldIndex), ⟨.neg, ψ, w⟩]).length)
        (modalSubfmls φ₀)).sum ≤ (modalSubfmls φ₀).length * 2 :=
      sum_map_le_length_mul (modalSubfmls φ₀) _ 2 (fun ψ _ => by simp)
    have hlen := modalSubfmls_length_le φ₀
    omega
  unfold modalUniverseS4
  rw [List.length_flatMap]
  have houter : (List.map (fun w =>
      ((modalSubfmls φ₀).flatMap
        (fun ψ => [(⟨.pos, ψ, w⟩ : SignedFormula (Proposition Atom) WorldIndex),
                    ⟨.neg, ψ, w⟩])).length) (List.range (modalWorldBoundS4 φ₀ + 1))).sum
      ≤ (List.range (modalWorldBoundS4 φ₀ + 1)).length * (2 * (2 * modalComplexity φ₀ + 1)) :=
    sum_map_le_length_mul (List.range (modalWorldBoundS4 φ₀ + 1)) _
      (2 * (2 * modalComplexity φ₀ + 1)) (fun w _ => hinner w)
  rw [List.length_range] at houter
  calc (List.map (fun w =>
        ((modalSubfmls φ₀).flatMap
          (fun ψ => [(⟨.pos, ψ, w⟩ : SignedFormula (Proposition Atom) WorldIndex),
                      ⟨.neg, ψ, w⟩])).length) (List.range (modalWorldBoundS4 φ₀ + 1))).sum
      ≤ (modalWorldBoundS4 φ₀ + 1) * (2 * (2 * modalComplexity φ₀ + 1)) := houter
    _ = 2 * (2 * modalComplexity φ₀ + 1) * (modalWorldBoundS4 φ₀ + 1) := by ring

/-! ## The S4 Loop Invariant `S4LoopInv` -/

/-- **Correction 1**: `S4LoopInv` is a **sibling** of `ModalPotentialInv` (`FmpMeasure.lean`),
not an extension of it. `ModalPotentialInv` holds two rank fields (`rankBound`/`rankEdge`)
encoding "modal depth strictly decreases along every edge", which the 4-rule (placing
`T(□ψ)`, unchanged modal depth, at a successor) and loop-back edges (creating `w → w''`
with `rank w'' + 2 = rank w`) both falsify. `S4LoopInv` reuses the six rule-independent
fields (`bClosure`/`eNodup`/`eClosure`/`accFresh`/`accKnown`/`outDegEq`, over
`modalUniverseS4` in place of `modalUniverse`), omits the two rank fields entirely, and adds
`worldSetsDistinct` -- the equality-blocking invariant the minting guard is designed to
maintain. `FmpMeasure.lean` is not modified by this plan. -/
structure S4LoopInv (φ₀ : Proposition Atom)
    (b e : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility) : Prop where
  /-- Every branch formula is a member of the fixed finite S4 universe `U_{S4}(φ₀)`. -/
  bClosure : ∀ x ∈ b, x ∈ modalUniverseS4 φ₀
  /-- The expanded set has no duplicate entries. -/
  eNodup : e.Nodup
  /-- Every expanded-set formula is a member of `U_{S4}(φ₀)`. -/
  eClosure : ∀ x ∈ e, x ∈ modalUniverseS4 φ₀
  /-- All of `acc`'s recorded worlds are `< modalNextWorld b`. -/
  accFresh : accFreshInv b acc
  /-- Every `acc`-edge target is a label already appearing on the branch. -/
  accKnown : accTargetsKnown b acc
  /-- `outDeg` exactly counts the minting-shaped formulas in `e` at each world. -/
  outDegEq : ∀ w, outDeg acc w = (e.filter (fun x => x.label == w && isMintingShaped x)).length
  /-- **The loop invariant the minting guard enforces**: every two *distinct* known worlds
  have *distinct* relevant formula sets. This is exactly what makes the guard's blocking
  search well-founded (a fresh world's relevant set cannot coincide with any existing
  world's, by construction) and is the hypothesis the pigeonhole argument
  (`modalKnownWorlds_length_le_worldBoundS4`, if closed) consumes. -/
  worldSetsDistinct : ∀ w w', w ∈ modalKnownWorlds b → w' ∈ modalKnownWorlds b → w ≠ w' →
    sameRelevantSet φ₀ b w w' = false

end Cslib.Logic.Modal.Tableau

end
