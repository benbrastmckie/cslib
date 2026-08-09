/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Modal.Tableau.Rules

/-! # Frame-Specific Modal Tableau Rules

This module adds the T-system (reflexive-frame) tableau rule on top of the modal K rules
(`Rules.lean`). Per the Strategy-B (closure-at-extraction) design: the T rule does **not**
need any accessibility edge to fire — it propagates `T(□φ)@w ⊢ T(φ)@w` and
`F(◇φ)@w ⊢ F(φ)@w` unconditionally at the *same* world `w`, justified purely by the frame
condition (`Std.Refl`) that will hold of the *extracted* model's relation, not by any edge
recorded in `acc`. This mirrors a self-loop `w → w` that reflexive closure (`Relation.ReflGen`)
adds "for free" at model-extraction time.

This module also adds the S4 4-rule (transitive-frame box/diamond propagation) on top of
the T rules. The 4-rule propagates the *box itself* (not its unwrapped body) to every
recorded successor: `T(□φ)@w` with an edge `w → w'` yields `T(□φ)@w'` (not `T(φ)@w'`,
which is already produced by the K `boxPos` arm). This is what lets a later
`Relation.ReflTransGen`-closed reachability bridge (`LoopChecking.lean`) carry `T(□φ)`
along an entire path by induction, recovering transitivity without any transitive-closure
reasoning baked into `acc` itself.

## Main Definitions

- `modalTBoxSelf`/`modalTDiaNegSelf`: the two T-specific propagation helpers (self-world,
  unconditional on `acc`).
- `modalApplyOneT`: apply the K rules (`modalApplyOne`) together with the T self-propagation
  arms, merging persistent-rule outputs. Reduces to `modalApplyOne` exactly outside the two
  T-relevant signed-formula shapes (`T(□φ)@w`, `F(◇φ)@w`).
- `modalFourBoxProp`/`modalFourDiaNegProp`: the two S4-specific propagation helpers
  (box-itself across a recorded successor edge, unconditional on any T arm).
- `modalApplyOneS4Rules`: apply `modalApplyOneT` (K + T) together with the 4-rule
  propagation arms, merging persistent-rule outputs. Reduces to `modalApplyOneT` exactly
  outside the two 4-relevant signed-formula shapes (`T(□φ)@w`, `F(◇φ)@w`).

## References

* [M. Fitting, *Proof Methods for Modal and Intuitionistic Logics*][Fitting1983], Chapter 2
* [P. Blackburn, M. de Rijke, Y. Venema, *Modal Logic*][Blackburn2001]
-/

@[expose] public section

namespace Cslib.Logic.Modal.Tableau

open Cslib.Logic.Tableau Cslib.Logic.Modal

variable {Atom : Type*} [DecidableEq Atom] [Hashable Atom]

/-! ## T-Specific Propagation Helpers -/

/-- The T self-propagation for box-positives: from `T(□φ)@w`, generate `T(φ)@w` (the *same*
world `w`, not a recorded successor), filtered to exclude formulas already on the branch.
Justified by the reflexivity of the extracted model's relation (Strategy B), not by any
`acc` edge. -/
def modalTBoxSelf (b : List (SignedFormula (Proposition Atom) WorldIndex))
    (φ : Proposition Atom) (w : WorldIndex) :
    List (SignedFormula (Proposition Atom) WorldIndex) :=
  let sf : SignedFormula (Proposition Atom) WorldIndex := ⟨.pos, φ, w⟩
  if b.any (· == sf) then [] else [sf]

/-- The T self-propagation for diamond-negatives: from `F(◇φ)@w`, generate `F(φ)@w` (the
*same* world `w`), filtered to exclude formulas already on the branch. Dual of
`modalTBoxSelf`. -/
def modalTDiaNegSelf (b : List (SignedFormula (Proposition Atom) WorldIndex))
    (φ : Proposition Atom) (w : WorldIndex) :
    List (SignedFormula (Proposition Atom) WorldIndex) :=
  let sf : SignedFormula (Proposition Atom) WorldIndex := ⟨.neg, φ, w⟩
  if b.any (· == sf) then [] else [sf]

/-! ## T-Augmented Rule Application -/

/-- Apply the K modal rules together with the T self-propagation arms. For the two
T-relevant shapes (`T(□φ)@w`, `F(◇φ)@w`), the T self-propagation formulas are merged into
the K rule's `persistent` output (deduplicated); for every other signed-formula shape,
`modalApplyOneT` reduces to exactly `modalApplyOne` (the K rule dispatch), matching the
report's "no new worlds" claim: the T arms are pure `persistent` outputs at existing worlds,
never `linear`/`branching`. -/
def modalApplyOneT
    (sf : SignedFormula (Proposition Atom) WorldIndex)
    (b : List (SignedFormula (Proposition Atom) WorldIndex))
    (acc : Accessibility) :
    RuleResult (Proposition Atom) WorldIndex × Accessibility :=
  let (kResult, kAcc) := modalApplyOne sf b acc
  match sf.sign, sf.formula with
  | .pos, .box φ =>
    let selfNew := modalTBoxSelf b φ sf.label
    match kResult with
    | .persistent kForms =>
      (.persistent (kForms ++ selfNew.filter (fun x => !(kForms.any (· == x)))), kAcc)
    | .notApplicable =>
      if selfNew.isEmpty then (.notApplicable, kAcc) else (.persistent selfNew, kAcc)
    | other => (other, kAcc)
  | .neg, .diamond φ =>
    let selfNew := modalTDiaNegSelf b φ sf.label
    match kResult with
    | .persistent kForms =>
      (.persistent (kForms ++ selfNew.filter (fun x => !(kForms.any (· == x)))), kAcc)
    | .notApplicable =>
      if selfNew.isEmpty then (.notApplicable, kAcc) else (.persistent selfNew, kAcc)
    | other => (other, kAcc)
  | _, _ => (kResult, kAcc)

omit [Hashable Atom] in
/-- `modalApplyOneT` agrees with `modalApplyOne` outside the two T-relevant shapes
(`T(□φ)@w`, `F(◇φ)@w`): the T arms never affect any other rule dispatch. -/
lemma modalApplyOneT_eq_of_not_boxPos_diaNeg
    (sf : SignedFormula (Proposition Atom) WorldIndex)
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (h : ¬ (sf.sign = .pos ∧ ∃ φ, sf.formula = .box φ) ∧
         ¬ (sf.sign = .neg ∧ ∃ φ, sf.formula = .diamond φ)) :
    modalApplyOneT sf b acc = modalApplyOne sf b acc := by
  obtain ⟨h1, h2⟩ := h
  unfold modalApplyOneT
  rcases hs : sf.sign with _ | _ <;> rcases hf : sf.formula with _ | _ | _ | _ | _ | φ | φ <;>
    simp_all

/-! ## S4-Specific (4-Rule) Propagation Helpers -/

/-- The 4-rule propagation for box-positives: from `T(□φ)@w`, generate `T(□φ)@w'` (the box
formula *itself*, not its unwrapped body) for each recorded successor `w'` of `w`, filtered
to exclude formulas already present on the branch.

This is the S4-specific content: K's `boxPos` arm (`Rules.lean`) already produces
`T(φ)@w'`; the 4-rule additionally propagates the box itself so it can fire again at `w'`,
recovering transitivity along a path of edges without ever transitively closing `acc`. -/
def modalFourBoxProp (b : List (SignedFormula (Proposition Atom) WorldIndex))
    (acc : Accessibility) (φ : Proposition Atom) (w : WorldIndex) :
    List (SignedFormula (Proposition Atom) WorldIndex) :=
  (acc.successorsOf w).filterMap fun w' =>
    let sf : SignedFormula (Proposition Atom) WorldIndex := ⟨.pos, .box φ, w'⟩
    if b.any (· == sf) then none else some sf

/-- The 4-rule propagation for diamond-negatives: from `F(◇φ)@w`, generate `F(◇φ)@w'` (the
diamond formula *itself*) for each recorded successor `w'` of `w`, filtered to exclude
formulas already present on the branch. Dual of `modalFourBoxProp`. -/
def modalFourDiaNegProp (b : List (SignedFormula (Proposition Atom) WorldIndex))
    (acc : Accessibility) (φ : Proposition Atom) (w : WorldIndex) :
    List (SignedFormula (Proposition Atom) WorldIndex) :=
  (acc.successorsOf w).filterMap fun w' =>
    let sf : SignedFormula (Proposition Atom) WorldIndex := ⟨.neg, .diamond φ, w'⟩
    if b.any (· == sf) then none else some sf

/-! ## S4-Augmented Rule Application -/

/-- Apply `modalApplyOneT` (K + T) together with the 4-rule propagation arms. For the two
4-relevant shapes (`T(□φ)@w`, `F(◇φ)@w`), the 4-rule propagation formulas are merged into
the T-augmented rule's `persistent` output (deduplicated); for every other signed-formula
shape, `modalApplyOneS4Rules` reduces to exactly `modalApplyOneT`. This wraps
`modalApplyOneT` rather than `modalApplyOne` so the reflexive (T) component is inherited
alongside the transitive (4) component, giving the reflexive-transitive S4 rule set. -/
def modalApplyOneS4Rules
    (sf : SignedFormula (Proposition Atom) WorldIndex)
    (b : List (SignedFormula (Proposition Atom) WorldIndex))
    (acc : Accessibility) :
    RuleResult (Proposition Atom) WorldIndex × Accessibility :=
  let (tResult, tAcc) := modalApplyOneT sf b acc
  match sf.sign, sf.formula with
  | .pos, .box φ =>
    let fourNew := modalFourBoxProp b acc φ sf.label
    match tResult with
    | .persistent tForms =>
      (.persistent (tForms ++ fourNew.filter (fun x => !(tForms.any (· == x)))), tAcc)
    | .notApplicable =>
      if fourNew.isEmpty then (.notApplicable, tAcc) else (.persistent fourNew, tAcc)
    | other => (other, tAcc)
  | .neg, .diamond φ =>
    let fourNew := modalFourDiaNegProp b acc φ sf.label
    match tResult with
    | .persistent tForms =>
      (.persistent (tForms ++ fourNew.filter (fun x => !(tForms.any (· == x)))), tAcc)
    | .notApplicable =>
      if fourNew.isEmpty then (.notApplicable, tAcc) else (.persistent fourNew, tAcc)
    | other => (other, tAcc)
  | _, _ => (tResult, tAcc)

omit [Hashable Atom] in
/-- `modalApplyOneS4Rules` agrees with `modalApplyOneT` outside the two 4-relevant shapes
(`T(□φ)@w`, `F(◇φ)@w`): the 4-rule arms never affect any other rule dispatch. -/
lemma modalApplyOneS4Rules_eq_of_not_boxPos_diaNeg
    (sf : SignedFormula (Proposition Atom) WorldIndex)
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (h : ¬ (sf.sign = .pos ∧ ∃ φ, sf.formula = .box φ) ∧
         ¬ (sf.sign = .neg ∧ ∃ φ, sf.formula = .diamond φ)) :
    modalApplyOneS4Rules sf b acc = modalApplyOneT sf b acc := by
  obtain ⟨h1, h2⟩ := h
  unfold modalApplyOneS4Rules
  rcases hs : sf.sign with _ | _ <;> rcases hf : sf.formula with _ | _ | _ | _ | _ | φ | φ <;>
    simp_all

/-! ## B-Specific (Symmetric-Frame) Backward-Propagation Helpers

The B rule propagates **backward** along already-recorded edges: given `T(□φ)@w` and a raw
tableau edge `v → w` (`acc.hasEdge v w = true`), it emits `T(φ)@v`; dually for `F(◇φ)@w`. This
is the source-directed mirror of K's own `boxPos`/`diamondNeg` arms (which propagate *forward*
along `w`'s own successors); `Accessibility` (`Branch.lean`) exposes only `successorsOf`
(forward), so `modalBPredecessorsOf` below reads `acc.edges` directly for the reverse
direction.

**Known-worlds filter (the delicate part)**: unlike T's self-propagation (same world `w`,
trivially known since `sf ∈ b`) and S4's forward propagation (successors, known via
`accTargetsKnown`), a raw predecessor `v` of `w` is a **source**, not a target, of an
`acc`-edge, so `RuleApplicationSpec.knownWorldsStep`'s hypothesis bundle
(`accTargetsKnown b acc`, target-only) does not by itself place `v ∈ modalKnownWorlds b`. The
backward arms therefore filter `modalBPredecessorsOf` down to predecessors that are
*already* known worlds of `b`. This filter is a no-op on every branch/accessibility pair
actually reachable by the tableau algorithm (every edge source is `sf.label` for some `sf`
already on the branch at the moment the edge is minted, by `RuleApplicationSpec.freshLocal`'s
own shape, and branches only grow thereafter) -- `BDriver.lean`'s `accSourcesKnown` invariant
makes this precise and is what the B completeness bridge (`FrameCompleteness.lean`) consumes to
show the filter never excludes a genuine predecessor on a real derivation. Restricting to known
predecessors is what makes `RuleApplicationSpec.knownWorldsStep` dischargeable *unconditionally*
(for arbitrary `b`/`acc`, not just reachable ones), exactly as the interface requires.

## Main Definitions

- `modalBPredecessorsOf`: the raw predecessors of a world `w` in `acc` (reverse of
  `Accessibility.successorsOf`).
- `modalBBoxBack`/`modalBDiaNegBack`: the two B-specific backward-propagation helpers.
- `modalApplyOneB`: apply the K rules (`modalApplyOne`) together with the B backward-propagation
  arms, merging persistent-rule outputs. Reduces to `modalApplyOne` exactly outside the two
  B-relevant signed-formula shapes (`T(□φ)@w`, `F(◇φ)@w`). -/

/-- All predecessors of world `w` in the accessibility relation: worlds `v` such that the raw
edge `v → w` is recorded in `acc`. Reverse direction of `Accessibility.successorsOf`
(`Branch.lean`), which `Accessibility` does not itself expose. -/
def modalBPredecessorsOf (acc : Accessibility) (w : WorldIndex) : List WorldIndex :=
  acc.edges.filterMap fun (src, tgt) => if tgt == w then some src else none

omit [DecidableEq Atom] [Hashable Atom] in
/-- Every `modalBPredecessorsOf acc w` member `v` witnesses a raw recorded edge `v → w`. -/
lemma modalBPredecessorsOf_hasEdge {acc : Accessibility} {v w : WorldIndex}
    (h : v ∈ modalBPredecessorsOf acc w) : acc.hasEdge v w = true := by
  unfold modalBPredecessorsOf at h
  obtain ⟨⟨src, tgt⟩, hmem, heq⟩ := List.mem_filterMap.mp h
  dsimp only at heq
  simp only [Accessibility.hasEdge, List.any_eq_true]
  by_cases hc : (tgt == w) = true
  · rw [if_pos hc] at heq
    obtain rfl : src = v := by injection heq
    obtain rfl : tgt = w := eq_of_beq hc
    exact ⟨_, hmem, by simp⟩
  · rw [if_neg hc] at heq
    exact absurd heq (by simp)

/-- The B backward-propagation for box-positives: from `T(□φ)@w`, generate `T(φ)@v` for every
recorded predecessor `v` of `w` that is already a known world of `b`, filtered to exclude
formulas already present on the branch. Backward-along-edges dual of K's forward `boxPos` arm
(`Rules.lean`); see the module docstring above for why the known-worlds filter is needed. -/
def modalBBoxBack (b : List (SignedFormula (Proposition Atom) WorldIndex))
    (acc : Accessibility) (φ : Proposition Atom) (w : WorldIndex) :
    List (SignedFormula (Proposition Atom) WorldIndex) :=
  ((modalBPredecessorsOf acc w).filter (fun v => (modalKnownWorlds b).any (· == v))).filterMap
    fun v =>
      let sf : SignedFormula (Proposition Atom) WorldIndex := ⟨.pos, φ, v⟩
      if b.any (· == sf) then none else some sf

/-- The B backward-propagation for diamond-negatives: from `F(◇φ)@w`, generate `F(φ)@v` for
every recorded predecessor `v` of `w` that is already a known world of `b`, filtered to
exclude formulas already present on the branch. Dual of `modalBBoxBack`. -/
def modalBDiaNegBack (b : List (SignedFormula (Proposition Atom) WorldIndex))
    (acc : Accessibility) (φ : Proposition Atom) (w : WorldIndex) :
    List (SignedFormula (Proposition Atom) WorldIndex) :=
  ((modalBPredecessorsOf acc w).filter (fun v => (modalKnownWorlds b).any (· == v))).filterMap
    fun v =>
      let sf : SignedFormula (Proposition Atom) WorldIndex := ⟨.neg, φ, v⟩
      if b.any (· == sf) then none else some sf

omit [Hashable Atom] in
/-- Membership dichotomy for `modalBBoxBack`: every emitted formula `⟨.pos, φ, v⟩` has `v` a
known-world predecessor of `w` and was not already on `b`. -/
lemma modalBBoxBack_mem {b : List (SignedFormula (Proposition Atom) WorldIndex)}
    {acc : Accessibility} {φ : Proposition Atom} {w : WorldIndex}
    {x : SignedFormula (Proposition Atom) WorldIndex} (h : x ∈ modalBBoxBack b acc φ w) :
    x = (⟨.pos, φ, x.label⟩ : SignedFormula (Proposition Atom) WorldIndex) ∧
      x.label ∈ modalBPredecessorsOf acc w ∧ x.label ∈ modalKnownWorlds b ∧ x ∉ b := by
  unfold modalBBoxBack at h
  obtain ⟨v, hv, heq⟩ := List.mem_filterMap.mp h
  simp only [List.mem_filter] at hv
  obtain ⟨hpred, hknown⟩ := hv
  dsimp only at heq
  by_cases hmem : (b.any (· == (⟨.pos, φ, v⟩ : SignedFormula (Proposition Atom) WorldIndex))) = true
  · rw [if_pos hmem] at heq; exact absurd heq (by simp)
  · rw [if_neg hmem] at heq
    obtain rfl : (⟨.pos, φ, v⟩ : SignedFormula (Proposition Atom) WorldIndex) = x := by
      injection heq
    exact ⟨rfl, hpred, by simpa using hknown, by simpa using hmem⟩

omit [Hashable Atom] in
/-- Membership dichotomy for `modalBDiaNegBack`, dual of `modalBBoxBack_mem`. -/
lemma modalBDiaNegBack_mem {b : List (SignedFormula (Proposition Atom) WorldIndex)}
    {acc : Accessibility} {φ : Proposition Atom} {w : WorldIndex}
    {x : SignedFormula (Proposition Atom) WorldIndex} (h : x ∈ modalBDiaNegBack b acc φ w) :
    x = (⟨.neg, φ, x.label⟩ : SignedFormula (Proposition Atom) WorldIndex) ∧
      x.label ∈ modalBPredecessorsOf acc w ∧ x.label ∈ modalKnownWorlds b ∧ x ∉ b := by
  unfold modalBDiaNegBack at h
  obtain ⟨v, hv, heq⟩ := List.mem_filterMap.mp h
  simp only [List.mem_filter] at hv
  obtain ⟨hpred, hknown⟩ := hv
  dsimp only at heq
  by_cases hmem : (b.any (· == (⟨.neg, φ, v⟩ : SignedFormula (Proposition Atom) WorldIndex))) = true
  · rw [if_pos hmem] at heq; exact absurd heq (by simp)
  · rw [if_neg hmem] at heq
    obtain rfl : (⟨.neg, φ, v⟩ : SignedFormula (Proposition Atom) WorldIndex) = x := by
      injection heq
    exact ⟨rfl, hpred, by simpa using hknown, by simpa using hmem⟩

omit [DecidableEq Atom] [Hashable Atom] in
/-- Converse of `modalBPredecessorsOf_hasEdge`: every raw recorded edge `v → w` witnesses `v`
as a `modalBPredecessorsOf acc w` member. -/
lemma modalBPredecessorsOf_mem_of_hasEdge {acc : Accessibility} {v w : WorldIndex}
    (h : acc.hasEdge v w = true) : v ∈ modalBPredecessorsOf acc w := by
  simp only [Accessibility.hasEdge, List.any_eq_true] at h
  obtain ⟨⟨src, tgt⟩, hmem, hbeq⟩ := h
  simp only [Bool.and_eq_true, beq_iff_eq] at hbeq
  obtain ⟨h1, h2⟩ := hbeq
  subst h1; subst h2
  simp only [modalBPredecessorsOf, List.mem_filterMap]
  exact ⟨_, hmem, by simp⟩

omit [Hashable Atom] in
/-- Introduction direction for `modalBBoxBack`, converse of `modalBBoxBack_mem`: a known-world
predecessor `v` of `w` not already carrying `T(φ)@v` on `b` witnesses `T(φ)@v ∈
modalBBoxBack b acc φ w`. -/
lemma modalBBoxBack_mem_of {b : List (SignedFormula (Proposition Atom) WorldIndex)}
    {acc : Accessibility} {φ : Proposition Atom} {w v : WorldIndex}
    (hpred : v ∈ modalBPredecessorsOf acc w) (hknown : v ∈ modalKnownWorlds b)
    (hnotin : (⟨.pos, φ, v⟩ : SignedFormula (Proposition Atom) WorldIndex) ∉ b) :
    (⟨.pos, φ, v⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ modalBBoxBack b acc φ w := by
  simp only [modalBBoxBack, List.mem_filterMap, List.mem_filter]
  refine ⟨v, ⟨hpred, ?_⟩, ?_⟩
  · exact List.any_eq_true.mpr ⟨v, hknown, by simp⟩
  · rw [if_neg (by simpa using hnotin)]

omit [Hashable Atom] in
/-- Introduction direction for `modalBDiaNegBack`, dual of `modalBBoxBack_mem_of`. -/
lemma modalBDiaNegBack_mem_of {b : List (SignedFormula (Proposition Atom) WorldIndex)}
    {acc : Accessibility} {φ : Proposition Atom} {w v : WorldIndex}
    (hpred : v ∈ modalBPredecessorsOf acc w) (hknown : v ∈ modalKnownWorlds b)
    (hnotin : (⟨.neg, φ, v⟩ : SignedFormula (Proposition Atom) WorldIndex) ∉ b) :
    (⟨.neg, φ, v⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈
      modalBDiaNegBack b acc φ w := by
  simp only [modalBDiaNegBack, List.mem_filterMap, List.mem_filter]
  refine ⟨v, ⟨hpred, ?_⟩, ?_⟩
  · exact List.any_eq_true.mpr ⟨v, hknown, by simp⟩
  · rw [if_neg (by simpa using hnotin)]

/-! ## B-Augmented Rule Application -/

/-- Apply the K modal rules together with the B backward-propagation arms. For the two
B-relevant shapes (`T(□φ)@w`, `F(◇φ)@w`), the backward-propagation formulas are merged into
the K rule's `persistent` output (deduplicated); for every other signed-formula shape,
`modalApplyOneB` reduces to exactly `modalApplyOne` (the K rule dispatch): the B arms are pure
`persistent` outputs at existing (known) worlds, never `linear`/`branching`, matching the
report's "no new worlds" classification for B. -/
def modalApplyOneB
    (sf : SignedFormula (Proposition Atom) WorldIndex)
    (b : List (SignedFormula (Proposition Atom) WorldIndex))
    (acc : Accessibility) :
    RuleResult (Proposition Atom) WorldIndex × Accessibility :=
  let (kResult, kAcc) := modalApplyOne sf b acc
  match sf.sign, sf.formula with
  | .pos, .box φ =>
    let backNew := modalBBoxBack b acc φ sf.label
    match kResult with
    | .persistent kForms =>
      (.persistent (kForms ++ backNew.filter (fun x => !(kForms.any (· == x)))), kAcc)
    | .notApplicable =>
      if backNew.isEmpty then (.notApplicable, kAcc) else (.persistent backNew, kAcc)
    | other => (other, kAcc)
  | .neg, .diamond φ =>
    let backNew := modalBDiaNegBack b acc φ sf.label
    match kResult with
    | .persistent kForms =>
      (.persistent (kForms ++ backNew.filter (fun x => !(kForms.any (· == x)))), kAcc)
    | .notApplicable =>
      if backNew.isEmpty then (.notApplicable, kAcc) else (.persistent backNew, kAcc)
    | other => (other, kAcc)
  | _, _ => (kResult, kAcc)

omit [Hashable Atom] in
/-- `modalApplyOneB` agrees with `modalApplyOne` outside the two B-relevant shapes
(`T(□φ)@w`, `F(◇φ)@w`): the B arms never affect any other rule dispatch. -/
lemma modalApplyOneB_eq_of_not_boxPos_diaNeg
    (sf : SignedFormula (Proposition Atom) WorldIndex)
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (h : ¬ (sf.sign = .pos ∧ ∃ φ, sf.formula = .box φ) ∧
         ¬ (sf.sign = .neg ∧ ∃ φ, sf.formula = .diamond φ)) :
    modalApplyOneB sf b acc = modalApplyOne sf b acc := by
  obtain ⟨h1, h2⟩ := h
  unfold modalApplyOneB
  rcases hs : sf.sign with _ | _ <;> rcases hf : sf.formula with _ | _ | _ | _ | _ | φ | φ <;>
    simp_all

/-! ## TB-Augmented Rule Application

TB's rule is the merge of T's self-propagation arms (`modalTBoxSelf`, `modalTDiaNegSelf`) and
B's predecessor-backward arms (`modalBBoxBack`, `modalBDiaNegBack`). B's arms are the
predecessor-lookup family and carry the larger spec discharge (`BDriver.lean`, 1,124 lines,
versus `TDriver.lean`, 809 lines), so `modalApplyOneTB` wraps `modalApplyOneB` (the inner
layer) with T's self-propagation arms merged into the outer layer -- the exact layering pattern
`modalApplyOneS4Rules` uses over `modalApplyOneT`, keeping the larger spec discharge innermost
and maximising reuse from `modalApplyOneB_spec`. -/

/-- Apply `modalApplyOneB` (K + B) together with the T self-propagation arms. For the two
T-relevant shapes (`T(□φ)@w`, `F(◇φ)@w`), the T self-propagation formulas are merged into the
B-augmented rule's `persistent` output (deduplicated); for every other signed-formula shape,
`modalApplyOneTB` reduces to exactly `modalApplyOneB`. This wraps `modalApplyOneB` rather than
`modalApplyOneT` so the symmetric (B) component -- the larger spec discharge -- stays
innermost, giving the reflexive-symmetric TB rule set. -/
def modalApplyOneTB
    (sf : SignedFormula (Proposition Atom) WorldIndex)
    (b : List (SignedFormula (Proposition Atom) WorldIndex))
    (acc : Accessibility) :
    RuleResult (Proposition Atom) WorldIndex × Accessibility :=
  let (bResult, bAcc) := modalApplyOneB sf b acc
  match sf.sign, sf.formula with
  | .pos, .box φ =>
    let selfNew := modalTBoxSelf b φ sf.label
    match bResult with
    | .persistent bForms =>
      (.persistent (bForms ++ selfNew.filter (fun x => !(bForms.any (· == x)))), bAcc)
    | .notApplicable =>
      if selfNew.isEmpty then (.notApplicable, bAcc) else (.persistent selfNew, bAcc)
    | other => (other, bAcc)
  | .neg, .diamond φ =>
    let selfNew := modalTDiaNegSelf b φ sf.label
    match bResult with
    | .persistent bForms =>
      (.persistent (bForms ++ selfNew.filter (fun x => !(bForms.any (· == x)))), bAcc)
    | .notApplicable =>
      if selfNew.isEmpty then (.notApplicable, bAcc) else (.persistent selfNew, bAcc)
    | other => (other, bAcc)
  | _, _ => (bResult, bAcc)

omit [Hashable Atom] in
/-- `modalApplyOneTB` agrees with `modalApplyOneB` outside the two T-relevant shapes
(`T(□φ)@w`, `F(◇φ)@w`): the T self-propagation arms never affect any other rule dispatch. This
is the load-bearing reuse mechanism: chained with `modalApplyOneB_eq_of_not_boxPos_diaNeg`
(above) and `modalApplyOne`'s own case analysis, it lets TB inherit every propositional and
mint case from K unchanged. -/
lemma modalApplyOneTB_eq_of_not_boxPos_diaNeg
    (sf : SignedFormula (Proposition Atom) WorldIndex)
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (h : ¬ (sf.sign = .pos ∧ ∃ φ, sf.formula = .box φ) ∧
         ¬ (sf.sign = .neg ∧ ∃ φ, sf.formula = .diamond φ)) :
    modalApplyOneTB sf b acc = modalApplyOneB sf b acc := by
  obtain ⟨h1, h2⟩ := h
  unfold modalApplyOneTB
  rcases hs : sf.sign with _ | _ <;> rcases hf : sf.formula with _ | _ | _ | _ | _ | φ | φ <;>
    simp_all

/-! ## D-Specific (Serial-Frame) Dual-Propagation Helpers

The D rule encodes seriality (`Relation.Serial`, i.e. every world has a successor) via two
PERSISTENT dual arms at the *same* world `w`, mirroring T's self-propagation shape rather than
minting any new successor: `T(□φ)@w ⊢ T(◇φ)@w` and `F(◇φ)@w ⊢ F(□φ)@w`. This is deliberately
**not** the `.linear`-mint pattern K's `boxPos`/`diamondNeg` arms use for possibly-new
successors -- minting there would trip `RuleApplicationSpec.boxPosNotExpanding` (F9), which
forbids a `.linear` result at exactly the box-positive shape a naive D rule would mint at. The
dual arms sidestep this by staying `persistent`, exactly as T's self-propagation does.

**Universe note**: unlike T's self-propagation (whose output `φ` is already a subformula of the
seed `φ0`, since `□φ ∈ modalSubfmls φ0 → φ ∈ modalSubfmls φ0`), D's dual output `◇φ`/`□φ` is
generally *not* a subformula of a plain `φ0` -- `modalApplyOneD_outputsSubsetUniverse_fails`
(`DDriver.lean`) is the machine-checked counterexample. `RuleApplicationSpecAt`
(`GenericDriver.lean`) and `modalDualAugment` (`DDriver.lean`) exist precisely to fix D's
universe at a dual-closed `φ0`, additively, without touching `modalSubfmls` or the plain
`RuleApplicationSpec` any other rule in this cube discharges.

## Main Definitions

- `modalDBoxDual`/`modalDDiaNegDual`: the two D-specific dual-propagation helpers (self-world,
  unconditional on `acc`, persistent).
- `modalApplyOneD`: apply the K rules (`modalApplyOne`) together with the D dual-propagation
  arms, merging persistent-rule outputs. Reduces to `modalApplyOne` exactly outside the two
  D-relevant signed-formula shapes (`T(□φ)@w`, `F(◇φ)@w`). -/

/-- The D dual-propagation for box-positives: from `T(□φ)@w`, generate `T(◇φ)@w` (the *same*
world `w`, not a recorded successor), filtered to exclude formulas already on the branch.
Justified by the seriality of the extracted model's relation (Strategy B), not by any `acc`
edge. -/
def modalDBoxDual (b : List (SignedFormula (Proposition Atom) WorldIndex))
    (φ : Proposition Atom) (w : WorldIndex) :
    List (SignedFormula (Proposition Atom) WorldIndex) :=
  let sf : SignedFormula (Proposition Atom) WorldIndex := ⟨.pos, .diamond φ, w⟩
  if b.any (· == sf) then [] else [sf]

/-- The D dual-propagation for diamond-negatives: from `F(◇φ)@w`, generate `F(□φ)@w` (the
*same* world `w`), filtered to exclude formulas already on the branch. Dual of
`modalDBoxDual`. -/
def modalDDiaNegDual (b : List (SignedFormula (Proposition Atom) WorldIndex))
    (φ : Proposition Atom) (w : WorldIndex) :
    List (SignedFormula (Proposition Atom) WorldIndex) :=
  let sf : SignedFormula (Proposition Atom) WorldIndex := ⟨.neg, .box φ, w⟩
  if b.any (· == sf) then [] else [sf]

/-! ## D-Augmented Rule Application -/

/-- Apply the K modal rules together with the D dual-propagation arms. For the two
D-relevant shapes (`T(□φ)@w`, `F(◇φ)@w`), the D dual-propagation formulas are merged into
the K rule's `persistent` output (deduplicated); for every other signed-formula shape,
`modalApplyOneD` reduces to exactly `modalApplyOne` (the K rule dispatch), matching the same
"no new worlds" shape as `modalApplyOneT`: the D arms are pure `persistent` outputs at
existing worlds, never `linear`/`branching`. -/
def modalApplyOneD
    (sf : SignedFormula (Proposition Atom) WorldIndex)
    (b : List (SignedFormula (Proposition Atom) WorldIndex))
    (acc : Accessibility) :
    RuleResult (Proposition Atom) WorldIndex × Accessibility :=
  let (kResult, kAcc) := modalApplyOne sf b acc
  match sf.sign, sf.formula with
  | .pos, .box φ =>
    let dualNew := modalDBoxDual b φ sf.label
    match kResult with
    | .persistent kForms =>
      (.persistent (kForms ++ dualNew.filter (fun x => !(kForms.any (· == x)))), kAcc)
    | .notApplicable =>
      if dualNew.isEmpty then (.notApplicable, kAcc) else (.persistent dualNew, kAcc)
    | other => (other, kAcc)
  | .neg, .diamond φ =>
    let dualNew := modalDDiaNegDual b φ sf.label
    match kResult with
    | .persistent kForms =>
      (.persistent (kForms ++ dualNew.filter (fun x => !(kForms.any (· == x)))), kAcc)
    | .notApplicable =>
      if dualNew.isEmpty then (.notApplicable, kAcc) else (.persistent dualNew, kAcc)
    | other => (other, kAcc)
  | _, _ => (kResult, kAcc)

omit [Hashable Atom] in
/-- `modalApplyOneD` agrees with `modalApplyOne` outside the two D-relevant shapes
(`T(□φ)@w`, `F(◇φ)@w`): the D arms never affect any other rule dispatch. -/
lemma modalApplyOneD_eq_of_not_boxPos_diaNeg
    (sf : SignedFormula (Proposition Atom) WorldIndex)
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (h : ¬ (sf.sign = .pos ∧ ∃ φ, sf.formula = .box φ) ∧
         ¬ (sf.sign = .neg ∧ ∃ φ, sf.formula = .diamond φ)) :
    modalApplyOneD sf b acc = modalApplyOne sf b acc := by
  obtain ⟨h1, h2⟩ := h
  unfold modalApplyOneD
  rcases hs : sf.sign with _ | _ <;> rcases hf : sf.formula with _ | _ | _ | _ | _ | φ | φ <;>
    simp_all

end Cslib.Logic.Modal.Tableau

end
