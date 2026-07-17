/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Modal.Tableau.S5Simplification

/-! # 5/KB5 Rooted-Cluster Tableau Simplification

This module defines the root-aware universal-propagation rule `modalApplyOneFive`, the 5/KB5
analogue of `S5Simplification.lean`'s `modalApplyOneS5w`. It realises the Euclidean (not
necessarily reflexive) frame property directly, reusing the *entire* S5 witness-reuse termination
machinery (task 515 Phases 1-7) verbatim, per the parent plan's Phase 18: the mint arms
(`T(◇φ)@w`, `F(□φ)@w`) are shape-identical to `modalApplyOneS5w`'s, so `modalOps`/`mintTags`/
`S5wTagInv`/`usedTags`/`S5wWorldInv`/`modalMaxWorld_lt_worldBound_of_S5w` (all rule-independent)
apply unchanged; only the two *propagation* arms (`T(□φ)@w`, `F(◇φ)@w`) differ.

## Main Definitions

- `modalFiveBoxAll`/`modalFiveDiaNegAll`: the root-aware propagation helpers. From `T(□φ)@w`
  (any trigger world `w`, including the root `0`), emit `T(φ)@w'` for every known world `w' ≠ 0`
  of the branch -- **excluding the root from every propagation target**, since a rooted Euclidean
  (not-necessarily-reflexive) frame need not relate the root to itself or the root to be a
  successor of anything. This is the one-line semantic difference from `modalS5BoxAll`, which
  propagates to *every* known world including the trigger's own (root-inclusive, since S5's
  relation is an equivalence and hence reflexive). Dually for `F(◇φ)@w`.
- `modalApplyOneFiveProp`: apply the K modal rules together with the root-aware propagation arms.
  Mirrors `modalApplyOneS5` declaration-for-declaration, substituting `modalFiveBoxAll`/
  `modalFiveDiaNegAll` for `modalS5BoxAll`/`modalS5DiaNegAll`.
- `modalApplyOneFive`: the shipped rule -- witness-reuse (Phase 1's `witnessWorldS5`, reused
  verbatim: it is already rule-independent, parametrized only over `b`/`s`/`φ`) at the two mint
  shapes, falling through to `modalApplyOneFiveProp` everywhere else. Mirrors `modalApplyOneS5w`.
- `modalStepBranchFive`/`modalExpandBranchesFive`/`modalTableauFive`: the 5-system driver,
  instantiated at `apply := modalApplyOneFive` throughout (unlike the S5 chain, which staged
  `modalApplyOneS5`/`modalApplyOneS5w` separately for historical reasons -- Five needs only the
  one, already-witness-reuse, rule from the start).

## Strategy

Every field of `RuleApplicationSpecCore modalApplyOneFive` reduces along the same two-layer
agreement chain as S5w's own discharge (`modalApplyOneFive_eq_of_not_mint_shape` /
`modalApplyOneFiveProp_eq_of_not_boxPos_diaNeg`): outside the four modal shapes, `modalApplyOneFive`
is definitionally `modalApplyOne` (K), so K's own field witnesses apply unchanged. At the two
propagation shapes, the merged root-excluded content is bounded by `modalKnownWorlds b` (hence by
`modalWorldBound φ0`) and a subformula of `φ0`. At the two witness-reuse shapes, the reuse arm's
witness world is drawn from `modalKnownWorlds b` by `witnessWorldS5`'s own construction, and the
mint arm falls through to K's own mint witness -- identical to S5w's own discharge.

## References

* [P. Blackburn, M. de Rijke, Y. Venema, *Modal Logic*][Blackburn2001], §4.5 (Euclidean frames,
  the logic K5) and §6.6 (the rooted normal form for K45/S5-adjacent systems).
* [R. Goré, *Tableau Methods for Modal and Temporal Logics*][Gore1999].
-/

@[expose] public section

namespace Cslib.Logic.Modal.Tableau

open Cslib.Logic.Tableau Cslib.Logic.Modal

variable {Atom : Type*} [DecidableEq Atom] [Hashable Atom]

/-! ## Root-Aware Propagation Helpers -/

/-- The root/non-root-asymmetric propagation for box-positives (Route (1), see
`reports/07_phase19-soundness-blocker-remediation.md`): from `T(□φ)@w`, generate `T(φ)@w'` for
known worlds `w' ≠ 0` of the branch, **excluding the root** from every propagation target
(unconditionally, exactly as before). When the trigger `w` is the **root** (`w = 0`), an
**additional** guard restricts the target set to `w'` with a genuine recorded edge
`acc.hasEdge 0 w'` -- direct root successors -- since `RightEuclidean` alone does not relate the
root to worlds beyond its direct successors (the `Fin 3` counterexample in Phase 19's blocker
record). When the trigger `w ≠ 0`, the target set is the full non-root cluster, unchanged: this
direction is sound via the codomain equivalence (`Relation.rooted_cluster_isEquiv`), not frame
reflexivity. The root case's output is a **subset** of the non-root case's (same list, filtered
further), so every world-bound / catalog-membership fact proved for the old uniform shape
continues to hold for the root arm. -/
def modalFiveBoxAll (b : List (SignedFormula (Proposition Atom) WorldIndex))
    (acc : Accessibility) (φ : Proposition Atom) (w : WorldIndex) :
    List (SignedFormula (Proposition Atom) WorldIndex) :=
  (modalKnownWorlds b).filterMap fun w' =>
    if w' == (0 : WorldIndex) then none
    else if w == (0 : WorldIndex) then
      (if acc.hasEdge 0 w' then
        let sf : SignedFormula (Proposition Atom) WorldIndex := ⟨.pos, φ, w'⟩
        if b.any (· == sf) then none else some sf
      else none)
    else
      let sf : SignedFormula (Proposition Atom) WorldIndex := ⟨.pos, φ, w'⟩
      if b.any (· == sf) then none else some sf

/-- The root/non-root-asymmetric propagation for diamond-negatives, dual of `modalFiveBoxAll`. -/
def modalFiveDiaNegAll (b : List (SignedFormula (Proposition Atom) WorldIndex))
    (acc : Accessibility) (φ : Proposition Atom) (w : WorldIndex) :
    List (SignedFormula (Proposition Atom) WorldIndex) :=
  (modalKnownWorlds b).filterMap fun w' =>
    if w' == (0 : WorldIndex) then none
    else if w == (0 : WorldIndex) then
      (if acc.hasEdge 0 w' then
        let sf : SignedFormula (Proposition Atom) WorldIndex := ⟨.neg, φ, w'⟩
        if b.any (· == sf) then none else some sf
      else none)
    else
      let sf : SignedFormula (Proposition Atom) WorldIndex := ⟨.neg, φ, w'⟩
      if b.any (· == sf) then none else some sf

omit [Hashable Atom] in
/-- Membership dichotomy for `modalFiveBoxAll`: every emitted formula `⟨.pos, φ, w'⟩` has `w'` a
known, non-root world of `b`, and was not already on `b`. Conclusion unchanged from the
pre-Route-1 shape (verbatim); the extra root-arm guard only adds a `by_cases` to the proof. -/
lemma modalFiveBoxAll_mem {b : List (SignedFormula (Proposition Atom) WorldIndex)}
    {acc : Accessibility} {φ : Proposition Atom} {w : WorldIndex}
    {x : SignedFormula (Proposition Atom) WorldIndex} (h : x ∈ modalFiveBoxAll b acc φ w) :
    x = (⟨.pos, φ, x.label⟩ : SignedFormula (Proposition Atom) WorldIndex) ∧
      x.label ∈ modalKnownWorlds b ∧ x.label ≠ 0 ∧ x ∉ b := by
  unfold modalFiveBoxAll at h
  obtain ⟨v, hv, heq⟩ := List.mem_filterMap.mp h
  dsimp only at heq
  by_cases hz : (v == (0 : WorldIndex)) = true
  · rw [if_pos hz] at heq; exact absurd heq (by simp)
  · rw [if_neg hz] at heq
    by_cases hw0 : (w == (0 : WorldIndex)) = true
    · rw [if_pos hw0] at heq
      by_cases hedge : acc.hasEdge 0 v = true
      · rw [if_pos hedge] at heq
        by_cases hmem :
            (b.any (· == (⟨.pos, φ, v⟩ : SignedFormula (Proposition Atom) WorldIndex))) = true
        · rw [if_pos hmem] at heq; exact absurd heq (by simp)
        · rw [if_neg hmem] at heq
          obtain rfl : (⟨.pos, φ, v⟩ : SignedFormula (Proposition Atom) WorldIndex) = x := by
            injection heq
          refine ⟨rfl, hv, ?_, by simpa using hmem⟩
          simpa using hz
      · rw [if_neg hedge] at heq; exact absurd heq (by simp)
    · rw [if_neg hw0] at heq
      by_cases hmem : (b.any (· == (⟨.pos, φ, v⟩ : SignedFormula (Proposition Atom) WorldIndex))) =
          true
      · rw [if_pos hmem] at heq; exact absurd heq (by simp)
      · rw [if_neg hmem] at heq
        obtain rfl : (⟨.pos, φ, v⟩ : SignedFormula (Proposition Atom) WorldIndex) = x := by
          injection heq
        refine ⟨rfl, hv, ?_, by simpa using hmem⟩
        simpa using hz

omit [Hashable Atom] in
/-- **Root-arm edge witness** for `modalFiveBoxAll`: when the trigger is the root (`w = 0`), every
emitted target `x.label` has a genuine recorded edge `acc.hasEdge 0 x.label`. This is the fact
Phase 19's `accReachableInv_related_five` root case needs (the standard K-style realized-edge
argument on `acc.successorsOf 0`). -/
lemma modalFiveBoxAll_root_hasEdge {b : List (SignedFormula (Proposition Atom) WorldIndex)}
    {acc : Accessibility} {φ : Proposition Atom}
    {x : SignedFormula (Proposition Atom) WorldIndex}
    (h : x ∈ modalFiveBoxAll b acc φ (0 : WorldIndex)) : acc.hasEdge 0 x.label = true := by
  unfold modalFiveBoxAll at h
  obtain ⟨v, hv, heq⟩ := List.mem_filterMap.mp h
  dsimp only at heq
  by_cases hz : (v == (0 : WorldIndex)) = true
  · rw [if_pos hz] at heq; exact absurd heq (by simp)
  · rw [if_neg hz] at heq
    rw [if_pos (by simp : ((0 : WorldIndex) == (0 : WorldIndex)) = true)] at heq
    by_cases hedge : acc.hasEdge 0 v = true
    · rw [if_pos hedge] at heq
      by_cases hmem :
          (b.any (· == (⟨.pos, φ, v⟩ : SignedFormula (Proposition Atom) WorldIndex))) = true
      · rw [if_pos hmem] at heq; exact absurd heq (by simp)
      · rw [if_neg hmem] at heq
        obtain rfl : (⟨.pos, φ, v⟩ : SignedFormula (Proposition Atom) WorldIndex) = x := by
          injection heq
        simpa using hedge
    · rw [if_neg hedge] at heq; exact absurd heq (by simp)

omit [Hashable Atom] in
/-- Membership dichotomy for `modalFiveDiaNegAll`, dual of `modalFiveBoxAll_mem`. -/
lemma modalFiveDiaNegAll_mem {b : List (SignedFormula (Proposition Atom) WorldIndex)}
    {acc : Accessibility} {φ : Proposition Atom} {w : WorldIndex}
    {x : SignedFormula (Proposition Atom) WorldIndex} (h : x ∈ modalFiveDiaNegAll b acc φ w) :
    x = (⟨.neg, φ, x.label⟩ : SignedFormula (Proposition Atom) WorldIndex) ∧
      x.label ∈ modalKnownWorlds b ∧ x.label ≠ 0 ∧ x ∉ b := by
  unfold modalFiveDiaNegAll at h
  obtain ⟨v, hv, heq⟩ := List.mem_filterMap.mp h
  dsimp only at heq
  by_cases hz : (v == (0 : WorldIndex)) = true
  · rw [if_pos hz] at heq; exact absurd heq (by simp)
  · rw [if_neg hz] at heq
    by_cases hw0 : (w == (0 : WorldIndex)) = true
    · rw [if_pos hw0] at heq
      by_cases hedge : acc.hasEdge 0 v = true
      · rw [if_pos hedge] at heq
        by_cases hmem :
            (b.any (· == (⟨.neg, φ, v⟩ : SignedFormula (Proposition Atom) WorldIndex))) = true
        · rw [if_pos hmem] at heq; exact absurd heq (by simp)
        · rw [if_neg hmem] at heq
          obtain rfl : (⟨.neg, φ, v⟩ : SignedFormula (Proposition Atom) WorldIndex) = x := by
            injection heq
          refine ⟨rfl, hv, ?_, by simpa using hmem⟩
          simpa using hz
      · rw [if_neg hedge] at heq; exact absurd heq (by simp)
    · rw [if_neg hw0] at heq
      by_cases hmem : (b.any (· == (⟨.neg, φ, v⟩ : SignedFormula (Proposition Atom) WorldIndex))) =
          true
      · rw [if_pos hmem] at heq; exact absurd heq (by simp)
      · rw [if_neg hmem] at heq
        obtain rfl : (⟨.neg, φ, v⟩ : SignedFormula (Proposition Atom) WorldIndex) = x := by
          injection heq
        refine ⟨rfl, hv, ?_, by simpa using hmem⟩
        simpa using hz

omit [Hashable Atom] in
/-- **Root-arm edge witness** for `modalFiveDiaNegAll`, dual of `modalFiveBoxAll_root_hasEdge`. -/
lemma modalFiveDiaNegAll_root_hasEdge {b : List (SignedFormula (Proposition Atom) WorldIndex)}
    {acc : Accessibility} {φ : Proposition Atom}
    {x : SignedFormula (Proposition Atom) WorldIndex}
    (h : x ∈ modalFiveDiaNegAll b acc φ (0 : WorldIndex)) : acc.hasEdge 0 x.label = true := by
  unfold modalFiveDiaNegAll at h
  obtain ⟨v, hv, heq⟩ := List.mem_filterMap.mp h
  dsimp only at heq
  by_cases hz : (v == (0 : WorldIndex)) = true
  · rw [if_pos hz] at heq; exact absurd heq (by simp)
  · rw [if_neg hz] at heq
    rw [if_pos (by simp : ((0 : WorldIndex) == (0 : WorldIndex)) = true)] at heq
    by_cases hedge : acc.hasEdge 0 v = true
    · rw [if_pos hedge] at heq
      by_cases hmem :
          (b.any (· == (⟨.neg, φ, v⟩ : SignedFormula (Proposition Atom) WorldIndex))) = true
      · rw [if_pos hmem] at heq; exact absurd heq (by simp)
      · rw [if_neg hmem] at heq
        obtain rfl : (⟨.neg, φ, v⟩ : SignedFormula (Proposition Atom) WorldIndex) = x := by
          injection heq
        simpa using hedge
    · rw [if_neg hedge] at heq; exact absurd heq (by simp)

/-! ## Root-Aware Rule Application -/

/-- Apply the K modal rules together with the root-aware propagation arms. Mirrors
`modalApplyOneS5` declaration-for-declaration, substituting `modalFiveBoxAll`/`modalFiveDiaNegAll`
for `modalS5BoxAll`/`modalS5DiaNegAll`. -/
def modalApplyOneFiveProp
    (sf : SignedFormula (Proposition Atom) WorldIndex)
    (b : List (SignedFormula (Proposition Atom) WorldIndex))
    (acc : Accessibility) :
    RuleResult (Proposition Atom) WorldIndex × Accessibility :=
  let (kResult, kAcc) := modalApplyOne sf b acc
  match sf.sign, sf.formula with
  | .pos, .box φ =>
    let allNew := modalFiveBoxAll b acc φ sf.label
    match kResult with
    | .persistent kForms =>
      (.persistent (kForms ++ allNew.filter (fun x => !(kForms.any (· == x)))), kAcc)
    | .notApplicable =>
      if allNew.isEmpty then (.notApplicable, kAcc) else (.persistent allNew, kAcc)
    | other => (other, kAcc)
  | .neg, .diamond φ =>
    let allNew := modalFiveDiaNegAll b acc φ sf.label
    match kResult with
    | .persistent kForms =>
      (.persistent (kForms ++ allNew.filter (fun x => !(kForms.any (· == x)))), kAcc)
    | .notApplicable =>
      if allNew.isEmpty then (.notApplicable, kAcc) else (.persistent allNew, kAcc)
    | other => (other, kAcc)
  | _, _ => (kResult, kAcc)

omit [Hashable Atom] in
/-- `modalApplyOneFiveProp` agrees with `modalApplyOne` outside the two propagation shapes.
Mirrors `modalApplyOneS5_eq_of_not_boxPos_diaNeg`. -/
lemma modalApplyOneFiveProp_eq_of_not_boxPos_diaNeg
    (sf : SignedFormula (Proposition Atom) WorldIndex)
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (h : ¬ (sf.sign = .pos ∧ ∃ φ, sf.formula = .box φ) ∧
         ¬ (sf.sign = .neg ∧ ∃ φ, sf.formula = .diamond φ)) :
    modalApplyOneFiveProp sf b acc = modalApplyOne sf b acc := by
  obtain ⟨h1, h2⟩ := h
  unfold modalApplyOneFiveProp
  rcases hs : sf.sign with _ | _ <;> rcases hf : sf.formula with _ | _ | _ | _ | _ | φ | φ <;>
    simp_all

/-- At the two propagation shapes, `modalApplyOneFiveProp` never mints (its accessibility output
is exactly K's, unchanged) and only appends formulas at existing known worlds. Mirrors
`modalApplyOneS5_boxPos_diaNeg_eq`. -/
lemma modalApplyOneFiveProp_boxPos_diaNeg_eq
    (sf : SignedFormula (Proposition Atom) WorldIndex)
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (hsfmem : sf ∈ b) (hknown : accTargetsKnown b acc)
    (h : (sf.sign = .pos ∧ ∃ φ, sf.formula = .box φ) ∨
         (sf.sign = .neg ∧ ∃ φ, sf.formula = .diamond φ)) :
    (modalApplyOneFiveProp sf b acc).snd = acc ∧
    ((modalApplyOneFiveProp sf b acc).fst = .notApplicable ∨
      ∃ out, (modalApplyOneFiveProp sf b acc).fst = .persistent out ∧
        ∀ x ∈ out, x.label ∈ modalKnownWorlds b) := by
  rcases h with ⟨hs, φ, hf⟩ | ⟨hs, φ, hf⟩
  · obtain ⟨s, ff, l⟩ := sf
    simp only at hs hf
    subst hs; subst hf
    have hK := modalApplyOne_boxPos_eq
      (⟨.pos, .box φ, l⟩ : SignedFormula (Proposition Atom) WorldIndex) rfl φ rfl b acc
    have hKW := modalApplyOne_knownWorlds_step
      (⟨.pos, .box φ, l⟩ : SignedFormula (Proposition Atom) WorldIndex) b acc hsfmem hknown
    unfold modalApplyOneFiveProp
    rcases hp : modalApplyOne
        (⟨.pos, .box φ, l⟩ : SignedFormula (Proposition Atom) WorldIndex) b acc
        with ⟨kResult, kAcc⟩
    rw [hp] at hK
    simp only at hK
    rw [hp] at hKW
    simp only at hKW
    rcases hK with hK | ⟨out0, hK⟩ <;> subst hK
    · rcases hKW with ⟨hsndeq, -⟩ | ⟨-, hmatch⟩
      swap
      · exact hmatch.elim
      subst hsndeq
      dsimp only
      split_ifs with hemp
      · exact ⟨rfl, Or.inl rfl⟩
      · refine ⟨rfl, Or.inr ⟨_, rfl, ?_⟩⟩
        intro x hx
        exact (modalFiveBoxAll_mem hx).2.1
    · rcases hKW with ⟨hsndeq, hmatch⟩ | ⟨-, hmatch⟩
      swap
      · exact hmatch.elim
      subst hsndeq
      dsimp only
      refine ⟨rfl, Or.inr ⟨_, rfl, ?_⟩⟩
      intro x hx
      simp only [List.mem_append, List.mem_filter] at hx
      rcases hx with hx | ⟨hx, -⟩
      · exact hmatch x hx
      · exact (modalFiveBoxAll_mem hx).2.1
  · obtain ⟨s, ff, l⟩ := sf
    simp only at hs hf
    subst hs; subst hf
    have hK := modalApplyOne_diamondNeg_eq
      (⟨.neg, .diamond φ, l⟩ : SignedFormula (Proposition Atom) WorldIndex) rfl φ rfl b acc
    have hKW := modalApplyOne_knownWorlds_step
      (⟨.neg, .diamond φ, l⟩ : SignedFormula (Proposition Atom) WorldIndex) b acc hsfmem hknown
    unfold modalApplyOneFiveProp
    rcases hp : modalApplyOne
        (⟨.neg, .diamond φ, l⟩ : SignedFormula (Proposition Atom) WorldIndex) b acc
        with ⟨kResult, kAcc⟩
    rw [hp] at hK
    simp only at hK
    rw [hp] at hKW
    simp only at hKW
    rcases hK with hK | ⟨out0, hK⟩ <;> subst hK
    · rcases hKW with ⟨hsndeq, -⟩ | ⟨-, hmatch⟩
      swap
      · exact hmatch.elim
      subst hsndeq
      dsimp only
      split_ifs with hemp
      · exact ⟨rfl, Or.inl rfl⟩
      · refine ⟨rfl, Or.inr ⟨_, rfl, ?_⟩⟩
        intro x hx
        exact (modalFiveDiaNegAll_mem hx).2.1
    · rcases hKW with ⟨hsndeq, hmatch⟩ | ⟨-, hmatch⟩
      swap
      · exact hmatch.elim
      subst hsndeq
      dsimp only
      refine ⟨rfl, Or.inr ⟨_, rfl, ?_⟩⟩
      intro x hx
      simp only [List.mem_append, List.mem_filter] at hx
      rcases hx with hx | ⟨hx, -⟩
      · exact hmatch x hx
      · exact (modalFiveDiaNegAll_mem hx).2.1

/-! ## The 5/KB5 Witness-Reuse Rule -/

/-- The shipped 5/KB5 rule: `witnessWorldS5` (Phase 1, `S5Simplification.lean`, already
rule-independent -- parametrized only over `b`/`s`/`φ`) at the two mint shapes, falling through to
`modalApplyOneFiveProp` everywhere else, including the two root-aware propagation shapes. Mirrors
`modalApplyOneS5w`; every load-bearing design constraint (`.linear [witness]`, no `hasEdge` guard)
carries over unchanged, since the mint arms are shape-identical. -/
def modalApplyOneFive : RuleApply Atom := fun sf b acc =>
  match sf.sign, sf.formula with
  | .pos, .diamond φ =>
    (match witnessWorldS5 b .pos φ with
     | some w' => (.linear [⟨.pos, φ, w'⟩], acc.addEdge sf.label w')
     | none => modalApplyOneFiveProp sf b acc)
  | .neg, .box φ =>
    (match witnessWorldS5 b .neg φ with
     | some w' => (.linear [⟨.neg, φ, w'⟩], acc.addEdge sf.label w')
     | none => modalApplyOneFiveProp sf b acc)
  | _, _ => modalApplyOneFiveProp sf b acc

/-- Free bridge: on the box-positive (propagation, non-mint) shape, `modalApplyOneFive` falls
through to `modalApplyOneFiveProp` by the definitional `| _, _ =>` catch-all -- `rfl`. -/
lemma modalApplyOneFive_boxPos_eq
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (φ : Proposition Atom) (w : WorldIndex) :
    modalApplyOneFive (⟨.pos, .box φ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) b acc
      = modalApplyOneFiveProp
          (⟨.pos, .box φ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) b acc :=
  rfl

/-- Free bridge, dual of `modalApplyOneFive_boxPos_eq`. -/
lemma modalApplyOneFive_diaNeg_eq
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (φ : Proposition Atom) (w : WorldIndex) :
    modalApplyOneFive (⟨.neg, .diamond φ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) b acc
      = modalApplyOneFiveProp
          (⟨.neg, .diamond φ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) b acc :=
  rfl

/-- `modalApplyOneFive` agrees with `modalApplyOneFiveProp` outside the two mint shapes.
Mirrors `modalApplyOneS5w_eq_of_not_mint_shape`. -/
lemma modalApplyOneFive_eq_of_not_mint_shape
    (sf : SignedFormula (Proposition Atom) WorldIndex)
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (h : ¬ (sf.sign = .pos ∧ ∃ φ, sf.formula = .diamond φ) ∧
         ¬ (sf.sign = .neg ∧ ∃ φ, sf.formula = .box φ)) :
    modalApplyOneFive sf b acc = modalApplyOneFiveProp sf b acc := by
  obtain ⟨h1, h2⟩ := h
  unfold modalApplyOneFive
  rcases hs : sf.sign with _ | _ <;> rcases hf : sf.formula with _ | _ | _ | _ | _ | φ | φ <;>
    simp_all

omit [Hashable Atom] in
/-- `modalApplyOneFiveProp`'s accessibility output agrees with K's `modalApplyOne` at every
shape. Mirrors `modalApplyOneS5_snd_eq`. -/
lemma modalApplyOneFiveProp_snd_eq
    (sf : SignedFormula (Proposition Atom) WorldIndex)
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility) :
    (modalApplyOneFiveProp sf b acc).snd = (modalApplyOne sf b acc).snd := by
  unfold modalApplyOneFiveProp
  rcases hs : sf.sign with _ | _ <;> rcases hf : sf.formula with _ | _ | _ | _ | _ | φ | φ <;>
    simp_all <;>
    rcases h1 : (modalApplyOne sf b acc).1 with _ | _ | _ | _ <;> simp <;> split <;> simp

omit [Hashable Atom] in
/-- Whenever K's own result is `.linear`, `modalApplyOneFiveProp` agrees with `modalApplyOne`
entirely (both `fst` and `snd`): `.linear` never arises from the two propagation shapes
themselves (which only ever produce `.notApplicable`/`.persistent`), so K's own `.linear` result
must have come from a non-propagation shape, where the two functions agree definitionally.
Mirrors `modalApplyOneS5_eq_of_linear`. -/
lemma modalApplyOneFiveProp_eq_of_linear
    (sf : SignedFormula (Proposition Atom) WorldIndex)
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (nf : List (SignedFormula (Proposition Atom) WorldIndex))
    (h : (modalApplyOne sf b acc).fst = RuleResult.linear nf) :
    modalApplyOneFiveProp sf b acc = modalApplyOne sf b acc := by
  unfold modalApplyOneFiveProp
  rcases hp : modalApplyOne sf b acc with ⟨kResult, kAcc⟩
  rw [hp] at h
  simp only [] at h
  subst h
  rcases hs : sf.sign with _ | _ <;> rcases hf : sf.formula with _ | _ | _ | _ | _ | φ | φ <;>
    simp_all

omit [Hashable Atom] in
/-- Local re-derivation of `S5Simplification.lean`'s `private lemma
modalApplyOneS5_fresh_local_local` (unavailable across files): `modalApplyOneFiveProp` satisfies
the same `freshLocal` dichotomy as `modalApplyOne`. -/
private lemma modalApplyOneFiveProp_fresh_local_local
    (sf : SignedFormula (Proposition Atom) WorldIndex)
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility) :
    (modalApplyOneFiveProp sf b acc).snd = acc ∨
    (∃ wsf rest, (modalApplyOneFiveProp sf b acc).fst = RuleResult.linear (wsf :: rest)
      ∧ (modalApplyOneFiveProp sf b acc).snd = acc.addEdge sf.label wsf.label) := by
  rcases modalApplyOne_fresh_local sf b acc with hsame | ⟨wsf, rest, hfst, hsnd⟩
  · exact Or.inl (by rw [modalApplyOneFiveProp_snd_eq]; exact hsame)
  · have heq := modalApplyOneFiveProp_eq_of_linear sf b acc (wsf :: rest) hfst
    exact Or.inr ⟨wsf, rest, by rw [heq]; exact hfst, by rw [heq]; exact hsnd⟩

/-- `modalApplyOneFive` satisfies the same `freshLocal` dichotomy as `modalApplyOne` /
`modalApplyOneFiveProp`: either `acc` is left unchanged, or exactly one edge is added with a
`.linear` result headed by the new witness. Mirrors `modalApplyOneS5w_fresh_local`. -/
lemma modalApplyOneFive_fresh_local
    (sf : SignedFormula (Proposition Atom) WorldIndex)
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility) :
    (modalApplyOneFive sf b acc).snd = acc ∨
    (∃ wsf rest, (modalApplyOneFive sf b acc).fst = RuleResult.linear (wsf :: rest) ∧
      (modalApplyOneFive sf b acc).snd = acc.addEdge sf.label wsf.label) := by
  obtain ⟨s, ff, w⟩ := sf
  rcases s with _ | _
  · rcases ff with _ | _ | ⟨a, c⟩ | ⟨x, y⟩ | ⟨x, y⟩ | φ | φ
    case atom =>
      rw [modalApplyOneFive_eq_of_not_mint_shape _ b acc (by simp)]
      exact modalApplyOneFiveProp_fresh_local_local _ b acc
    case bot =>
      rw [modalApplyOneFive_eq_of_not_mint_shape _ b acc (by simp)]
      exact modalApplyOneFiveProp_fresh_local_local _ b acc
    case imp =>
      rw [modalApplyOneFive_eq_of_not_mint_shape _ b acc (by simp)]
      exact modalApplyOneFiveProp_fresh_local_local _ b acc
    case and =>
      rw [modalApplyOneFive_eq_of_not_mint_shape _ b acc (by simp)]
      exact modalApplyOneFiveProp_fresh_local_local _ b acc
    case or =>
      rw [modalApplyOneFive_eq_of_not_mint_shape _ b acc (by simp)]
      exact modalApplyOneFiveProp_fresh_local_local _ b acc
    case box =>
      rw [modalApplyOneFive_eq_of_not_mint_shape _ b acc (by simp)]
      exact modalApplyOneFiveProp_fresh_local_local _ b acc
    case diamond =>
      unfold modalApplyOneFive
      cases hw : witnessWorldS5 b Sign.pos φ with
      | none =>
        simp only [hw]
        rw [modalApplyOneFiveProp_eq_of_not_boxPos_diaNeg _ b acc (by simp)]
        exact modalApplyOne_fresh_local _ b acc
      | some w' =>
        simp only [hw]
        exact Or.inr ⟨⟨.pos, φ, w'⟩, [], rfl, rfl⟩
  · rcases ff with _ | _ | ⟨a, c⟩ | ⟨x, y⟩ | ⟨x, y⟩ | φ | φ
    case atom =>
      rw [modalApplyOneFive_eq_of_not_mint_shape _ b acc (by simp)]
      exact modalApplyOneFiveProp_fresh_local_local _ b acc
    case bot =>
      rw [modalApplyOneFive_eq_of_not_mint_shape _ b acc (by simp)]
      exact modalApplyOneFiveProp_fresh_local_local _ b acc
    case imp =>
      rw [modalApplyOneFive_eq_of_not_mint_shape _ b acc (by simp)]
      exact modalApplyOneFiveProp_fresh_local_local _ b acc
    case and =>
      rw [modalApplyOneFive_eq_of_not_mint_shape _ b acc (by simp)]
      exact modalApplyOneFiveProp_fresh_local_local _ b acc
    case or =>
      rw [modalApplyOneFive_eq_of_not_mint_shape _ b acc (by simp)]
      exact modalApplyOneFiveProp_fresh_local_local _ b acc
    case diamond =>
      rw [modalApplyOneFive_eq_of_not_mint_shape _ b acc (by simp)]
      exact modalApplyOneFiveProp_fresh_local_local _ b acc
    case box =>
      unfold modalApplyOneFive
      cases hw : witnessWorldS5 b Sign.neg φ with
      | none =>
        simp only [hw]
        rw [modalApplyOneFiveProp_eq_of_not_boxPos_diaNeg _ b acc (by simp)]
        exact modalApplyOne_fresh_local _ b acc
      | some w' =>
        simp only [hw]
        exact Or.inr ⟨⟨.neg, φ, w'⟩, [], rfl, rfl⟩

/-! ## Driver Instantiation -/

/-- One-step branch expansion for the 5/KB5 (Euclidean-frame) tableau: the generic driver
instantiated at `apply := modalApplyOneFive`. -/
def modalStepBranchFive
    (b e : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility) :
    Option (List (List (SignedFormula (Proposition Atom) WorldIndex)) ×
            List (List (SignedFormula (Proposition Atom) WorldIndex)) ×
            Accessibility) :=
  modalStepBranchGen modalApplyOneFive b e acc

/-- Fuel-based expansion of a list of 5/KB5-system branches. -/
def modalExpandBranchesFive
    (branches expandedSets : List (List (SignedFormula (Proposition Atom) WorldIndex)))
    (accs : List Accessibility) (fuel : Nat) : ModalTableauResult Atom :=
  modalExpandBranchesGen modalApplyOneFive branches expandedSets accs fuel

/-- The 5-system (Euclidean-frame) modal tableau **decision procedure**: the generic entry point
instantiated at `apply := modalApplyOneFive`, starting the signed tableau from `F(φ)` at world
`0`. Unlike the S5 chain, no separate unguarded-rule stage is needed: `modalApplyOneFive` is
already the witness-reuse rule from the start. -/
def modalTableauFive (φ : Proposition Atom) : ModalTableauResult Atom :=
  modalTableauGen modalApplyOneFive φ

/-- `modalStepBranchFive` is exactly `modalStepBranchGen modalApplyOneFive` -- true `rfl`. -/
theorem modalStepBranchFive_eq
    (b e : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility) :
    modalStepBranchFive b e acc = modalStepBranchGen modalApplyOneFive b e acc := rfl

/-- `modalExpandBranchesFive` is exactly `modalExpandBranchesGen modalApplyOneFive` -- true
`rfl`. -/
theorem modalExpandBranchesFive_eq
    (branches expandedSets : List (List (SignedFormula (Proposition Atom) WorldIndex)))
    (accs : List Accessibility) (fuel : Nat) :
    modalExpandBranchesFive branches expandedSets accs fuel =
      modalExpandBranchesGen modalApplyOneFive branches expandedSets accs fuel := rfl

/-- `modalTableauFive` is exactly `modalTableauGen modalApplyOneFive` -- true `rfl`. -/
theorem modalTableauFive_eq (φ : Proposition Atom) :
    modalTableauFive φ = modalTableauGen modalApplyOneFive φ := rfl

/-! ## `modalKnownWorlds`/`modalUniverse` Local Re-Derivations

`FmpMeasure.lean`'s `mem_modalKnownWorlds`/`modalKnownWorlds_le_modalMaxWorld`/
`mem_modalUniverse_of`/`modalSubfmls_trans` are `private` (hence unavailable across files). Local
re-derivation, mirroring `S5Simplification.lean`'s own `_S5`/`_S5w`-suffixed pattern, renamed for
Five. -/

omit [DecidableEq Atom] [Hashable Atom] in
/-- Local re-derivation of `FmpMeasure.lean`'s `private lemma modalSubfmls_trans` (unavailable
across files): a subformula of a subformula is a subformula. -/
private lemma modalSubfmls_trans_Five {a b c : Proposition Atom}
    (hab : a ∈ modalSubfmls b) (hbc : b ∈ modalSubfmls c) : a ∈ modalSubfmls c := by
  induction c with
  | atom p =>
    simp only [modalSubfmls, List.mem_singleton] at hbc; subst hbc; exact hab
  | bot =>
    simp only [modalSubfmls, List.mem_singleton] at hbc; subst hbc; exact hab
  | imp x y ihx ihy =>
    simp only [modalSubfmls, List.mem_cons, List.mem_append] at hbc
    rcases hbc with (rfl | hx) | hy
    · exact hab
    · exact List.mem_cons_of_mem _ (List.mem_append_left _ (ihx hx))
    · exact List.mem_cons_of_mem _ (List.mem_append_right _ (ihy hy))
  | and x y ihx ihy =>
    simp only [modalSubfmls, List.mem_cons, List.mem_append] at hbc
    rcases hbc with (rfl | hx) | hy
    · exact hab
    · exact List.mem_cons_of_mem _ (List.mem_append_left _ (ihx hx))
    · exact List.mem_cons_of_mem _ (List.mem_append_right _ (ihy hy))
  | or x y ihx ihy =>
    simp only [modalSubfmls, List.mem_cons, List.mem_append] at hbc
    rcases hbc with (rfl | hx) | hy
    · exact hab
    · exact List.mem_cons_of_mem _ (List.mem_append_left _ (ihx hx))
    · exact List.mem_cons_of_mem _ (List.mem_append_right _ (ihy hy))
  | box x ihx =>
    simp only [modalSubfmls, List.mem_cons] at hbc
    rcases hbc with rfl | hx
    · exact hab
    · exact List.mem_cons_of_mem _ (ihx hx)
  | diamond x ihx =>
    simp only [modalSubfmls, List.mem_cons] at hbc
    rcases hbc with rfl | hx
    · exact hab
    · exact List.mem_cons_of_mem _ (ihx hx)

omit [DecidableEq Atom] [Hashable Atom] in
/-- Local re-derivation of `FmpMeasure.lean`'s `private lemma modalKnownWorlds_fold_spec`
(unavailable across files), dropping the `Nodup` conjunct this development does not need. -/
private lemma modalKnownWorlds_fold_spec_Five
    (l : List (SignedFormula (Proposition Atom) WorldIndex)) (ws0 : List WorldIndex) :
    ∀ x, x ∈ l.foldl (fun ws sf => if ws.any (· == sf.label) then ws else sf.label :: ws) ws0 ↔
      x ∈ ws0 ∨ ∃ sf ∈ l, sf.label = x := by
  induction l generalizing ws0 with
  | nil => simp
  | cons sf rest ih =>
    by_cases hc : ws0.any (· == sf.label)
    · simp only [List.foldl_cons, if_pos hc]
      intro x
      rw [ih ws0]
      have hmemws0 : sf.label ∈ ws0 := by simpa [List.any_eq_true] using hc
      constructor
      · rintro (h | ⟨sf', hsf', rfl⟩)
        · exact Or.inl h
        · exact Or.inr ⟨sf', List.mem_cons_of_mem _ hsf', rfl⟩
      · rintro (h | ⟨sf', hsf', hfeq⟩)
        · exact Or.inl h
        · rcases List.mem_cons.mp hsf' with rfl | hsf'
          · exact Or.inl (hfeq ▸ hmemws0)
          · exact Or.inr ⟨sf', hsf', hfeq⟩
    · simp only [List.foldl_cons, if_neg hc]
      intro x
      rw [ih (sf.label :: ws0)]
      constructor
      · rintro (h | ⟨sf', hsf', rfl⟩)
        · rcases List.mem_cons.mp h with rfl | h
          · exact Or.inr ⟨sf, List.mem_cons_self, rfl⟩
          · exact Or.inl h
        · exact Or.inr ⟨sf', List.mem_cons_of_mem _ hsf', rfl⟩
      · rintro (h | ⟨sf', hsf', hfeq⟩)
        · exact Or.inl (List.mem_cons_of_mem _ h)
        · rcases List.mem_cons.mp hsf' with rfl | hsf'
          · exact Or.inl (hfeq ▸ List.mem_cons_self)
          · exact Or.inr ⟨sf', hsf', hfeq⟩

omit [DecidableEq Atom] [Hashable Atom] in
/-- Local re-derivation of `FmpMeasure.lean`'s `private lemma mem_modalKnownWorlds`. -/
private lemma mem_modalKnownWorlds_Five
    (l : List (SignedFormula (Proposition Atom) WorldIndex)) (x : WorldIndex) :
    x ∈ modalKnownWorlds l ↔ ∃ sf ∈ l, sf.label = x := by
  unfold modalKnownWorlds
  simpa using modalKnownWorlds_fold_spec_Five l [] x

omit [DecidableEq Atom] [Hashable Atom] in
/-- Local re-derivation of `FmpMeasure.lean`'s `private lemma modalKnownWorlds_le_modalMaxWorld`:
any known-world label is bounded by `modalMaxWorld b`. -/
private lemma known_label_le_modalMaxWorld_Five
    {b : List (SignedFormula (Proposition Atom) WorldIndex)} {w : WorldIndex}
    (h : w ∈ modalKnownWorlds b) : w ≤ modalMaxWorld b := by
  obtain ⟨y, hy, hyeq⟩ := (mem_modalKnownWorlds_Five b w).mp h
  rw [← hyeq]; exact label_le_modalMaxWorld hy

omit [DecidableEq Atom] [Hashable Atom] in
/-- Local re-derivation of `FmpMeasure.lean`'s `private lemma modalUniverse_mem_formula`: extracts
the formula-component bound. -/
private lemma modalUniverse_mem_formula_Five {φ0 : Proposition Atom}
    {x : SignedFormula (Proposition Atom) WorldIndex} (hx : x ∈ modalUniverse φ0) :
    x.formula ∈ modalSubfmls φ0 := by
  simp only [modalUniverse, List.mem_flatMap, List.mem_range, List.mem_cons,
    List.not_mem_nil, or_false] at hx
  obtain ⟨w, -, ψ, hψ, heq | heq⟩ := hx <;> (subst heq; exact hψ)

omit [DecidableEq Atom] [Hashable Atom] in
/-- Local re-derivation of `FmpMeasure.lean`'s `private lemma mem_modalUniverse_of`, swapped to
plain `modalUniverse`/`modalWorldBound`. -/
private lemma mem_modalUniverse_of_Five {φ0 : Proposition Atom} {s : Sign} {φ : Proposition Atom}
    {w : WorldIndex} (hw : w ≤ modalWorldBound φ0) (hφ : φ ∈ modalSubfmls φ0) :
    (⟨s, φ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ modalUniverse φ0 := by
  have hlt : w < modalWorldBound φ0 + 1 := Nat.lt_succ_of_le hw
  simp only [modalUniverse, List.mem_flatMap, List.mem_range]
  exact ⟨w, hlt, φ, hφ, by cases s <;> simp⟩

/-! ## `RuleApplicationSpecCore` for `modalApplyOneFive`

Discharges `RuleApplicationSpecCore modalApplyOneFive` (`GenericDriver.lean`): the nine
Hintikka/saturation-forcing fields (dropping `rankStep`/`outDegStep`/`knownWorldsStep`, unreachable
for the same reason as S5w -- `modalApplyOneS5_rankStep_not_dischargeable`'s counterexample
transfers verbatim, since it is witnessed at a formula shape where the root-aware and universal
propagation targets coincide). Every field reduces along the two-layer agreement chain
`modalApplyOneFive → modalApplyOneFiveProp → modalApplyOne`, mirroring `modalApplyOneS5w`'s own
discharge declaration-for-declaration. -/

omit [Hashable Atom] in
/-- **Combined F9/F10 shape fact for Five** (hypothesis-free): at `modalApplyOneFiveProp`'s two
propagation shapes, the result is always `.notApplicable` or `.persistent`. Mirrors
`modalApplyOneS5_boxPos_diaNeg_shape`. -/
private lemma modalApplyOneFiveProp_boxPos_diaNeg_shape
    (sf : SignedFormula (Proposition Atom) WorldIndex)
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (h : (sf.sign = .pos ∧ ∃ φ, sf.formula = .box φ) ∨
         (sf.sign = .neg ∧ ∃ φ, sf.formula = .diamond φ)) :
    (modalApplyOneFiveProp sf b acc).fst = .notApplicable ∨
      ∃ out, (modalApplyOneFiveProp sf b acc).fst = .persistent out := by
  rcases h with ⟨hs, φ, hf⟩ | ⟨hs, φ, hf⟩
  · obtain ⟨s, ff, l⟩ := sf
    simp only at hs hf; subst hs; subst hf
    have hK := modalApplyOne_boxPos_eq
      (⟨.pos, .box φ, l⟩ : SignedFormula (Proposition Atom) WorldIndex) rfl φ rfl b acc
    unfold modalApplyOneFiveProp
    rcases hp : modalApplyOne
        (⟨.pos, .box φ, l⟩ : SignedFormula (Proposition Atom) WorldIndex) b acc
        with ⟨kResult, kAcc⟩
    rw [hp] at hK
    simp only at hK
    rcases hK with hK | ⟨out0, hK⟩ <;> subst hK
    · dsimp only; split_ifs with hemp
      · exact Or.inl rfl
      · exact Or.inr ⟨_, rfl⟩
    · exact Or.inr ⟨_, rfl⟩
  · obtain ⟨s, ff, l⟩ := sf
    simp only at hs hf; subst hs; subst hf
    have hK := modalApplyOne_diamondNeg_eq
      (⟨.neg, .diamond φ, l⟩ : SignedFormula (Proposition Atom) WorldIndex) rfl φ rfl b acc
    unfold modalApplyOneFiveProp
    rcases hp : modalApplyOne
        (⟨.neg, .diamond φ, l⟩ : SignedFormula (Proposition Atom) WorldIndex) b acc
        with ⟨kResult, kAcc⟩
    rw [hp] at hK
    simp only at hK
    rcases hK with hK | ⟨out0, hK⟩ <;> subst hK
    · dsimp only; split_ifs with hemp
      · exact Or.inl rfl
      · exact Or.inr ⟨_, rfl⟩
    · exact Or.inr ⟨_, rfl⟩

/-- **F9 discharge for `modalApplyOneFive`**. Mirrors `modalApplyOneS5w_boxPosNotExpanding`. -/
private lemma modalApplyOneFive_boxPosNotExpanding
    (sf : SignedFormula (Proposition Atom) WorldIndex)
    (hsign : sf.sign = .pos) (ψ : Proposition Atom) (hform : sf.formula = .box ψ)
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility) :
    (modalApplyOneFive sf b acc).fst = .notApplicable ∨
      ∃ out, (modalApplyOneFive sf b acc).fst = .persistent out := by
  rw [modalApplyOneFive_eq_of_not_mint_shape sf b acc (by simp [hsign, hform])]
  exact modalApplyOneFiveProp_boxPos_diaNeg_shape sf b acc (Or.inl ⟨hsign, ψ, hform⟩)

/-- **F10 discharge for `modalApplyOneFive`**, dual of `modalApplyOneFive_boxPosNotExpanding`. -/
private lemma modalApplyOneFive_diaNegNotExpanding
    (sf : SignedFormula (Proposition Atom) WorldIndex)
    (hsign : sf.sign = .neg) (ψ : Proposition Atom) (hform : sf.formula = .diamond ψ)
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility) :
    (modalApplyOneFive sf b acc).fst = .notApplicable ∨
      ∃ out, (modalApplyOneFive sf b acc).fst = .persistent out := by
  rw [modalApplyOneFive_eq_of_not_mint_shape sf b acc (by simp [hsign, hform])]
  exact modalApplyOneFiveProp_boxPos_diaNeg_shape sf b acc (Or.inr ⟨hsign, ψ, hform⟩)

/-- **F8 discharge for `modalApplyOneFive`**. Mirrors `modalApplyOneS5w_localShapeInvariance`. -/
private lemma modalApplyOneFive_localShapeInvariance
    (s : Sign) (φ : Proposition Atom) (w : WorldIndex)
    (hnb : ∀ ψ, φ ≠ .box ψ) (hnd : ∀ ψ, φ ≠ .diamond ψ)
    (b b' : List (SignedFormula (Proposition Atom) WorldIndex)) (acc acc' : Accessibility) :
    (modalApplyOneFive ⟨s, φ, w⟩ b acc).1 = (modalApplyOneFive ⟨s, φ, w⟩ b' acc').1 := by
  rw [modalApplyOneFive_eq_of_not_mint_shape ⟨s, φ, w⟩ b acc ⟨by simp [hnd], by simp [hnb]⟩,
    modalApplyOneFive_eq_of_not_mint_shape ⟨s, φ, w⟩ b' acc' ⟨by simp [hnd], by simp [hnb]⟩,
    modalApplyOneFiveProp_eq_of_not_boxPos_diaNeg ⟨s, φ, w⟩ b acc ⟨by simp [hnb], by simp [hnd]⟩,
    modalApplyOneFiveProp_eq_of_not_boxPos_diaNeg ⟨s, φ, w⟩ b' acc' ⟨by simp [hnb], by simp [hnd]⟩]
  exact modalApplyOne_fst_eq_of_not_box s φ w hnb hnd b b' acc acc'

/-- **F7 discharge for `modalApplyOneFive`**. Mirrors `modalApplyOneS5w_branchingLength`. -/
private lemma modalApplyOneFive_branchingLength
    (sf : SignedFormula (Proposition Atom) WorldIndex)
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (brs : List (List (SignedFormula (Proposition Atom) WorldIndex)))
    (h : (modalApplyOneFive sf b acc).fst = RuleResult.branching brs) :
    brs.length = 2 := by
  by_cases hmint : (sf.sign = .pos ∧ ∃ φ, sf.formula = .diamond φ) ∨
      (sf.sign = .neg ∧ ∃ φ, sf.formula = .box φ)
  · rcases hmint with ⟨hs, φ, hf⟩ | ⟨hs, φ, hf⟩
    · obtain ⟨s, ff, w⟩ := sf
      simp only at hs hf; subst hs; subst hf
      simp only [modalApplyOneFive] at h
      cases hw : witnessWorldS5 b Sign.pos φ with
      | some w' => rw [hw] at h; simp at h
      | none =>
        rw [hw] at h
        rw [modalApplyOneFiveProp_eq_of_not_boxPos_diaNeg _ b acc (by simp)] at h
        exact modalApplyOne_branching_length _ b acc brs h
    · obtain ⟨s, ff, w⟩ := sf
      simp only at hs hf; subst hs; subst hf
      simp only [modalApplyOneFive] at h
      cases hw : witnessWorldS5 b Sign.neg φ with
      | some w' => rw [hw] at h; simp at h
      | none =>
        rw [hw] at h
        rw [modalApplyOneFiveProp_eq_of_not_boxPos_diaNeg _ b acc (by simp)] at h
        exact modalApplyOne_branching_length _ b acc brs h
  · rw [modalApplyOneFive_eq_of_not_mint_shape sf b acc
        ⟨fun hc => hmint (Or.inl hc), fun hc => hmint (Or.inr hc)⟩] at h
    by_cases hprop : (sf.sign = .pos ∧ ∃ φ, sf.formula = .box φ) ∨
        (sf.sign = .neg ∧ ∃ φ, sf.formula = .diamond φ)
    · exfalso
      rcases modalApplyOneFiveProp_boxPos_diaNeg_shape sf b acc hprop with hna | ⟨out, hpe⟩
      · rw [hna] at h; simp at h
      · rw [hpe] at h; simp at h
    · rw [modalApplyOneFiveProp_eq_of_not_boxPos_diaNeg sf b acc
          ⟨fun hc => hprop (Or.inl hc), fun hc => hprop (Or.inr hc)⟩] at h
      exact modalApplyOne_branching_length sf b acc brs h

/-- **F3 discharge for `modalApplyOneFive`**. Mirrors `modalApplyOneS5w_persistentFresh`. -/
private lemma modalApplyOneFive_persistentFresh
    (sf : SignedFormula (Proposition Atom) WorldIndex)
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (nf : List (SignedFormula (Proposition Atom) WorldIndex))
    (h : (modalApplyOneFive sf b acc).fst = RuleResult.persistent nf) :
    nf ≠ [] ∧ ∀ x ∈ nf, x ∉ b := by
  by_cases hmint : (sf.sign = .pos ∧ ∃ φ, sf.formula = .diamond φ) ∨
      (sf.sign = .neg ∧ ∃ φ, sf.formula = .box φ)
  · rcases hmint with ⟨hs, φ, hf⟩ | ⟨hs, φ, hf⟩
    · obtain ⟨s, ff, w⟩ := sf
      simp only at hs hf; subst hs; subst hf
      simp only [modalApplyOneFive] at h
      cases hw : witnessWorldS5 b Sign.pos φ with
      | some w' => rw [hw] at h; simp at h
      | none =>
        rw [hw] at h
        rw [modalApplyOneFiveProp_eq_of_not_boxPos_diaNeg _ b acc (by simp)] at h
        exact modalApplyOne_persistent_props _ b acc nf h
    · obtain ⟨s, ff, w⟩ := sf
      simp only at hs hf; subst hs; subst hf
      simp only [modalApplyOneFive] at h
      cases hw : witnessWorldS5 b Sign.neg φ with
      | some w' => rw [hw] at h; simp at h
      | none =>
        rw [hw] at h
        rw [modalApplyOneFiveProp_eq_of_not_boxPos_diaNeg _ b acc (by simp)] at h
        exact modalApplyOne_persistent_props _ b acc nf h
  · rw [modalApplyOneFive_eq_of_not_mint_shape sf b acc
        ⟨fun hc => hmint (Or.inl hc), fun hc => hmint (Or.inr hc)⟩] at h
    by_cases hprop : (sf.sign = .pos ∧ ∃ φ, sf.formula = .box φ) ∨
        (sf.sign = .neg ∧ ∃ φ, sf.formula = .diamond φ)
    · rcases hprop with ⟨hs, φ, hf⟩ | ⟨hs, φ, hf⟩
      · obtain ⟨s, ff, l⟩ := sf
        simp only at hs hf; subst hs; subst hf
        have hK := modalApplyOne_boxPos_eq
          (⟨.pos, .box φ, l⟩ : SignedFormula (Proposition Atom) WorldIndex) rfl φ rfl b acc
        have hKfresh := modalApplyOne_persistent_props
          (⟨.pos, .box φ, l⟩ : SignedFormula (Proposition Atom) WorldIndex) b acc
        simp only [modalApplyOneFiveProp] at h
        rcases hp : modalApplyOne
            (⟨.pos, .box φ, l⟩ : SignedFormula (Proposition Atom) WorldIndex) b acc
            with ⟨kResult, kAcc⟩
        rw [hp] at h hK
        simp only at hK
        rcases hK with hK | ⟨out0, hK⟩ <;> subst hK
        · -- kResult = .notApplicable
          dsimp only at h
          split_ifs at h with hemp
          rw [RuleResult.persistent.injEq] at h
          refine ⟨?_, ?_⟩
          · rw [← h]; simpa using hemp
          · intro x hx
            rw [← h] at hx
            exact (modalFiveBoxAll_mem hx).2.2.2
        · -- kResult = .persistent out0
          simp only at h
          obtain ⟨hne, hfresh⟩ := hKfresh out0 (by rw [hp])
          rw [RuleResult.persistent.injEq] at h
          refine ⟨by rw [← h]; simp [hne], ?_⟩
          intro x hx
          rw [← h] at hx
          simp only [List.mem_append, List.mem_filter] at hx
          rcases hx with hx | ⟨hx, -⟩
          · exact hfresh x hx
          · exact (modalFiveBoxAll_mem hx).2.2.2
      · obtain ⟨s, ff, l⟩ := sf
        simp only at hs hf; subst hs; subst hf
        have hK := modalApplyOne_diamondNeg_eq
          (⟨.neg, .diamond φ, l⟩ : SignedFormula (Proposition Atom) WorldIndex) rfl φ rfl b acc
        have hKfresh := modalApplyOne_persistent_props
          (⟨.neg, .diamond φ, l⟩ : SignedFormula (Proposition Atom) WorldIndex) b acc
        simp only [modalApplyOneFiveProp] at h
        rcases hp : modalApplyOne
            (⟨.neg, .diamond φ, l⟩ : SignedFormula (Proposition Atom) WorldIndex) b acc
            with ⟨kResult, kAcc⟩
        rw [hp] at h hK
        simp only at hK
        rcases hK with hK | ⟨out0, hK⟩ <;> subst hK
        · -- kResult = .notApplicable
          dsimp only at h
          split_ifs at h with hemp
          rw [RuleResult.persistent.injEq] at h
          refine ⟨?_, ?_⟩
          · rw [← h]; simpa using hemp
          · intro x hx
            rw [← h] at hx
            exact (modalFiveDiaNegAll_mem hx).2.2.2
        · -- kResult = .persistent out0
          simp only at h
          obtain ⟨hne, hfresh⟩ := hKfresh out0 (by rw [hp])
          rw [RuleResult.persistent.injEq] at h
          refine ⟨by rw [← h]; simp [hne], ?_⟩
          intro x hx
          rw [← h] at hx
          simp only [List.mem_append, List.mem_filter] at hx
          rcases hx with hx | ⟨hx, -⟩
          · exact hfresh x hx
          · exact (modalFiveDiaNegAll_mem hx).2.2.2
    · rw [modalApplyOneFiveProp_eq_of_not_boxPos_diaNeg sf b acc
          ⟨fun hc => hprop (Or.inl hc), fun hc => hprop (Or.inr hc)⟩] at h
      exact modalApplyOne_persistent_props sf b acc nf h

/-- **F2 discharge for `modalApplyOneFive`**. Mirrors `modalApplyOneS5w_outputsSubsetUniverse`. -/
private lemma modalApplyOneFive_outputsSubsetUniverse
    (φ0 : Proposition Atom) (sf : SignedFormula (Proposition Atom) WorldIndex)
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (hb : ∀ x ∈ b, x ∈ modalUniverse φ0) (hsf : sf ∈ b) (hInv : accFreshInv b acc)
    (hW : modalMaxWorld b < modalWorldBound φ0) :
    (match (modalApplyOneFive sf b acc).fst with
      | .linear formulas => ∀ x ∈ formulas, x ∈ modalUniverse φ0
      | .branching branches => ∀ x ∈ branches.flatten, x ∈ modalUniverse φ0
      | .persistent formulas => ∀ x ∈ formulas, x ∈ modalUniverse φ0
      | .notApplicable => True) := by
  by_cases hmint : (sf.sign = .pos ∧ ∃ φ, sf.formula = .diamond φ) ∨
      (sf.sign = .neg ∧ ∃ φ, sf.formula = .box φ)
  · rcases hmint with ⟨hs, φ, hf⟩ | ⟨hs, φ, hf⟩
    · obtain ⟨s, ff, l⟩ := sf
      simp only at hs hf; subst hs; subst hf
      have hKsub := modalApplyOne_outputs_subset φ0
        (⟨.pos, .diamond φ, l⟩ : SignedFormula (Proposition Atom) WorldIndex) b acc hb hsf hInv hW
      unfold modalApplyOneFive
      cases hw : witnessWorldS5 b Sign.pos φ with
      | some w' =>
        simp only [hw]
        have hwknown : w' ∈ modalKnownWorlds b :=
          label_mem_modalKnownWorlds (witnessWorldS5_mem hw)
        have hwle : w' ≤ modalWorldBound φ0 :=
          le_trans (known_label_le_modalMaxWorld_Five hwknown) (le_of_lt hW)
        have hφsub : φ ∈ modalSubfmls φ0 := by
          have hform : Proposition.diamond φ ∈ modalSubfmls φ0 :=
            modalUniverse_mem_formula_Five (hb _ hsf)
          exact modalSubfmls_trans_Five (b := Proposition.diamond φ)
            (List.mem_cons_of_mem _ (modalSubfmls_self_mem φ)) hform
        intro x hx
        simp only [List.mem_singleton] at hx
        rw [hx]
        exact mem_modalUniverse_of_Five hwle hφsub
      | none =>
        simp only [hw]
        rw [modalApplyOneFiveProp_eq_of_not_boxPos_diaNeg _ b acc (by simp)]
        exact hKsub
    · obtain ⟨s, ff, l⟩ := sf
      simp only at hs hf; subst hs; subst hf
      have hKsub := modalApplyOne_outputs_subset φ0
        (⟨.neg, .box φ, l⟩ : SignedFormula (Proposition Atom) WorldIndex) b acc hb hsf hInv hW
      unfold modalApplyOneFive
      cases hw : witnessWorldS5 b Sign.neg φ with
      | some w' =>
        simp only [hw]
        have hwknown : w' ∈ modalKnownWorlds b :=
          label_mem_modalKnownWorlds (witnessWorldS5_mem hw)
        have hwle : w' ≤ modalWorldBound φ0 :=
          le_trans (known_label_le_modalMaxWorld_Five hwknown) (le_of_lt hW)
        have hφsub : φ ∈ modalSubfmls φ0 := by
          have hform : Proposition.box φ ∈ modalSubfmls φ0 :=
            modalUniverse_mem_formula_Five (hb _ hsf)
          exact modalSubfmls_trans_Five (b := Proposition.box φ)
            (List.mem_cons_of_mem _ (modalSubfmls_self_mem φ)) hform
        intro x hx
        simp only [List.mem_singleton] at hx
        rw [hx]
        exact mem_modalUniverse_of_Five hwle hφsub
      | none =>
        simp only [hw]
        rw [modalApplyOneFiveProp_eq_of_not_boxPos_diaNeg _ b acc (by simp)]
        exact hKsub
  · rw [modalApplyOneFive_eq_of_not_mint_shape sf b acc
        ⟨fun hc => hmint (Or.inl hc), fun hc => hmint (Or.inr hc)⟩] at *
    by_cases hprop : (sf.sign = .pos ∧ ∃ φ, sf.formula = .box φ) ∨
        (sf.sign = .neg ∧ ∃ φ, sf.formula = .diamond φ)
    · rcases hprop with ⟨hs, φ, hf⟩ | ⟨hs, φ, hf⟩
      · obtain ⟨s, ff, l⟩ := sf
        simp only at hs hf; subst hs; subst hf
        have hK := modalApplyOne_boxPos_eq
          (⟨.pos, .box φ, l⟩ : SignedFormula (Proposition Atom) WorldIndex) rfl φ rfl b acc
        have hKsub := modalApplyOne_outputs_subset φ0
          (⟨.pos, .box φ, l⟩ : SignedFormula (Proposition Atom) WorldIndex) b acc hb hsf hInv hW
        simp only [modalApplyOneFiveProp]
        rcases hp : modalApplyOne
            (⟨.pos, .box φ, l⟩ : SignedFormula (Proposition Atom) WorldIndex) b acc
            with ⟨kResult, kAcc⟩
        rw [hp] at hKsub hK
        simp only at hK
        have hφsub : φ ∈ modalSubfmls φ0 := by
          have hform : Proposition.box φ ∈ modalSubfmls φ0 :=
            modalUniverse_mem_formula_Five (hb _ hsf)
          exact modalSubfmls_trans_Five (b := Proposition.box φ)
            (List.mem_cons_of_mem _ (modalSubfmls_self_mem φ)) hform
        have hallNew : ∀ x ∈ modalFiveBoxAll b acc φ l, x ∈ modalUniverse φ0 := by
          intro x hx
          obtain ⟨hxeq, hxknown, -, -⟩ := modalFiveBoxAll_mem hx
          have hxle : x.label ≤ modalWorldBound φ0 :=
            le_trans (known_label_le_modalMaxWorld_Five hxknown) (le_of_lt hW)
          rw [hxeq]; exact mem_modalUniverse_of_Five hxle hφsub
        rcases hK with hK | ⟨out0, hK⟩ <;> subst hK
        · -- kResult = .notApplicable
          simp only
          split_ifs with hemp
          · trivial
          · exact hallNew
        · -- kResult = .persistent out0
          simp only at hKsub ⊢
          intro x hx
          simp only [List.mem_append, List.mem_filter] at hx
          rcases hx with hx | ⟨hx, -⟩
          · exact hKsub x hx
          · exact hallNew x hx
      · obtain ⟨s, ff, l⟩ := sf
        simp only at hs hf; subst hs; subst hf
        have hK := modalApplyOne_diamondNeg_eq
          (⟨.neg, .diamond φ, l⟩ : SignedFormula (Proposition Atom) WorldIndex) rfl φ rfl b acc
        have hKsub := modalApplyOne_outputs_subset φ0
          (⟨.neg, .diamond φ, l⟩ : SignedFormula (Proposition Atom) WorldIndex) b acc hb hsf
            hInv hW
        simp only [modalApplyOneFiveProp]
        rcases hp : modalApplyOne
            (⟨.neg, .diamond φ, l⟩ : SignedFormula (Proposition Atom) WorldIndex) b acc
            with ⟨kResult, kAcc⟩
        rw [hp] at hKsub hK
        simp only at hK
        have hφsub : φ ∈ modalSubfmls φ0 := by
          have hform : Proposition.diamond φ ∈ modalSubfmls φ0 :=
            modalUniverse_mem_formula_Five (hb _ hsf)
          exact modalSubfmls_trans_Five (b := Proposition.diamond φ)
            (List.mem_cons_of_mem _ (modalSubfmls_self_mem φ)) hform
        have hallNew : ∀ x ∈ modalFiveDiaNegAll b acc φ l, x ∈ modalUniverse φ0 := by
          intro x hx
          obtain ⟨hxeq, hxknown, -, -⟩ := modalFiveDiaNegAll_mem hx
          have hxle : x.label ≤ modalWorldBound φ0 :=
            le_trans (known_label_le_modalMaxWorld_Five hxknown) (le_of_lt hW)
          rw [hxeq]; exact mem_modalUniverse_of_Five hxle hφsub
        rcases hK with hK | ⟨out0, hK⟩ <;> subst hK
        · -- kResult = .notApplicable
          simp only
          split_ifs with hemp
          · trivial
          · exact hallNew
        · -- kResult = .persistent out0
          simp only at hKsub ⊢
          intro x hx
          simp only [List.mem_append, List.mem_filter] at hx
          rcases hx with hx | ⟨hx, -⟩
          · exact hKsub x hx
          · exact hallNew x hx
    · rw [modalApplyOneFiveProp_eq_of_not_boxPos_diaNeg sf b acc
          ⟨fun hc => hprop (Or.inl hc), fun hc => hprop (Or.inr hc)⟩] at *
      exact modalApplyOne_outputs_subset φ0 sf b acc hb hsf hInv hW

/-- **F12' discharge for `modalApplyOneFive`**: the diamond-positive witness-reuse field,
existentially quantified on the witness world. Mirrors `modalApplyOneS5w_diaPosWitness'`. -/
private lemma modalApplyOneFive_diaPosWitness'
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (ψ : Proposition Atom) (w : WorldIndex) :
    ∃ w', (modalApplyOneFive (⟨.pos, .diamond ψ, w⟩ : SignedFormula (Proposition Atom) WorldIndex)
        b acc).snd = acc.addEdge w w' ∧
      ∃ rest,
        (modalApplyOneFive (⟨.pos, .diamond ψ, w⟩ : SignedFormula (Proposition Atom) WorldIndex)
            b acc).fst
          = RuleResult.linear
              ((⟨.pos, ψ, w'⟩ : SignedFormula (Proposition Atom) WorldIndex) :: rest) := by
  simp only [modalApplyOneFive]
  cases h : witnessWorldS5 b .pos ψ with
  | some w' => exact ⟨w', by simp, [], by simp⟩
  | none =>
    obtain ⟨hsnd, rest, hfst⟩ := modalApplyOne_diamondPos_witness b acc ψ w
    have heq := modalApplyOneFiveProp_eq_of_not_boxPos_diaNeg
      (⟨.pos, .diamond ψ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) b acc (by simp)
    simp only [heq]
    exact ⟨modalNextWorld b, hsnd, rest, hfst⟩

/-- **F11' discharge for `modalApplyOneFive`**, symmetric to `modalApplyOneFive_diaPosWitness'`. -/
private lemma modalApplyOneFive_boxNegWitness'
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (ψ : Proposition Atom) (w : WorldIndex) :
    ∃ w', (modalApplyOneFive (⟨.neg, .box ψ, w⟩ : SignedFormula (Proposition Atom) WorldIndex)
        b acc).snd = acc.addEdge w w' ∧
      ∃ rest,
        (modalApplyOneFive (⟨.neg, .box ψ, w⟩ : SignedFormula (Proposition Atom) WorldIndex)
            b acc).fst
          = RuleResult.linear
              ((⟨.neg, ψ, w'⟩ : SignedFormula (Proposition Atom) WorldIndex) :: rest) := by
  simp only [modalApplyOneFive]
  cases h : witnessWorldS5 b .neg ψ with
  | some w' => exact ⟨w', by simp, [], by simp⟩
  | none =>
    obtain ⟨hsnd, rest, hfst⟩ := modalApplyOne_boxNeg_witness b acc ψ w
    have heq := modalApplyOneFiveProp_eq_of_not_boxPos_diaNeg
      (⟨.neg, .box ψ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) b acc (by simp)
    simp only [heq]
    exact ⟨modalNextWorld b, hsnd, rest, hfst⟩

/-! ## Reachability Bridge (Task 515 Phase 19)

The remaining Phase 19 soundness assembly (`modalTableauFive_sound`, `FrameSoundness.lean`) needs
two structural facts about `modalApplyOneFive`/`modalApplyOneFiveProp`, mirroring the S5 chain's
`modalApplyOneS5_knownWorlds_step` (`S5Simplification.lean`) and `modalApplyOneS5w_s5SoundSpec`
(`FrameSoundness.lean`). Since Five has only the one shipped rule (no separate unguarded/witness
staging), both are stated directly, without the `RuleApply`/`S5SoundSpec` abstraction layer S5
needed to cover two distinct rules. -/

/-- The Five analogue of K's `modalApplyOne_knownWorlds_step`, stated directly over
`modalApplyOneFiveProp` (the non-reuse propagation rule, exact structural analogue of
`modalApplyOneS5`): either `modalApplyOneFiveProp` leaves `acc` unchanged with every emitted
formula's label a known world of `b` (covering both the ordinary agreement shapes, via
`modalApplyOneFiveProp_eq_of_not_boxPos_diaNeg` + K's own step lemma, and the two Five-relevant
propagation shapes, via `modalApplyOneFiveProp_boxPos_diaNeg_eq`), or it mints exactly one edge
with a nonempty `.linear` result entirely labeled at `modalNextWorld b` (only possible at the two
K-minting shapes, disjoint from the two propagation-relevant shapes, so `modalApplyOneFiveProp`
agrees with K there too). Mirrors `modalApplyOneS5_knownWorlds_step`. -/
lemma modalApplyOneFiveProp_knownWorlds_step
    (sf : SignedFormula (Proposition Atom) WorldIndex)
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (hsfmem : sf ∈ b) (hknown : accTargetsKnown b acc) :
    ((modalApplyOneFiveProp sf b acc).snd = acc ∧
      (match (modalApplyOneFiveProp sf b acc).fst with
        | .linear formulas => ∀ x ∈ formulas, x.label ∈ modalKnownWorlds b
        | .branching branches => ∀ x ∈ branches.flatten, x.label ∈ modalKnownWorlds b
        | .persistent formulas => ∀ x ∈ formulas, x.label ∈ modalKnownWorlds b
        | .notApplicable => True)) ∨
    ((modalApplyOneFiveProp sf b acc).snd = acc.addEdge sf.label (modalNextWorld b) ∧
      (match (modalApplyOneFiveProp sf b acc).fst with
        | .linear formulas => formulas ≠ [] ∧ ∀ x ∈ formulas, x.label = modalNextWorld b
        | .branching _ => False
        | .persistent _ => False
        | .notApplicable => False)) := by
  by_cases hbd : (sf.sign = .pos ∧ ∃ φ, sf.formula = .box φ) ∨
      (sf.sign = .neg ∧ ∃ φ, sf.formula = .diamond φ)
  · obtain ⟨hsndeq, hor⟩ := modalApplyOneFiveProp_boxPos_diaNeg_eq sf b acc hsfmem hknown hbd
    refine Or.inl ⟨hsndeq, ?_⟩
    rcases hor with hnot | ⟨out, hpers, hlabel⟩
    · rw [hnot]; trivial
    · rw [hpers]; exact hlabel
  · have hnbox : ¬ (sf.sign = .pos ∧ ∃ φ, sf.formula = .box φ) := fun hc => hbd (Or.inl hc)
    have hndia : ¬ (sf.sign = .neg ∧ ∃ φ, sf.formula = .diamond φ) := fun hc => hbd (Or.inr hc)
    rw [modalApplyOneFiveProp_eq_of_not_boxPos_diaNeg sf b acc ⟨hnbox, hndia⟩]
    exact modalApplyOne_knownWorlds_step sf b acc hsfmem hknown

/-- `modalApplyOneFive` either agrees with `modalApplyOneFiveProp` outright, or fires a witness
reuse -- emitting `.linear [sf']` for a signed formula `sf'` already present on the branch, plus
the single edge `sf.label → sf'.label`. The Five analogue of `modalApplyOneS5w_s5SoundSpec`,
stated directly (no `RuleApply`/`S5SoundSpec` abstraction needed, since Five has only the one
shipped rule). This is the per-call dichotomy the remaining Phase 19 assembly
(`FrameSoundness.lean`) consumes in place of threading an `S5SoundSpec`-style hypothesis. -/
lemma modalApplyOneFive_agree_or_reuse
    (sf : SignedFormula (Proposition Atom) WorldIndex)
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility) :
    modalApplyOneFive sf b acc = modalApplyOneFiveProp sf b acc ∨
    ∃ sf' : SignedFormula (Proposition Atom) WorldIndex,
      sf' ∈ b ∧ modalApplyOneFive sf b acc =
        (RuleResult.linear [sf'], acc.addEdge sf.label sf'.label) := by
  obtain ⟨s, ff, w⟩ := sf
  rcases s with _ | _ <;> rcases ff with _ | _ | ⟨a, c⟩ | ⟨x, y⟩ | ⟨x, y⟩ | φ | φ
  case pos.diamond =>
    unfold modalApplyOneFive
    cases hw : witnessWorldS5 b Sign.pos φ with
    | none => exact Or.inl (by simp only [hw])
    | some w' => exact Or.inr ⟨⟨.pos, φ, w'⟩, witnessWorldS5_mem hw, by simp only [hw]⟩
  case neg.box =>
    unfold modalApplyOneFive
    cases hw : witnessWorldS5 b Sign.neg φ with
    | none => exact Or.inl (by simp only [hw])
    | some w' => exact Or.inr ⟨⟨.neg, φ, w'⟩, witnessWorldS5_mem hw, by simp only [hw]⟩
  all_goals exact Or.inl (modalApplyOneFive_eq_of_not_mint_shape _ b acc (by simp))

/-- **`modalApplyOneFive` satisfies `RuleApplicationSpecCore`**: the witness-reuse root-aware rule
discharges every field the Hintikka/saturation machinery needs, mirroring
`modalApplyOneS5w_specCore` declaration-for-declaration. This is the interface witness Phase 21's
parametric Hintikka lift will consume to get 5-completeness for free. -/
theorem modalApplyOneFive_specCore :
    RuleApplicationSpecCore (Atom := Atom) modalApplyOneFive where
  freshLocal := modalApplyOneFive_fresh_local
  outputsSubsetUniverse := modalApplyOneFive_outputsSubsetUniverse
  persistentFresh := modalApplyOneFive_persistentFresh
  branchingLength := modalApplyOneFive_branchingLength
  localShapeInvariance := modalApplyOneFive_localShapeInvariance
  boxPosNotExpanding := modalApplyOneFive_boxPosNotExpanding
  diaNegNotExpanding := modalApplyOneFive_diaNegNotExpanding
  boxNegWitness' := modalApplyOneFive_boxNegWitness'
  diaPosWitness' := modalApplyOneFive_diaPosWitness'

end Cslib.Logic.Modal.Tableau

end
