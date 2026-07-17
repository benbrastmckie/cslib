/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Modal.Tableau.GenericDriver
public import Cslib.Logics.Modal.Tableau.S5Simplification
public import Mathlib.Data.Prod.Basic
public import Mathlib.Data.Nat.Basic
import Mathlib.Tactic.Ring

/-! # 5/KB5 Rooted-Cluster Tableau Simplification

This module defines the root-aware universal-propagation rule `modalApplyOneFive`, the 5/KB5
analogue of `S5Simplification.lean`'s `modalApplyOneS5w`. It realises the Euclidean (not
necessarily reflexive) frame property directly. The mint arms (`T(◇φ)@w`, `F(□φ)@w`) are
shape-identical to `modalApplyOneS5w`'s *except* for the Route (a) root-aware guard (landed
`56a84d07`): a root-triggered mint (`sf.label = 0`) never consults a witness search, so it may
fire even when a non-root witness for the same tag already exists elsewhere on the branch. This
means only `modalOps`/`mintTags`/`S5wTagInv` (and their tag-membership corollaries
`modalApplyOneS5w_diamondPos_tag_mem`/`_boxNeg_tag_mem`) -- all genuinely rule-independent, since
they say nothing about `witnessWorldS5`/`witnessWorldFive` -- apply unchanged, reused verbatim
from `S5Simplification.lean`. The witness-reuse-*specific* pieces (`usedTags`/`S5wWorldInv`/
`modalMaxWorld_lt_worldBound_of_S5w`) do **not** carry over unchanged under the guard; their
Five-local, source-split analogues (`usedTagsFiveNonRoot`/`usedTagsFiveRoot`/`FiveWorldInv`/
`modalMaxWorld_lt_worldBound_of_FiveWorldInv`) are defined near the end of this file
(Phase 19a's termination-bound re-derivation, `reports/08_mint-arm-reuse-route-decision.md`).
Only the two *propagation* arms (`T(□φ)@w`, `F(◇φ)@w`) differ from `modalApplyOneS5w`'s shape
directly (Route 1, landed earlier).

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
- `modalApplyOneFive`: the shipped rule -- Route (a) guarded witness-reuse (`witnessWorldFive`,
  the root-`0`-excluding refinement of Phase 1's `witnessWorldS5`) at the two mint shapes, with a
  root-triggered mint (`sf.label = 0`) never consulting the search at all, falling through to
  `modalApplyOneFiveProp` everywhere else. Mirrors `modalApplyOneS5w`'s shape modulo this guard.
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
witness world is drawn from `modalKnownWorlds b` by `witnessWorldFive`'s own construction, and the
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

/-- **Route (a) root-aware mint-arm witness search**
(`reports/08_mint-arm-reuse-route-decision.md`): the Five-local refinement of `witnessWorldS5`
(`S5Simplification.lean`) that **excludes root `0` from witness candidacy**. Root `0` has
in-degree zero in a rooted tableau (nothing ever emits an edge *into* the root) and
`RightEuclidean` (`fiveFC`) does not relate the root to an arbitrary known world absent a recorded
edge (the two-island adversarial-model kill in `reports/08_*`), so a reuse witness `w' = 0` can
never be soundly justified. Combined with the root-trigger guard on `modalApplyOneFive` below
(which never even consults this search when the trigger is root), this closes both the
root-as-witness and root-as-trigger unsound sub-cases (`reports/08_*`). -/
def witnessWorldFive (b : List (SignedFormula (Proposition Atom) WorldIndex))
    (s : Sign) (φ : Proposition Atom) : Option WorldIndex :=
  (modalKnownWorlds b).find? (fun w' =>
    !(w' == (0 : WorldIndex)) && b.any (· == (⟨s, φ, w'⟩ : SignedFormula _ _)))

omit [Hashable Atom] in
/-- If `witnessWorldFive b s φ = some w'`, then `⟨s, φ, w'⟩` is genuinely present on `b` and
`w' ≠ 0`. -/
lemma witnessWorldFive_mem {b : List (SignedFormula (Proposition Atom) WorldIndex)}
    {s : Sign} {φ : Proposition Atom} {w' : WorldIndex}
    (h : witnessWorldFive b s φ = some w') :
    (⟨s, φ, w'⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b ∧ w' ≠ 0 := by
  have hp := List.find?_some h
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at hp
  obtain ⟨hne, hany⟩ := hp
  refine ⟨by simpa using (List.any_eq_true.mp hany), ?_⟩
  simpa using hne

/-- The shipped 5/KB5 rule: **Route (a) guarded** witness reuse at the two mint shapes
(`reports/08_*`) -- (i) a **root-triggered** mint (`sf.label = 0`) never consults the witness
search and always falls through to a fresh mint (`modalApplyOneFiveProp`, hence K's own mint arm);
(ii) a **non-root-triggered** mint consults `witnessWorldFive` (which itself excludes root `0` as
a candidate witness) and reuses only a genuine non-root witness, falling through to a fresh mint
otherwise. Both guard branches fall through to `modalApplyOneFiveProp`, **never** to
`.notApplicable` -- the mint arm is a strict narrowing of when reuse fires, not a new
`.notApplicable` outcome (verified by `modalApplyOneFive_boxPosNotExpanding`/
`_diaNegNotExpanding`'s shape and the F9/F10-style discharges below, which never depend on the
guard). Mirrors `modalApplyOneS5w`'s shape everywhere except this root split. -/
def modalApplyOneFive : RuleApply Atom := fun sf b acc =>
  match sf.sign, sf.formula with
  | .pos, .diamond φ =>
    (if sf.label == (0 : WorldIndex) then modalApplyOneFiveProp sf b acc
     else
       match witnessWorldFive b .pos φ with
       | some w' => (.linear [⟨.pos, φ, w'⟩], acc.addEdge sf.label w')
       | none => modalApplyOneFiveProp sf b acc)
  | .neg, .box φ =>
    (if sf.label == (0 : WorldIndex) then modalApplyOneFiveProp sf b acc
     else
       match witnessWorldFive b .neg φ with
       | some w' => (.linear [⟨.neg, φ, w'⟩], acc.addEdge sf.label w')
       | none => modalApplyOneFiveProp sf b acc)
  | _, _ => modalApplyOneFiveProp sf b acc

/-- **Case-split helper for the diamond-positive mint shape**, packaging the root-trigger guard
and the `witnessWorldFive` match into the same two-way dichotomy the pre-guard code enjoyed
(`modalApplyOneFive = modalApplyOneFiveProp` either because the trigger is root or because no
non-root witness exists, vs. a genuine non-root reuse). Every downstream consumer of the old
`cases hw : witnessWorldS5 b Sign.pos φ with | none => .. | some w' => ..` pattern rewrites via
this lemma instead. -/
lemma modalApplyOneFive_diaPos_eq_or_reuse
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (φ : Proposition Atom) (w : WorldIndex) :
    (modalApplyOneFive (⟨.pos, .diamond φ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) b acc
       = modalApplyOneFiveProp
           (⟨.pos, .diamond φ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) b acc) ∨
    (∃ w', witnessWorldFive b .pos φ = some w' ∧
      modalApplyOneFive (⟨.pos, .diamond φ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) b acc
        = (RuleResult.linear [⟨.pos, φ, w'⟩], acc.addEdge w w')) := by
  unfold modalApplyOneFive
  dsimp only
  by_cases hz : (w == (0 : WorldIndex)) = true
  · rw [if_pos hz]; exact Or.inl rfl
  · rw [if_neg hz]
    cases hw : witnessWorldFive b .pos φ with
    | none => exact Or.inl rfl
    | some w' => exact Or.inr ⟨w', rfl, rfl⟩

/-- **Case-split helper for the box-negative mint shape**, dual of
`modalApplyOneFive_diaPos_eq_or_reuse`. -/
lemma modalApplyOneFive_boxNeg_eq_or_reuse
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (φ : Proposition Atom) (w : WorldIndex) :
    (modalApplyOneFive (⟨.neg, .box φ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) b acc
       = modalApplyOneFiveProp
           (⟨.neg, .box φ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) b acc) ∨
    (∃ w', witnessWorldFive b .neg φ = some w' ∧
      modalApplyOneFive (⟨.neg, .box φ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) b acc
        = (RuleResult.linear [⟨.neg, φ, w'⟩], acc.addEdge w w')) := by
  unfold modalApplyOneFive
  dsimp only
  by_cases hz : (w == (0 : WorldIndex)) = true
  · rw [if_pos hz]; exact Or.inl rfl
  · rw [if_neg hz]
    cases hw : witnessWorldFive b .neg φ with
    | none => exact Or.inl rfl
    | some w' => exact Or.inr ⟨w', rfl, rfl⟩

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
      rcases modalApplyOneFive_diaPos_eq_or_reuse b acc φ w with heq | ⟨w', hw', heq⟩
      · rw [heq, modalApplyOneFiveProp_eq_of_not_boxPos_diaNeg _ b acc (by simp)]
        exact modalApplyOne_fresh_local _ b acc
      · rw [heq]
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
      rcases modalApplyOneFive_boxNeg_eq_or_reuse b acc φ w with heq | ⟨w', hw', heq⟩
      · rw [heq, modalApplyOneFiveProp_eq_of_not_boxPos_diaNeg _ b acc (by simp)]
        exact modalApplyOne_fresh_local _ b acc
      · rw [heq]
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
      rcases modalApplyOneFive_diaPos_eq_or_reuse b acc φ w with heq | ⟨w', -, heq⟩
      · rw [heq, modalApplyOneFiveProp_eq_of_not_boxPos_diaNeg _ b acc (by simp)] at h
        exact modalApplyOne_branching_length _ b acc brs h
      · rw [heq] at h; simp at h
    · obtain ⟨s, ff, w⟩ := sf
      simp only at hs hf; subst hs; subst hf
      rcases modalApplyOneFive_boxNeg_eq_or_reuse b acc φ w with heq | ⟨w', -, heq⟩
      · rw [heq, modalApplyOneFiveProp_eq_of_not_boxPos_diaNeg _ b acc (by simp)] at h
        exact modalApplyOne_branching_length _ b acc brs h
      · rw [heq] at h; simp at h
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
      rcases modalApplyOneFive_diaPos_eq_or_reuse b acc φ w with heq | ⟨w', -, heq⟩
      · rw [heq, modalApplyOneFiveProp_eq_of_not_boxPos_diaNeg _ b acc (by simp)] at h
        exact modalApplyOne_persistent_props _ b acc nf h
      · rw [heq] at h; simp at h
    · obtain ⟨s, ff, w⟩ := sf
      simp only at hs hf; subst hs; subst hf
      rcases modalApplyOneFive_boxNeg_eq_or_reuse b acc φ w with heq | ⟨w', -, heq⟩
      · rw [heq, modalApplyOneFiveProp_eq_of_not_boxPos_diaNeg _ b acc (by simp)] at h
        exact modalApplyOne_persistent_props _ b acc nf h
      · rw [heq] at h; simp at h
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
      rcases modalApplyOneFive_diaPos_eq_or_reuse b acc φ l with heq | ⟨w', hw', heq⟩
      · rw [heq, modalApplyOneFiveProp_eq_of_not_boxPos_diaNeg _ b acc (by simp)]
        exact hKsub
      · rw [heq]
        have hwknown : w' ∈ modalKnownWorlds b :=
          label_mem_modalKnownWorlds (witnessWorldFive_mem hw').1
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
    · obtain ⟨s, ff, l⟩ := sf
      simp only at hs hf; subst hs; subst hf
      have hKsub := modalApplyOne_outputs_subset φ0
        (⟨.neg, .box φ, l⟩ : SignedFormula (Proposition Atom) WorldIndex) b acc hb hsf hInv hW
      rcases modalApplyOneFive_boxNeg_eq_or_reuse b acc φ l with heq | ⟨w', hw', heq⟩
      · rw [heq, modalApplyOneFiveProp_eq_of_not_boxPos_diaNeg _ b acc (by simp)]
        exact hKsub
      · rw [heq]
        have hwknown : w' ∈ modalKnownWorlds b :=
          label_mem_modalKnownWorlds (witnessWorldFive_mem hw').1
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
  rcases modalApplyOneFive_diaPos_eq_or_reuse b acc ψ w with heqp | ⟨w', -, heqp⟩
  · obtain ⟨hsnd, rest, hfst⟩ := modalApplyOne_diamondPos_witness b acc ψ w
    have heq := modalApplyOneFiveProp_eq_of_not_boxPos_diaNeg
      (⟨.pos, .diamond ψ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) b acc (by simp)
    rw [heqp, heq]
    exact ⟨modalNextWorld b, hsnd, rest, hfst⟩
  · exact ⟨w', by rw [heqp], [], by rw [heqp]⟩

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
  rcases modalApplyOneFive_boxNeg_eq_or_reuse b acc ψ w with heqp | ⟨w', -, heqp⟩
  · obtain ⟨hsnd, rest, hfst⟩ := modalApplyOne_boxNeg_witness b acc ψ w
    have heq := modalApplyOneFiveProp_eq_of_not_boxPos_diaNeg
      (⟨.neg, .box ψ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) b acc (by simp)
    rw [heqp, heq]
    exact ⟨modalNextWorld b, hsnd, rest, hfst⟩
  · exact ⟨w', by rw [heqp], [], by rw [heqp]⟩

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
    rcases modalApplyOneFive_diaPos_eq_or_reuse b acc φ w with heq | ⟨w', hw', heq⟩
    · exact Or.inl heq
    · exact Or.inr ⟨⟨.pos, φ, w'⟩, (witnessWorldFive_mem hw').1, heq⟩
  case neg.box =>
    rcases modalApplyOneFive_boxNeg_eq_or_reuse b acc φ w with heq | ⟨w', hw', heq⟩
    · exact Or.inl heq
    · exact Or.inr ⟨⟨.neg, φ, w'⟩, (witnessWorldFive_mem hw').1, heq⟩
  all_goals exact Or.inl (modalApplyOneFive_eq_of_not_mint_shape _ b acc (by simp))

/-- **Task 515 (Phase 19b)**: strengthens `modalApplyOneFive_diaPos_eq_or_reuse` with the fact
that a reuse call's trigger is never the root -- reuse only fires in the `else` branch of
`modalApplyOneFive`'s `if sf.label == 0 then .. else ..` guard, i.e. exactly when `w ≠ 0`. Needed
by `modalStepBranchFive_preserves_satIn` (`FrameSoundness.lean`) to invoke
`accReachableInv_related_five`, which requires **both** endpoints of a reuse edge to be
non-root. -/
lemma modalApplyOneFive_diaPos_eq_or_reuse_ne_root
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (φ : Proposition Atom) (w : WorldIndex) :
    (modalApplyOneFive (⟨.pos, .diamond φ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) b acc
       = modalApplyOneFiveProp
           (⟨.pos, .diamond φ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) b acc) ∨
    (∃ w', w ≠ 0 ∧ witnessWorldFive b .pos φ = some w' ∧
      modalApplyOneFive (⟨.pos, .diamond φ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) b acc
        = (RuleResult.linear [⟨.pos, φ, w'⟩], acc.addEdge w w')) := by
  unfold modalApplyOneFive
  dsimp only
  by_cases hz : (w == (0 : WorldIndex)) = true
  · rw [if_pos hz]; exact Or.inl rfl
  · rw [if_neg hz]
    have hwne : w ≠ 0 := by simpa using hz
    cases hw : witnessWorldFive b .pos φ with
    | none => exact Or.inl rfl
    | some w' => exact Or.inr ⟨w', hwne, rfl, rfl⟩

/-- **Task 515 (Phase 19b)**: dual of `modalApplyOneFive_diaPos_eq_or_reuse_ne_root` for the
box-negative mint shape. -/
lemma modalApplyOneFive_boxNeg_eq_or_reuse_ne_root
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (φ : Proposition Atom) (w : WorldIndex) :
    (modalApplyOneFive (⟨.neg, .box φ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) b acc
       = modalApplyOneFiveProp
           (⟨.neg, .box φ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) b acc) ∨
    (∃ w', w ≠ 0 ∧ witnessWorldFive b .neg φ = some w' ∧
      modalApplyOneFive (⟨.neg, .box φ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) b acc
        = (RuleResult.linear [⟨.neg, φ, w'⟩], acc.addEdge w w')) := by
  unfold modalApplyOneFive
  dsimp only
  by_cases hz : (w == (0 : WorldIndex)) = true
  · rw [if_pos hz]; exact Or.inl rfl
  · rw [if_neg hz]
    have hwne : w ≠ 0 := by simpa using hz
    cases hw : witnessWorldFive b .neg φ with
    | none => exact Or.inl rfl
    | some w' => exact Or.inr ⟨w', hwne, rfl, rfl⟩

/-- **Task 515 (Phase 19b)**: `modalApplyOneFive` either agrees with `modalApplyOneFiveProp`
outright, or fires a witness reuse **away from the root, targeting a non-root witness** --
strengthens `modalApplyOneFive_agree_or_reuse` with the `sf.label ≠ 0 ∧ sf'.label ≠ 0` facts
`modalStepBranchFive_preserves_satIn` needs to invoke `accReachableInv_related_five` (which
requires **both** endpoints of a reuse edge to be non-root, unlike S5's
`accReachableInv_related_s5`, which needs no such exclusion since `s5FC` is an equivalence). -/
lemma modalApplyOneFive_agree_or_reuse_ne_root
    (sf : SignedFormula (Proposition Atom) WorldIndex)
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility) :
    modalApplyOneFive sf b acc = modalApplyOneFiveProp sf b acc ∨
    ∃ sf' : SignedFormula (Proposition Atom) WorldIndex,
      sf' ∈ b ∧ sf.label ≠ 0 ∧ sf'.label ≠ 0 ∧ modalApplyOneFive sf b acc =
        (RuleResult.linear [sf'], acc.addEdge sf.label sf'.label) := by
  obtain ⟨s, ff, w⟩ := sf
  rcases s with _ | _ <;> rcases ff with _ | _ | ⟨a, c⟩ | ⟨x, y⟩ | ⟨x, y⟩ | φ | φ
  case pos.diamond =>
    rcases modalApplyOneFive_diaPos_eq_or_reuse_ne_root b acc φ w with
      heq | ⟨w', hwne, hw', heq⟩
    · exact Or.inl heq
    · exact Or.inr
        ⟨⟨.pos, φ, w'⟩, (witnessWorldFive_mem hw').1, hwne, (witnessWorldFive_mem hw').2, heq⟩
  case neg.box =>
    rcases modalApplyOneFive_boxNeg_eq_or_reuse_ne_root b acc φ w with
      heq | ⟨w', hwne, hw', heq⟩
    · exact Or.inl heq
    · exact Or.inr
        ⟨⟨.neg, φ, w'⟩, (witnessWorldFive_mem hw').1, hwne, (witnessWorldFive_mem hw').2, heq⟩
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

/-! ## Source-Split Termination Invariant (Phase 19a Task 2: Route (a) termination re-derivation)

`reports/08_mint-arm-reuse-route-decision.md`'s termination-bound re-derivation, required by the
root-aware mint-arm guard (`witnessWorldFive`/`modalApplyOneFive`, landed `56a84d07`). The LANDED
`S5w*` tag-injection chain (`S5Simplification.lean`) bounds `modalMaxWorld b` by "≤1 mint per
`(sign, formula)` tag, GLOBALLY" -- sound for `modalApplyOneS5w`, whose mint arms always consult
`witnessWorldS5` before minting. Under Five's guard, a root-triggered mint (`sf.label = 0`) never
consults `witnessWorldFive`, so it may fire even when a non-root witness for the *same* tag
already exists elsewhere on the branch -- refining the invariant to "≤1 mint per tag PER
SOURCE-CLASS {root, non-root}" (`reports/08_*`).

`mintTags`/`S5wTagInv` (and their tag-membership corollaries `modalApplyOneS5w_diamondPos_tag_mem`
/`_boxNeg_tag_mem`) are **rule-independent** and reused **verbatim** from `S5Simplification.lean`:
they say nothing about `witnessWorldS5`/`witnessWorldFive` at all, only about branch content and
`φ₀`'s finite subformula structure. Only `usedTags`/`S5wWorldInv`/
`modalMaxWorld_lt_worldBound_of_S5w` are **witness-reuse-specific**, hence need the Five-local,
source-split analogues below: `usedTagsFiveNonRoot`/`usedTagsFiveRoot`/`FiveWorldInv`/
`modalMaxWorld_lt_worldBound_of_FiveWorldInv`.

**Scope note**: this section lands the *static* source-split structures and the final arithmetic
bound (mirroring `S5wWorldInv`/`modalMaxWorld_lt_worldBound_of_S5w`'s own shape, which likewise
take the world-bound invariant as a hypothesis rather than proving it holds at every reachable
branch). The *inductive* step-preservation proof establishing `FiveWorldInv` holds across the
whole fuel-driven expansion (the source-split analogue of `S5wTagInv_S5wWorldInv_step`) is
Phase 19b-scale work, for whatever call site eventually maintains it across the fuel induction --
consistent with `reports/08_*`'s own scoping (`FiveSimplification.lean`'s `outputsSubsetUniverse`
field already takes its world-bound fact as a raw hypothesis parameter, discharged nowhere in this
file yet). -/

omit [Hashable Atom] in
/-- **Non-root usedTags** (Route (a) source-split invariant): the subset of `mintTags φ₀` whose
witness formula already appears at some NON-ROOT world of branch `b`. Matches `witnessWorldFive`'s
own search domain exactly (root `0` excluded), so a `witnessWorldFive`-miss is equivalent to "tag
unused in the non-root source-class" (`witnessWorldFive_none_not_mem_usedTagsFiveNonRoot`, below)
-- the direct analogue of `witnessWorldS5_none_not_mem_usedTags` for the non-root reuse-miss
case. -/
def usedTagsFiveNonRoot (φ₀ : Proposition Atom)
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) :
    Finset (Sign × Proposition Atom) :=
  (mintTags φ₀).filter (fun p =>
    b.any (fun x => (x.sign == p.1 && x.formula == p.2) && !(x.label == (0 : WorldIndex))))

omit [Hashable Atom] in
/-- **Root usedTags** (Route (a) source-split invariant): the subset of `mintTags φ₀` whose
root-mint TRIGGER (`⟨.pos, .diamond ψ, 0⟩` for tag `(pos, ψ)`, `⟨.neg, .box ψ, 0⟩` for tag
`(neg, ψ)`) already appears at world `0` of branch `b`. Since `modalApplyOneFive`'s root-triggered
mint arms never consult a witness search, this source class's contribution to `modalMaxWorld` is
bounded purely by how many DISTINCT triggers can ever appear at the root -- not by a reuse
argument -- exactly `reports/08_*`'s "the root contributes at most one mint per tag, bounded by
the root's own diamond/negated-box subformulas": a formula sitting at the root was never itself
minted (root formulas arrive by decomposition, never via `witnessWorldFive`), so a root-triggered
mint for a given tag is always that tag's first mint in the root source-class, and the driver's
`.linear`-result memoization (`modalStepBranchGen`'s `expanded` bookkeeping, `Saturation.lean`)
ensures the exact trigger occurrence `⟨s, .diamond/.box ψ, 0⟩` fires at most once, so it is that
tag's *only* root-side mint. -/
def usedTagsFiveRoot (φ₀ : Proposition Atom)
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) :
    Finset (Sign × Proposition Atom) :=
  (mintTags φ₀).filter (fun p =>
    b.any (fun x => x.label == (0 : WorldIndex) &&
      ((p.1 == Sign.pos && x.sign == Sign.pos && x.formula == Proposition.diamond p.2) ||
       (p.1 == Sign.neg && x.sign == Sign.neg && x.formula == Proposition.box p.2))))

omit [Hashable Atom] in
/-- `usedTagsFiveNonRoot` is monotone under branch growth. Mirrors `usedTags_mono`. -/
lemma usedTagsFiveNonRoot_mono {φ₀ : Proposition Atom}
    {b b' : List (SignedFormula (Proposition Atom) WorldIndex)} (h : ∀ x ∈ b, x ∈ b') :
    usedTagsFiveNonRoot φ₀ b ⊆ usedTagsFiveNonRoot φ₀ b' := by
  intro p hp
  simp only [usedTagsFiveNonRoot, Finset.mem_filter] at hp ⊢
  obtain ⟨hp1, hp2⟩ := hp
  refine ⟨hp1, ?_⟩
  obtain ⟨x, hx, hxeq⟩ := List.any_eq_true.mp hp2
  exact List.any_eq_true.mpr ⟨x, h x hx, hxeq⟩

omit [Hashable Atom] in
/-- `usedTagsFiveRoot` is monotone under branch growth. Mirrors `usedTags_mono`. -/
lemma usedTagsFiveRoot_mono {φ₀ : Proposition Atom}
    {b b' : List (SignedFormula (Proposition Atom) WorldIndex)} (h : ∀ x ∈ b, x ∈ b') :
    usedTagsFiveRoot φ₀ b ⊆ usedTagsFiveRoot φ₀ b' := by
  intro p hp
  simp only [usedTagsFiveRoot, Finset.mem_filter] at hp ⊢
  obtain ⟨hp1, hp2⟩ := hp
  refine ⟨hp1, ?_⟩
  obtain ⟨x, hx, hxeq⟩ := List.any_eq_true.mp hp2
  exact List.any_eq_true.mpr ⟨x, h x hx, hxeq⟩

omit [Hashable Atom] in
/-- **Non-root mint-tag miss** (Route (a) termination re-derivation task 2, non-root case): the
direct analogue of `witnessWorldS5_none_not_mem_usedTags` for `witnessWorldFive`.
`witnessWorldFive b s φ = none` implies `(s, φ)` is not (yet) a used tag in the NON-ROOT
source-class on `b`: if some non-root `x ∈ b` had `x.sign = s ∧ x.formula = φ`, `witnessWorldFive`'s
`find?` (which searches exactly the non-root known worlds of `b`) would have returned `some _`,
contradicting `= none`. -/
lemma witnessWorldFive_none_not_mem_usedTagsFiveNonRoot {φ₀ : Proposition Atom}
    {b : List (SignedFormula (Proposition Atom) WorldIndex)} {s : Sign} {φ : Proposition Atom}
    (h : witnessWorldFive b s φ = none) : (s, φ) ∉ usedTagsFiveNonRoot φ₀ b := by
  simp only [usedTagsFiveNonRoot, Finset.mem_filter, not_and]
  intro _ hany
  obtain ⟨x, hxmem, hxeq⟩ := List.any_eq_true.mp hany
  simp only [Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq] at hxeq
  obtain ⟨⟨hxs, hxf⟩, hxlabel⟩ := hxeq
  have hxsf : x = (⟨s, φ, x.label⟩ : SignedFormula (Proposition Atom) WorldIndex) := by
    cases x; simp_all
  have hknown : x.label ∈ modalKnownWorlds b :=
    (mem_modalKnownWorlds_Five b x.label).mpr ⟨x, hxmem, rfl⟩
  unfold witnessWorldFive at h
  have hcontra := List.find?_eq_none.mp h x.label hknown
  refine hcontra ?_
  simp only [Bool.and_eq_true, Bool.not_eq_true']
  exact ⟨hxlabel, List.any_eq_true.mpr ⟨x, hxmem, beq_iff_eq.mpr hxsf⟩⟩

omit [Hashable Atom] in
/-- **Root-side mint-tag membership** (Route (a) termination re-derivation task 2, the
root-trigger-always-fresh case): if the root-mint trigger `⟨.pos, .diamond φ, 0⟩` is present on
`b` and `(pos, φ) ∈ mintTags φ₀` (e.g. via `S5wTagInv` + `modalApplyOneS5w_diamondPos_tag_mem`,
both reused verbatim), then `(pos, φ)` is already a member of `usedTagsFiveRoot φ₀ b` -- witnessed
by the trigger itself. Unlike the non-root case, **no "unused" precondition is needed**: the
root-triggered mint arm fires unconditionally, so this fact holds regardless of whether a
witness search would have found anything. -/
lemma diamondPos_root_mem_usedTagsFiveRoot {φ₀ : Proposition Atom}
    {b : List (SignedFormula (Proposition Atom) WorldIndex)} {φ : Proposition Atom}
    (hsf : (⟨.pos, .diamond φ, (0 : WorldIndex)⟩ :
      SignedFormula (Proposition Atom) WorldIndex) ∈ b)
    (htag : (Sign.pos, φ) ∈ mintTags φ₀) :
    (Sign.pos, φ) ∈ usedTagsFiveRoot φ₀ b := by
  simp only [usedTagsFiveRoot, Finset.mem_filter]
  refine ⟨htag, ?_⟩
  exact List.any_eq_true.mpr ⟨_, hsf, by simp⟩

omit [Hashable Atom] in
/-- Dual of `diamondPos_root_mem_usedTagsFiveRoot` for the box-negative mint shape
(`⟨.neg, .box φ, 0⟩`, tag `(neg, φ)`). -/
lemma boxNeg_root_mem_usedTagsFiveRoot {φ₀ : Proposition Atom}
    {b : List (SignedFormula (Proposition Atom) WorldIndex)} {φ : Proposition Atom}
    (hsf : (⟨.neg, .box φ, (0 : WorldIndex)⟩ :
      SignedFormula (Proposition Atom) WorldIndex) ∈ b)
    (htag : (Sign.neg, φ) ∈ mintTags φ₀) :
    (Sign.neg, φ) ∈ usedTagsFiveRoot φ₀ b := by
  simp only [usedTagsFiveRoot, Finset.mem_filter]
  refine ⟨htag, ?_⟩
  exact List.any_eq_true.mpr ⟨_, hsf, by simp⟩

/-- The source-split world-bound invariant (Route (a) termination re-derivation,
`reports/08_*`): `modalMaxWorld b` never exceeds the SUM of the non-root usedTags count and the
root usedTags count. Refines `S5wWorldInv`'s single global count to the "≤1 mint per tag per
source-class {root, non-root}" invariant the guarded mint arms require. -/
def FiveWorldInv (φ₀ : Proposition Atom) (b : List (SignedFormula (Proposition Atom) WorldIndex)) :
    Prop :=
  modalMaxWorld b ≤ (usedTagsFiveNonRoot φ₀ b).card + (usedTagsFiveRoot φ₀ b).card

omit [DecidableEq Atom] [Hashable Atom] in
/-- Arithmetic companion to `modalOps_lt_worldBound` (`S5Simplification.lean`): TWICE `modalOps φ`
still stays strictly under `modalWorldBound φ`, since `modalWorldBound φ = (2c+1)^(c+1)` with
`c := modalComplexity φ` dominates `2c + 1` (`Nat.pow_le_pow_right` at exponent `1`), and
`modalOps φ ≤ c` (`modalOps_le_complexity`) gives `2 * modalOps φ ≤ 2c < 2c + 1 ≤ modalWorldBound
φ`. The larger constant (`2·modalOps φ₀` vs. the S5 chain's `modalOps φ₀`) that Route (a)'s
source-split invariant needs -- still LINEAR, not a worse asymptotic (`reports/08_*`). -/
lemma two_mul_modalOps_lt_worldBound (φ : Proposition Atom) :
    2 * modalOps φ < modalWorldBound φ := by
  have h1 : modalOps φ ≤ modalComplexity φ := modalOps_le_complexity φ
  have h2 : (2 * modalComplexity φ + 1) ≤ modalWorldBound φ := by
    unfold modalWorldBound
    calc (2 * modalComplexity φ + 1) = (2 * modalComplexity φ + 1) ^ 1 := by ring
      _ ≤ (2 * modalComplexity φ + 1) ^ (modalComplexity φ + 1) :=
          Nat.pow_le_pow_right (by omega) (by omega)
  omega

omit [Hashable Atom] in
/-- **Task 3**: chains `FiveWorldInv`, both `usedTagsFiveNonRoot φ₀ b ⊆ mintTags φ₀` and
`usedTagsFiveRoot φ₀ b ⊆ mintTags φ₀` (`Finset.filter_subset`), `mintTags_card_le_modalOps`, and
`two_mul_modalOps_lt_worldBound` into the Five-local world bound: the drop-in, source-split
replacement for `modalMaxWorld_lt_worldBound_of_S5w`, at a larger (but still LINEAR, `≈
2·modalOps φ₀`) constant, matching `outputsSubsetUniverse`'s `hW : modalMaxWorld b <
modalWorldBound φ0` hypothesis shape exactly, so this theorem can discharge that hypothesis at
whatever call site eventually maintains `FiveWorldInv` across Phase 19b's fuel induction. -/
theorem modalMaxWorld_lt_worldBound_of_FiveWorldInv {φ₀ : Proposition Atom}
    {b : List (SignedFormula (Proposition Atom) WorldIndex)} (hW : FiveWorldInv φ₀ b) :
    modalMaxWorld b < modalWorldBound φ₀ := by
  have h1 : (usedTagsFiveNonRoot φ₀ b).card ≤ modalOps φ₀ :=
    le_trans (Finset.card_le_card (Finset.filter_subset _ _)) (mintTags_card_le_modalOps φ₀)
  have h2 : (usedTagsFiveRoot φ₀ b).card ≤ modalOps φ₀ :=
    le_trans (Finset.card_le_card (Finset.filter_subset _ _)) (mintTags_card_le_modalOps φ₀)
  have h3 : 2 * modalOps φ₀ < modalWorldBound φ₀ := two_mul_modalOps_lt_worldBound φ₀
  unfold FiveWorldInv at hW
  calc modalMaxWorld b ≤ (usedTagsFiveNonRoot φ₀ b).card + (usedTagsFiveRoot φ₀ b).card := hW
    _ ≤ modalOps φ₀ + modalOps φ₀ := Nat.add_le_add h1 h2
    _ = 2 * modalOps φ₀ := by ring
    _ < modalWorldBound φ₀ := h3

end Cslib.Logic.Modal.Tableau

end
