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

omit [Hashable Atom] in
/-- **Introduction direction for `modalFiveBoxAll` at a non-root trigger** (task 515 Phase 20),
converse of `modalFiveBoxAll_mem` restricted to `w ≠ 0`: a known, non-root world `v` of `b` not
already carrying `T(φ)@v` on `b` witnesses `T(φ)@v ∈ modalFiveBoxAll b acc φ w`, provided the
trigger `w` itself is non-root (so the propagation target set is the full non-root cluster,
unguarded by any edge condition). Mirrors `modalS5BoxAll_mem_of`, split into the root/non-root
cases `modalFiveBoxAll`'s own definition requires. -/
lemma modalFiveBoxAll_mem_of_ne_root {b : List (SignedFormula (Proposition Atom) WorldIndex)}
    {acc : Accessibility} {φ : Proposition Atom} {w v : WorldIndex}
    (hw : w ≠ (0 : WorldIndex))
    (hknown : v ∈ modalKnownWorlds b) (hvne : v ≠ (0 : WorldIndex))
    (hnotin : (⟨.pos, φ, v⟩ : SignedFormula (Proposition Atom) WorldIndex) ∉ b) :
    (⟨.pos, φ, v⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ modalFiveBoxAll b acc φ w := by
  simp only [modalFiveBoxAll, List.mem_filterMap]
  refine ⟨v, hknown, ?_⟩
  rw [if_neg (by simpa using hvne), if_neg (by simpa using hw), if_neg (by simpa using hnotin)]

omit [Hashable Atom] in
/-- **Introduction direction for `modalFiveBoxAll` at the root trigger** (task 515 Phase 20),
converse of `modalFiveBoxAll_mem` restricted to `w = 0`: a known, non-root world `v` reached from
the root by a genuine recorded edge and not already carrying `T(φ)@v` on `b` witnesses
`T(φ)@v ∈ modalFiveBoxAll b acc φ 0`. Dual case-split of `modalFiveBoxAll_mem_of_ne_root`. -/
lemma modalFiveBoxAll_mem_of_root {b : List (SignedFormula (Proposition Atom) WorldIndex)}
    {acc : Accessibility} {φ : Proposition Atom} {v : WorldIndex}
    (hknown : v ∈ modalKnownWorlds b) (hvne : v ≠ (0 : WorldIndex))
    (hedge : acc.hasEdge 0 v = true)
    (hnotin : (⟨.pos, φ, v⟩ : SignedFormula (Proposition Atom) WorldIndex) ∉ b) :
    (⟨.pos, φ, v⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈
      modalFiveBoxAll b acc φ (0 : WorldIndex) := by
  simp only [modalFiveBoxAll, List.mem_filterMap]
  refine ⟨v, hknown, ?_⟩
  rw [if_neg (by simpa using hvne),
    if_pos (by simp : ((0 : WorldIndex) == (0 : WorldIndex)) = true), if_pos hedge,
    if_neg (by simpa using hnotin)]

omit [Hashable Atom] in
/-- **Introduction direction for `modalFiveDiaNegAll` at a non-root trigger**, dual of
`modalFiveBoxAll_mem_of_ne_root`. -/
lemma modalFiveDiaNegAll_mem_of_ne_root {b : List (SignedFormula (Proposition Atom) WorldIndex)}
    {acc : Accessibility} {φ : Proposition Atom} {w v : WorldIndex}
    (hw : w ≠ (0 : WorldIndex))
    (hknown : v ∈ modalKnownWorlds b) (hvne : v ≠ (0 : WorldIndex))
    (hnotin : (⟨.neg, φ, v⟩ : SignedFormula (Proposition Atom) WorldIndex) ∉ b) :
    (⟨.neg, φ, v⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈
      modalFiveDiaNegAll b acc φ w := by
  simp only [modalFiveDiaNegAll, List.mem_filterMap]
  refine ⟨v, hknown, ?_⟩
  rw [if_neg (by simpa using hvne), if_neg (by simpa using hw), if_neg (by simpa using hnotin)]

omit [Hashable Atom] in
/-- **Introduction direction for `modalFiveDiaNegAll` at the root trigger**, dual of
`modalFiveBoxAll_mem_of_root`. -/
lemma modalFiveDiaNegAll_mem_of_root {b : List (SignedFormula (Proposition Atom) WorldIndex)}
    {acc : Accessibility} {φ : Proposition Atom} {v : WorldIndex}
    (hknown : v ∈ modalKnownWorlds b) (hvne : v ≠ (0 : WorldIndex))
    (hedge : acc.hasEdge 0 v = true)
    (hnotin : (⟨.neg, φ, v⟩ : SignedFormula (Proposition Atom) WorldIndex) ∉ b) :
    (⟨.neg, φ, v⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈
      modalFiveDiaNegAll b acc φ (0 : WorldIndex) := by
  simp only [modalFiveDiaNegAll, List.mem_filterMap]
  refine ⟨v, hknown, ?_⟩
  rw [if_neg (by simpa using hvne),
    if_pos (by simp : ((0 : WorldIndex) == (0 : WorldIndex)) = true), if_pos hedge,
    if_neg (by simpa using hnotin)]

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

/-! ## KB5 Instantiation (task 515 Phase 22)

**Factor, not clone.** `modalApplyOneFive`'s tableau rule is **purely syntactic**: it is a
function of the branch and the accessibility relation alone, and its definition (and every field
of `RuleApplicationSpecCore modalApplyOneFive` above) never inspects a frame condition. Its
soundness proof (`modalTableauFive_sound`, `FrameSoundness.lean`) shows that a branch the rule
closes is unsatisfiable on **every** Euclidean frame (`fiveFC`). Since
`kb5FC := Std.Symm r ∧ Relation.RightEuclidean r` is *strictly stronger* than
`fiveFC := Relation.RightEuclidean r` (every KB5 frame is, in particular, a Five frame -- the
`Std.Symm` conjunct only narrows the frame class further), a branch unsatisfiable on every
Euclidean frame is unsatisfiable on every KB5 frame too. **The unmodified `modalApplyOneFive`
rule is therefore already a sound KB5 tableau rule**: no cloned rule, root-aware mint-arm guard,
or Phase 18/19a/19b-style termination-bound re-derivation is needed for soundness.
`modalApplyOneKb5` below is a plain alias for `modalApplyOneFive`, and
`modalApplyOneKb5_specCore`/`modalTableauKb5` transfer by definitional equality -- the entire KB5
driver chain reduces to `rfl` against its Five counterpart. This is *cheaper* than the literal
three-way clone the plan flags as a fallback, because the syntactic rule genuinely does not
depend on which frame condition its soundness proof targets; only the **semantic** wrapper
differs, and that lives in `FrameSoundness.lean`
(`fiveValid_imp_kb5Valid`/`modalTableauKb5_sound`) as a frame-class-monotonicity corollary, not a
re-derived fuel-induction chain.

This factoring is sound *only* for the soundness direction (`.closed → kb5Valid`): completeness
(`kb5Valid → .closed`, task 515 Phase 23) is a genuinely different question, since `kb5Valid` is
strictly weaker than `fiveValid` (`kb5FC` is a proper subclass of `fiveFC`-frames) and may hold on
formulas the Five tableau leaves open. Phase 23's own extraction (`extractModelKb5`) is expected
to need a bespoke symmetric-model construction from an open KB5 branch; that is out of this
phase's scope.

**Update**: the alias above stays in place (it is still the cheapest sound-only route and nothing
below retires it), but a `FrameCompleteness.lean` blocker note (retained there as documentation)
identified that *completeness* needs a genuinely different, KB5-specific rule -- reaching into the
full known non-root cluster on a root trigger, rather than `modalApplyOneFive`'s edge-gated root
arm. That rule now exists alongside this alias: see `modalApplyOneKb5'` (`## KB5-Specific
Full-Cluster Propagation Rule` section below), its own `RuleApplicationSpecCore` instance
(`modalApplyOneKb5'_specCore`), and its own direct-against-`kb5FC` soundness theorem
(`modalTableauKb5'_sound`, `FrameSoundness.lean` -- proved without this section's
frame-class-monotonicity shortcut, which is unsound for `modalApplyOneKb5'`'s unrestricted root
propagation). `modalApplyOneKb5'` itself is complete only up to a shallow root-only repair, still
insufficient in general (`FrameCompleteness.lean`'s blocker note above has the full witness); full
KB5 completeness is delivered by the corrected-gate rule beside it instead (`## The Corrected-Gate
KB5 Rule` section below: `modalApplyOneKb5''`, and `FrameCompleteness.lean`'s
`modalTableauKb5''_complete`/`kb5Valid_decides`/`instDecidableKb5Valid`). -/

/-- The KB5 tableau rule: **literally** `modalApplyOneFive`, not a clone -- see this section's
module note for the "factor, not clone" argument. -/
def modalApplyOneKb5 : RuleApply Atom := modalApplyOneFive

/-- `modalApplyOneKb5` satisfies `RuleApplicationSpecCore`: definitionally `modalApplyOneFive`'s
own witness, since `modalApplyOneKb5 = modalApplyOneFive` by `rfl`. -/
theorem modalApplyOneKb5_specCore :
    RuleApplicationSpecCore (Atom := Atom) modalApplyOneKb5 :=
  modalApplyOneFive_specCore

/-- One-step branch expansion for the KB5 (symmetric-Euclidean-frame) tableau: the generic driver
instantiated at `apply := modalApplyOneKb5` (= `modalApplyOneFive`). -/
def modalStepBranchKb5
    (b e : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility) :
    Option (List (List (SignedFormula (Proposition Atom) WorldIndex)) ×
            List (List (SignedFormula (Proposition Atom) WorldIndex)) ×
            Accessibility) :=
  modalStepBranchGen modalApplyOneKb5 b e acc

/-- Fuel-based expansion of a list of KB5-system branches. -/
def modalExpandBranchesKb5
    (branches expandedSets : List (List (SignedFormula (Proposition Atom) WorldIndex)))
    (accs : List Accessibility) (fuel : Nat) : ModalTableauResult Atom :=
  modalExpandBranchesGen modalApplyOneKb5 branches expandedSets accs fuel

/-- The KB5-system (symmetric-Euclidean-frame) modal tableau **decision procedure**: the generic
entry point instantiated at `apply := modalApplyOneKb5`, starting the signed tableau from `F(φ)`
at world `0`. -/
def modalTableauKb5 (φ : Proposition Atom) : ModalTableauResult Atom :=
  modalTableauGen modalApplyOneKb5 φ

/-- `modalStepBranchKb5` is exactly `modalStepBranchGen modalApplyOneKb5` -- true `rfl`. -/
theorem modalStepBranchKb5_eq
    (b e : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility) :
    modalStepBranchKb5 b e acc = modalStepBranchGen modalApplyOneKb5 b e acc := rfl

/-- `modalExpandBranchesKb5` is exactly `modalExpandBranchesGen modalApplyOneKb5` -- true `rfl`.
-/
theorem modalExpandBranchesKb5_eq
    (branches expandedSets : List (List (SignedFormula (Proposition Atom) WorldIndex)))
    (accs : List Accessibility) (fuel : Nat) :
    modalExpandBranchesKb5 branches expandedSets accs fuel =
      modalExpandBranchesGen modalApplyOneKb5 branches expandedSets accs fuel := rfl

/-- `modalTableauKb5` is exactly `modalTableauGen modalApplyOneKb5` -- true `rfl`. -/
theorem modalTableauKb5_eq (φ : Proposition Atom) :
    modalTableauKb5 φ = modalTableauGen modalApplyOneKb5 φ := rfl

/-- **`modalTableauKb5` coincides with `modalTableauFive`**: both instantiate the generic driver
at the same underlying rule (`modalApplyOneKb5 = modalApplyOneFive` by `rfl`). This is the bridge
`FrameSoundness.lean`'s `modalTableauKb5_sound` composes with `modalTableauFive_sound`. -/
theorem modalTableauKb5_eq_modalTableauFive (φ : Proposition Atom) :
    modalTableauKb5 φ = modalTableauFive φ := rfl

/-! ## KB5-Specific Full-Cluster Propagation Rule (task 524)

`modalApplyOneKb5 := modalApplyOneFive` (the "factor, not clone" alias above) is sound for KB5 but
not *complete*: `FrameCompleteness.lean`'s Phase 23 blocker note (`extractModelKb5_root_reach_scout`
et al.) shows `extractModelKb5`'s forced relation (`Relation.EuclGen (Relation.SymmGen
acc.hasEdge)`) relates the root `0` to **every** world reachable via a raw-edge chain, not merely
to `modalFiveBoxAll`/`modalFiveDiaNegAll`'s edge-gated direct successors. Reaching completeness
needs a genuinely new rule whose root-triggered box-positive/diamond-negative propagation (i) dumps
to the **full** known non-root cluster unconditionally -- matching the non-root arm's own
unconditional propagation, since the model forces the root into the same equivalence class as
everyone it can reach (`Relation.rooted_cluster_isEquiv`/`Relation.rooted_mem_cod`) -- and (ii)
propagates the root's own content back onto world `0` itself whenever the known cluster is
nonempty, since a symmetric right-Euclidean root with *any* successor is reflexive
(`Relation.symm_rightEuclidean_root_refl`, `Euclidean.lean:362`). This is unsound for the *larger*
`fiveFC` class (Five's root need not be reflexive, and an edge-isolated Five root need not relate
to a disconnected branch world), so it cannot be an alias of `modalApplyOneFive`; it gets its own
name, its own `RuleApplicationSpecCore` instance, and its own soundness theorem, proved directly
against `kb5FC` (`FrameSoundness.lean`) -- the `fiveValid_imp_kb5Valid` frame-class-monotonicity
shortcut is unavailable for this direction. The mint (existential) shapes `.pos .diamond`/
`.neg .box` are **untouched**: they retain `modalApplyOneFive`'s witness-reuse behavior verbatim
(root-triggered mints still fall through to a fresh K-style mint, never consulting
`witnessWorldFive`), since universally asserting a diamond/box-negative witness at every known
world would turn an existential claim into an unsound universal one -- only the two *universal*
propagation shapes change. -/

/-- **Full-cluster root-aware propagation for box-positives** (task 524): the KB5-specific
analogue of `modalFiveBoxAll`. The non-root targets (`nonRootTargets`, computed once) are
*unconditional* -- every known non-root world of `b`, regardless of whether the trigger `w` is
the root or not, exactly matching `modalFiveBoxAll`'s own non-root arm and dropping its root-arm
`acc.hasEdge 0 w'` restriction entirely (justified by `Relation.rooted_cluster_isEquiv`/
`Relation.rooted_mem_cod`: the model forces every reachable non-root world into the root's own
equivalence class regardless of a *direct* recorded edge). An **additional** self-target `w' = 0`
fires only when the trigger `w` is itself the root **and** the known cluster already has some
non-root member (`Relation.symm_rightEuclidean_root_refl`: a symmetric right-Euclidean root with
any successor is reflexive) -- the guard that keeps this rule sound on an edge-isolated-root KB5
model, where `□p → p` may still fail vacuously. -/
def modalKb5BoxAllFull (b : List (SignedFormula (Proposition Atom) WorldIndex))
    (φ : Proposition Atom) (w : WorldIndex) :
    List (SignedFormula (Proposition Atom) WorldIndex) :=
  let nonRootTargets : List (SignedFormula (Proposition Atom) WorldIndex) :=
    (modalKnownWorlds b).filterMap fun w' =>
      if w' == (0 : WorldIndex) then none
      else
        let sf : SignedFormula (Proposition Atom) WorldIndex := ⟨.pos, φ, w'⟩
        if b.any (· == sf) then none else some sf
  if w == (0 : WorldIndex) && (modalKnownWorlds b).any (fun v => !(v == (0 : WorldIndex))) then
    let sf0 : SignedFormula (Proposition Atom) WorldIndex := ⟨.pos, φ, (0 : WorldIndex)⟩
    nonRootTargets ++ (if b.any (· == sf0) then [] else [sf0])
  else
    nonRootTargets

/-- **Full-cluster root-aware propagation for diamond-negatives**, dual of `modalKb5BoxAllFull`.
-/
def modalKb5DiaNegAllFull (b : List (SignedFormula (Proposition Atom) WorldIndex))
    (φ : Proposition Atom) (w : WorldIndex) :
    List (SignedFormula (Proposition Atom) WorldIndex) :=
  let nonRootTargets : List (SignedFormula (Proposition Atom) WorldIndex) :=
    (modalKnownWorlds b).filterMap fun w' =>
      if w' == (0 : WorldIndex) then none
      else
        let sf : SignedFormula (Proposition Atom) WorldIndex := ⟨.neg, φ, w'⟩
        if b.any (· == sf) then none else some sf
  if w == (0 : WorldIndex) && (modalKnownWorlds b).any (fun v => !(v == (0 : WorldIndex))) then
    let sf0 : SignedFormula (Proposition Atom) WorldIndex := ⟨.neg, φ, (0 : WorldIndex)⟩
    nonRootTargets ++ (if b.any (· == sf0) then [] else [sf0])
  else
    nonRootTargets

omit [Hashable Atom] in
/-- Membership dichotomy for `modalKb5BoxAllFull`: every emitted formula is fresh (`x ∉ b`) and
either (a) targets a known non-root world (the unconditional cluster-dump arm), or (b) is the
self-target `⟨.pos, φ, 0⟩`, which only fires when the trigger `w` is itself the root and the
known cluster has some other, non-root member `v` (the cluster-nonempty witness the soundness
proof's `symm_rightEuclidean_root_refl` application needs). -/
lemma modalKb5BoxAllFull_mem {b : List (SignedFormula (Proposition Atom) WorldIndex)}
    {φ : Proposition Atom} {w : WorldIndex}
    {x : SignedFormula (Proposition Atom) WorldIndex} (h : x ∈ modalKb5BoxAllFull b φ w) :
    x ∉ b ∧
    ((x = (⟨.pos, φ, x.label⟩ : SignedFormula (Proposition Atom) WorldIndex) ∧
        x.label ∈ modalKnownWorlds b ∧ x.label ≠ 0) ∨
     (x = (⟨.pos, φ, (0 : WorldIndex)⟩ : SignedFormula (Proposition Atom) WorldIndex) ∧
        w = (0 : WorldIndex) ∧ ∃ v ∈ modalKnownWorlds b, v ≠ (0 : WorldIndex))) := by
  unfold modalKb5BoxAllFull at h
  dsimp only at h
  by_cases hgate :
      (w == (0 : WorldIndex) && (modalKnownWorlds b).any (fun v => !(v == (0 : WorldIndex))))
        = true
  · rw [if_pos hgate] at h
    simp only [Bool.and_eq_true, beq_iff_eq] at hgate
    obtain ⟨hw0, hcluster⟩ := hgate
    simp only [List.any_eq_true, Bool.not_eq_true', beq_eq_false_iff_ne, ne_eq] at hcluster
    obtain ⟨v, hv, hvne⟩ := hcluster
    by_cases hmem0 :
        (b.any (· == (⟨.pos, φ, (0 : WorldIndex)⟩ : SignedFormula (Proposition Atom) WorldIndex)))
          = true
    · rw [if_pos hmem0] at h
      simp only [List.append_nil, List.mem_filterMap] at h
      obtain ⟨u, hu, heq⟩ := h
      by_cases huz : (u == (0 : WorldIndex)) = true
      · rw [if_pos huz] at heq; exact absurd heq (by simp)
      · rw [if_neg huz] at heq
        by_cases humem :
            (b.any (· == (⟨.pos, φ, u⟩ : SignedFormula (Proposition Atom) WorldIndex))) = true
        · rw [if_pos humem] at heq; exact absurd heq (by simp)
        · rw [if_neg humem] at heq
          obtain rfl : (⟨.pos, φ, u⟩ : SignedFormula (Proposition Atom) WorldIndex) = x := by
            injection heq
          refine ⟨by simpa using humem, Or.inl ⟨rfl, hu, ?_⟩⟩
          simpa using huz
    · rw [if_neg hmem0] at h
      simp only [List.mem_append, List.mem_filterMap, List.mem_singleton] at h
      rcases h with ⟨u, hu, heq⟩ | heq
      · by_cases huz : (u == (0 : WorldIndex)) = true
        · rw [if_pos huz] at heq; exact absurd heq (by simp)
        · rw [if_neg huz] at heq
          by_cases humem :
              (b.any (· == (⟨.pos, φ, u⟩ : SignedFormula (Proposition Atom) WorldIndex))) = true
          · rw [if_pos humem] at heq; exact absurd heq (by simp)
          · rw [if_neg humem] at heq
            obtain rfl : (⟨.pos, φ, u⟩ : SignedFormula (Proposition Atom) WorldIndex) = x := by
              injection heq
            refine ⟨by simpa using humem, Or.inl ⟨rfl, hu, ?_⟩⟩
            simpa using huz
      · subst heq
        exact ⟨by simpa using hmem0, Or.inr ⟨rfl, hw0, v, hv, hvne⟩⟩
  · rw [if_neg hgate] at h
    simp only [List.mem_filterMap] at h
    obtain ⟨u, hu, heq⟩ := h
    by_cases huz : (u == (0 : WorldIndex)) = true
    · rw [if_pos huz] at heq; exact absurd heq (by simp)
    · rw [if_neg huz] at heq
      by_cases humem :
          (b.any (· == (⟨.pos, φ, u⟩ : SignedFormula (Proposition Atom) WorldIndex))) = true
      · rw [if_pos humem] at heq; exact absurd heq (by simp)
      · rw [if_neg humem] at heq
        obtain rfl : (⟨.pos, φ, u⟩ : SignedFormula (Proposition Atom) WorldIndex) = x := by
          injection heq
        refine ⟨by simpa using humem, Or.inl ⟨rfl, hu, ?_⟩⟩
        simpa using huz

omit [Hashable Atom] in
/-- Membership dichotomy for `modalKb5DiaNegAllFull`, dual of `modalKb5BoxAllFull_mem`. -/
lemma modalKb5DiaNegAllFull_mem {b : List (SignedFormula (Proposition Atom) WorldIndex)}
    {φ : Proposition Atom} {w : WorldIndex}
    {x : SignedFormula (Proposition Atom) WorldIndex} (h : x ∈ modalKb5DiaNegAllFull b φ w) :
    x ∉ b ∧
    ((x = (⟨.neg, φ, x.label⟩ : SignedFormula (Proposition Atom) WorldIndex) ∧
        x.label ∈ modalKnownWorlds b ∧ x.label ≠ 0) ∨
     (x = (⟨.neg, φ, (0 : WorldIndex)⟩ : SignedFormula (Proposition Atom) WorldIndex) ∧
        w = (0 : WorldIndex) ∧ ∃ v ∈ modalKnownWorlds b, v ≠ (0 : WorldIndex))) := by
  unfold modalKb5DiaNegAllFull at h
  dsimp only at h
  by_cases hgate :
      (w == (0 : WorldIndex) && (modalKnownWorlds b).any (fun v => !(v == (0 : WorldIndex))))
        = true
  · rw [if_pos hgate] at h
    simp only [Bool.and_eq_true, beq_iff_eq] at hgate
    obtain ⟨hw0, hcluster⟩ := hgate
    simp only [List.any_eq_true, Bool.not_eq_true', beq_eq_false_iff_ne, ne_eq] at hcluster
    obtain ⟨v, hv, hvne⟩ := hcluster
    by_cases hmem0 :
        (b.any (· == (⟨.neg, φ, (0 : WorldIndex)⟩ : SignedFormula (Proposition Atom) WorldIndex)))
          = true
    · rw [if_pos hmem0] at h
      simp only [List.append_nil, List.mem_filterMap] at h
      obtain ⟨u, hu, heq⟩ := h
      by_cases huz : (u == (0 : WorldIndex)) = true
      · rw [if_pos huz] at heq; exact absurd heq (by simp)
      · rw [if_neg huz] at heq
        by_cases humem :
            (b.any (· == (⟨.neg, φ, u⟩ : SignedFormula (Proposition Atom) WorldIndex))) = true
        · rw [if_pos humem] at heq; exact absurd heq (by simp)
        · rw [if_neg humem] at heq
          obtain rfl : (⟨.neg, φ, u⟩ : SignedFormula (Proposition Atom) WorldIndex) = x := by
            injection heq
          refine ⟨by simpa using humem, Or.inl ⟨rfl, hu, ?_⟩⟩
          simpa using huz
    · rw [if_neg hmem0] at h
      simp only [List.mem_append, List.mem_filterMap, List.mem_singleton] at h
      rcases h with ⟨u, hu, heq⟩ | heq
      · by_cases huz : (u == (0 : WorldIndex)) = true
        · rw [if_pos huz] at heq; exact absurd heq (by simp)
        · rw [if_neg huz] at heq
          by_cases humem :
              (b.any (· == (⟨.neg, φ, u⟩ : SignedFormula (Proposition Atom) WorldIndex))) = true
          · rw [if_pos humem] at heq; exact absurd heq (by simp)
          · rw [if_neg humem] at heq
            obtain rfl : (⟨.neg, φ, u⟩ : SignedFormula (Proposition Atom) WorldIndex) = x := by
              injection heq
            refine ⟨by simpa using humem, Or.inl ⟨rfl, hu, ?_⟩⟩
            simpa using huz
      · subst heq
        exact ⟨by simpa using hmem0, Or.inr ⟨rfl, hw0, v, hv, hvne⟩⟩
  · rw [if_neg hgate] at h
    simp only [List.mem_filterMap] at h
    obtain ⟨u, hu, heq⟩ := h
    by_cases huz : (u == (0 : WorldIndex)) = true
    · rw [if_pos huz] at heq; exact absurd heq (by simp)
    · rw [if_neg huz] at heq
      by_cases humem :
          (b.any (· == (⟨.neg, φ, u⟩ : SignedFormula (Proposition Atom) WorldIndex))) = true
      · rw [if_pos humem] at heq; exact absurd heq (by simp)
      · rw [if_neg humem] at heq
        obtain rfl : (⟨.neg, φ, u⟩ : SignedFormula (Proposition Atom) WorldIndex) = x := by
          injection heq
        refine ⟨by simpa using humem, Or.inl ⟨rfl, hu, ?_⟩⟩
        simpa using huz

omit [Hashable Atom] in
/-- Every emitted formula's label is a known world of `b`, regardless of which case of
`modalKb5BoxAllFull_mem`'s dichotomy produced it -- the general fact `outputsSubsetUniverse`/
`persistentFresh` (Phase 4) need. -/
lemma modalKb5BoxAllFull_mem_known {b : List (SignedFormula (Proposition Atom) WorldIndex)}
    {φ : Proposition Atom} {w : WorldIndex}
    {x : SignedFormula (Proposition Atom) WorldIndex} (h : x ∈ modalKb5BoxAllFull b φ w)
    (hw : w ∈ modalKnownWorlds b) : x.label ∈ modalKnownWorlds b := by
  rcases (modalKb5BoxAllFull_mem h).2 with ⟨_, hkn, _⟩ | ⟨hxeq, hw0, _⟩
  · exact hkn
  · rw [hxeq]; dsimp only; rw [← hw0]; exact hw

omit [Hashable Atom] in
/-- Dual of `modalKb5BoxAllFull_mem_known` for `modalKb5DiaNegAllFull`. -/
lemma modalKb5DiaNegAllFull_mem_known {b : List (SignedFormula (Proposition Atom) WorldIndex)}
    {φ : Proposition Atom} {w : WorldIndex}
    {x : SignedFormula (Proposition Atom) WorldIndex} (h : x ∈ modalKb5DiaNegAllFull b φ w)
    (hw : w ∈ modalKnownWorlds b) : x.label ∈ modalKnownWorlds b := by
  rcases (modalKb5DiaNegAllFull_mem h).2 with ⟨_, hkn, _⟩ | ⟨hxeq, hw0, _⟩
  · exact hkn
  · rw [hxeq]; dsimp only; rw [← hw0]; exact hw

omit [Hashable Atom] in
/-- Every emitted formula's shape is `⟨.pos, φ, x.label⟩` regardless of which case of
`modalKb5BoxAllFull_mem`'s dichotomy produced it. -/
lemma modalKb5BoxAllFull_mem_eq {b : List (SignedFormula (Proposition Atom) WorldIndex)}
    {φ : Proposition Atom} {w : WorldIndex} {x : SignedFormula (Proposition Atom) WorldIndex}
    (h : x ∈ modalKb5BoxAllFull b φ w) :
    x = (⟨.pos, φ, x.label⟩ : SignedFormula (Proposition Atom) WorldIndex) := by
  rcases (modalKb5BoxAllFull_mem h).2 with ⟨heq, -, -⟩ | ⟨heq, -, -⟩
  · exact heq
  · subst heq; rfl

omit [Hashable Atom] in
/-- Dual of `modalKb5BoxAllFull_mem_eq` for `modalKb5DiaNegAllFull`. -/
lemma modalKb5DiaNegAllFull_mem_eq {b : List (SignedFormula (Proposition Atom) WorldIndex)}
    {φ : Proposition Atom} {w : WorldIndex} {x : SignedFormula (Proposition Atom) WorldIndex}
    (h : x ∈ modalKb5DiaNegAllFull b φ w) :
    x = (⟨.neg, φ, x.label⟩ : SignedFormula (Proposition Atom) WorldIndex) := by
  rcases (modalKb5DiaNegAllFull_mem h).2 with ⟨heq, -, -⟩ | ⟨heq, -, -⟩
  · exact heq
  · subst heq; rfl

/-! ## Rule Application (task 524) -/

/-- Apply the K modal rules together with the KB5 full-cluster propagation arms. Mirrors
`modalApplyOneFiveProp` declaration-for-declaration, substituting `modalKb5BoxAllFull`/
`modalKb5DiaNegAllFull` for `modalFiveBoxAll`/`modalFiveDiaNegAll`. -/
def modalApplyOneKb5'Prop
    (sf : SignedFormula (Proposition Atom) WorldIndex)
    (b : List (SignedFormula (Proposition Atom) WorldIndex))
    (acc : Accessibility) :
    RuleResult (Proposition Atom) WorldIndex × Accessibility :=
  let (kResult, kAcc) := modalApplyOne sf b acc
  match sf.sign, sf.formula with
  | .pos, .box φ =>
    let allNew := modalKb5BoxAllFull b φ sf.label
    match kResult with
    | .persistent kForms =>
      (.persistent (kForms ++ allNew.filter (fun x => !(kForms.any (· == x)))), kAcc)
    | .notApplicable =>
      if allNew.isEmpty then (.notApplicable, kAcc) else (.persistent allNew, kAcc)
    | other => (other, kAcc)
  | .neg, .diamond φ =>
    let allNew := modalKb5DiaNegAllFull b φ sf.label
    match kResult with
    | .persistent kForms =>
      (.persistent (kForms ++ allNew.filter (fun x => !(kForms.any (· == x)))), kAcc)
    | .notApplicable =>
      if allNew.isEmpty then (.notApplicable, kAcc) else (.persistent allNew, kAcc)
    | other => (other, kAcc)
  | _, _ => (kResult, kAcc)

omit [Hashable Atom] in
/-- `modalApplyOneKb5'Prop` agrees with `modalApplyOne` outside the two propagation shapes.
Mirrors `modalApplyOneFiveProp_eq_of_not_boxPos_diaNeg`. -/
lemma modalApplyOneKb5'Prop_eq_of_not_boxPos_diaNeg
    (sf : SignedFormula (Proposition Atom) WorldIndex)
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (h : ¬ (sf.sign = .pos ∧ ∃ φ, sf.formula = .box φ) ∧
         ¬ (sf.sign = .neg ∧ ∃ φ, sf.formula = .diamond φ)) :
    modalApplyOneKb5'Prop sf b acc = modalApplyOne sf b acc := by
  obtain ⟨h1, h2⟩ := h
  unfold modalApplyOneKb5'Prop
  rcases hs : sf.sign with _ | _ <;> rcases hf : sf.formula with _ | _ | _ | _ | _ | φ | φ <;>
    simp_all

/-- At the two propagation shapes, `modalApplyOneKb5'Prop` never mints (its accessibility output
is exactly K's, unchanged) and only appends formulas at existing known worlds. Mirrors
`modalApplyOneFiveProp_boxPos_diaNeg_eq`. -/
lemma modalApplyOneKb5'Prop_boxPos_diaNeg_eq
    (sf : SignedFormula (Proposition Atom) WorldIndex)
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (hsfmem : sf ∈ b) (hknown : accTargetsKnown b acc)
    (h : (sf.sign = .pos ∧ ∃ φ, sf.formula = .box φ) ∨
         (sf.sign = .neg ∧ ∃ φ, sf.formula = .diamond φ)) :
    (modalApplyOneKb5'Prop sf b acc).snd = acc ∧
    ((modalApplyOneKb5'Prop sf b acc).fst = .notApplicable ∨
      ∃ out, (modalApplyOneKb5'Prop sf b acc).fst = .persistent out ∧
        ∀ x ∈ out, x.label ∈ modalKnownWorlds b) := by
  rcases h with ⟨hs, φ, hf⟩ | ⟨hs, φ, hf⟩
  · obtain ⟨s, ff, l⟩ := sf
    simp only at hs hf
    subst hs; subst hf
    have hK := modalApplyOne_boxPos_eq
      (⟨.pos, .box φ, l⟩ : SignedFormula (Proposition Atom) WorldIndex) rfl φ rfl b acc
    have hKW := modalApplyOne_knownWorlds_step
      (⟨.pos, .box φ, l⟩ : SignedFormula (Proposition Atom) WorldIndex) b acc hsfmem hknown
    unfold modalApplyOneKb5'Prop
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
        exact (modalKb5BoxAllFull_mem hx).2.elim (fun ⟨_, hkn, _⟩ => hkn)
          (fun ⟨hxeq, hw0, _⟩ => by
            rw [hxeq]; dsimp only; rw [← hw0]
            exact label_mem_modalKnownWorlds hsfmem)
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
      · exact (modalKb5BoxAllFull_mem hx).2.elim (fun ⟨_, hkn, _⟩ => hkn)
          (fun ⟨hxeq, hw0, _⟩ => by
            rw [hxeq]; dsimp only; rw [← hw0]
            exact label_mem_modalKnownWorlds hsfmem)
  · obtain ⟨s, ff, l⟩ := sf
    simp only at hs hf
    subst hs; subst hf
    have hK := modalApplyOne_diamondNeg_eq
      (⟨.neg, .diamond φ, l⟩ : SignedFormula (Proposition Atom) WorldIndex) rfl φ rfl b acc
    have hKW := modalApplyOne_knownWorlds_step
      (⟨.neg, .diamond φ, l⟩ : SignedFormula (Proposition Atom) WorldIndex) b acc hsfmem hknown
    unfold modalApplyOneKb5'Prop
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
        exact (modalKb5DiaNegAllFull_mem hx).2.elim (fun ⟨_, hkn, _⟩ => hkn)
          (fun ⟨hxeq, hw0, _⟩ => by
            rw [hxeq]; dsimp only; rw [← hw0]
            exact label_mem_modalKnownWorlds hsfmem)
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
      · exact (modalKb5DiaNegAllFull_mem hx).2.elim (fun ⟨_, hkn, _⟩ => hkn)
          (fun ⟨hxeq, hw0, _⟩ => by
            rw [hxeq]; dsimp only; rw [← hw0]
            exact label_mem_modalKnownWorlds hsfmem)

/-- The Kb5' analogue of K's `modalApplyOne_knownWorlds_step`, stated directly over
`modalApplyOneKb5'Prop`. Mirrors `modalApplyOneFiveProp_knownWorlds_step`. Needed by
`modalStepBranchKb5'_preserves_accReachableInv` (`FrameSoundness.lean`). -/
lemma modalApplyOneKb5'Prop_knownWorlds_step
    (sf : SignedFormula (Proposition Atom) WorldIndex)
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (hsfmem : sf ∈ b) (hknown : accTargetsKnown b acc) :
    ((modalApplyOneKb5'Prop sf b acc).snd = acc ∧
      (match (modalApplyOneKb5'Prop sf b acc).fst with
        | .linear formulas => ∀ x ∈ formulas, x.label ∈ modalKnownWorlds b
        | .branching branches => ∀ x ∈ branches.flatten, x.label ∈ modalKnownWorlds b
        | .persistent formulas => ∀ x ∈ formulas, x.label ∈ modalKnownWorlds b
        | .notApplicable => True)) ∨
    ((modalApplyOneKb5'Prop sf b acc).snd = acc.addEdge sf.label (modalNextWorld b) ∧
      (match (modalApplyOneKb5'Prop sf b acc).fst with
        | .linear formulas => formulas ≠ [] ∧ ∀ x ∈ formulas, x.label = modalNextWorld b
        | .branching _ => False
        | .persistent _ => False
        | .notApplicable => False)) := by
  by_cases hbd : (sf.sign = .pos ∧ ∃ φ, sf.formula = .box φ) ∨
      (sf.sign = .neg ∧ ∃ φ, sf.formula = .diamond φ)
  · obtain ⟨hsndeq, hor⟩ := modalApplyOneKb5'Prop_boxPos_diaNeg_eq sf b acc hsfmem hknown hbd
    refine Or.inl ⟨hsndeq, ?_⟩
    rcases hor with hnot | ⟨out, hpers, hlabel⟩
    · rw [hnot]; trivial
    · rw [hpers]; exact hlabel
  · have hnbox : ¬ (sf.sign = .pos ∧ ∃ φ, sf.formula = .box φ) := fun hc => hbd (Or.inl hc)
    have hndia : ¬ (sf.sign = .neg ∧ ∃ φ, sf.formula = .diamond φ) := fun hc => hbd (Or.inr hc)
    rw [modalApplyOneKb5'Prop_eq_of_not_boxPos_diaNeg sf b acc ⟨hnbox, hndia⟩]
    exact modalApplyOne_knownWorlds_step sf b acc hsfmem hknown

/-! ## The KB5 Full-Cluster Rule -/

/-- **The new KB5-specific rule** (task 524): the mint (existential) shapes are
`modalApplyOneFive`'s witness-reuse behavior, verbatim and unchanged; only the two propagation
(universal) shapes differ, routing through `modalApplyOneKb5'Prop` instead of
`modalApplyOneFiveProp`. NOT an alias of `modalApplyOneFive`: its root-triggered propagation is
strictly more permissive (full cluster, plus self), sound only for `kb5FC`. -/
def modalApplyOneKb5' : RuleApply Atom := fun sf b acc =>
  match sf.sign, sf.formula with
  | .pos, .diamond φ =>
    (if sf.label == (0 : WorldIndex) then modalApplyOneKb5'Prop sf b acc
     else
       match witnessWorldFive b .pos φ with
       | some w' => (.linear [⟨.pos, φ, w'⟩], acc.addEdge sf.label w')
       | none => modalApplyOneKb5'Prop sf b acc)
  | .neg, .box φ =>
    (if sf.label == (0 : WorldIndex) then modalApplyOneKb5'Prop sf b acc
     else
       match witnessWorldFive b .neg φ with
       | some w' => (.linear [⟨.neg, φ, w'⟩], acc.addEdge sf.label w')
       | none => modalApplyOneKb5'Prop sf b acc)
  | _, _ => modalApplyOneKb5'Prop sf b acc

/-- Case-split helper for the diamond-positive mint shape, mirrors
`modalApplyOneFive_diaPos_eq_or_reuse`. -/
lemma modalApplyOneKb5'_diaPos_eq_or_reuse
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (φ : Proposition Atom) (w : WorldIndex) :
    (modalApplyOneKb5' (⟨.pos, .diamond φ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) b acc
       = modalApplyOneKb5'Prop
           (⟨.pos, .diamond φ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) b acc) ∨
    (∃ w', witnessWorldFive b .pos φ = some w' ∧
      modalApplyOneKb5' (⟨.pos, .diamond φ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) b acc
        = (RuleResult.linear [⟨.pos, φ, w'⟩], acc.addEdge w w')) := by
  unfold modalApplyOneKb5'
  dsimp only
  by_cases hz : (w == (0 : WorldIndex)) = true
  · rw [if_pos hz]; exact Or.inl rfl
  · rw [if_neg hz]
    cases hw : witnessWorldFive b .pos φ with
    | none => exact Or.inl rfl
    | some w' => exact Or.inr ⟨w', rfl, rfl⟩

/-- Case-split helper for the box-negative mint shape, dual of
`modalApplyOneKb5'_diaPos_eq_or_reuse`. -/
lemma modalApplyOneKb5'_boxNeg_eq_or_reuse
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (φ : Proposition Atom) (w : WorldIndex) :
    (modalApplyOneKb5' (⟨.neg, .box φ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) b acc
       = modalApplyOneKb5'Prop
           (⟨.neg, .box φ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) b acc) ∨
    (∃ w', witnessWorldFive b .neg φ = some w' ∧
      modalApplyOneKb5' (⟨.neg, .box φ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) b acc
        = (RuleResult.linear [⟨.neg, φ, w'⟩], acc.addEdge w w')) := by
  unfold modalApplyOneKb5'
  dsimp only
  by_cases hz : (w == (0 : WorldIndex)) = true
  · rw [if_pos hz]; exact Or.inl rfl
  · rw [if_neg hz]
    cases hw : witnessWorldFive b .neg φ with
    | none => exact Or.inl rfl
    | some w' => exact Or.inr ⟨w', rfl, rfl⟩

/-- Free bridge: on the box-positive (propagation, non-mint) shape, `modalApplyOneKb5'` falls
through to `modalApplyOneKb5'Prop` by the definitional `| _, _ =>` catch-all -- `rfl`. -/
lemma modalApplyOneKb5'_boxPos_eq
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (φ : Proposition Atom) (w : WorldIndex) :
    modalApplyOneKb5' (⟨.pos, .box φ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) b acc
      = modalApplyOneKb5'Prop
          (⟨.pos, .box φ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) b acc :=
  rfl

/-- Free bridge, dual of `modalApplyOneKb5'_boxPos_eq`. -/
lemma modalApplyOneKb5'_diaNeg_eq
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (φ : Proposition Atom) (w : WorldIndex) :
    modalApplyOneKb5' (⟨.neg, .diamond φ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) b acc
      = modalApplyOneKb5'Prop
          (⟨.neg, .diamond φ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) b acc :=
  rfl

/-- `modalApplyOneKb5'` agrees with `modalApplyOneKb5'Prop` outside the two mint shapes. Mirrors
`modalApplyOneFive_eq_of_not_mint_shape`. -/
lemma modalApplyOneKb5'_eq_of_not_mint_shape
    (sf : SignedFormula (Proposition Atom) WorldIndex)
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (h : ¬ (sf.sign = .pos ∧ ∃ φ, sf.formula = .diamond φ) ∧
         ¬ (sf.sign = .neg ∧ ∃ φ, sf.formula = .box φ)) :
    modalApplyOneKb5' sf b acc = modalApplyOneKb5'Prop sf b acc := by
  obtain ⟨h1, h2⟩ := h
  unfold modalApplyOneKb5'
  rcases hs : sf.sign with _ | _ <;> rcases hf : sf.formula with _ | _ | _ | _ | _ | φ | φ <;>
    simp_all

/-- **Task 524**: strengthens `modalApplyOneKb5'_diaPos_eq_or_reuse` with the fact that a reuse
call's trigger is never the root -- reuse only fires in the `else` branch of
`modalApplyOneKb5'`'s `if sf.label == 0 then .. else ..` guard, i.e. exactly when `w ≠ 0`. Mirrors
`modalApplyOneFive_diaPos_eq_or_reuse_ne_root`. -/
lemma modalApplyOneKb5'_diaPos_eq_or_reuse_ne_root
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (φ : Proposition Atom) (w : WorldIndex) :
    (modalApplyOneKb5' (⟨.pos, .diamond φ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) b acc
       = modalApplyOneKb5'Prop
           (⟨.pos, .diamond φ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) b acc) ∨
    (∃ w', w ≠ 0 ∧ witnessWorldFive b .pos φ = some w' ∧
      modalApplyOneKb5' (⟨.pos, .diamond φ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) b acc
        = (RuleResult.linear [⟨.pos, φ, w'⟩], acc.addEdge w w')) := by
  unfold modalApplyOneKb5'
  dsimp only
  by_cases hz : (w == (0 : WorldIndex)) = true
  · rw [if_pos hz]; exact Or.inl rfl
  · rw [if_neg hz]
    have hwne : w ≠ 0 := by simpa using hz
    cases hw : witnessWorldFive b .pos φ with
    | none => exact Or.inl rfl
    | some w' => exact Or.inr ⟨w', hwne, rfl, rfl⟩

/-- **Task 524**: dual of `modalApplyOneKb5'_diaPos_eq_or_reuse_ne_root` for the box-negative
mint shape. Mirrors `modalApplyOneFive_boxNeg_eq_or_reuse_ne_root`. -/
lemma modalApplyOneKb5'_boxNeg_eq_or_reuse_ne_root
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (φ : Proposition Atom) (w : WorldIndex) :
    (modalApplyOneKb5' (⟨.neg, .box φ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) b acc
       = modalApplyOneKb5'Prop
           (⟨.neg, .box φ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) b acc) ∨
    (∃ w', w ≠ 0 ∧ witnessWorldFive b .neg φ = some w' ∧
      modalApplyOneKb5' (⟨.neg, .box φ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) b acc
        = (RuleResult.linear [⟨.neg, φ, w'⟩], acc.addEdge w w')) := by
  unfold modalApplyOneKb5'
  dsimp only
  by_cases hz : (w == (0 : WorldIndex)) = true
  · rw [if_pos hz]; exact Or.inl rfl
  · rw [if_neg hz]
    have hwne : w ≠ 0 := by simpa using hz
    cases hw : witnessWorldFive b .neg φ with
    | none => exact Or.inl rfl
    | some w' => exact Or.inr ⟨w', hwne, rfl, rfl⟩

/-- `modalApplyOneKb5'` either agrees with `modalApplyOneKb5'Prop` outright, or fires a witness
reuse away from the root, targeting a non-root witness (verbatim `modalApplyOneFive` mint
behavior). Mirrors `modalApplyOneFive_agree_or_reuse_ne_root`. -/
lemma modalApplyOneKb5'_agree_or_reuse_ne_root
    (sf : SignedFormula (Proposition Atom) WorldIndex)
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility) :
    modalApplyOneKb5' sf b acc = modalApplyOneKb5'Prop sf b acc ∨
    ∃ sf' : SignedFormula (Proposition Atom) WorldIndex,
      sf' ∈ b ∧ sf.label ≠ 0 ∧ sf'.label ≠ 0 ∧ modalApplyOneKb5' sf b acc =
        (RuleResult.linear [sf'], acc.addEdge sf.label sf'.label) := by
  obtain ⟨s, ff, w⟩ := sf
  rcases s with _ | _ <;> rcases ff with _ | _ | ⟨a, c⟩ | ⟨x, y⟩ | ⟨x, y⟩ | φ | φ
  case pos.diamond =>
    rcases modalApplyOneKb5'_diaPos_eq_or_reuse_ne_root b acc φ w with
      heq | ⟨w', hwne, hw', heq⟩
    · exact Or.inl heq
    · exact Or.inr
        ⟨⟨.pos, φ, w'⟩, (witnessWorldFive_mem hw').1, hwne, (witnessWorldFive_mem hw').2, heq⟩
  case neg.box =>
    rcases modalApplyOneKb5'_boxNeg_eq_or_reuse_ne_root b acc φ w with
      heq | ⟨w', hwne, hw', heq⟩
    · exact Or.inl heq
    · exact Or.inr
        ⟨⟨.neg, φ, w'⟩, (witnessWorldFive_mem hw').1, hwne, (witnessWorldFive_mem hw').2, heq⟩
  all_goals exact Or.inl (modalApplyOneKb5'_eq_of_not_mint_shape _ b acc (by simp))

/-- Plain (non-root-excluded) agree-or-reuse dichotomy for `modalApplyOneKb5'`, mirrors
`modalApplyOneFive_agree_or_reuse`. Needed by `modalStepBranchKb5'_preserves_accReachableInv`
(`FrameSoundness.lean`), which does not need the root exclusion. -/
lemma modalApplyOneKb5'_agree_or_reuse
    (sf : SignedFormula (Proposition Atom) WorldIndex)
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility) :
    modalApplyOneKb5' sf b acc = modalApplyOneKb5'Prop sf b acc ∨
    ∃ sf' : SignedFormula (Proposition Atom) WorldIndex,
      sf' ∈ b ∧ modalApplyOneKb5' sf b acc =
        (RuleResult.linear [sf'], acc.addEdge sf.label sf'.label) := by
  obtain ⟨s, ff, w⟩ := sf
  rcases s with _ | _ <;> rcases ff with _ | _ | ⟨a, c⟩ | ⟨x, y⟩ | ⟨x, y⟩ | φ | φ
  case pos.diamond =>
    rcases modalApplyOneKb5'_diaPos_eq_or_reuse b acc φ w with heq | ⟨w', hw', heq⟩
    · exact Or.inl heq
    · exact Or.inr ⟨⟨.pos, φ, w'⟩, (witnessWorldFive_mem hw').1, heq⟩
  case neg.box =>
    rcases modalApplyOneKb5'_boxNeg_eq_or_reuse b acc φ w with heq | ⟨w', hw', heq⟩
    · exact Or.inl heq
    · exact Or.inr ⟨⟨.neg, φ, w'⟩, (witnessWorldFive_mem hw').1, heq⟩
  all_goals exact Or.inl (modalApplyOneKb5'_eq_of_not_mint_shape _ b acc (by simp))

/-! ## Driver Instantiation (task 524) -/

/-- One-step branch expansion for the new KB5 full-cluster tableau: the generic driver
instantiated at `apply := modalApplyOneKb5'`. -/
def modalStepBranchKb5'
    (b e : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility) :
    Option (List (List (SignedFormula (Proposition Atom) WorldIndex)) ×
            List (List (SignedFormula (Proposition Atom) WorldIndex)) ×
            Accessibility) :=
  modalStepBranchGen modalApplyOneKb5' b e acc

/-- Fuel-based expansion of a list of KB5 full-cluster-system branches. -/
def modalExpandBranchesKb5'
    (branches expandedSets : List (List (SignedFormula (Proposition Atom) WorldIndex)))
    (accs : List Accessibility) (fuel : Nat) : ModalTableauResult Atom :=
  modalExpandBranchesGen modalApplyOneKb5' branches expandedSets accs fuel

/-- The KB5 full-cluster modal tableau **decision procedure**: the generic entry point
instantiated at `apply := modalApplyOneKb5'`, starting the signed tableau from `F(φ)` at world
`0`. -/
def modalTableauKb5' (φ : Proposition Atom) : ModalTableauResult Atom :=
  modalTableauGen modalApplyOneKb5' φ

/-- `modalStepBranchKb5'` is exactly `modalStepBranchGen modalApplyOneKb5'` -- true `rfl`. -/
theorem modalStepBranchKb5'_eq
    (b e : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility) :
    modalStepBranchKb5' b e acc = modalStepBranchGen modalApplyOneKb5' b e acc := rfl

/-- `modalExpandBranchesKb5'` is exactly `modalExpandBranchesGen modalApplyOneKb5'` -- true `rfl`.
-/
theorem modalExpandBranchesKb5'_eq
    (branches expandedSets : List (List (SignedFormula (Proposition Atom) WorldIndex)))
    (accs : List Accessibility) (fuel : Nat) :
    modalExpandBranchesKb5' branches expandedSets accs fuel =
      modalExpandBranchesGen modalApplyOneKb5' branches expandedSets accs fuel := rfl

/-- `modalTableauKb5'` is exactly `modalTableauGen modalApplyOneKb5'` -- true `rfl`. -/
theorem modalTableauKb5'_eq (φ : Proposition Atom) :
    modalTableauKb5' φ = modalTableauGen modalApplyOneKb5' φ := rfl

/-! ## The Corrected-Gate KB5 Rule

`modalTruthLemmaKb5` is mathematically FALSE for `modalApplyOneKb5'`'s 0-target propagation arm,
witnessed by `extractModelKb5_nonRoot_boxPos_gap` (`FrameCompleteness.lean`) at `φ₀ = ¬◇◇□p`. The
root cause is a single misplaced boolean gate: the 0-target arm of `modalKb5BoxAllFull`/
`modalKb5DiaNegAllFull` fires on `w == 0 && clusterNonempty` (trigger-identity) when it must fire
on `clusterNonempty` alone -- `extractModelKb5`'s forced relation is already the *total/universal*
cluster on the connected edge-touched world set (`Relation.EuclGen (Relation.SymmGen
acc.hasEdge)` over a connected symmetric graph is total on its field), so the self-target `w' = 0`
formula must propagate regardless of *which* world triggered the rule, not only when the trigger
happens to be the root itself. This section clones the frozen `*Full` helpers into `*Univ`
siblings with exactly that one gate change, and clones the dispatcher/entry point around them.
The frozen `modalApplyOneKb5'`/`modalTableauKb5'`/`modalKb5BoxAllFull`/`modalKb5DiaNegAllFull`
above are left byte-for-byte untouched; the new rule sits beside them. -/

/-- **Corrected-gate full-cluster propagation for box-positives**: identical to
`modalKb5BoxAllFull` except the self-target `w' = 0` arm fires whenever the known cluster has any
non-root member, regardless of whether the trigger `w` is itself the root. This is the gate fix:
dropping the `w == 0` conjunct from `modalKb5BoxAllFull`'s guard. Sound because a symmetric
right-Euclidean root with any successor is reflexive (`Relation.symm_rightEuclidean_root_refl`)
independently of which world raised `T(□φ)` first -- the forced relation is already total on the
cluster, so any non-root trigger's box-positive content belongs at the root too. -/
def modalKb5BoxAllUniv (b : List (SignedFormula (Proposition Atom) WorldIndex))
    (φ : Proposition Atom) (_w : WorldIndex) :
    List (SignedFormula (Proposition Atom) WorldIndex) :=
  let nonRootTargets : List (SignedFormula (Proposition Atom) WorldIndex) :=
    (modalKnownWorlds b).filterMap fun w' =>
      if w' == (0 : WorldIndex) then none
      else
        let sf : SignedFormula (Proposition Atom) WorldIndex := ⟨.pos, φ, w'⟩
        if b.any (· == sf) then none else some sf
  if (modalKnownWorlds b).any (fun v => !(v == (0 : WorldIndex))) then
    let sf0 : SignedFormula (Proposition Atom) WorldIndex := ⟨.pos, φ, (0 : WorldIndex)⟩
    nonRootTargets ++ (if b.any (· == sf0) then [] else [sf0])
  else
    nonRootTargets

/-- **Corrected-gate full-cluster propagation for diamond-negatives**, dual of
`modalKb5BoxAllUniv`. -/
def modalKb5DiaNegAllUniv (b : List (SignedFormula (Proposition Atom) WorldIndex))
    (φ : Proposition Atom) (_w : WorldIndex) :
    List (SignedFormula (Proposition Atom) WorldIndex) :=
  let nonRootTargets : List (SignedFormula (Proposition Atom) WorldIndex) :=
    (modalKnownWorlds b).filterMap fun w' =>
      if w' == (0 : WorldIndex) then none
      else
        let sf : SignedFormula (Proposition Atom) WorldIndex := ⟨.neg, φ, w'⟩
        if b.any (· == sf) then none else some sf
  if (modalKnownWorlds b).any (fun v => !(v == (0 : WorldIndex))) then
    let sf0 : SignedFormula (Proposition Atom) WorldIndex := ⟨.neg, φ, (0 : WorldIndex)⟩
    nonRootTargets ++ (if b.any (· == sf0) then [] else [sf0])
  else
    nonRootTargets

omit [Hashable Atom] in
/-- **Trigger-free membership dichotomy** for `modalKb5BoxAllUniv`: every emitted formula is
fresh (`x ∉ b`) and either (a) targets a known non-root world (the unconditional cluster-dump
arm), or (b) is the self-target `⟨.pos, φ, 0⟩`, which fires whenever the known cluster has some
non-root member `v` -- the trigger `w` no longer appears in the dichotomy at all, in contrast to
`modalKb5BoxAllFull_mem`. -/
lemma modalKb5BoxAllUniv_mem {b : List (SignedFormula (Proposition Atom) WorldIndex)}
    {φ : Proposition Atom} {w : WorldIndex}
    {x : SignedFormula (Proposition Atom) WorldIndex} (h : x ∈ modalKb5BoxAllUniv b φ w) :
    x ∉ b ∧
    ((x = (⟨.pos, φ, x.label⟩ : SignedFormula (Proposition Atom) WorldIndex) ∧
        x.label ∈ modalKnownWorlds b ∧ x.label ≠ 0) ∨
     (x = (⟨.pos, φ, (0 : WorldIndex)⟩ : SignedFormula (Proposition Atom) WorldIndex) ∧
        ∃ v ∈ modalKnownWorlds b, v ≠ (0 : WorldIndex))) := by
  unfold modalKb5BoxAllUniv at h
  dsimp only at h
  by_cases hgate : ((modalKnownWorlds b).any (fun v => !(v == (0 : WorldIndex)))) = true
  · rw [if_pos hgate] at h
    simp only [List.any_eq_true, Bool.not_eq_true', beq_eq_false_iff_ne, ne_eq] at hgate
    obtain ⟨v, hv, hvne⟩ := hgate
    by_cases hmem0 :
        (b.any (· == (⟨.pos, φ, (0 : WorldIndex)⟩ : SignedFormula (Proposition Atom) WorldIndex)))
          = true
    · rw [if_pos hmem0] at h
      simp only [List.append_nil, List.mem_filterMap] at h
      obtain ⟨u, hu, heq⟩ := h
      by_cases huz : (u == (0 : WorldIndex)) = true
      · rw [if_pos huz] at heq; exact absurd heq (by simp)
      · rw [if_neg huz] at heq
        by_cases humem :
            (b.any (· == (⟨.pos, φ, u⟩ : SignedFormula (Proposition Atom) WorldIndex))) = true
        · rw [if_pos humem] at heq; exact absurd heq (by simp)
        · rw [if_neg humem] at heq
          obtain rfl : (⟨.pos, φ, u⟩ : SignedFormula (Proposition Atom) WorldIndex) = x := by
            injection heq
          refine ⟨by simpa using humem, Or.inl ⟨rfl, hu, ?_⟩⟩
          simpa using huz
    · rw [if_neg hmem0] at h
      simp only [List.mem_append, List.mem_filterMap, List.mem_singleton] at h
      rcases h with ⟨u, hu, heq⟩ | heq
      · by_cases huz : (u == (0 : WorldIndex)) = true
        · rw [if_pos huz] at heq; exact absurd heq (by simp)
        · rw [if_neg huz] at heq
          by_cases humem :
              (b.any (· == (⟨.pos, φ, u⟩ : SignedFormula (Proposition Atom) WorldIndex))) = true
          · rw [if_pos humem] at heq; exact absurd heq (by simp)
          · rw [if_neg humem] at heq
            obtain rfl : (⟨.pos, φ, u⟩ : SignedFormula (Proposition Atom) WorldIndex) = x := by
              injection heq
            refine ⟨by simpa using humem, Or.inl ⟨rfl, hu, ?_⟩⟩
            simpa using huz
      · subst heq
        exact ⟨by simpa using hmem0, Or.inr ⟨rfl, v, hv, hvne⟩⟩
  · rw [if_neg hgate] at h
    simp only [List.mem_filterMap] at h
    obtain ⟨u, hu, heq⟩ := h
    by_cases huz : (u == (0 : WorldIndex)) = true
    · rw [if_pos huz] at heq; exact absurd heq (by simp)
    · rw [if_neg huz] at heq
      by_cases humem :
          (b.any (· == (⟨.pos, φ, u⟩ : SignedFormula (Proposition Atom) WorldIndex))) = true
      · rw [if_pos humem] at heq; exact absurd heq (by simp)
      · rw [if_neg humem] at heq
        obtain rfl : (⟨.pos, φ, u⟩ : SignedFormula (Proposition Atom) WorldIndex) = x := by
          injection heq
        refine ⟨by simpa using humem, Or.inl ⟨rfl, hu, ?_⟩⟩
        simpa using huz

omit [Hashable Atom] in
/-- Trigger-free membership dichotomy for `modalKb5DiaNegAllUniv`, dual of
`modalKb5BoxAllUniv_mem`. -/
lemma modalKb5DiaNegAllUniv_mem {b : List (SignedFormula (Proposition Atom) WorldIndex)}
    {φ : Proposition Atom} {w : WorldIndex}
    {x : SignedFormula (Proposition Atom) WorldIndex} (h : x ∈ modalKb5DiaNegAllUniv b φ w) :
    x ∉ b ∧
    ((x = (⟨.neg, φ, x.label⟩ : SignedFormula (Proposition Atom) WorldIndex) ∧
        x.label ∈ modalKnownWorlds b ∧ x.label ≠ 0) ∨
     (x = (⟨.neg, φ, (0 : WorldIndex)⟩ : SignedFormula (Proposition Atom) WorldIndex) ∧
        ∃ v ∈ modalKnownWorlds b, v ≠ (0 : WorldIndex))) := by
  unfold modalKb5DiaNegAllUniv at h
  dsimp only at h
  by_cases hgate : ((modalKnownWorlds b).any (fun v => !(v == (0 : WorldIndex)))) = true
  · rw [if_pos hgate] at h
    simp only [List.any_eq_true, Bool.not_eq_true', beq_eq_false_iff_ne, ne_eq] at hgate
    obtain ⟨v, hv, hvne⟩ := hgate
    by_cases hmem0 :
        (b.any (· == (⟨.neg, φ, (0 : WorldIndex)⟩ : SignedFormula (Proposition Atom) WorldIndex)))
          = true
    · rw [if_pos hmem0] at h
      simp only [List.append_nil, List.mem_filterMap] at h
      obtain ⟨u, hu, heq⟩ := h
      by_cases huz : (u == (0 : WorldIndex)) = true
      · rw [if_pos huz] at heq; exact absurd heq (by simp)
      · rw [if_neg huz] at heq
        by_cases humem :
            (b.any (· == (⟨.neg, φ, u⟩ : SignedFormula (Proposition Atom) WorldIndex))) = true
        · rw [if_pos humem] at heq; exact absurd heq (by simp)
        · rw [if_neg humem] at heq
          obtain rfl : (⟨.neg, φ, u⟩ : SignedFormula (Proposition Atom) WorldIndex) = x := by
            injection heq
          refine ⟨by simpa using humem, Or.inl ⟨rfl, hu, ?_⟩⟩
          simpa using huz
    · rw [if_neg hmem0] at h
      simp only [List.mem_append, List.mem_filterMap, List.mem_singleton] at h
      rcases h with ⟨u, hu, heq⟩ | heq
      · by_cases huz : (u == (0 : WorldIndex)) = true
        · rw [if_pos huz] at heq; exact absurd heq (by simp)
        · rw [if_neg huz] at heq
          by_cases humem :
              (b.any (· == (⟨.neg, φ, u⟩ : SignedFormula (Proposition Atom) WorldIndex))) = true
          · rw [if_pos humem] at heq; exact absurd heq (by simp)
          · rw [if_neg humem] at heq
            obtain rfl : (⟨.neg, φ, u⟩ : SignedFormula (Proposition Atom) WorldIndex) = x := by
              injection heq
            refine ⟨by simpa using humem, Or.inl ⟨rfl, hu, ?_⟩⟩
            simpa using huz
      · subst heq
        exact ⟨by simpa using hmem0, Or.inr ⟨rfl, v, hv, hvne⟩⟩
  · rw [if_neg hgate] at h
    simp only [List.mem_filterMap] at h
    obtain ⟨u, hu, heq⟩ := h
    by_cases huz : (u == (0 : WorldIndex)) = true
    · rw [if_pos huz] at heq; exact absurd heq (by simp)
    · rw [if_neg huz] at heq
      by_cases humem :
          (b.any (· == (⟨.neg, φ, u⟩ : SignedFormula (Proposition Atom) WorldIndex))) = true
      · rw [if_pos humem] at heq; exact absurd heq (by simp)
      · rw [if_neg humem] at heq
        obtain rfl : (⟨.neg, φ, u⟩ : SignedFormula (Proposition Atom) WorldIndex) = x := by
          injection heq
        refine ⟨by simpa using humem, Or.inl ⟨rfl, hu, ?_⟩⟩
        simpa using huz

omit [Hashable Atom] in
/-- Every emitted formula's shape is `⟨.pos, φ, x.label⟩` regardless of which case of
`modalKb5BoxAllUniv_mem`'s dichotomy produced it. -/
lemma modalKb5BoxAllUniv_mem_eq {b : List (SignedFormula (Proposition Atom) WorldIndex)}
    {φ : Proposition Atom} {w : WorldIndex} {x : SignedFormula (Proposition Atom) WorldIndex}
    (h : x ∈ modalKb5BoxAllUniv b φ w) :
    x = (⟨.pos, φ, x.label⟩ : SignedFormula (Proposition Atom) WorldIndex) := by
  rcases (modalKb5BoxAllUniv_mem h).2 with ⟨heq, -, -⟩ | ⟨heq, -⟩
  · exact heq
  · subst heq; rfl

omit [Hashable Atom] in
/-- Dual of `modalKb5BoxAllUniv_mem_eq` for `modalKb5DiaNegAllUniv`. -/
lemma modalKb5DiaNegAllUniv_mem_eq {b : List (SignedFormula (Proposition Atom) WorldIndex)}
    {φ : Proposition Atom} {w : WorldIndex} {x : SignedFormula (Proposition Atom) WorldIndex}
    (h : x ∈ modalKb5DiaNegAllUniv b φ w) :
    x = (⟨.neg, φ, x.label⟩ : SignedFormula (Proposition Atom) WorldIndex) := by
  rcases (modalKb5DiaNegAllUniv_mem h).2 with ⟨heq, -, -⟩ | ⟨heq, -⟩
  · exact heq
  · subst heq; rfl

omit [Hashable Atom] in
/-- **Introduction direction for `modalKb5BoxAllUniv`**, converse of `modalKb5BoxAllUniv_mem`.
Trigger-free: unlike `modalKb5BoxAllFull_mem_of` (`FrameCompleteness.lean`), the self-target
condition drops the `w = 0` conjunct entirely -- the corrected gate's self-target arm fires for
any trigger. -/
lemma modalKb5BoxAllUniv_mem_of {b : List (SignedFormula (Proposition Atom) WorldIndex)}
    {φ : Proposition Atom} {w v : WorldIndex}
    (hnotin : (⟨.pos, φ, v⟩ : SignedFormula (Proposition Atom) WorldIndex) ∉ b)
    (hcond : (v ∈ modalKnownWorlds b ∧ v ≠ (0 : WorldIndex)) ∨
      (v = (0 : WorldIndex) ∧ ∃ u ∈ modalKnownWorlds b, u ≠ (0 : WorldIndex))) :
    (⟨.pos, φ, v⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ modalKb5BoxAllUniv b φ w := by
  rcases hcond with ⟨hv, hvne⟩ | ⟨rfl, u, hu, hune⟩
  · unfold modalKb5BoxAllUniv
    dsimp only
    have hmemNR :
        (⟨.pos, φ, v⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈
          (modalKnownWorlds b).filterMap fun w' =>
            if w' == (0 : WorldIndex) then none
            else
              if b.any (· == (⟨.pos, φ, w'⟩ : SignedFormula (Proposition Atom) WorldIndex))
              then none else some ⟨.pos, φ, w'⟩ := by
      simp only [List.mem_filterMap]
      exact ⟨v, hv, by rw [if_neg (by simpa using hvne), if_neg (by simpa using hnotin)]⟩
    by_cases hgate : ((modalKnownWorlds b).any (fun v => !(v == (0 : WorldIndex)))) = true
    · rw [if_pos hgate]
      exact List.mem_append_left _ hmemNR
    · rw [if_neg hgate]
      exact hmemNR
  · unfold modalKb5BoxAllUniv
    dsimp only
    rw [if_pos (by
      simp only [List.any_eq_true, Bool.not_eq_true', beq_eq_false_iff_ne, ne_eq]
      exact ⟨u, hu, hune⟩)]
    rw [if_neg (by simpa using hnotin)]
    exact List.mem_append_right _ (List.mem_singleton_self _)

omit [Hashable Atom] in
/-- Dual of `modalKb5BoxAllUniv_mem_of` for `modalKb5DiaNegAllUniv`. -/
lemma modalKb5DiaNegAllUniv_mem_of {b : List (SignedFormula (Proposition Atom) WorldIndex)}
    {φ : Proposition Atom} {w v : WorldIndex}
    (hnotin : (⟨.neg, φ, v⟩ : SignedFormula (Proposition Atom) WorldIndex) ∉ b)
    (hcond : (v ∈ modalKnownWorlds b ∧ v ≠ (0 : WorldIndex)) ∨
      (v = (0 : WorldIndex) ∧ ∃ u ∈ modalKnownWorlds b, u ≠ (0 : WorldIndex))) :
    (⟨.neg, φ, v⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈
      modalKb5DiaNegAllUniv b φ w := by
  rcases hcond with ⟨hv, hvne⟩ | ⟨rfl, u, hu, hune⟩
  · unfold modalKb5DiaNegAllUniv
    dsimp only
    have hmemNR :
        (⟨.neg, φ, v⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈
          (modalKnownWorlds b).filterMap fun w' =>
            if w' == (0 : WorldIndex) then none
            else
              if b.any (· == (⟨.neg, φ, w'⟩ : SignedFormula (Proposition Atom) WorldIndex))
              then none else some ⟨.neg, φ, w'⟩ := by
      simp only [List.mem_filterMap]
      exact ⟨v, hv, by rw [if_neg (by simpa using hvne), if_neg (by simpa using hnotin)]⟩
    by_cases hgate : ((modalKnownWorlds b).any (fun v => !(v == (0 : WorldIndex)))) = true
    · rw [if_pos hgate]
      exact List.mem_append_left _ hmemNR
    · rw [if_neg hgate]
      exact hmemNR
  · unfold modalKb5DiaNegAllUniv
    dsimp only
    rw [if_pos (by
      simp only [List.any_eq_true, Bool.not_eq_true', beq_eq_false_iff_ne, ne_eq]
      exact ⟨u, hu, hune⟩)]
    rw [if_neg (by simpa using hnotin)]
    exact List.mem_append_right _ (List.mem_singleton_self _)

/-- Apply the K modal rules together with the KB5 corrected-gate full-cluster propagation arms.
Mirrors `modalApplyOneKb5'Prop` declaration-for-declaration, substituting `modalKb5BoxAllUniv`/
`modalKb5DiaNegAllUniv` for `modalKb5BoxAllFull`/`modalKb5DiaNegAllFull`. -/
def modalApplyOneKb5''Prop
    (sf : SignedFormula (Proposition Atom) WorldIndex)
    (b : List (SignedFormula (Proposition Atom) WorldIndex))
    (acc : Accessibility) :
    RuleResult (Proposition Atom) WorldIndex × Accessibility :=
  let (kResult, kAcc) := modalApplyOne sf b acc
  match sf.sign, sf.formula with
  | .pos, .box φ =>
    let allNew := modalKb5BoxAllUniv b φ sf.label
    match kResult with
    | .persistent kForms =>
      (.persistent (kForms ++ allNew.filter (fun x => !(kForms.any (· == x)))), kAcc)
    | .notApplicable =>
      if allNew.isEmpty then (.notApplicable, kAcc) else (.persistent allNew, kAcc)
    | other => (other, kAcc)
  | .neg, .diamond φ =>
    let allNew := modalKb5DiaNegAllUniv b φ sf.label
    match kResult with
    | .persistent kForms =>
      (.persistent (kForms ++ allNew.filter (fun x => !(kForms.any (· == x)))), kAcc)
    | .notApplicable =>
      if allNew.isEmpty then (.notApplicable, kAcc) else (.persistent allNew, kAcc)
    | other => (other, kAcc)
  | _, _ => (kResult, kAcc)

omit [Hashable Atom] in
/-- `modalApplyOneKb5''Prop` agrees with `modalApplyOne` outside the two propagation shapes.
Mirrors `modalApplyOneKb5'Prop_eq_of_not_boxPos_diaNeg`. -/
lemma modalApplyOneKb5''Prop_eq_of_not_boxPos_diaNeg
    (sf : SignedFormula (Proposition Atom) WorldIndex)
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (h : ¬ (sf.sign = .pos ∧ ∃ φ, sf.formula = .box φ) ∧
         ¬ (sf.sign = .neg ∧ ∃ φ, sf.formula = .diamond φ)) :
    modalApplyOneKb5''Prop sf b acc = modalApplyOne sf b acc := by
  obtain ⟨h1, h2⟩ := h
  unfold modalApplyOneKb5''Prop
  rcases hs : sf.sign with _ | _ <;> rcases hf : sf.formula with _ | _ | _ | _ | _ | φ | φ <;>
    simp_all

/-- **The corrected-gate KB5 rule**: the mint (existential) shapes are `modalApplyOneFive`'s
witness-reuse behavior, verbatim and unchanged (identical to `modalApplyOneKb5'`'s mint arms);
only the two propagation (universal) shapes differ, routing through `modalApplyOneKb5''Prop`
instead of `modalApplyOneKb5'Prop`. Mirrors `modalApplyOneKb5'` declaration-for-declaration. -/
def modalApplyOneKb5'' : RuleApply Atom := fun sf b acc =>
  match sf.sign, sf.formula with
  | .pos, .diamond φ =>
    (if sf.label == (0 : WorldIndex) then modalApplyOneKb5''Prop sf b acc
     else
       match witnessWorldFive b .pos φ with
       | some w' => (.linear [⟨.pos, φ, w'⟩], acc.addEdge sf.label w')
       | none => modalApplyOneKb5''Prop sf b acc)
  | .neg, .box φ =>
    (if sf.label == (0 : WorldIndex) then modalApplyOneKb5''Prop sf b acc
     else
       match witnessWorldFive b .neg φ with
       | some w' => (.linear [⟨.neg, φ, w'⟩], acc.addEdge sf.label w')
       | none => modalApplyOneKb5''Prop sf b acc)
  | _, _ => modalApplyOneKb5''Prop sf b acc

/-- Case-split helper for the diamond-positive mint shape, mirrors
`modalApplyOneKb5'_diaPos_eq_or_reuse`. -/
lemma modalApplyOneKb5''_diaPos_eq_or_reuse
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (φ : Proposition Atom) (w : WorldIndex) :
    (modalApplyOneKb5'' (⟨.pos, .diamond φ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) b acc
       = modalApplyOneKb5''Prop
           (⟨.pos, .diamond φ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) b acc) ∨
    (∃ w', witnessWorldFive b .pos φ = some w' ∧
      modalApplyOneKb5'' (⟨.pos, .diamond φ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) b acc
        = (RuleResult.linear [⟨.pos, φ, w'⟩], acc.addEdge w w')) := by
  unfold modalApplyOneKb5''
  dsimp only
  by_cases hz : (w == (0 : WorldIndex)) = true
  · rw [if_pos hz]; exact Or.inl rfl
  · rw [if_neg hz]
    cases hw : witnessWorldFive b .pos φ with
    | none => exact Or.inl rfl
    | some w' => exact Or.inr ⟨w', rfl, rfl⟩

/-- Case-split helper for the box-negative mint shape, dual of
`modalApplyOneKb5''_diaPos_eq_or_reuse`. -/
lemma modalApplyOneKb5''_boxNeg_eq_or_reuse
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (φ : Proposition Atom) (w : WorldIndex) :
    (modalApplyOneKb5'' (⟨.neg, .box φ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) b acc
       = modalApplyOneKb5''Prop
           (⟨.neg, .box φ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) b acc) ∨
    (∃ w', witnessWorldFive b .neg φ = some w' ∧
      modalApplyOneKb5'' (⟨.neg, .box φ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) b acc
        = (RuleResult.linear [⟨.neg, φ, w'⟩], acc.addEdge w w')) := by
  unfold modalApplyOneKb5''
  dsimp only
  by_cases hz : (w == (0 : WorldIndex)) = true
  · rw [if_pos hz]; exact Or.inl rfl
  · rw [if_neg hz]
    cases hw : witnessWorldFive b .neg φ with
    | none => exact Or.inl rfl
    | some w' => exact Or.inr ⟨w', rfl, rfl⟩

/-- Free bridge: on the box-positive (propagation, non-mint) shape, `modalApplyOneKb5''` falls
through to `modalApplyOneKb5''Prop` by the definitional `| _, _ =>` catch-all -- `rfl`. -/
lemma modalApplyOneKb5''_boxPos_eq
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (φ : Proposition Atom) (w : WorldIndex) :
    modalApplyOneKb5'' (⟨.pos, .box φ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) b acc
      = modalApplyOneKb5''Prop
          (⟨.pos, .box φ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) b acc :=
  rfl

/-- Free bridge, dual of `modalApplyOneKb5''_boxPos_eq`. -/
lemma modalApplyOneKb5''_diaNeg_eq
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (φ : Proposition Atom) (w : WorldIndex) :
    modalApplyOneKb5'' (⟨.neg, .diamond φ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) b acc
      = modalApplyOneKb5''Prop
          (⟨.neg, .diamond φ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) b acc :=
  rfl

/-- `modalApplyOneKb5''` agrees with `modalApplyOneKb5''Prop` outside the two mint shapes. Mirrors
`modalApplyOneKb5'_eq_of_not_mint_shape`. -/
lemma modalApplyOneKb5''_eq_of_not_mint_shape
    (sf : SignedFormula (Proposition Atom) WorldIndex)
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (h : ¬ (sf.sign = .pos ∧ ∃ φ, sf.formula = .diamond φ) ∧
         ¬ (sf.sign = .neg ∧ ∃ φ, sf.formula = .box φ)) :
    modalApplyOneKb5'' sf b acc = modalApplyOneKb5''Prop sf b acc := by
  obtain ⟨h1, h2⟩ := h
  unfold modalApplyOneKb5''
  rcases hs : sf.sign with _ | _ <;> rcases hf : sf.formula with _ | _ | _ | _ | _ | φ | φ <;>
    simp_all

/-- **Task 528**: strengthens `modalApplyOneKb5''_diaPos_eq_or_reuse` with the fact that a reuse
call's trigger is never the root -- reuse only fires in the `else` branch of
`modalApplyOneKb5''`'s `if sf.label == 0 then .. else ..` guard, i.e. exactly when `w ≠ 0`.
Mirrors `modalApplyOneKb5'_diaPos_eq_or_reuse_ne_root`. -/
lemma modalApplyOneKb5''_diaPos_eq_or_reuse_ne_root
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (φ : Proposition Atom) (w : WorldIndex) :
    (modalApplyOneKb5'' (⟨.pos, .diamond φ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) b acc
       = modalApplyOneKb5''Prop
           (⟨.pos, .diamond φ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) b acc) ∨
    (∃ w', w ≠ 0 ∧ witnessWorldFive b .pos φ = some w' ∧
      modalApplyOneKb5'' (⟨.pos, .diamond φ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) b acc
        = (RuleResult.linear [⟨.pos, φ, w'⟩], acc.addEdge w w')) := by
  unfold modalApplyOneKb5''
  dsimp only
  by_cases hz : (w == (0 : WorldIndex)) = true
  · rw [if_pos hz]; exact Or.inl rfl
  · rw [if_neg hz]
    have hwne : w ≠ 0 := by simpa using hz
    cases hw : witnessWorldFive b .pos φ with
    | none => exact Or.inl rfl
    | some w' => exact Or.inr ⟨w', hwne, rfl, rfl⟩

/-- **Task 528**: dual of `modalApplyOneKb5''_diaPos_eq_or_reuse_ne_root` for the box-negative
mint shape. Mirrors `modalApplyOneKb5'_boxNeg_eq_or_reuse_ne_root`. -/
lemma modalApplyOneKb5''_boxNeg_eq_or_reuse_ne_root
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (φ : Proposition Atom) (w : WorldIndex) :
    (modalApplyOneKb5'' (⟨.neg, .box φ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) b acc
       = modalApplyOneKb5''Prop
           (⟨.neg, .box φ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) b acc) ∨
    (∃ w', w ≠ 0 ∧ witnessWorldFive b .neg φ = some w' ∧
      modalApplyOneKb5'' (⟨.neg, .box φ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) b acc
        = (RuleResult.linear [⟨.neg, φ, w'⟩], acc.addEdge w w')) := by
  unfold modalApplyOneKb5''
  dsimp only
  by_cases hz : (w == (0 : WorldIndex)) = true
  · rw [if_pos hz]; exact Or.inl rfl
  · rw [if_neg hz]
    have hwne : w ≠ 0 := by simpa using hz
    cases hw : witnessWorldFive b .neg φ with
    | none => exact Or.inl rfl
    | some w' => exact Or.inr ⟨w', hwne, rfl, rfl⟩

/-- `modalApplyOneKb5''` either agrees with `modalApplyOneKb5''Prop` outright, or fires a witness
reuse away from the root, targeting a non-root witness (verbatim `modalApplyOneFive` mint
behavior). Mirrors `modalApplyOneKb5'_agree_or_reuse_ne_root`. -/
lemma modalApplyOneKb5''_agree_or_reuse_ne_root
    (sf : SignedFormula (Proposition Atom) WorldIndex)
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility) :
    modalApplyOneKb5'' sf b acc = modalApplyOneKb5''Prop sf b acc ∨
    ∃ sf' : SignedFormula (Proposition Atom) WorldIndex,
      sf' ∈ b ∧ sf.label ≠ 0 ∧ sf'.label ≠ 0 ∧ modalApplyOneKb5'' sf b acc =
        (RuleResult.linear [sf'], acc.addEdge sf.label sf'.label) := by
  obtain ⟨s, ff, w⟩ := sf
  rcases s with _ | _ <;> rcases ff with _ | _ | ⟨a, c⟩ | ⟨x, y⟩ | ⟨x, y⟩ | φ | φ
  case pos.diamond =>
    rcases modalApplyOneKb5''_diaPos_eq_or_reuse_ne_root b acc φ w with
      heq | ⟨w', hwne, hw', heq⟩
    · exact Or.inl heq
    · exact Or.inr
        ⟨⟨.pos, φ, w'⟩, (witnessWorldFive_mem hw').1, hwne, (witnessWorldFive_mem hw').2, heq⟩
  case neg.box =>
    rcases modalApplyOneKb5''_boxNeg_eq_or_reuse_ne_root b acc φ w with
      heq | ⟨w', hwne, hw', heq⟩
    · exact Or.inl heq
    · exact Or.inr
        ⟨⟨.neg, φ, w'⟩, (witnessWorldFive_mem hw').1, hwne, (witnessWorldFive_mem hw').2, heq⟩
  all_goals exact Or.inl (modalApplyOneKb5''_eq_of_not_mint_shape _ b acc (by simp))

/-- Plain (non-root-excluded) agree-or-reuse dichotomy for `modalApplyOneKb5''`, mirrors
`modalApplyOneKb5'_agree_or_reuse`. -/
lemma modalApplyOneKb5''_agree_or_reuse
    (sf : SignedFormula (Proposition Atom) WorldIndex)
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility) :
    modalApplyOneKb5'' sf b acc = modalApplyOneKb5''Prop sf b acc ∨
    ∃ sf' : SignedFormula (Proposition Atom) WorldIndex,
      sf' ∈ b ∧ modalApplyOneKb5'' sf b acc =
        (RuleResult.linear [sf'], acc.addEdge sf.label sf'.label) := by
  obtain ⟨s, ff, w⟩ := sf
  rcases s with _ | _ <;> rcases ff with _ | _ | ⟨a, c⟩ | ⟨x, y⟩ | ⟨x, y⟩ | φ | φ
  case pos.diamond =>
    rcases modalApplyOneKb5''_diaPos_eq_or_reuse b acc φ w with heq | ⟨w', hw', heq⟩
    · exact Or.inl heq
    · exact Or.inr ⟨⟨.pos, φ, w'⟩, (witnessWorldFive_mem hw').1, heq⟩
  case neg.box =>
    rcases modalApplyOneKb5''_boxNeg_eq_or_reuse b acc φ w with heq | ⟨w', hw', heq⟩
    · exact Or.inl heq
    · exact Or.inr ⟨⟨.neg, φ, w'⟩, (witnessWorldFive_mem hw').1, heq⟩
  all_goals exact Or.inl (modalApplyOneKb5''_eq_of_not_mint_shape _ b acc (by simp))

/-! ## Driver Instantiation (task 528) -/

/-- One-step branch expansion for the corrected-gate KB5 tableau: the generic driver
instantiated at `apply := modalApplyOneKb5''`. -/
def modalStepBranchKb5''
    (b e : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility) :
    Option (List (List (SignedFormula (Proposition Atom) WorldIndex)) ×
            List (List (SignedFormula (Proposition Atom) WorldIndex)) ×
            Accessibility) :=
  modalStepBranchGen modalApplyOneKb5'' b e acc

/-- Fuel-based expansion of a list of corrected-gate-KB5-system branches. -/
def modalExpandBranchesKb5''
    (branches expandedSets : List (List (SignedFormula (Proposition Atom) WorldIndex)))
    (accs : List Accessibility) (fuel : Nat) : ModalTableauResult Atom :=
  modalExpandBranchesGen modalApplyOneKb5'' branches expandedSets accs fuel

/-- The corrected-gate KB5 modal tableau **decision procedure**: the generic entry point
instantiated at `apply := modalApplyOneKb5''`, starting the signed tableau from `F(φ)` at world
`0`. -/
def modalTableauKb5'' (φ : Proposition Atom) : ModalTableauResult Atom :=
  modalTableauGen modalApplyOneKb5'' φ

/-- `modalStepBranchKb5''` is exactly `modalStepBranchGen modalApplyOneKb5''` -- true `rfl`. -/
theorem modalStepBranchKb5''_eq
    (b e : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility) :
    modalStepBranchKb5'' b e acc = modalStepBranchGen modalApplyOneKb5'' b e acc := rfl

/-- `modalExpandBranchesKb5''` is exactly `modalExpandBranchesGen modalApplyOneKb5''` -- true
`rfl`. -/
theorem modalExpandBranchesKb5''_eq
    (branches expandedSets : List (List (SignedFormula (Proposition Atom) WorldIndex)))
    (accs : List Accessibility) (fuel : Nat) :
    modalExpandBranchesKb5'' branches expandedSets accs fuel =
      modalExpandBranchesGen modalApplyOneKb5'' branches expandedSets accs fuel := rfl

/-- `modalTableauKb5''` is exactly `modalTableauGen modalApplyOneKb5''` -- true `rfl`. -/
theorem modalTableauKb5''_eq (φ : Proposition Atom) :
    modalTableauKb5'' φ = modalTableauGen modalApplyOneKb5'' φ := rfl

/-! ## `RuleApplicationSpecCore` for `modalApplyOneKb5''`

Discharges `RuleApplicationSpecCore modalApplyOneKb5''` (`GenericDriver.lean`), mirroring
`modalApplyOneKb5'_specCore`'s discharge declaration-for-declaration. The two mint shapes
(`.pos .diamond`/`.neg .box`) are byte-identical to `modalApplyOneKb5'`'s own discharge (verbatim
witness-reuse behavior); only the two propagation shapes (`.pos .box`/`.neg .diamond`) need fresh
proofs against `modalKb5BoxAllUniv`/`modalKb5DiaNegAllUniv`'s membership facts. Only
`RuleApplicationSpecCore` (not the extended `RuleApplicationSpec` with its `rankStep`/`outDegStep`/
`knownWorldsStep` termination-measure fields) is targeted -- this is all the Hintikka/saturation
completeness machinery (`CompletenessLoop.lean`) consumes, and all this plan's task requires. -/

omit [Hashable Atom] in
/-- `modalApplyOneKb5''Prop`'s accessibility output agrees with K's `modalApplyOne` at every
shape. Mirrors `modalApplyOneKb5'Prop_snd_eq`. -/
lemma modalApplyOneKb5''Prop_snd_eq
    (sf : SignedFormula (Proposition Atom) WorldIndex)
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility) :
    (modalApplyOneKb5''Prop sf b acc).snd = (modalApplyOne sf b acc).snd := by
  unfold modalApplyOneKb5''Prop
  rcases hs : sf.sign with _ | _ <;> rcases hf : sf.formula with _ | _ | _ | _ | _ | φ | φ <;>
    simp_all <;>
    rcases h1 : (modalApplyOne sf b acc).1 with _ | _ | _ | _ <;> simp <;> split <;> simp

omit [Hashable Atom] in
/-- Whenever K's own result is `.linear`, `modalApplyOneKb5''Prop` agrees with `modalApplyOne`
entirely. Mirrors `modalApplyOneKb5'Prop_eq_of_linear`. -/
lemma modalApplyOneKb5''Prop_eq_of_linear
    (sf : SignedFormula (Proposition Atom) WorldIndex)
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (nf : List (SignedFormula (Proposition Atom) WorldIndex))
    (h : (modalApplyOne sf b acc).fst = RuleResult.linear nf) :
    modalApplyOneKb5''Prop sf b acc = modalApplyOne sf b acc := by
  unfold modalApplyOneKb5''Prop
  rcases hp : modalApplyOne sf b acc with ⟨kResult, kAcc⟩
  rw [hp] at h
  simp only [] at h
  subst h
  rcases hs : sf.sign with _ | _ <;> rcases hf : sf.formula with _ | _ | _ | _ | _ | φ | φ <;>
    simp_all

omit [Hashable Atom] in
/-- Local re-derivation of `modalApplyOneKb5'Prop_fresh_local_local` for `modalApplyOneKb5''Prop`.
-/
private lemma modalApplyOneKb5''Prop_fresh_local_local
    (sf : SignedFormula (Proposition Atom) WorldIndex)
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility) :
    (modalApplyOneKb5''Prop sf b acc).snd = acc ∨
    (∃ wsf rest, (modalApplyOneKb5''Prop sf b acc).fst = RuleResult.linear (wsf :: rest)
      ∧ (modalApplyOneKb5''Prop sf b acc).snd = acc.addEdge sf.label wsf.label) := by
  rcases modalApplyOne_fresh_local sf b acc with hsame | ⟨wsf, rest, hfst, hsnd⟩
  · exact Or.inl (by rw [modalApplyOneKb5''Prop_snd_eq]; exact hsame)
  · have heq := modalApplyOneKb5''Prop_eq_of_linear sf b acc (wsf :: rest) hfst
    exact Or.inr ⟨wsf, rest, by rw [heq]; exact hfst, by rw [heq]; exact hsnd⟩

/-- **F1 discharge for `modalApplyOneKb5''`**. Mirrors `modalApplyOneKb5'_fresh_local`. -/
lemma modalApplyOneKb5''_fresh_local
    (sf : SignedFormula (Proposition Atom) WorldIndex)
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility) :
    (modalApplyOneKb5'' sf b acc).snd = acc ∨
    (∃ wsf rest, (modalApplyOneKb5'' sf b acc).fst = RuleResult.linear (wsf :: rest) ∧
      (modalApplyOneKb5'' sf b acc).snd = acc.addEdge sf.label wsf.label) := by
  obtain ⟨s, ff, w⟩ := sf
  rcases s with _ | _
  · rcases ff with _ | _ | ⟨a, c⟩ | ⟨x, y⟩ | ⟨x, y⟩ | φ | φ
    case atom =>
      rw [modalApplyOneKb5''_eq_of_not_mint_shape _ b acc (by simp)]
      exact modalApplyOneKb5''Prop_fresh_local_local _ b acc
    case bot =>
      rw [modalApplyOneKb5''_eq_of_not_mint_shape _ b acc (by simp)]
      exact modalApplyOneKb5''Prop_fresh_local_local _ b acc
    case imp =>
      rw [modalApplyOneKb5''_eq_of_not_mint_shape _ b acc (by simp)]
      exact modalApplyOneKb5''Prop_fresh_local_local _ b acc
    case and =>
      rw [modalApplyOneKb5''_eq_of_not_mint_shape _ b acc (by simp)]
      exact modalApplyOneKb5''Prop_fresh_local_local _ b acc
    case or =>
      rw [modalApplyOneKb5''_eq_of_not_mint_shape _ b acc (by simp)]
      exact modalApplyOneKb5''Prop_fresh_local_local _ b acc
    case box =>
      rw [modalApplyOneKb5''_eq_of_not_mint_shape _ b acc (by simp)]
      exact modalApplyOneKb5''Prop_fresh_local_local _ b acc
    case diamond =>
      rcases modalApplyOneKb5''_diaPos_eq_or_reuse b acc φ w with heq | ⟨w', hw', heq⟩
      · rw [heq, modalApplyOneKb5''Prop_eq_of_not_boxPos_diaNeg _ b acc (by simp)]
        exact modalApplyOne_fresh_local _ b acc
      · rw [heq]
        exact Or.inr ⟨⟨.pos, φ, w'⟩, [], rfl, rfl⟩
  · rcases ff with _ | _ | ⟨a, c⟩ | ⟨x, y⟩ | ⟨x, y⟩ | φ | φ
    case atom =>
      rw [modalApplyOneKb5''_eq_of_not_mint_shape _ b acc (by simp)]
      exact modalApplyOneKb5''Prop_fresh_local_local _ b acc
    case bot =>
      rw [modalApplyOneKb5''_eq_of_not_mint_shape _ b acc (by simp)]
      exact modalApplyOneKb5''Prop_fresh_local_local _ b acc
    case imp =>
      rw [modalApplyOneKb5''_eq_of_not_mint_shape _ b acc (by simp)]
      exact modalApplyOneKb5''Prop_fresh_local_local _ b acc
    case and =>
      rw [modalApplyOneKb5''_eq_of_not_mint_shape _ b acc (by simp)]
      exact modalApplyOneKb5''Prop_fresh_local_local _ b acc
    case or =>
      rw [modalApplyOneKb5''_eq_of_not_mint_shape _ b acc (by simp)]
      exact modalApplyOneKb5''Prop_fresh_local_local _ b acc
    case diamond =>
      rw [modalApplyOneKb5''_eq_of_not_mint_shape _ b acc (by simp)]
      exact modalApplyOneKb5''Prop_fresh_local_local _ b acc
    case box =>
      rcases modalApplyOneKb5''_boxNeg_eq_or_reuse b acc φ w with heq | ⟨w', hw', heq⟩
      · rw [heq, modalApplyOneKb5''Prop_eq_of_not_boxPos_diaNeg _ b acc (by simp)]
        exact modalApplyOne_fresh_local _ b acc
      · rw [heq]
        exact Or.inr ⟨⟨.neg, φ, w'⟩, [], rfl, rfl⟩

/-! ### `knownWorlds_step` for `modalApplyOneKb5''Prop`

Unlike the frozen `modalApplyOneKb5'Prop_knownWorlds_step` (whose self-target arm ties
`x.label = 0` to the trigger `lbl = 0`, already known via `hsfmem`), the corrected rule's
self-target arm fires for ANY trigger, so `x.label = 0`'s known-ness is no longer derivable from
the trigger's own known-ness. These two lemmas take an explicit
`(h0 : (0 : WorldIndex) ∈ modalKnownWorlds b)` hypothesis instead -- the "root always known"
invariant every branch in this tableau satisfies (it starts from the singleton `[F(φ)@0]` and
formulas are never removed), threaded the same way completeness proofs elsewhere in this
development already thread `F(φ)@0 ∈ b` explicitly. -/

/-- At the two propagation shapes, `modalApplyOneKb5''Prop` never mints (its accessibility output
is exactly K's, unchanged) and only appends formulas at existing known worlds -- given the root is
already known. Mirrors `modalApplyOneKb5'Prop_boxPos_diaNeg_eq`, with the extra `h0` hypothesis
the self-target arm's `x.label = 0` case needs. -/
lemma modalApplyOneKb5''Prop_boxPos_diaNeg_eq
    (sf : SignedFormula (Proposition Atom) WorldIndex)
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (hsfmem : sf ∈ b) (hknown : accTargetsKnown b acc)
    (h0 : (0 : WorldIndex) ∈ modalKnownWorlds b)
    (h : (sf.sign = .pos ∧ ∃ φ, sf.formula = .box φ) ∨
         (sf.sign = .neg ∧ ∃ φ, sf.formula = .diamond φ)) :
    (modalApplyOneKb5''Prop sf b acc).snd = acc ∧
    ((modalApplyOneKb5''Prop sf b acc).fst = .notApplicable ∨
      ∃ out, (modalApplyOneKb5''Prop sf b acc).fst = .persistent out ∧
        ∀ x ∈ out, x.label ∈ modalKnownWorlds b) := by
  rcases h with ⟨hs, φ, hf⟩ | ⟨hs, φ, hf⟩
  · obtain ⟨s, ff, l⟩ := sf
    simp only at hs hf
    subst hs; subst hf
    have hK := modalApplyOne_boxPos_eq
      (⟨.pos, .box φ, l⟩ : SignedFormula (Proposition Atom) WorldIndex) rfl φ rfl b acc
    have hKW := modalApplyOne_knownWorlds_step
      (⟨.pos, .box φ, l⟩ : SignedFormula (Proposition Atom) WorldIndex) b acc hsfmem hknown
    unfold modalApplyOneKb5''Prop
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
        rcases (modalKb5BoxAllUniv_mem hx).2 with ⟨-, hkn, -⟩ | ⟨hxeq, -⟩
        · exact hkn
        · rw [hxeq]; dsimp only; exact h0
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
      · rcases (modalKb5BoxAllUniv_mem hx).2 with ⟨-, hkn, -⟩ | ⟨hxeq, -⟩
        · exact hkn
        · rw [hxeq]; dsimp only; exact h0
  · obtain ⟨s, ff, l⟩ := sf
    simp only at hs hf
    subst hs; subst hf
    have hK := modalApplyOne_diamondNeg_eq
      (⟨.neg, .diamond φ, l⟩ : SignedFormula (Proposition Atom) WorldIndex) rfl φ rfl b acc
    have hKW := modalApplyOne_knownWorlds_step
      (⟨.neg, .diamond φ, l⟩ : SignedFormula (Proposition Atom) WorldIndex) b acc hsfmem hknown
    unfold modalApplyOneKb5''Prop
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
        rcases (modalKb5DiaNegAllUniv_mem hx).2 with ⟨-, hkn, -⟩ | ⟨hxeq, -⟩
        · exact hkn
        · rw [hxeq]; dsimp only; exact h0
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
      · rcases (modalKb5DiaNegAllUniv_mem hx).2 with ⟨-, hkn, -⟩ | ⟨hxeq, -⟩
        · exact hkn
        · rw [hxeq]; dsimp only; exact h0

/-- The Kb5'' analogue of K's `modalApplyOne_knownWorlds_step`, stated directly over
`modalApplyOneKb5''Prop`, given the root is already known. Mirrors
`modalApplyOneKb5'Prop_knownWorlds_step`, with the extra `h0` hypothesis. -/
lemma modalApplyOneKb5''Prop_knownWorlds_step
    (sf : SignedFormula (Proposition Atom) WorldIndex)
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (hsfmem : sf ∈ b) (hknown : accTargetsKnown b acc)
    (h0 : (0 : WorldIndex) ∈ modalKnownWorlds b) :
    ((modalApplyOneKb5''Prop sf b acc).snd = acc ∧
      (match (modalApplyOneKb5''Prop sf b acc).fst with
        | .linear formulas => ∀ x ∈ formulas, x.label ∈ modalKnownWorlds b
        | .branching branches => ∀ x ∈ branches.flatten, x.label ∈ modalKnownWorlds b
        | .persistent formulas => ∀ x ∈ formulas, x.label ∈ modalKnownWorlds b
        | .notApplicable => True)) ∨
    ((modalApplyOneKb5''Prop sf b acc).snd = acc.addEdge sf.label (modalNextWorld b) ∧
      (match (modalApplyOneKb5''Prop sf b acc).fst with
        | .linear formulas => formulas ≠ [] ∧ ∀ x ∈ formulas, x.label = modalNextWorld b
        | .branching _ => False
        | .persistent _ => False
        | .notApplicable => False)) := by
  by_cases hbd : (sf.sign = .pos ∧ ∃ φ, sf.formula = .box φ) ∨
      (sf.sign = .neg ∧ ∃ φ, sf.formula = .diamond φ)
  · obtain ⟨hsndeq, hor⟩ :=
      modalApplyOneKb5''Prop_boxPos_diaNeg_eq sf b acc hsfmem hknown h0 hbd
    refine Or.inl ⟨hsndeq, ?_⟩
    rcases hor with hnot | ⟨out, hpers, hlabel⟩
    · rw [hnot]; trivial
    · rw [hpers]; exact hlabel
  · have hnbox : ¬ (sf.sign = .pos ∧ ∃ φ, sf.formula = .box φ) := fun hc => hbd (Or.inl hc)
    have hndia : ¬ (sf.sign = .neg ∧ ∃ φ, sf.formula = .diamond φ) := fun hc => hbd (Or.inr hc)
    rw [modalApplyOneKb5''Prop_eq_of_not_boxPos_diaNeg sf b acc ⟨hnbox, hndia⟩]
    exact modalApplyOne_knownWorlds_step sf b acc hsfmem hknown

omit [Hashable Atom] in
/-- **Combined F9/F10 shape fact for `modalApplyOneKb5''Prop`** (hypothesis-free). Mirrors
`modalApplyOneKb5'Prop_boxPos_diaNeg_shape`. -/
private lemma modalApplyOneKb5''Prop_boxPos_diaNeg_shape
    (sf : SignedFormula (Proposition Atom) WorldIndex)
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (h : (sf.sign = .pos ∧ ∃ φ, sf.formula = .box φ) ∨
         (sf.sign = .neg ∧ ∃ φ, sf.formula = .diamond φ)) :
    (modalApplyOneKb5''Prop sf b acc).fst = .notApplicable ∨
      ∃ out, (modalApplyOneKb5''Prop sf b acc).fst = .persistent out := by
  rcases h with ⟨hs, φ, hf⟩ | ⟨hs, φ, hf⟩
  · obtain ⟨s, ff, l⟩ := sf
    simp only at hs hf; subst hs; subst hf
    have hK := modalApplyOne_boxPos_eq
      (⟨.pos, .box φ, l⟩ : SignedFormula (Proposition Atom) WorldIndex) rfl φ rfl b acc
    unfold modalApplyOneKb5''Prop
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
    unfold modalApplyOneKb5''Prop
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

/-- **F9 discharge for `modalApplyOneKb5''`**. Mirrors `modalApplyOneKb5'_boxPosNotExpanding`. -/
private lemma modalApplyOneKb5''_boxPosNotExpanding
    (sf : SignedFormula (Proposition Atom) WorldIndex)
    (hsign : sf.sign = .pos) (ψ : Proposition Atom) (hform : sf.formula = .box ψ)
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility) :
    (modalApplyOneKb5'' sf b acc).fst = .notApplicable ∨
      ∃ out, (modalApplyOneKb5'' sf b acc).fst = .persistent out := by
  rw [modalApplyOneKb5''_eq_of_not_mint_shape sf b acc (by simp [hsign, hform])]
  exact modalApplyOneKb5''Prop_boxPos_diaNeg_shape sf b acc (Or.inl ⟨hsign, ψ, hform⟩)

/-- **F10 discharge for `modalApplyOneKb5''`**, dual of `modalApplyOneKb5''_boxPosNotExpanding`. -/
private lemma modalApplyOneKb5''_diaNegNotExpanding
    (sf : SignedFormula (Proposition Atom) WorldIndex)
    (hsign : sf.sign = .neg) (ψ : Proposition Atom) (hform : sf.formula = .diamond ψ)
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility) :
    (modalApplyOneKb5'' sf b acc).fst = .notApplicable ∨
      ∃ out, (modalApplyOneKb5'' sf b acc).fst = .persistent out := by
  rw [modalApplyOneKb5''_eq_of_not_mint_shape sf b acc (by simp [hsign, hform])]
  exact modalApplyOneKb5''Prop_boxPos_diaNeg_shape sf b acc (Or.inr ⟨hsign, ψ, hform⟩)

/-- **F8 discharge for `modalApplyOneKb5''`**. Mirrors `modalApplyOneKb5'_localShapeInvariance`.
-/
private lemma modalApplyOneKb5''_localShapeInvariance
    (s : Sign) (φ : Proposition Atom) (w : WorldIndex)
    (hnb : ∀ ψ, φ ≠ .box ψ) (hnd : ∀ ψ, φ ≠ .diamond ψ)
    (b b' : List (SignedFormula (Proposition Atom) WorldIndex)) (acc acc' : Accessibility) :
    (modalApplyOneKb5'' ⟨s, φ, w⟩ b acc).1 = (modalApplyOneKb5'' ⟨s, φ, w⟩ b' acc').1 := by
  rw [modalApplyOneKb5''_eq_of_not_mint_shape ⟨s, φ, w⟩ b acc ⟨by simp [hnd], by simp [hnb]⟩,
    modalApplyOneKb5''_eq_of_not_mint_shape ⟨s, φ, w⟩ b' acc' ⟨by simp [hnd], by simp [hnb]⟩,
    modalApplyOneKb5''Prop_eq_of_not_boxPos_diaNeg ⟨s, φ, w⟩ b acc ⟨by simp [hnb], by simp [hnd]⟩,
    modalApplyOneKb5''Prop_eq_of_not_boxPos_diaNeg ⟨s, φ, w⟩ b' acc' ⟨by simp [hnb], by simp [hnd]⟩]
  exact modalApplyOne_fst_eq_of_not_box s φ w hnb hnd b b' acc acc'

/-- **F7 discharge for `modalApplyOneKb5''`**. Mirrors `modalApplyOneKb5'_branchingLength`. -/
private lemma modalApplyOneKb5''_branchingLength
    (sf : SignedFormula (Proposition Atom) WorldIndex)
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (brs : List (List (SignedFormula (Proposition Atom) WorldIndex)))
    (h : (modalApplyOneKb5'' sf b acc).fst = RuleResult.branching brs) :
    brs.length = 2 := by
  by_cases hmint : (sf.sign = .pos ∧ ∃ φ, sf.formula = .diamond φ) ∨
      (sf.sign = .neg ∧ ∃ φ, sf.formula = .box φ)
  · rcases hmint with ⟨hs, φ, hf⟩ | ⟨hs, φ, hf⟩
    · obtain ⟨s, ff, w⟩ := sf
      simp only at hs hf; subst hs; subst hf
      rcases modalApplyOneKb5''_diaPos_eq_or_reuse b acc φ w with heq | ⟨w', -, heq⟩
      · rw [heq, modalApplyOneKb5''Prop_eq_of_not_boxPos_diaNeg _ b acc (by simp)] at h
        exact modalApplyOne_branching_length _ b acc brs h
      · rw [heq] at h; simp at h
    · obtain ⟨s, ff, w⟩ := sf
      simp only at hs hf; subst hs; subst hf
      rcases modalApplyOneKb5''_boxNeg_eq_or_reuse b acc φ w with heq | ⟨w', -, heq⟩
      · rw [heq, modalApplyOneKb5''Prop_eq_of_not_boxPos_diaNeg _ b acc (by simp)] at h
        exact modalApplyOne_branching_length _ b acc brs h
      · rw [heq] at h; simp at h
  · rw [modalApplyOneKb5''_eq_of_not_mint_shape sf b acc
        ⟨fun hc => hmint (Or.inl hc), fun hc => hmint (Or.inr hc)⟩] at h
    by_cases hprop : (sf.sign = .pos ∧ ∃ φ, sf.formula = .box φ) ∨
        (sf.sign = .neg ∧ ∃ φ, sf.formula = .diamond φ)
    · exfalso
      rcases modalApplyOneKb5''Prop_boxPos_diaNeg_shape sf b acc hprop with hna | ⟨out, hpe⟩
      · rw [hna] at h; simp at h
      · rw [hpe] at h; simp at h
    · rw [modalApplyOneKb5''Prop_eq_of_not_boxPos_diaNeg sf b acc
          ⟨fun hc => hprop (Or.inl hc), fun hc => hprop (Or.inr hc)⟩] at h
      exact modalApplyOne_branching_length sf b acc brs h

/-- **F3 discharge for `modalApplyOneKb5''`**. Mirrors `modalApplyOneKb5'_persistentFresh`. -/
private lemma modalApplyOneKb5''_persistentFresh
    (sf : SignedFormula (Proposition Atom) WorldIndex)
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (nf : List (SignedFormula (Proposition Atom) WorldIndex))
    (h : (modalApplyOneKb5'' sf b acc).fst = RuleResult.persistent nf) :
    nf ≠ [] ∧ ∀ x ∈ nf, x ∉ b := by
  by_cases hmint : (sf.sign = .pos ∧ ∃ φ, sf.formula = .diamond φ) ∨
      (sf.sign = .neg ∧ ∃ φ, sf.formula = .box φ)
  · rcases hmint with ⟨hs, φ, hf⟩ | ⟨hs, φ, hf⟩
    · obtain ⟨s, ff, w⟩ := sf
      simp only at hs hf; subst hs; subst hf
      rcases modalApplyOneKb5''_diaPos_eq_or_reuse b acc φ w with heq | ⟨w', -, heq⟩
      · rw [heq, modalApplyOneKb5''Prop_eq_of_not_boxPos_diaNeg _ b acc (by simp)] at h
        exact modalApplyOne_persistent_props _ b acc nf h
      · rw [heq] at h; simp at h
    · obtain ⟨s, ff, w⟩ := sf
      simp only at hs hf; subst hs; subst hf
      rcases modalApplyOneKb5''_boxNeg_eq_or_reuse b acc φ w with heq | ⟨w', -, heq⟩
      · rw [heq, modalApplyOneKb5''Prop_eq_of_not_boxPos_diaNeg _ b acc (by simp)] at h
        exact modalApplyOne_persistent_props _ b acc nf h
      · rw [heq] at h; simp at h
  · rw [modalApplyOneKb5''_eq_of_not_mint_shape sf b acc
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
        simp only [modalApplyOneKb5''Prop] at h
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
            exact (modalKb5BoxAllUniv_mem hx).1
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
          · exact (modalKb5BoxAllUniv_mem hx).1
      · obtain ⟨s, ff, l⟩ := sf
        simp only at hs hf; subst hs; subst hf
        have hK := modalApplyOne_diamondNeg_eq
          (⟨.neg, .diamond φ, l⟩ : SignedFormula (Proposition Atom) WorldIndex) rfl φ rfl b acc
        have hKfresh := modalApplyOne_persistent_props
          (⟨.neg, .diamond φ, l⟩ : SignedFormula (Proposition Atom) WorldIndex) b acc
        simp only [modalApplyOneKb5''Prop] at h
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
            exact (modalKb5DiaNegAllUniv_mem hx).1
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
          · exact (modalKb5DiaNegAllUniv_mem hx).1
    · rw [modalApplyOneKb5''Prop_eq_of_not_boxPos_diaNeg sf b acc
          ⟨fun hc => hprop (Or.inl hc), fun hc => hprop (Or.inr hc)⟩] at h
      exact modalApplyOne_persistent_props sf b acc nf h

/-- **F2 discharge for `modalApplyOneKb5''`**. Mirrors `modalApplyOneKb5'_outputsSubsetUniverse`.
Unlike the frozen `Full` version (which routes the self-target case through
`modalKb5BoxAllFull_mem_known`, needing the trigger to be known-and-equal-to-root), the corrected
`Univ` version's self-target case needs no `modalKnownWorlds`-level argument at all: `x.label = 0`
there, and `0 ≤ modalWorldBound φ0` holds unconditionally (`Nat.zero_le`, `WorldIndex := Nat`), so
`mem_modalUniverse_of_Five` discharges it directly off `modalKb5BoxAllUniv_mem`'s dichotomy. -/
private lemma modalApplyOneKb5''_outputsSubsetUniverse
    (φ0 : Proposition Atom) (sf : SignedFormula (Proposition Atom) WorldIndex)
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (hb : ∀ x ∈ b, x ∈ modalUniverse φ0) (hsf : sf ∈ b) (hInv : accFreshInv b acc)
    (hW : modalMaxWorld b < modalWorldBound φ0) :
    (match (modalApplyOneKb5'' sf b acc).fst with
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
      rcases modalApplyOneKb5''_diaPos_eq_or_reuse b acc φ l with heq | ⟨w', hw', heq⟩
      · rw [heq, modalApplyOneKb5''Prop_eq_of_not_boxPos_diaNeg _ b acc (by simp)]
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
      rcases modalApplyOneKb5''_boxNeg_eq_or_reuse b acc φ l with heq | ⟨w', hw', heq⟩
      · rw [heq, modalApplyOneKb5''Prop_eq_of_not_boxPos_diaNeg _ b acc (by simp)]
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
  · rw [modalApplyOneKb5''_eq_of_not_mint_shape sf b acc
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
        simp only [modalApplyOneKb5''Prop]
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
        have hallNew : ∀ x ∈ modalKb5BoxAllUniv b φ l, x ∈ modalUniverse φ0 := by
          intro x hx
          rcases (modalKb5BoxAllUniv_mem hx).2 with ⟨hxeq, hxkn, -⟩ | ⟨hxeq, -⟩
          · have hxle : x.label ≤ modalWorldBound φ0 :=
              le_trans (known_label_le_modalMaxWorld_Five hxkn) (le_of_lt hW)
            rw [hxeq]; exact mem_modalUniverse_of_Five hxle hφsub
          · rw [hxeq]; exact mem_modalUniverse_of_Five (Nat.zero_le _) hφsub
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
        simp only [modalApplyOneKb5''Prop]
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
        have hallNew : ∀ x ∈ modalKb5DiaNegAllUniv b φ l, x ∈ modalUniverse φ0 := by
          intro x hx
          rcases (modalKb5DiaNegAllUniv_mem hx).2 with ⟨hxeq, hxkn, -⟩ | ⟨hxeq, -⟩
          · have hxle : x.label ≤ modalWorldBound φ0 :=
              le_trans (known_label_le_modalMaxWorld_Five hxkn) (le_of_lt hW)
            rw [hxeq]; exact mem_modalUniverse_of_Five hxle hφsub
          · rw [hxeq]; exact mem_modalUniverse_of_Five (Nat.zero_le _) hφsub
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
    · rw [modalApplyOneKb5''Prop_eq_of_not_boxPos_diaNeg sf b acc
          ⟨fun hc => hprop (Or.inl hc), fun hc => hprop (Or.inr hc)⟩] at *
      exact modalApplyOne_outputs_subset φ0 sf b acc hb hsf hInv hW

/-- **F12' discharge for `modalApplyOneKb5''`**: mint (existential) shapes are verbatim
`modalApplyOneFive`'s behavior. Mirrors `modalApplyOneKb5'_diaPosWitness'`. -/
private lemma modalApplyOneKb5''_diaPosWitness'
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (ψ : Proposition Atom) (w : WorldIndex) :
    ∃ w', (modalApplyOneKb5'' (⟨.pos, .diamond ψ, w⟩ : SignedFormula (Proposition Atom) WorldIndex)
        b acc).snd = acc.addEdge w w' ∧
      ∃ rest,
        (modalApplyOneKb5'' (⟨.pos, .diamond ψ, w⟩ : SignedFormula (Proposition Atom) WorldIndex)
            b acc).fst
          = RuleResult.linear
              ((⟨.pos, ψ, w'⟩ : SignedFormula (Proposition Atom) WorldIndex) :: rest) := by
  rcases modalApplyOneKb5''_diaPos_eq_or_reuse b acc ψ w with heqp | ⟨w', -, heqp⟩
  · obtain ⟨hsnd, rest, hfst⟩ := modalApplyOne_diamondPos_witness b acc ψ w
    have heq := modalApplyOneKb5''Prop_eq_of_not_boxPos_diaNeg
      (⟨.pos, .diamond ψ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) b acc (by simp)
    rw [heqp, heq]
    exact ⟨modalNextWorld b, hsnd, rest, hfst⟩
  · exact ⟨w', by rw [heqp], [], by rw [heqp]⟩

/-- **F11' discharge for `modalApplyOneKb5''`**, symmetric to `modalApplyOneKb5''_diaPosWitness'`.
-/
private lemma modalApplyOneKb5''_boxNegWitness'
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (ψ : Proposition Atom) (w : WorldIndex) :
    ∃ w', (modalApplyOneKb5'' (⟨.neg, .box ψ, w⟩ : SignedFormula (Proposition Atom) WorldIndex)
        b acc).snd = acc.addEdge w w' ∧
      ∃ rest,
        (modalApplyOneKb5'' (⟨.neg, .box ψ, w⟩ : SignedFormula (Proposition Atom) WorldIndex)
            b acc).fst
          = RuleResult.linear
              ((⟨.neg, ψ, w'⟩ : SignedFormula (Proposition Atom) WorldIndex) :: rest) := by
  rcases modalApplyOneKb5''_boxNeg_eq_or_reuse b acc ψ w with heqp | ⟨w', -, heqp⟩
  · obtain ⟨hsnd, rest, hfst⟩ := modalApplyOne_boxNeg_witness b acc ψ w
    have heq := modalApplyOneKb5''Prop_eq_of_not_boxPos_diaNeg
      (⟨.neg, .box ψ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) b acc (by simp)
    rw [heqp, heq]
    exact ⟨modalNextWorld b, hsnd, rest, hfst⟩
  · exact ⟨w', by rw [heqp], [], by rw [heqp]⟩

/-- **`modalApplyOneKb5''` satisfies `RuleApplicationSpecCore`**: the corrected-gate full-cluster
rule discharges every field the Hintikka/saturation machinery needs, mirroring
`modalApplyOneKb5'_specCore` declaration-for-declaration. -/
theorem modalApplyOneKb5''_specCore :
    RuleApplicationSpecCore (Atom := Atom) modalApplyOneKb5'' where
  freshLocal := modalApplyOneKb5''_fresh_local
  outputsSubsetUniverse := modalApplyOneKb5''_outputsSubsetUniverse
  persistentFresh := modalApplyOneKb5''_persistentFresh
  branchingLength := modalApplyOneKb5''_branchingLength
  localShapeInvariance := modalApplyOneKb5''_localShapeInvariance
  boxPosNotExpanding := modalApplyOneKb5''_boxPosNotExpanding
  diaNegNotExpanding := modalApplyOneKb5''_diaNegNotExpanding
  boxNegWitness' := modalApplyOneKb5''_boxNegWitness'
  diaPosWitness' := modalApplyOneKb5''_diaPosWitness'

/-! ## `RuleApplicationSpecCore` for `modalApplyOneKb5'` (task 524 Phase 4)

Discharges `RuleApplicationSpecCore modalApplyOneKb5'` (`GenericDriver.lean`), mirroring
`modalApplyOneFive_specCore`'s discharge declaration-for-declaration. The two mint shapes
(`.pos .diamond`/`.neg .box`) are byte-identical to `modalApplyOneFive`'s own discharge (verbatim
witness-reuse behavior, Phase 1); only the two propagation shapes (`.pos .box`/`.neg .diamond`)
need fresh proofs against `modalKb5BoxAllFull`/`modalKb5DiaNegAllFull`'s membership facts. -/

omit [Hashable Atom] in
/-- `modalApplyOneKb5'Prop`'s accessibility output agrees with K's `modalApplyOne` at every
shape. Mirrors `modalApplyOneFiveProp_snd_eq`. -/
lemma modalApplyOneKb5'Prop_snd_eq
    (sf : SignedFormula (Proposition Atom) WorldIndex)
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility) :
    (modalApplyOneKb5'Prop sf b acc).snd = (modalApplyOne sf b acc).snd := by
  unfold modalApplyOneKb5'Prop
  rcases hs : sf.sign with _ | _ <;> rcases hf : sf.formula with _ | _ | _ | _ | _ | φ | φ <;>
    simp_all <;>
    rcases h1 : (modalApplyOne sf b acc).1 with _ | _ | _ | _ <;> simp <;> split <;> simp

omit [Hashable Atom] in
/-- Whenever K's own result is `.linear`, `modalApplyOneKb5'Prop` agrees with `modalApplyOne`
entirely. Mirrors `modalApplyOneFiveProp_eq_of_linear`. -/
lemma modalApplyOneKb5'Prop_eq_of_linear
    (sf : SignedFormula (Proposition Atom) WorldIndex)
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (nf : List (SignedFormula (Proposition Atom) WorldIndex))
    (h : (modalApplyOne sf b acc).fst = RuleResult.linear nf) :
    modalApplyOneKb5'Prop sf b acc = modalApplyOne sf b acc := by
  unfold modalApplyOneKb5'Prop
  rcases hp : modalApplyOne sf b acc with ⟨kResult, kAcc⟩
  rw [hp] at h
  simp only [] at h
  subst h
  rcases hs : sf.sign with _ | _ <;> rcases hf : sf.formula with _ | _ | _ | _ | _ | φ | φ <;>
    simp_all

omit [Hashable Atom] in
/-- Local re-derivation of `modalApplyOneFiveProp_fresh_local_local` for `modalApplyOneKb5'Prop`.
-/
private lemma modalApplyOneKb5'Prop_fresh_local_local
    (sf : SignedFormula (Proposition Atom) WorldIndex)
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility) :
    (modalApplyOneKb5'Prop sf b acc).snd = acc ∨
    (∃ wsf rest, (modalApplyOneKb5'Prop sf b acc).fst = RuleResult.linear (wsf :: rest)
      ∧ (modalApplyOneKb5'Prop sf b acc).snd = acc.addEdge sf.label wsf.label) := by
  rcases modalApplyOne_fresh_local sf b acc with hsame | ⟨wsf, rest, hfst, hsnd⟩
  · exact Or.inl (by rw [modalApplyOneKb5'Prop_snd_eq]; exact hsame)
  · have heq := modalApplyOneKb5'Prop_eq_of_linear sf b acc (wsf :: rest) hfst
    exact Or.inr ⟨wsf, rest, by rw [heq]; exact hfst, by rw [heq]; exact hsnd⟩

/-- **F1 discharge for `modalApplyOneKb5'`**. Mirrors `modalApplyOneFive_fresh_local`. -/
lemma modalApplyOneKb5'_fresh_local
    (sf : SignedFormula (Proposition Atom) WorldIndex)
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility) :
    (modalApplyOneKb5' sf b acc).snd = acc ∨
    (∃ wsf rest, (modalApplyOneKb5' sf b acc).fst = RuleResult.linear (wsf :: rest) ∧
      (modalApplyOneKb5' sf b acc).snd = acc.addEdge sf.label wsf.label) := by
  obtain ⟨s, ff, w⟩ := sf
  rcases s with _ | _
  · rcases ff with _ | _ | ⟨a, c⟩ | ⟨x, y⟩ | ⟨x, y⟩ | φ | φ
    case atom =>
      rw [modalApplyOneKb5'_eq_of_not_mint_shape _ b acc (by simp)]
      exact modalApplyOneKb5'Prop_fresh_local_local _ b acc
    case bot =>
      rw [modalApplyOneKb5'_eq_of_not_mint_shape _ b acc (by simp)]
      exact modalApplyOneKb5'Prop_fresh_local_local _ b acc
    case imp =>
      rw [modalApplyOneKb5'_eq_of_not_mint_shape _ b acc (by simp)]
      exact modalApplyOneKb5'Prop_fresh_local_local _ b acc
    case and =>
      rw [modalApplyOneKb5'_eq_of_not_mint_shape _ b acc (by simp)]
      exact modalApplyOneKb5'Prop_fresh_local_local _ b acc
    case or =>
      rw [modalApplyOneKb5'_eq_of_not_mint_shape _ b acc (by simp)]
      exact modalApplyOneKb5'Prop_fresh_local_local _ b acc
    case box =>
      rw [modalApplyOneKb5'_eq_of_not_mint_shape _ b acc (by simp)]
      exact modalApplyOneKb5'Prop_fresh_local_local _ b acc
    case diamond =>
      rcases modalApplyOneKb5'_diaPos_eq_or_reuse b acc φ w with heq | ⟨w', hw', heq⟩
      · rw [heq, modalApplyOneKb5'Prop_eq_of_not_boxPos_diaNeg _ b acc (by simp)]
        exact modalApplyOne_fresh_local _ b acc
      · rw [heq]
        exact Or.inr ⟨⟨.pos, φ, w'⟩, [], rfl, rfl⟩
  · rcases ff with _ | _ | ⟨a, c⟩ | ⟨x, y⟩ | ⟨x, y⟩ | φ | φ
    case atom =>
      rw [modalApplyOneKb5'_eq_of_not_mint_shape _ b acc (by simp)]
      exact modalApplyOneKb5'Prop_fresh_local_local _ b acc
    case bot =>
      rw [modalApplyOneKb5'_eq_of_not_mint_shape _ b acc (by simp)]
      exact modalApplyOneKb5'Prop_fresh_local_local _ b acc
    case imp =>
      rw [modalApplyOneKb5'_eq_of_not_mint_shape _ b acc (by simp)]
      exact modalApplyOneKb5'Prop_fresh_local_local _ b acc
    case and =>
      rw [modalApplyOneKb5'_eq_of_not_mint_shape _ b acc (by simp)]
      exact modalApplyOneKb5'Prop_fresh_local_local _ b acc
    case or =>
      rw [modalApplyOneKb5'_eq_of_not_mint_shape _ b acc (by simp)]
      exact modalApplyOneKb5'Prop_fresh_local_local _ b acc
    case diamond =>
      rw [modalApplyOneKb5'_eq_of_not_mint_shape _ b acc (by simp)]
      exact modalApplyOneKb5'Prop_fresh_local_local _ b acc
    case box =>
      rcases modalApplyOneKb5'_boxNeg_eq_or_reuse b acc φ w with heq | ⟨w', hw', heq⟩
      · rw [heq, modalApplyOneKb5'Prop_eq_of_not_boxPos_diaNeg _ b acc (by simp)]
        exact modalApplyOne_fresh_local _ b acc
      · rw [heq]
        exact Or.inr ⟨⟨.neg, φ, w'⟩, [], rfl, rfl⟩

omit [Hashable Atom] in
/-- **Combined F9/F10 shape fact for `modalApplyOneKb5'Prop`** (hypothesis-free). Mirrors
`modalApplyOneFiveProp_boxPos_diaNeg_shape`. -/
private lemma modalApplyOneKb5'Prop_boxPos_diaNeg_shape
    (sf : SignedFormula (Proposition Atom) WorldIndex)
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (h : (sf.sign = .pos ∧ ∃ φ, sf.formula = .box φ) ∨
         (sf.sign = .neg ∧ ∃ φ, sf.formula = .diamond φ)) :
    (modalApplyOneKb5'Prop sf b acc).fst = .notApplicable ∨
      ∃ out, (modalApplyOneKb5'Prop sf b acc).fst = .persistent out := by
  rcases h with ⟨hs, φ, hf⟩ | ⟨hs, φ, hf⟩
  · obtain ⟨s, ff, l⟩ := sf
    simp only at hs hf; subst hs; subst hf
    have hK := modalApplyOne_boxPos_eq
      (⟨.pos, .box φ, l⟩ : SignedFormula (Proposition Atom) WorldIndex) rfl φ rfl b acc
    unfold modalApplyOneKb5'Prop
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
    unfold modalApplyOneKb5'Prop
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

/-- **F9 discharge for `modalApplyOneKb5'`**. Mirrors `modalApplyOneFive_boxPosNotExpanding`. -/
private lemma modalApplyOneKb5'_boxPosNotExpanding
    (sf : SignedFormula (Proposition Atom) WorldIndex)
    (hsign : sf.sign = .pos) (ψ : Proposition Atom) (hform : sf.formula = .box ψ)
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility) :
    (modalApplyOneKb5' sf b acc).fst = .notApplicable ∨
      ∃ out, (modalApplyOneKb5' sf b acc).fst = .persistent out := by
  rw [modalApplyOneKb5'_eq_of_not_mint_shape sf b acc (by simp [hsign, hform])]
  exact modalApplyOneKb5'Prop_boxPos_diaNeg_shape sf b acc (Or.inl ⟨hsign, ψ, hform⟩)

/-- **F10 discharge for `modalApplyOneKb5'`**, dual of `modalApplyOneKb5'_boxPosNotExpanding`. -/
private lemma modalApplyOneKb5'_diaNegNotExpanding
    (sf : SignedFormula (Proposition Atom) WorldIndex)
    (hsign : sf.sign = .neg) (ψ : Proposition Atom) (hform : sf.formula = .diamond ψ)
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility) :
    (modalApplyOneKb5' sf b acc).fst = .notApplicable ∨
      ∃ out, (modalApplyOneKb5' sf b acc).fst = .persistent out := by
  rw [modalApplyOneKb5'_eq_of_not_mint_shape sf b acc (by simp [hsign, hform])]
  exact modalApplyOneKb5'Prop_boxPos_diaNeg_shape sf b acc (Or.inr ⟨hsign, ψ, hform⟩)

/-- **F8 discharge for `modalApplyOneKb5'`**. Mirrors `modalApplyOneFive_localShapeInvariance`. -/
private lemma modalApplyOneKb5'_localShapeInvariance
    (s : Sign) (φ : Proposition Atom) (w : WorldIndex)
    (hnb : ∀ ψ, φ ≠ .box ψ) (hnd : ∀ ψ, φ ≠ .diamond ψ)
    (b b' : List (SignedFormula (Proposition Atom) WorldIndex)) (acc acc' : Accessibility) :
    (modalApplyOneKb5' ⟨s, φ, w⟩ b acc).1 = (modalApplyOneKb5' ⟨s, φ, w⟩ b' acc').1 := by
  rw [modalApplyOneKb5'_eq_of_not_mint_shape ⟨s, φ, w⟩ b acc ⟨by simp [hnd], by simp [hnb]⟩,
    modalApplyOneKb5'_eq_of_not_mint_shape ⟨s, φ, w⟩ b' acc' ⟨by simp [hnd], by simp [hnb]⟩,
    modalApplyOneKb5'Prop_eq_of_not_boxPos_diaNeg ⟨s, φ, w⟩ b acc ⟨by simp [hnb], by simp [hnd]⟩,
    modalApplyOneKb5'Prop_eq_of_not_boxPos_diaNeg ⟨s, φ, w⟩ b' acc' ⟨by simp [hnb], by simp [hnd]⟩]
  exact modalApplyOne_fst_eq_of_not_box s φ w hnb hnd b b' acc acc'

/-- **F7 discharge for `modalApplyOneKb5'`**. Mirrors `modalApplyOneFive_branchingLength`. -/
private lemma modalApplyOneKb5'_branchingLength
    (sf : SignedFormula (Proposition Atom) WorldIndex)
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (brs : List (List (SignedFormula (Proposition Atom) WorldIndex)))
    (h : (modalApplyOneKb5' sf b acc).fst = RuleResult.branching brs) :
    brs.length = 2 := by
  by_cases hmint : (sf.sign = .pos ∧ ∃ φ, sf.formula = .diamond φ) ∨
      (sf.sign = .neg ∧ ∃ φ, sf.formula = .box φ)
  · rcases hmint with ⟨hs, φ, hf⟩ | ⟨hs, φ, hf⟩
    · obtain ⟨s, ff, w⟩ := sf
      simp only at hs hf; subst hs; subst hf
      rcases modalApplyOneKb5'_diaPos_eq_or_reuse b acc φ w with heq | ⟨w', -, heq⟩
      · rw [heq, modalApplyOneKb5'Prop_eq_of_not_boxPos_diaNeg _ b acc (by simp)] at h
        exact modalApplyOne_branching_length _ b acc brs h
      · rw [heq] at h; simp at h
    · obtain ⟨s, ff, w⟩ := sf
      simp only at hs hf; subst hs; subst hf
      rcases modalApplyOneKb5'_boxNeg_eq_or_reuse b acc φ w with heq | ⟨w', -, heq⟩
      · rw [heq, modalApplyOneKb5'Prop_eq_of_not_boxPos_diaNeg _ b acc (by simp)] at h
        exact modalApplyOne_branching_length _ b acc brs h
      · rw [heq] at h; simp at h
  · rw [modalApplyOneKb5'_eq_of_not_mint_shape sf b acc
        ⟨fun hc => hmint (Or.inl hc), fun hc => hmint (Or.inr hc)⟩] at h
    by_cases hprop : (sf.sign = .pos ∧ ∃ φ, sf.formula = .box φ) ∨
        (sf.sign = .neg ∧ ∃ φ, sf.formula = .diamond φ)
    · exfalso
      rcases modalApplyOneKb5'Prop_boxPos_diaNeg_shape sf b acc hprop with hna | ⟨out, hpe⟩
      · rw [hna] at h; simp at h
      · rw [hpe] at h; simp at h
    · rw [modalApplyOneKb5'Prop_eq_of_not_boxPos_diaNeg sf b acc
          ⟨fun hc => hprop (Or.inl hc), fun hc => hprop (Or.inr hc)⟩] at h
      exact modalApplyOne_branching_length sf b acc brs h

/-- **F3 discharge for `modalApplyOneKb5'`**. Mirrors `modalApplyOneFive_persistentFresh`. -/
private lemma modalApplyOneKb5'_persistentFresh
    (sf : SignedFormula (Proposition Atom) WorldIndex)
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (nf : List (SignedFormula (Proposition Atom) WorldIndex))
    (h : (modalApplyOneKb5' sf b acc).fst = RuleResult.persistent nf) :
    nf ≠ [] ∧ ∀ x ∈ nf, x ∉ b := by
  by_cases hmint : (sf.sign = .pos ∧ ∃ φ, sf.formula = .diamond φ) ∨
      (sf.sign = .neg ∧ ∃ φ, sf.formula = .box φ)
  · rcases hmint with ⟨hs, φ, hf⟩ | ⟨hs, φ, hf⟩
    · obtain ⟨s, ff, w⟩ := sf
      simp only at hs hf; subst hs; subst hf
      rcases modalApplyOneKb5'_diaPos_eq_or_reuse b acc φ w with heq | ⟨w', -, heq⟩
      · rw [heq, modalApplyOneKb5'Prop_eq_of_not_boxPos_diaNeg _ b acc (by simp)] at h
        exact modalApplyOne_persistent_props _ b acc nf h
      · rw [heq] at h; simp at h
    · obtain ⟨s, ff, w⟩ := sf
      simp only at hs hf; subst hs; subst hf
      rcases modalApplyOneKb5'_boxNeg_eq_or_reuse b acc φ w with heq | ⟨w', -, heq⟩
      · rw [heq, modalApplyOneKb5'Prop_eq_of_not_boxPos_diaNeg _ b acc (by simp)] at h
        exact modalApplyOne_persistent_props _ b acc nf h
      · rw [heq] at h; simp at h
  · rw [modalApplyOneKb5'_eq_of_not_mint_shape sf b acc
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
        simp only [modalApplyOneKb5'Prop] at h
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
            exact (modalKb5BoxAllFull_mem hx).1
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
          · exact (modalKb5BoxAllFull_mem hx).1
      · obtain ⟨s, ff, l⟩ := sf
        simp only at hs hf; subst hs; subst hf
        have hK := modalApplyOne_diamondNeg_eq
          (⟨.neg, .diamond φ, l⟩ : SignedFormula (Proposition Atom) WorldIndex) rfl φ rfl b acc
        have hKfresh := modalApplyOne_persistent_props
          (⟨.neg, .diamond φ, l⟩ : SignedFormula (Proposition Atom) WorldIndex) b acc
        simp only [modalApplyOneKb5'Prop] at h
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
            exact (modalKb5DiaNegAllFull_mem hx).1
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
          · exact (modalKb5DiaNegAllFull_mem hx).1
    · rw [modalApplyOneKb5'Prop_eq_of_not_boxPos_diaNeg sf b acc
          ⟨fun hc => hprop (Or.inl hc), fun hc => hprop (Or.inr hc)⟩] at h
      exact modalApplyOne_persistent_props sf b acc nf h

/-- **F2 discharge for `modalApplyOneKb5'`**. Mirrors `modalApplyOneFive_outputsSubsetUniverse`.
The self-target case (`x.label = 0`) needs no separate world-bound argument: `0 ≤ modalWorldBound
φ0` holds unconditionally (`Nat.zero_le`), so `mem_modalUniverse_of_Five` discharges it exactly
like any other target once `x = ⟨.pos, φ, x.label⟩` is known
(`modalKb5BoxAllFull_mem_eq`)/(`modalKb5DiaNegAllFull_mem_eq`). -/
private lemma modalApplyOneKb5'_outputsSubsetUniverse
    (φ0 : Proposition Atom) (sf : SignedFormula (Proposition Atom) WorldIndex)
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (hb : ∀ x ∈ b, x ∈ modalUniverse φ0) (hsf : sf ∈ b) (hInv : accFreshInv b acc)
    (hW : modalMaxWorld b < modalWorldBound φ0) :
    (match (modalApplyOneKb5' sf b acc).fst with
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
      rcases modalApplyOneKb5'_diaPos_eq_or_reuse b acc φ l with heq | ⟨w', hw', heq⟩
      · rw [heq, modalApplyOneKb5'Prop_eq_of_not_boxPos_diaNeg _ b acc (by simp)]
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
      rcases modalApplyOneKb5'_boxNeg_eq_or_reuse b acc φ l with heq | ⟨w', hw', heq⟩
      · rw [heq, modalApplyOneKb5'Prop_eq_of_not_boxPos_diaNeg _ b acc (by simp)]
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
  · rw [modalApplyOneKb5'_eq_of_not_mint_shape sf b acc
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
        simp only [modalApplyOneKb5'Prop]
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
        have hallNew : ∀ x ∈ modalKb5BoxAllFull b φ l, x ∈ modalUniverse φ0 := by
          intro x hx
          have hxeq : x = (⟨.pos, φ, x.label⟩ : SignedFormula (Proposition Atom) WorldIndex) :=
            modalKb5BoxAllFull_mem_eq hx
          have hlknown : l ∈ modalKnownWorlds b := label_mem_modalKnownWorlds hsf
          have hxknown : x.label ∈ modalKnownWorlds b :=
            modalKb5BoxAllFull_mem_known hx hlknown
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
        simp only [modalApplyOneKb5'Prop]
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
        have hallNew : ∀ x ∈ modalKb5DiaNegAllFull b φ l, x ∈ modalUniverse φ0 := by
          intro x hx
          have hxeq : x = (⟨.neg, φ, x.label⟩ : SignedFormula (Proposition Atom) WorldIndex) :=
            modalKb5DiaNegAllFull_mem_eq hx
          have hlknown : l ∈ modalKnownWorlds b := label_mem_modalKnownWorlds hsf
          have hxknown : x.label ∈ modalKnownWorlds b :=
            modalKb5DiaNegAllFull_mem_known hx hlknown
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
    · rw [modalApplyOneKb5'Prop_eq_of_not_boxPos_diaNeg sf b acc
          ⟨fun hc => hprop (Or.inl hc), fun hc => hprop (Or.inr hc)⟩] at *
      exact modalApplyOne_outputs_subset φ0 sf b acc hb hsf hInv hW

/-- **F12' discharge for `modalApplyOneKb5'`**: mint (existential) shapes are verbatim
`modalApplyOneFive`'s behavior. Mirrors `modalApplyOneFive_diaPosWitness'`. -/
private lemma modalApplyOneKb5'_diaPosWitness'
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (ψ : Proposition Atom) (w : WorldIndex) :
    ∃ w', (modalApplyOneKb5' (⟨.pos, .diamond ψ, w⟩ : SignedFormula (Proposition Atom) WorldIndex)
        b acc).snd = acc.addEdge w w' ∧
      ∃ rest,
        (modalApplyOneKb5' (⟨.pos, .diamond ψ, w⟩ : SignedFormula (Proposition Atom) WorldIndex)
            b acc).fst
          = RuleResult.linear
              ((⟨.pos, ψ, w'⟩ : SignedFormula (Proposition Atom) WorldIndex) :: rest) := by
  rcases modalApplyOneKb5'_diaPos_eq_or_reuse b acc ψ w with heqp | ⟨w', -, heqp⟩
  · obtain ⟨hsnd, rest, hfst⟩ := modalApplyOne_diamondPos_witness b acc ψ w
    have heq := modalApplyOneKb5'Prop_eq_of_not_boxPos_diaNeg
      (⟨.pos, .diamond ψ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) b acc (by simp)
    rw [heqp, heq]
    exact ⟨modalNextWorld b, hsnd, rest, hfst⟩
  · exact ⟨w', by rw [heqp], [], by rw [heqp]⟩

/-- **F11' discharge for `modalApplyOneKb5'`**, symmetric to `modalApplyOneKb5'_diaPosWitness'`.
-/
private lemma modalApplyOneKb5'_boxNegWitness'
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (ψ : Proposition Atom) (w : WorldIndex) :
    ∃ w', (modalApplyOneKb5' (⟨.neg, .box ψ, w⟩ : SignedFormula (Proposition Atom) WorldIndex)
        b acc).snd = acc.addEdge w w' ∧
      ∃ rest,
        (modalApplyOneKb5' (⟨.neg, .box ψ, w⟩ : SignedFormula (Proposition Atom) WorldIndex)
            b acc).fst
          = RuleResult.linear
              ((⟨.neg, ψ, w'⟩ : SignedFormula (Proposition Atom) WorldIndex) :: rest) := by
  rcases modalApplyOneKb5'_boxNeg_eq_or_reuse b acc ψ w with heqp | ⟨w', -, heqp⟩
  · obtain ⟨hsnd, rest, hfst⟩ := modalApplyOne_boxNeg_witness b acc ψ w
    have heq := modalApplyOneKb5'Prop_eq_of_not_boxPos_diaNeg
      (⟨.neg, .box ψ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) b acc (by simp)
    rw [heqp, heq]
    exact ⟨modalNextWorld b, hsnd, rest, hfst⟩
  · exact ⟨w', by rw [heqp], [], by rw [heqp]⟩

/-- **`modalApplyOneKb5'` satisfies `RuleApplicationSpecCore`** (task 524 Phase 4): the
full-cluster-propagation rule discharges every field the Hintikka/saturation machinery needs,
mirroring `modalApplyOneFive_specCore` declaration-for-declaration. -/
theorem modalApplyOneKb5'_specCore :
    RuleApplicationSpecCore (Atom := Atom) modalApplyOneKb5' where
  freshLocal := modalApplyOneKb5'_fresh_local
  outputsSubsetUniverse := modalApplyOneKb5'_outputsSubsetUniverse
  persistentFresh := modalApplyOneKb5'_persistentFresh
  branchingLength := modalApplyOneKb5'_branchingLength
  localShapeInvariance := modalApplyOneKb5'_localShapeInvariance
  boxPosNotExpanding := modalApplyOneKb5'_boxPosNotExpanding
  diaNegNotExpanding := modalApplyOneKb5'_diaNegNotExpanding
  boxNegWitness' := modalApplyOneKb5'_boxNegWitness'
  diaPosWitness' := modalApplyOneKb5'_diaPosWitness'

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

/-! ## Step-Preservation of `FiveWorldInv` (task 515 Phase 21b: the Hintikka "wall")

The inductive step-preservation proof `FiveSimplification.lean`'s own docstring above flagged as
deferred. Mirrors `S5Simplification.lean`'s `modalApplyOneS5w_step` /
`modalStepBranchS5w_preserves_worldInv`, doubled for the root/non-root source-class split
`FiveWorldInv` introduces, **plus one genuine refinement `S5wWorldInv`'s single-class shape did
not need**: a root-triggered mint (`sf.label = 0`) consumes a tag that was already counted in
`usedTagsFiveRoot` the moment its TRIGGER first appeared on the branch (mere presence, not
processing) — chronologically *before* the mint itself fires. A bare, `e`-independent per-step
argument therefore cannot show `usedTagsFiveRoot`'s cardinality grows exactly when the root mint
fires (it does not; it already counted the tag). The fix threads the expanded-set `e` (already
present in `AuxStepPreserved`'s signature for exactly this kind of need) into a refined,
`e`-aware root-tag counter `expandedRootTagsFive`, counting a root tag only once its unique
trigger occurrence has been *dequeued* (`e`-membership), not merely present on `b`. This
strictly grows at the exact step a root-triggered mint fires (the trigger moves from
not-expanded to expanded), restoring the same "count grows in lockstep with `modalMaxWorld`"
argument `usedTagsFiveNonRoot` already gives non-root mints for free. Since
`expandedRootTagsFive φ₀ b e ⊆ usedTagsFiveRoot φ₀ b` unconditionally (a strictly stronger
filter predicate), the final bound consumed by `ModalLoopAuxFive_bounds` still routes through the
already-landed, `e`-independent `FiveWorldInv`/`modalMaxWorld_lt_worldBound_of_FiveWorldInv`
unchanged. -/

omit [Hashable Atom] in
/-- **`e`-aware root-tag counter**: the subset of `mintTags φ₀` whose root-mint TRIGGER is not
merely present on `b` (as `usedTagsFiveRoot` counts) but has already been *dequeued/processed*
(is a member of the expanded set `e`). Strictly stronger filter predicate than
`usedTagsFiveRoot`'s (adds the `e.any` conjunct), so `expandedRootTagsFive φ₀ b e ⊆
usedTagsFiveRoot φ₀ b` holds with no side hypothesis relating `e` to `b`
(`expandedRootTagsFive_subset_usedTagsFiveRoot` below). -/
def expandedRootTagsFive (φ₀ : Proposition Atom)
    (b e : List (SignedFormula (Proposition Atom) WorldIndex)) :
    Finset (Sign × Proposition Atom) :=
  (mintTags φ₀).filter (fun p =>
    b.any (fun x => x.label == (0 : WorldIndex) &&
      ((p.1 == Sign.pos && x.sign == Sign.pos && x.formula == Proposition.diamond p.2) ||
       (p.1 == Sign.neg && x.sign == Sign.neg && x.formula == Proposition.box p.2)) &&
      e.any (· == x)))

omit [Hashable Atom] in
/-- `expandedRootTagsFive φ₀ b e ⊆ usedTagsFiveRoot φ₀ b`: dropping the extra `e.any` conjunct
from `expandedRootTagsFive`'s filter predicate gives exactly `usedTagsFiveRoot`'s predicate, so
this is immediate from `Finset.filter_subset`-style monotonicity of `Finset.filter` under a
weaker predicate. -/
lemma expandedRootTagsFive_subset_usedTagsFiveRoot (φ₀ : Proposition Atom)
    (b e : List (SignedFormula (Proposition Atom) WorldIndex)) :
    expandedRootTagsFive φ₀ b e ⊆ usedTagsFiveRoot φ₀ b := by
  intro p hp
  simp only [expandedRootTagsFive, Finset.mem_filter] at hp
  obtain ⟨hp1, hp2⟩ := hp
  simp only [usedTagsFiveRoot, Finset.mem_filter]
  refine ⟨hp1, ?_⟩
  obtain ⟨x, hx, hxeq⟩ := List.any_eq_true.mp hp2
  simp only [Bool.and_eq_true] at hxeq
  exact List.any_eq_true.mpr ⟨x, hx, by simp [hxeq.1]⟩

omit [Hashable Atom] in
/-- `expandedRootTagsFive` is monotone under branch AND expanded-set growth together (the shape
`AuxStepPreserved`'s step lemma needs: both `b` and `e` grow across a step). -/
lemma expandedRootTagsFive_mono {φ₀ : Proposition Atom}
    {b b' e e' : List (SignedFormula (Proposition Atom) WorldIndex)}
    (hb : ∀ x ∈ b, x ∈ b') (he : ∀ x ∈ e, x ∈ e') :
    expandedRootTagsFive φ₀ b e ⊆ expandedRootTagsFive φ₀ b' e' := by
  intro p hp
  simp only [expandedRootTagsFive, Finset.mem_filter] at hp ⊢
  obtain ⟨hp1, hp2⟩ := hp
  refine ⟨hp1, ?_⟩
  obtain ⟨x, hxmem, hxeq⟩ := List.any_eq_true.mp hp2
  simp only [Bool.and_eq_true] at hxeq
  obtain ⟨⟨hxlab, hxshape⟩, hxexp⟩ := hxeq
  obtain ⟨y, hymem, hyeq⟩ := List.any_eq_true.mp hxexp
  have hyx : y = x := beq_iff_eq.mp hyeq
  refine List.any_eq_true.mpr ⟨x, hb x hxmem, ?_⟩
  simp only [Bool.and_eq_true]
  exact ⟨⟨hxlab, hxshape⟩, List.any_eq_true.mpr ⟨x, he x (hyx ▸ hymem), by simp⟩⟩

/-- **`e`-aware source-split world-bound invariant**: the version of `FiveWorldInv` that
`ModalLoopAuxFive` actually threads, replacing the presence-based `usedTagsFiveRoot` with the
dequeued-based `expandedRootTagsFive` so the per-step argument at a root-triggered mint (which
consumes a tag counted at TRIGGER-APPEARANCE time, strictly before the mint) goes through. Implies
plain `FiveWorldInv` via `expandedRootTagsFive_subset_usedTagsFiveRoot`
(`FiveWorldInvE_imp_FiveWorldInv` below). -/
def FiveWorldInvE (φ₀ : Proposition Atom)
    (b e : List (SignedFormula (Proposition Atom) WorldIndex)) : Prop :=
  modalMaxWorld b ≤ (usedTagsFiveNonRoot φ₀ b).card + (expandedRootTagsFive φ₀ b e).card

omit [Hashable Atom] in
lemma FiveWorldInvE_imp_FiveWorldInv {φ₀ : Proposition Atom}
    {b e : List (SignedFormula (Proposition Atom) WorldIndex)} (h : FiveWorldInvE φ₀ b e) :
    FiveWorldInv φ₀ b := by
  unfold FiveWorldInvE at h
  unfold FiveWorldInv
  refine le_trans h (Nat.add_le_add_left ?_ _)
  exact Finset.card_le_card (expandedRootTagsFive_subset_usedTagsFiveRoot φ₀ b e)

/-! ### K-Level Mint-Shape Unfold Helpers

Pure K mechanics (no S5/Five content): the two mint shapes' (`T(◇φ)@w`, `F(□φ)@w`) `.fst`
computation and the uniform-fresh-label fact about it, extracted once so both the root-triggered
and non-root-reuse-missed branches below (which both fall through to this exact K computation)
can share the same two small proofs. Mirrors the inline unfold `modalApplyOneS5w_step`
(`S5Simplification.lean`) performs at its own "none" branches. -/

omit [Hashable Atom] in
private lemma modalApplyOne_diamondPos_mint_fst
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (φ : Proposition Atom) (w : WorldIndex) :
    (modalApplyOne (⟨.pos, .diamond φ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) b acc).fst
      = RuleResult.linear ((⟨.pos, φ, modalNextWorld b⟩ :
          SignedFormula (Proposition Atom) WorldIndex) ::
        (boxPositivesOf b).filterMap (fun (ψ, src) =>
          if src == w then
            let sf' : SignedFormula (Proposition Atom) WorldIndex := ⟨.pos, ψ, modalNextWorld b⟩
            if b.any (· == sf') then none else some sf'
          else none) ++
        b.filterMap (fun sf' =>
          if sf'.sign == .neg && sf'.label == w then
            match sf'.formula with
            | .diamond ψ =>
              let prop : SignedFormula (Proposition Atom) WorldIndex := ⟨.neg, ψ, modalNextWorld b⟩
              if b.any (· == prop) then none else some prop
            | _ => none
          else none)) := by
  have htry : (tryAllPropRules modalAndOf? modalOrOf? modalImpOf? modalNegOf?
      (⟨.pos, .diamond φ, w⟩ : SignedFormula (Proposition Atom) WorldIndex)).isApplicable
        = false := by
    rw [tryAllPropRules_pos]
    simp [modalAndOf?, modalOrOf?, modalImpOf?, modalNegOf?, RuleResult.isApplicable]
  simp only [modalApplyOne]
  rw [if_neg (by simp [htry])]
  rfl

omit [Hashable Atom] in
private lemma modalApplyOne_diamondPos_mint_label
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (φ : Proposition Atom)
    (w : WorldIndex) :
    ∀ z ∈ ((⟨.pos, φ, modalNextWorld b⟩ : SignedFormula (Proposition Atom) WorldIndex) ::
        (boxPositivesOf b).filterMap (fun (ψ, src) =>
          if src == w then
            let sf' : SignedFormula (Proposition Atom) WorldIndex := ⟨.pos, ψ, modalNextWorld b⟩
            if b.any (· == sf') then none else some sf'
          else none) ++
        b.filterMap (fun sf' =>
          if sf'.sign == .neg && sf'.label == w then
            match sf'.formula with
            | .diamond ψ =>
              let prop : SignedFormula (Proposition Atom) WorldIndex := ⟨.neg, ψ, modalNextWorld b⟩
              if b.any (· == prop) then none else some prop
            | _ => none
          else none)),
      z.label = modalNextWorld b := by
  intro z hz
  simp only [List.mem_cons, List.mem_append] at hz
  rcases hz with (rfl | hbox) | hdia
  · rfl
  · simp only [List.mem_filterMap] at hbox
    obtain ⟨⟨ψ, src⟩, -, heq⟩ := hbox
    split at heq
    · split at heq
      · simp at heq
      · simp only [Option.some.injEq] at heq; rw [← heq]
    · simp at heq
  · simp only [List.mem_filterMap] at hdia
    obtain ⟨sf', -, heq⟩ := hdia
    split at heq
    · split at heq
      · rename_i ψ hform
        split at heq
        · simp at heq
        · simp only [Option.some.injEq] at heq; rw [← heq]
      · simp at heq
    · simp at heq

omit [Hashable Atom] in
private lemma modalApplyOne_boxNeg_mint_fst
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (φ : Proposition Atom) (w : WorldIndex) :
    (modalApplyOne (⟨.neg, .box φ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) b acc).fst
      = RuleResult.linear ((⟨.neg, φ, modalNextWorld b⟩ :
          SignedFormula (Proposition Atom) WorldIndex) ::
        (boxPositivesOf b).filterMap (fun (ψ, src) =>
          if src == w then
            let sf' : SignedFormula (Proposition Atom) WorldIndex := ⟨.pos, ψ, modalNextWorld b⟩
            if b.any (· == sf') then none else some sf'
          else none) ++
        b.filterMap (fun sf' =>
          if sf'.sign == .neg && sf'.label == w then
            match sf'.formula with
            | .diamond ψ =>
              let prop : SignedFormula (Proposition Atom) WorldIndex := ⟨.neg, ψ, modalNextWorld b⟩
              if b.any (· == prop) then none else some prop
            | _ => none
          else none)) := by
  have htry : (tryAllPropRules modalAndOf? modalOrOf? modalImpOf? modalNegOf?
      (⟨.neg, .box φ, w⟩ : SignedFormula (Proposition Atom) WorldIndex)).isApplicable
        = false := by
    rw [tryAllPropRules_neg]
    simp [modalAndOf?, modalOrOf?, modalImpOf?, modalNegOf?, RuleResult.isApplicable]
  simp only [modalApplyOne]
  rw [if_neg (by simp [htry])]
  rfl

omit [Hashable Atom] in
private lemma modalApplyOne_boxNeg_mint_label
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (φ : Proposition Atom)
    (w : WorldIndex) :
    ∀ z ∈ ((⟨.neg, φ, modalNextWorld b⟩ : SignedFormula (Proposition Atom) WorldIndex) ::
        (boxPositivesOf b).filterMap (fun (ψ, src) =>
          if src == w then
            let sf' : SignedFormula (Proposition Atom) WorldIndex := ⟨.pos, ψ, modalNextWorld b⟩
            if b.any (· == sf') then none else some sf'
          else none) ++
        b.filterMap (fun sf' =>
          if sf'.sign == .neg && sf'.label == w then
            match sf'.formula with
            | .diamond ψ =>
              let prop : SignedFormula (Proposition Atom) WorldIndex := ⟨.neg, ψ, modalNextWorld b⟩
              if b.any (· == prop) then none else some prop
            | _ => none
          else none)),
      z.label = modalNextWorld b := by
  intro z hz
  simp only [List.mem_cons, List.mem_append] at hz
  rcases hz with (rfl | hbox) | hdia
  · rfl
  · simp only [List.mem_filterMap] at hbox
    obtain ⟨⟨ψ, src⟩, -, heq⟩ := hbox
    split at heq
    · split at heq
      · simp at heq
      · simp only [Option.some.injEq] at heq; rw [← heq]
    · simp at heq
  · simp only [List.mem_filterMap] at hdia
    obtain ⟨sf', -, heq⟩ := hdia
    split at heq
    · split at heq
      · rename_i ψ hform
        split at heq
        · simp at heq
        · simp only [Option.some.injEq] at heq; rw [← heq]
      · simp at heq
    · simp at heq

/-- **World-growth dichotomy for `modalApplyOneFive`** (Phase 21b's per-call step lemma, mirroring
`modalApplyOneS5w_step` but split for `FiveWorldInvE`'s root/non-root division): given `sf`'s
formula is a subformula of `φ₀` (so any tag it mints belongs to `mintTags φ₀`), EITHER (a) every
emitted formula lands at an already-known world (propagation, witness reuse, or propositional
decomposition -- no growth), OR (b) a genuine NON-ROOT-triggered fresh mint occurred (the tag was
not yet in `usedTagsFiveNonRoot`), OR (c) a genuine ROOT-triggered fresh mint occurred
(`sf.label = 0`, unconditional per `modalApplyOneFive`'s guard -- no "not yet used" side
condition needed, since the root arm never consults a witness search). -/
lemma modalApplyOneFive_worldGrowth {φ₀ : Proposition Atom}
    (sf : SignedFormula (Proposition Atom) WorldIndex)
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (hsfmem : sf ∈ b) (hknown : accTargetsKnown b acc)
    (hsfform : sf.formula ∈ modalSubfmls φ₀) :
    (match (modalApplyOneFive sf b acc).fst with
      | .linear formulas =>
          (∀ x ∈ formulas, x.label ∈ modalKnownWorlds b) ∨
          (∃ s ψ, (s, ψ) ∉ usedTagsFiveNonRoot φ₀ b ∧ (s, ψ) ∈ mintTags φ₀ ∧
            (⟨s, ψ, modalNextWorld b⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈
              formulas ∧
            ∀ x ∈ formulas, x.label = modalNextWorld b) ∨
          (sf.label = (0 : WorldIndex) ∧ ∃ ψ,
            ((sf.sign = Sign.pos ∧ sf.formula = Proposition.diamond ψ) ∨
             (sf.sign = Sign.neg ∧ sf.formula = Proposition.box ψ)) ∧
            (sf.sign, ψ) ∈ mintTags φ₀ ∧
            (⟨sf.sign, ψ, modalNextWorld b⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈
              formulas ∧
            ∀ x ∈ formulas, x.label = modalNextWorld b)
      | .branching branches => ∀ x ∈ branches.flatten, x.label ∈ modalKnownWorlds b
      | .persistent formulas => ∀ x ∈ formulas, x.label ∈ modalKnownWorlds b
      | .notApplicable => True) := by
  by_cases hmint : (sf.sign = Sign.pos ∧ ∃ φ, sf.formula = Proposition.diamond φ) ∨
      (sf.sign = Sign.neg ∧ ∃ φ, sf.formula = Proposition.box φ)
  · rcases hmint with ⟨hs, φ, hf⟩ | ⟨hs, φ, hf⟩
    · obtain ⟨s, ff, w⟩ := sf
      simp only at hs hf hsfform
      subst hs; subst hf
      have hφmem : φ ∈ modalSubfmls (Proposition.diamond φ) :=
        List.mem_cons_of_mem _ (modalSubfmls_self_mem φ)
      have hφsub : φ ∈ modalSubfmls φ₀ := modalSubfmls_trans_Five hφmem hsfform
      have htagmem : (Sign.pos, φ) ∈ mintTags φ₀ := mem_mintTags_of_diamond_mem hsfform
      by_cases hz : w = (0 : WorldIndex)
      · subst hz
        have heq : modalApplyOneFive
            (⟨.pos, .diamond φ, (0 : WorldIndex)⟩ : SignedFormula (Proposition Atom) WorldIndex)
            b acc =
            modalApplyOneFiveProp
              (⟨.pos, .diamond φ, (0 : WorldIndex)⟩ :
                SignedFormula (Proposition Atom) WorldIndex) b acc := by
          unfold modalApplyOneFive; simp
        rw [heq, modalApplyOneFiveProp_eq_of_not_boxPos_diaNeg _ b acc (by simp),
          modalApplyOne_diamondPos_mint_fst]
        exact Or.inr (Or.inr ⟨rfl, φ, Or.inl ⟨rfl, rfl⟩, htagmem, List.mem_cons_self,
          modalApplyOne_diamondPos_mint_label b φ (0 : WorldIndex)⟩)
      · cases hw : witnessWorldFive b Sign.pos φ with
        | none =>
          have heq : modalApplyOneFive
              (⟨.pos, .diamond φ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) b acc =
              modalApplyOneFiveProp
                (⟨.pos, .diamond φ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) b acc := by
            unfold modalApplyOneFive
            dsimp only
            rw [if_neg (by simpa using hz), hw]
          rw [heq, modalApplyOneFiveProp_eq_of_not_boxPos_diaNeg _ b acc (by simp),
            modalApplyOne_diamondPos_mint_fst]
          exact Or.inr (Or.inl ⟨Sign.pos, φ,
            witnessWorldFive_none_not_mem_usedTagsFiveNonRoot hw, htagmem, List.mem_cons_self,
            modalApplyOne_diamondPos_mint_label b φ w⟩)
        | some w' =>
          have heq : modalApplyOneFive
              (⟨.pos, .diamond φ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) b acc =
              (RuleResult.linear [⟨.pos, φ, w'⟩], acc.addEdge w w') := by
            unfold modalApplyOneFive
            dsimp only
            rw [if_neg (by simpa using hz), hw]
          rw [heq]
          refine Or.inl (fun z hz' => ?_)
          simp only [List.mem_singleton] at hz'; subst hz'
          exact label_mem_modalKnownWorlds (witnessWorldFive_mem hw).1
    · obtain ⟨s, ff, w⟩ := sf
      simp only at hs hf hsfform
      subst hs; subst hf
      have hφmem : φ ∈ modalSubfmls (Proposition.box φ) :=
        List.mem_cons_of_mem _ (modalSubfmls_self_mem φ)
      have hφsub : φ ∈ modalSubfmls φ₀ := modalSubfmls_trans_Five hφmem hsfform
      have htagmem : (Sign.neg, φ) ∈ mintTags φ₀ := mem_mintTags_of_box_mem hsfform
      by_cases hz : w = (0 : WorldIndex)
      · subst hz
        have heq : modalApplyOneFive
            (⟨.neg, .box φ, (0 : WorldIndex)⟩ : SignedFormula (Proposition Atom) WorldIndex)
            b acc =
            modalApplyOneFiveProp
              (⟨.neg, .box φ, (0 : WorldIndex)⟩ :
                SignedFormula (Proposition Atom) WorldIndex) b acc := by
          unfold modalApplyOneFive; simp
        rw [heq, modalApplyOneFiveProp_eq_of_not_boxPos_diaNeg _ b acc (by simp),
          modalApplyOne_boxNeg_mint_fst]
        exact Or.inr (Or.inr ⟨rfl, φ, Or.inr ⟨rfl, rfl⟩, htagmem, List.mem_cons_self,
          modalApplyOne_boxNeg_mint_label b φ (0 : WorldIndex)⟩)
      · cases hw : witnessWorldFive b Sign.neg φ with
        | none =>
          have heq : modalApplyOneFive
              (⟨.neg, .box φ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) b acc =
              modalApplyOneFiveProp
                (⟨.neg, .box φ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) b acc := by
            unfold modalApplyOneFive
            dsimp only
            rw [if_neg (by simpa using hz), hw]
          rw [heq, modalApplyOneFiveProp_eq_of_not_boxPos_diaNeg _ b acc (by simp),
            modalApplyOne_boxNeg_mint_fst]
          exact Or.inr (Or.inl ⟨Sign.neg, φ,
            witnessWorldFive_none_not_mem_usedTagsFiveNonRoot hw, htagmem, List.mem_cons_self,
            modalApplyOne_boxNeg_mint_label b φ w⟩)
        | some w' =>
          have heq : modalApplyOneFive
              (⟨.neg, .box φ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) b acc =
              (RuleResult.linear [⟨.neg, φ, w'⟩], acc.addEdge w w') := by
            unfold modalApplyOneFive
            dsimp only
            rw [if_neg (by simpa using hz), hw]
          rw [heq]
          refine Or.inl (fun z hz' => ?_)
          simp only [List.mem_singleton] at hz'; subst hz'
          exact label_mem_modalKnownWorlds (witnessWorldFive_mem hw).1
  · rw [modalApplyOneFive_eq_of_not_mint_shape sf b acc
        ⟨fun hc => hmint (Or.inl hc), fun hc => hmint (Or.inr hc)⟩]
    by_cases hprop : (sf.sign = Sign.pos ∧ ∃ φ, sf.formula = Proposition.box φ) ∨
        (sf.sign = Sign.neg ∧ ∃ φ, sf.formula = Proposition.diamond φ)
    · obtain ⟨hsndeq, hor⟩ := modalApplyOneFiveProp_boxPos_diaNeg_eq sf b acc hsfmem hknown hprop
      rcases hor with hnot | ⟨out, hpers, hlabel⟩
      · rw [hnot]; trivial
      · rw [hpers]; exact hlabel
    · rw [modalApplyOneFiveProp_eq_of_not_boxPos_diaNeg sf b acc
          ⟨fun hc => hprop (Or.inl hc), fun hc => hprop (Or.inr hc)⟩]
      have hsflabel : sf.label ∈ modalKnownWorlds b :=
        (mem_modalKnownWorlds_Five b sf.label).mpr ⟨sf, hsfmem, rfl⟩
      have hprop2 := modalApplyOne_prop_outputs_subset sf
      unfold modalApplyOne
      by_cases hpa :
          (tryAllPropRules modalAndOf? modalOrOf? modalImpOf? modalNegOf? sf).isApplicable
      · simp only [hpa, if_true]
        rcases hpr : tryAllPropRules modalAndOf? modalOrOf? modalImpOf? modalNegOf? sf with
          formulas | branches | formulas | -
        · rw [hpr] at hprop2
          refine Or.inl (fun z hz => ?_)
          rw [(hprop2 z hz).2]; exact hsflabel
        · rw [hpr] at hprop2
          intro z hz
          rw [(hprop2 z hz).2]; exact hsflabel
        · rw [hpr] at hprop2
          intro z hz
          rw [(hprop2 z hz).2]; exact hsflabel
        · rw [hpr] at hpa
          simp [RuleResult.isApplicable] at hpa
      · rw [if_neg hpa]
        rcases hs : sf.sign with _ | _ <;>
          rcases hf : sf.formula with _ | _ | ⟨a, c⟩ | ⟨x, y⟩ | ⟨x, y⟩ | φ | φ <;> simp_all

omit [DecidableEq Atom] [Hashable Atom] in
/-- Local re-derivation of `S5Simplification.lean`'s `private lemma
modalMaxWorld_foldl_le_of_forall_S5w` (unavailable across files): threads an accumulator bound
through `List.foldl` to support induction. -/
private lemma modalMaxWorld_foldl_le_of_forall_Five
    {l : List (SignedFormula (Proposition Atom) WorldIndex)} {M init : WorldIndex}
    (hinit : init ≤ M) (h : ∀ z ∈ l, z.label ≤ M) :
    l.foldl (fun mx sf => max mx sf.label) init ≤ M := by
  induction l generalizing init with
  | nil => simpa using hinit
  | cons hd tl ih =>
    simp only [List.foldl_cons]
    exact ih (max_le hinit (h hd List.mem_cons_self))
      (fun z hz => h z (List.mem_cons_of_mem _ hz))

omit [DecidableEq Atom] [Hashable Atom] in
/-- Local re-derivation of `S5Simplification.lean`'s `private lemma
modalMaxWorld_le_of_forall_label_le_S5w`: `modalMaxWorld l` is bounded by `M` whenever every label
in `l` is bounded by `M`. -/
private lemma modalMaxWorld_le_of_forall_label_le_Five
    {l : List (SignedFormula (Proposition Atom) WorldIndex)} {M : WorldIndex}
    (h : ∀ z ∈ l, z.label ≤ M) : modalMaxWorld l ≤ M :=
  modalMaxWorld_foldl_le_of_forall_Five (Nat.zero_le M) h

/-- **Combined `e`-aware step-preservation for `ModalLoopAuxFive`'s two conjuncts**: one
`modalStepBranchGen modalApplyOneFive` step preserves both `∀x∈b,x∈modalUniverse φ₀` and
`FiveWorldInvE φ₀ b e` on every `(b', e')` child pair. Mirrors
`modalStepBranchS5w_preserves_worldInv`, using `modalApplyOneFive_outputsSubsetUniverse` (F2) for
the universe-closure half and `modalApplyOneFive_worldGrowth` above for the growth half, doubled
into three cases (known/non-root-mint/root-mint) instead of S5w's two (known/mint). -/
theorem modalStepBranchFive_preserves_worldInv {φ₀ : Proposition Atom}
    {b e : List (SignedFormula (Proposition Atom) WorldIndex)} {acc : Accessibility}
    {bs es : List (List (SignedFormula (Proposition Atom) WorldIndex))} {acc' : Accessibility}
    (hb : ∀ x ∈ b, x ∈ modalUniverse φ₀) (hWE : FiveWorldInvE φ₀ b e)
    (hFresh : accFreshInv b acc) (hK : accTargetsKnown b acc)
    (h : modalStepBranchGen modalApplyOneFive b e acc = some (bs, es, acc')) :
    ∀ p ∈ bs.zip es, (∀ x ∈ p.1, x ∈ modalUniverse φ₀) ∧ FiveWorldInvE φ₀ p.1 p.2 := by
  have hW : modalMaxWorld b < modalWorldBound φ₀ :=
    modalMaxWorld_lt_worldBound_of_FiveWorldInv (FiveWorldInvE_imp_FiveWorldInv hWE)
  simp only [modalStepBranchGen] at h
  obtain ⟨sf, hsfmem, hsf⟩ := List.exists_of_findSome?_eq_some h
  by_cases hexp : e.any (· == sf) = true
  · rw [if_pos hexp] at hsf; exact absurd hsf (by simp)
  · rw [if_neg hexp] at hsf
    have hsfform : sf.formula ∈ modalSubfmls φ₀ := modalUniverse_mem_formula_Five (hb sf hsfmem)
    have hgrowth := modalApplyOneFive_worldGrowth (φ₀ := φ₀) sf b acc hsfmem hK hsfform
    have houts := modalApplyOneFive_outputsSubsetUniverse φ₀ sf b acc hb hsfmem hFresh hW
    unfold FiveWorldInvE at hWE
    rcases hfstc : (modalApplyOneFive sf b acc).fst with nf | brs | nf | _
    · rw [hfstc] at hsf houts hgrowth
      simp only [Option.some.injEq, Prod.mk.injEq] at hsf
      intro p hp
      rw [← hsf.1, ← hsf.2.1] at hp
      simp only [List.zip_cons_cons, List.zip_nil_right, List.mem_singleton] at hp
      subst hp
      dsimp only
      have hbClosure : ∀ x ∈ nf ++ b, x ∈ modalUniverse φ₀ := by
        intro x hx
        simp only [List.mem_append] at hx
        rcases hx with hx | hx
        · exact houts x hx
        · exact hb x hx
      refine ⟨hbClosure, ?_⟩
      unfold FiveWorldInvE
      rcases hgrowth with hknownall | ⟨s, ψ, hnotused, htagmem, hmemnf, hlabelall⟩ |
          ⟨hroot, ψ, hshape, htagmem, hmemnf, hlabelall⟩
      · have hmaxle : modalMaxWorld (nf ++ b) ≤ modalMaxWorld b := by
          apply modalMaxWorld_le_of_forall_label_le_Five
          intro z hz
          simp only [List.mem_append] at hz
          rcases hz with hz | hz
          · exact known_label_le_modalMaxWorld_Five (hknownall z hz)
          · exact label_le_modalMaxWorld hz
        have hN : (usedTagsFiveNonRoot φ₀ b).card ≤ (usedTagsFiveNonRoot φ₀ (nf ++ b)).card :=
          Finset.card_le_card
            (usedTagsFiveNonRoot_mono (fun x hx => List.mem_append_right _ hx))
        have hE : (expandedRootTagsFive φ₀ b e).card ≤
            (expandedRootTagsFive φ₀ (nf ++ b) (e ++ [sf])).card :=
          Finset.card_le_card (expandedRootTagsFive_mono
            (fun x hx => List.mem_append_right _ hx) (fun x hx => List.mem_append_left _ hx))
        calc modalMaxWorld (nf ++ b) ≤ modalMaxWorld b := hmaxle
          _ ≤ (usedTagsFiveNonRoot φ₀ b).card + (expandedRootTagsFive φ₀ b e).card := hWE
          _ ≤ (usedTagsFiveNonRoot φ₀ (nf ++ b)).card +
              (expandedRootTagsFive φ₀ (nf ++ b) (e ++ [sf])).card := Nat.add_le_add hN hE
      · have hmaxeq : modalMaxWorld (nf ++ b) = modalNextWorld b := by
          apply le_antisymm
          · apply modalMaxWorld_le_of_forall_label_le_Five
            intro z hz
            simp only [List.mem_append] at hz
            rcases hz with hz | hz
            · rw [hlabelall z hz]
            · exact le_of_lt (modalNextWorld_gt b z hz)
          · exact label_le_modalMaxWorld (List.mem_append_left _ hmemnf)
        have hNsub : usedTagsFiveNonRoot φ₀ b ⊆ usedTagsFiveNonRoot φ₀ (nf ++ b) :=
          usedTagsFiveNonRoot_mono (fun x hx => List.mem_append_right _ hx)
        have hnewmem : (s, ψ) ∈ usedTagsFiveNonRoot φ₀ (nf ++ b) := by
          simp only [usedTagsFiveNonRoot, Finset.mem_filter]
          refine ⟨htagmem, ?_⟩
          exact List.any_eq_true.mpr
            ⟨⟨s, ψ, modalNextWorld b⟩, List.mem_append_left _ hmemnf,
              by simp [modalNextWorld]⟩
        have hNcard : (usedTagsFiveNonRoot φ₀ b).card + 1 ≤
            (usedTagsFiveNonRoot φ₀ (nf ++ b)).card :=
          Finset.card_lt_card
            ((Finset.ssubset_iff_of_subset hNsub).mpr ⟨(s, ψ), hnewmem, hnotused⟩)
        have hE : (expandedRootTagsFive φ₀ b e).card ≤
            (expandedRootTagsFive φ₀ (nf ++ b) (e ++ [sf])).card :=
          Finset.card_le_card (expandedRootTagsFive_mono
            (fun x hx => List.mem_append_right _ hx) (fun x hx => List.mem_append_left _ hx))
        rw [hmaxeq]
        change modalMaxWorld b + 1 ≤ _
        calc modalMaxWorld b + 1 ≤
              ((usedTagsFiveNonRoot φ₀ b).card + (expandedRootTagsFive φ₀ b e).card) + 1 :=
                Nat.add_le_add_right hWE 1
          _ = ((usedTagsFiveNonRoot φ₀ b).card + 1) + (expandedRootTagsFive φ₀ b e).card := by ring
          _ ≤ (usedTagsFiveNonRoot φ₀ (nf ++ b)).card +
              (expandedRootTagsFive φ₀ (nf ++ b) (e ++ [sf])).card := Nat.add_le_add hNcard hE
      · have hmaxeq : modalMaxWorld (nf ++ b) = modalNextWorld b := by
          apply le_antisymm
          · apply modalMaxWorld_le_of_forall_label_le_Five
            intro z hz
            simp only [List.mem_append] at hz
            rcases hz with hz | hz
            · rw [hlabelall z hz]
            · exact le_of_lt (modalNextWorld_gt b z hz)
          · exact label_le_modalMaxWorld (List.mem_append_left _ hmemnf)
        have hEsub :
            expandedRootTagsFive φ₀ b e ⊆ expandedRootTagsFive φ₀ (nf ++ b) (e ++ [sf]) :=
          expandedRootTagsFive_mono (fun x hx => List.mem_append_right _ hx)
            (fun x hx => List.mem_append_left _ hx)
        have hnotmem : (sf.sign, ψ) ∉ expandedRootTagsFive φ₀ b e := by
          simp only [expandedRootTagsFive, Finset.mem_filter, not_and]
          intro _ hany
          obtain ⟨x, hxmem, hxeq⟩ := List.any_eq_true.mp hany
          simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at hxeq
          obtain ⟨⟨hxlab, hxshape⟩, hxexp⟩ := hxeq
          obtain ⟨y, hymem, hyeq⟩ := List.any_eq_true.mp hxexp
          have hyx : y = x := beq_iff_eq.mp hyeq
          have hlabeq : x.label = sf.label := hxlab.trans hroot.symm
          have hxeqsf : x = sf := by
            rcases hshape with ⟨hs, hf⟩ | ⟨hs, hf⟩
            · rcases hxshape with ⟨⟨hspos, hxs⟩, hxf⟩ | ⟨⟨hsneg, hxs⟩, hxf⟩
              · have hsigneq : x.sign = sf.sign := hxs.trans hs.symm
                have hformeq : x.formula = sf.formula := hxf.trans hf.symm
                calc x = (⟨x.sign, x.formula, x.label⟩ :
                    SignedFormula (Proposition Atom) WorldIndex) := rfl
                  _ = (⟨sf.sign, sf.formula, sf.label⟩ :
                      SignedFormula (Proposition Atom) WorldIndex) := by
                    rw [hsigneq, hformeq, hlabeq]
                  _ = sf := rfl
              · rw [hs] at hsneg; exact absurd hsneg (by decide)
            · rcases hxshape with ⟨⟨hspos, hxs⟩, hxf⟩ | ⟨⟨hsneg, hxs⟩, hxf⟩
              · rw [hs] at hspos; exact absurd hspos (by decide)
              · have hsigneq : x.sign = sf.sign := hxs.trans hs.symm
                have hformeq : x.formula = sf.formula := hxf.trans hf.symm
                calc x = (⟨x.sign, x.formula, x.label⟩ :
                    SignedFormula (Proposition Atom) WorldIndex) := rfl
                  _ = (⟨sf.sign, sf.formula, sf.label⟩ :
                      SignedFormula (Proposition Atom) WorldIndex) := by
                    rw [hsigneq, hformeq, hlabeq]
                  _ = sf := rfl
          have hyeqsf : y = sf := hyx.trans hxeqsf
          exact hexp (hyeqsf ▸ List.any_eq_true.mpr ⟨y, hymem, by simp⟩)
        have hnewmem : (sf.sign, ψ) ∈ expandedRootTagsFive φ₀ (nf ++ b) (e ++ [sf]) := by
          simp only [expandedRootTagsFive, Finset.mem_filter]
          refine ⟨htagmem, List.any_eq_true.mpr ⟨sf, List.mem_append_right _ hsfmem, ?_⟩⟩
          rcases hshape with ⟨hs, hf⟩ | ⟨hs, hf⟩ <;> simp [hroot, hs, hf]
        have hEcard : (expandedRootTagsFive φ₀ b e).card + 1 ≤
            (expandedRootTagsFive φ₀ (nf ++ b) (e ++ [sf])).card :=
          Finset.card_lt_card
            ((Finset.ssubset_iff_of_subset hEsub).mpr ⟨(sf.sign, ψ), hnewmem, hnotmem⟩)
        have hN : (usedTagsFiveNonRoot φ₀ b).card ≤ (usedTagsFiveNonRoot φ₀ (nf ++ b)).card :=
          Finset.card_le_card (usedTagsFiveNonRoot_mono (fun x hx => List.mem_append_right _ hx))
        rw [hmaxeq]
        change modalMaxWorld b + 1 ≤ _
        calc modalMaxWorld b + 1 ≤
              ((usedTagsFiveNonRoot φ₀ b).card + (expandedRootTagsFive φ₀ b e).card) + 1 :=
                Nat.add_le_add_right hWE 1
          _ = (usedTagsFiveNonRoot φ₀ b).card +
              ((expandedRootTagsFive φ₀ b e).card + 1) := by ring
          _ ≤ (usedTagsFiveNonRoot φ₀ (nf ++ b)).card +
              (expandedRootTagsFive φ₀ (nf ++ b) (e ++ [sf])).card := Nat.add_le_add hN hEcard
    · rw [hfstc] at hsf houts hgrowth
      simp only [Option.some.injEq, Prod.mk.injEq] at hsf
      intro p hp
      rw [← hsf.1, ← hsf.2.1] at hp
      obtain ⟨hp1, hp2⟩ := List.of_mem_zip hp
      obtain ⟨br, hbr, hp1eq⟩ := List.mem_map.mp hp1
      obtain ⟨-, -, hp2eq⟩ := List.mem_map.mp hp2
      have hpeq : p = (br ++ b, e ++ [sf]) := by
        obtain ⟨p1, p2⟩ := p
        simp only [Prod.mk.injEq]
        exact ⟨hp1eq.symm, hp2eq.symm⟩
      subst hpeq
      dsimp only
      have hbClosure : ∀ x ∈ br ++ b, x ∈ modalUniverse φ₀ := by
        intro x hx
        simp only [List.mem_append] at hx
        rcases hx with hx | hx
        · exact houts x (List.mem_flatten.mpr ⟨br, hbr, hx⟩)
        · exact hb x hx
      refine ⟨hbClosure, ?_⟩
      unfold FiveWorldInvE
      have hmaxle : modalMaxWorld (br ++ b) ≤ modalMaxWorld b := by
        apply modalMaxWorld_le_of_forall_label_le_Five
        intro z hz
        simp only [List.mem_append] at hz
        rcases hz with hz | hz
        · exact known_label_le_modalMaxWorld_Five (hgrowth z (List.mem_flatten.mpr ⟨br, hbr, hz⟩))
        · exact label_le_modalMaxWorld hz
      have hN : (usedTagsFiveNonRoot φ₀ b).card ≤ (usedTagsFiveNonRoot φ₀ (br ++ b)).card :=
        Finset.card_le_card (usedTagsFiveNonRoot_mono (fun x hx => List.mem_append_right _ hx))
      have hE : (expandedRootTagsFive φ₀ b e).card ≤
          (expandedRootTagsFive φ₀ (br ++ b) (e ++ [sf])).card :=
        Finset.card_le_card (expandedRootTagsFive_mono
          (fun x hx => List.mem_append_right _ hx) (fun x hx => List.mem_append_left _ hx))
      calc modalMaxWorld (br ++ b) ≤ modalMaxWorld b := hmaxle
        _ ≤ (usedTagsFiveNonRoot φ₀ b).card + (expandedRootTagsFive φ₀ b e).card := hWE
        _ ≤ (usedTagsFiveNonRoot φ₀ (br ++ b)).card +
            (expandedRootTagsFive φ₀ (br ++ b) (e ++ [sf])).card := Nat.add_le_add hN hE
    · rw [hfstc] at hsf houts hgrowth
      simp only [Option.some.injEq, Prod.mk.injEq] at hsf
      intro p hp
      rw [← hsf.1, ← hsf.2.1] at hp
      simp only [List.zip_cons_cons, List.zip_nil_right, List.mem_singleton] at hp
      subst hp
      dsimp only
      have hbClosure : ∀ x ∈ nf ++ b, x ∈ modalUniverse φ₀ := by
        intro x hx
        simp only [List.mem_append] at hx
        rcases hx with hx | hx
        · exact houts x hx
        · exact hb x hx
      refine ⟨hbClosure, ?_⟩
      unfold FiveWorldInvE
      have hmaxle : modalMaxWorld (nf ++ b) ≤ modalMaxWorld b := by
        apply modalMaxWorld_le_of_forall_label_le_Five
        intro z hz
        simp only [List.mem_append] at hz
        rcases hz with hz | hz
        · exact known_label_le_modalMaxWorld_Five (hgrowth z hz)
        · exact label_le_modalMaxWorld hz
      have hN : (usedTagsFiveNonRoot φ₀ b).card ≤ (usedTagsFiveNonRoot φ₀ (nf ++ b)).card :=
        Finset.card_le_card (usedTagsFiveNonRoot_mono (fun x hx => List.mem_append_right _ hx))
      have hE : (expandedRootTagsFive φ₀ b e).card ≤
          (expandedRootTagsFive φ₀ (nf ++ b) e).card :=
        Finset.card_le_card (expandedRootTagsFive_mono
          (fun x hx => List.mem_append_right _ hx) (fun x hx => hx))
      calc modalMaxWorld (nf ++ b) ≤ modalMaxWorld b := hmaxle
        _ ≤ (usedTagsFiveNonRoot φ₀ b).card + (expandedRootTagsFive φ₀ b e).card := hWE
        _ ≤ (usedTagsFiveNonRoot φ₀ (nf ++ b)).card +
            (expandedRootTagsFive φ₀ (nf ++ b) e).card := Nat.add_le_add hN hE
    · rw [hfstc] at hsf; simp at hsf

/-! ## Termination Bound for `modalApplyOneKb5'` (task 524 Phase 3)

`FiveWorldInv`/`usedTagsFiveNonRoot`/`usedTagsFiveRoot`/
`modalMaxWorld_lt_worldBound_of_FiveWorldInv` above are **entirely rule-independent**: their
definitions inspect only branch content (which
signed formulas appear on `b`, at which labels) and `φ₀`'s finite subformula/tag structure --
never `modalApplyOneFive`/`modalApplyOneKb5'` by name. This is exactly what task 524's Phase 1
design relies on: `modalApplyOneKb5'`'s mint (existential) shapes (`.pos .diamond`/`.neg .box`)
are **verbatim** `modalApplyOneFive`'s witness-reuse behavior
(`modalApplyOneKb5'_diaPos_eq_or_reuse`/`_boxNeg_eq_or_reuse`, mirroring `modalApplyOneFive`'s own
case-split exactly) -- the only shapes
that ever mint a fresh world (`modalMaxWorld`-growing) are unchanged between the two rules. Only
the two *propagation* shapes (`.pos .box`/`.neg .diamond`) differ, and neither of those shapes
ever mints (`modalApplyOneKb5'Prop_boxPos_diaNeg_eq`: accessibility output is always `acc`
unchanged, result always `.notApplicable`/`.persistent`, never `.linear`/`.branching`). So the
world-count-vs-`modalWorldBound` bound `FiveWorldInv` establishes for Five transfers to
`modalApplyOneKb5'` with **no re-derivation needed** -- landed here as its own Kb5'-named
artifact per this phase's task list, rather than silently reusing the Five name at call sites
that are conceptually about the new rule. -/

/-- The KB5' full-cluster rule's source-split world-bound invariant: definitionally
`FiveWorldInv`, per this section's rule-independence note. -/
def Kb5'WorldInv (φ₀ : Proposition Atom)
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) : Prop :=
  FiveWorldInv φ₀ b

omit [Hashable Atom] in
/-- `Kb5'WorldInv` is exactly `FiveWorldInv` -- true `rfl`, since Phase 3's termination bound for
`modalApplyOneKb5'` reuses Five's rule-independent tag/world-count machinery verbatim (see this
section's module note). -/
theorem Kb5'WorldInv_eq (φ₀ : Proposition Atom)
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) :
    Kb5'WorldInv φ₀ b = FiveWorldInv φ₀ b := rfl

omit [Hashable Atom] in
/-- **Task 524 Phase 3**: the termination bound `modalApplyOneKb5'`'s catalog-membership field
(`outputsSubsetUniverse`, Phase 4) consumes: `Kb5'WorldInv` bounds `modalMaxWorld b` strictly
under `modalWorldBound φ₀`. Free corollary of `modalMaxWorld_lt_worldBound_of_FiveWorldInv` via
`Kb5'WorldInv_eq`. -/
theorem modalMaxWorld_lt_worldBound_of_Kb5'WorldInv {φ₀ : Proposition Atom}
    {b : List (SignedFormula (Proposition Atom) WorldIndex)} (hW : Kb5'WorldInv φ₀ b) :
    modalMaxWorld b < modalWorldBound φ₀ :=
  modalMaxWorld_lt_worldBound_of_FiveWorldInv (Kb5'WorldInv_eq φ₀ b ▸ hW)

/-! ## Termination Bound for `modalApplyOneKb5''`

Same rule-independence argument as `Kb5'WorldInv` above, applied to the corrected-gate rule:
`modalApplyOneKb5''`'s mint (existential) shapes are **verbatim** `modalApplyOneFive`'s
witness-reuse behavior (`modalApplyOneKb5''_diaPos_eq_or_reuse`/`_boxNeg_eq_or_reuse`, identical
to `modalApplyOneKb5'`'s own case-split), and its two propagation shapes never mint either
(`modalApplyOneKb5''Prop_boxPos_diaNeg_shape`: result is always `.notApplicable`/`.persistent`,
never `.linear`/`.branching`, so accessibility is never touched at those shapes -- the corrected
gate only changes *which formulas* a `.persistent` result carries, never the result *shape*).
So `FiveWorldInv`'s world-count-vs-`modalWorldBound` bound transfers to `modalApplyOneKb5''`
exactly as it did to `modalApplyOneKb5'`, with no re-derivation needed. -/

/-- The corrected-gate KB5 rule's source-split world-bound invariant: definitionally
`FiveWorldInv`, per this section's rule-independence note. Mirrors `Kb5'WorldInv`. -/
def Kb5''WorldInv (φ₀ : Proposition Atom)
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) : Prop :=
  FiveWorldInv φ₀ b

omit [Hashable Atom] in
/-- `Kb5''WorldInv` is exactly `FiveWorldInv` -- true `rfl`, since the termination bound for
`modalApplyOneKb5''` reuses Five's rule-independent tag/world-count machinery verbatim (see this
section's module note). Mirrors `Kb5'WorldInv_eq`. -/
theorem Kb5''WorldInv_eq (φ₀ : Proposition Atom)
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) :
    Kb5''WorldInv φ₀ b = FiveWorldInv φ₀ b := rfl

omit [Hashable Atom] in
/-- The termination bound `modalApplyOneKb5''`'s catalog-membership field
(`outputsSubsetUniverse`) consumes: `Kb5''WorldInv` bounds `modalMaxWorld b` strictly under
`modalWorldBound φ₀`. Free corollary of `modalMaxWorld_lt_worldBound_of_FiveWorldInv` via
`Kb5''WorldInv_eq`. Mirrors `modalMaxWorld_lt_worldBound_of_Kb5'WorldInv`. -/
theorem modalMaxWorld_lt_worldBound_of_Kb5''WorldInv {φ₀ : Proposition Atom}
    {b : List (SignedFormula (Proposition Atom) WorldIndex)} (hW : Kb5''WorldInv φ₀ b) :
    modalMaxWorld b < modalWorldBound φ₀ :=
  modalMaxWorld_lt_worldBound_of_FiveWorldInv (Kb5''WorldInv_eq φ₀ b ▸ hW)

/-! ## Step-Preservation of the World-Bound Invariant for `modalApplyOneKb5''` (task 528 Phase 6)

Mirrors `modalStepBranchFive_preserves_worldInv` above declaration-for-declaration, reusing
`FiveWorldInvE`/`expandedRootTagsFive`/`usedTagsFiveNonRoot`/`mintTags` directly (no `Kb5''`-named
fork of these -- per this file's own precedent above, they are already rule-independent, and the
`Kb5''WorldInv`/`Kb5''WorldInv_eq` aliasing pattern is reserved for names call sites elsewhere
actually reference by their own `Kb5''`-labeled identity; `FiveWorldInvE` has no such external
caller yet, so introducing a same-content alias here would only add surface area). The mint
(existential) shapes of `modalApplyOneKb5''_worldGrowth` below port `modalApplyOneFive_worldGrowth`
near-verbatim (Phase 1 already confirmed the mint arms are byte-identical witness-reuse behavior);
the propagation (box-positive/diamond-negative) shape is fresh, resting on
`modalApplyOneKb5''Prop_boxPos_diaNeg_eq` (Phase 3) instead of Five's own analogue -- unlike Five,
this needs the extra ambient hypothesis `h0 : 0 ∈ modalKnownWorlds b` the corrected gate's
self-target arm requires (its cluster-membership dichotomy no longer ties `x.label = 0` to the
trigger's own known-ness, since the gate now fires for *any* trigger, not only `w = 0`). -/

/-- **World-growth dichotomy for `modalApplyOneKb5''`**: mirrors `modalApplyOneFive_worldGrowth`.
The two mint shapes are Five's own case split verbatim, substituting
`modalApplyOneKb5''_diaPos_eq_or_reuse`/`modalApplyOneKb5''_boxNeg_eq_or_reuse` (Phase 1) for the
Five originals. The propagation shape is fresh: `modalApplyOneKb5''Prop_boxPos_diaNeg_eq` (Phase
3) already shows no growth is possible there (accessibility unchanged, every emitted label
known), given the extra `h0` hypothesis its self-target arm needs. -/
lemma modalApplyOneKb5''_worldGrowth {φ₀ : Proposition Atom}
    (sf : SignedFormula (Proposition Atom) WorldIndex)
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (hsfmem : sf ∈ b) (hknown : accTargetsKnown b acc)
    (h0 : (0 : WorldIndex) ∈ modalKnownWorlds b)
    (hsfform : sf.formula ∈ modalSubfmls φ₀) :
    (match (modalApplyOneKb5'' sf b acc).fst with
      | .linear formulas =>
          (∀ x ∈ formulas, x.label ∈ modalKnownWorlds b) ∨
          (∃ s ψ, (s, ψ) ∉ usedTagsFiveNonRoot φ₀ b ∧ (s, ψ) ∈ mintTags φ₀ ∧
            (⟨s, ψ, modalNextWorld b⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈
              formulas ∧
            ∀ x ∈ formulas, x.label = modalNextWorld b) ∨
          (sf.label = (0 : WorldIndex) ∧ ∃ ψ,
            ((sf.sign = Sign.pos ∧ sf.formula = Proposition.diamond ψ) ∨
             (sf.sign = Sign.neg ∧ sf.formula = Proposition.box ψ)) ∧
            (sf.sign, ψ) ∈ mintTags φ₀ ∧
            (⟨sf.sign, ψ, modalNextWorld b⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈
              formulas ∧
            ∀ x ∈ formulas, x.label = modalNextWorld b)
      | .branching branches => ∀ x ∈ branches.flatten, x.label ∈ modalKnownWorlds b
      | .persistent formulas => ∀ x ∈ formulas, x.label ∈ modalKnownWorlds b
      | .notApplicable => True) := by
  by_cases hmint : (sf.sign = Sign.pos ∧ ∃ φ, sf.formula = Proposition.diamond φ) ∨
      (sf.sign = Sign.neg ∧ ∃ φ, sf.formula = Proposition.box φ)
  · rcases hmint with ⟨hs, φ, hf⟩ | ⟨hs, φ, hf⟩
    · obtain ⟨s, ff, w⟩ := sf
      simp only at hs hf hsfform
      subst hs; subst hf
      have hφmem : φ ∈ modalSubfmls (Proposition.diamond φ) :=
        List.mem_cons_of_mem _ (modalSubfmls_self_mem φ)
      have hφsub : φ ∈ modalSubfmls φ₀ := modalSubfmls_trans_Five hφmem hsfform
      have htagmem : (Sign.pos, φ) ∈ mintTags φ₀ := mem_mintTags_of_diamond_mem hsfform
      by_cases hz : w = (0 : WorldIndex)
      · subst hz
        have heq : modalApplyOneKb5''
            (⟨.pos, .diamond φ, (0 : WorldIndex)⟩ : SignedFormula (Proposition Atom) WorldIndex)
            b acc =
            modalApplyOneKb5''Prop
              (⟨.pos, .diamond φ, (0 : WorldIndex)⟩ :
                SignedFormula (Proposition Atom) WorldIndex) b acc := by
          unfold modalApplyOneKb5''; simp
        rw [heq, modalApplyOneKb5''Prop_eq_of_not_boxPos_diaNeg _ b acc (by simp),
          modalApplyOne_diamondPos_mint_fst]
        exact Or.inr (Or.inr ⟨rfl, φ, Or.inl ⟨rfl, rfl⟩, htagmem, List.mem_cons_self,
          modalApplyOne_diamondPos_mint_label b φ (0 : WorldIndex)⟩)
      · cases hw : witnessWorldFive b Sign.pos φ with
        | none =>
          have heq : modalApplyOneKb5''
              (⟨.pos, .diamond φ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) b acc =
              modalApplyOneKb5''Prop
                (⟨.pos, .diamond φ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) b acc := by
            unfold modalApplyOneKb5''
            dsimp only
            rw [if_neg (by simpa using hz), hw]
          rw [heq, modalApplyOneKb5''Prop_eq_of_not_boxPos_diaNeg _ b acc (by simp),
            modalApplyOne_diamondPos_mint_fst]
          exact Or.inr (Or.inl ⟨Sign.pos, φ,
            witnessWorldFive_none_not_mem_usedTagsFiveNonRoot hw, htagmem, List.mem_cons_self,
            modalApplyOne_diamondPos_mint_label b φ w⟩)
        | some w' =>
          have heq : modalApplyOneKb5''
              (⟨.pos, .diamond φ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) b acc =
              (RuleResult.linear [⟨.pos, φ, w'⟩], acc.addEdge w w') := by
            unfold modalApplyOneKb5''
            dsimp only
            rw [if_neg (by simpa using hz), hw]
          rw [heq]
          refine Or.inl (fun z hz' => ?_)
          simp only [List.mem_singleton] at hz'; subst hz'
          exact label_mem_modalKnownWorlds (witnessWorldFive_mem hw).1
    · obtain ⟨s, ff, w⟩ := sf
      simp only at hs hf hsfform
      subst hs; subst hf
      have hφmem : φ ∈ modalSubfmls (Proposition.box φ) :=
        List.mem_cons_of_mem _ (modalSubfmls_self_mem φ)
      have hφsub : φ ∈ modalSubfmls φ₀ := modalSubfmls_trans_Five hφmem hsfform
      have htagmem : (Sign.neg, φ) ∈ mintTags φ₀ := mem_mintTags_of_box_mem hsfform
      by_cases hz : w = (0 : WorldIndex)
      · subst hz
        have heq : modalApplyOneKb5''
            (⟨.neg, .box φ, (0 : WorldIndex)⟩ : SignedFormula (Proposition Atom) WorldIndex)
            b acc =
            modalApplyOneKb5''Prop
              (⟨.neg, .box φ, (0 : WorldIndex)⟩ :
                SignedFormula (Proposition Atom) WorldIndex) b acc := by
          unfold modalApplyOneKb5''; simp
        rw [heq, modalApplyOneKb5''Prop_eq_of_not_boxPos_diaNeg _ b acc (by simp),
          modalApplyOne_boxNeg_mint_fst]
        exact Or.inr (Or.inr ⟨rfl, φ, Or.inr ⟨rfl, rfl⟩, htagmem, List.mem_cons_self,
          modalApplyOne_boxNeg_mint_label b φ (0 : WorldIndex)⟩)
      · cases hw : witnessWorldFive b Sign.neg φ with
        | none =>
          have heq : modalApplyOneKb5''
              (⟨.neg, .box φ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) b acc =
              modalApplyOneKb5''Prop
                (⟨.neg, .box φ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) b acc := by
            unfold modalApplyOneKb5''
            dsimp only
            rw [if_neg (by simpa using hz), hw]
          rw [heq, modalApplyOneKb5''Prop_eq_of_not_boxPos_diaNeg _ b acc (by simp),
            modalApplyOne_boxNeg_mint_fst]
          exact Or.inr (Or.inl ⟨Sign.neg, φ,
            witnessWorldFive_none_not_mem_usedTagsFiveNonRoot hw, htagmem, List.mem_cons_self,
            modalApplyOne_boxNeg_mint_label b φ w⟩)
        | some w' =>
          have heq : modalApplyOneKb5''
              (⟨.neg, .box φ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) b acc =
              (RuleResult.linear [⟨.neg, φ, w'⟩], acc.addEdge w w') := by
            unfold modalApplyOneKb5''
            dsimp only
            rw [if_neg (by simpa using hz), hw]
          rw [heq]
          refine Or.inl (fun z hz' => ?_)
          simp only [List.mem_singleton] at hz'; subst hz'
          exact label_mem_modalKnownWorlds (witnessWorldFive_mem hw).1
  · rw [modalApplyOneKb5''_eq_of_not_mint_shape sf b acc
        ⟨fun hc => hmint (Or.inl hc), fun hc => hmint (Or.inr hc)⟩]
    by_cases hprop : (sf.sign = Sign.pos ∧ ∃ φ, sf.formula = Proposition.box φ) ∨
        (sf.sign = Sign.neg ∧ ∃ φ, sf.formula = Proposition.diamond φ)
    · obtain ⟨hsndeq, hor⟩ :=
        modalApplyOneKb5''Prop_boxPos_diaNeg_eq sf b acc hsfmem hknown h0 hprop
      rcases hor with hnot | ⟨out, hpers, hlabel⟩
      · rw [hnot]; trivial
      · rw [hpers]; exact hlabel
    · rw [modalApplyOneKb5''Prop_eq_of_not_boxPos_diaNeg sf b acc
          ⟨fun hc => hprop (Or.inl hc), fun hc => hprop (Or.inr hc)⟩]
      have hsflabel : sf.label ∈ modalKnownWorlds b :=
        (mem_modalKnownWorlds_Five b sf.label).mpr ⟨sf, hsfmem, rfl⟩
      have hprop2 := modalApplyOne_prop_outputs_subset sf
      unfold modalApplyOne
      by_cases hpa :
          (tryAllPropRules modalAndOf? modalOrOf? modalImpOf? modalNegOf? sf).isApplicable
      · simp only [hpa, if_true]
        rcases hpr : tryAllPropRules modalAndOf? modalOrOf? modalImpOf? modalNegOf? sf with
          formulas | branches | formulas | -
        · rw [hpr] at hprop2
          refine Or.inl (fun z hz => ?_)
          rw [(hprop2 z hz).2]; exact hsflabel
        · rw [hpr] at hprop2
          intro z hz
          rw [(hprop2 z hz).2]; exact hsflabel
        · rw [hpr] at hprop2
          intro z hz
          rw [(hprop2 z hz).2]; exact hsflabel
        · rw [hpr] at hpa
          simp [RuleResult.isApplicable] at hpa
      · rw [if_neg hpa]
        rcases hs : sf.sign with _ | _ <;>
          rcases hf : sf.formula with _ | _ | ⟨a, c⟩ | ⟨x, y⟩ | ⟨x, y⟩ | φ | φ <;> simp_all

/-- **Combined `e`-aware step-preservation for `modalApplyOneKb5''`'s two conjuncts**: one
`modalStepBranchGen modalApplyOneKb5''` step preserves both `∀x∈b,x∈modalUniverse φ₀` and
`FiveWorldInvE φ₀ b e` on every `(b', e')` child pair, given the extra ambient
`h0 : 0 ∈ modalKnownWorlds b` the corrected gate's propagation shape needs. Mirrors
`modalStepBranchFive_preserves_worldInv` declaration-for-declaration, threading `h0` through to
`modalApplyOneKb5''_worldGrowth` and substituting `modalApplyOneKb5''_outputsSubsetUniverse` (F2)
for Five's own F2 discharge. -/
theorem modalStepBranchKb5''_preserves_worldInv {φ₀ : Proposition Atom}
    {b e : List (SignedFormula (Proposition Atom) WorldIndex)} {acc : Accessibility}
    {bs es : List (List (SignedFormula (Proposition Atom) WorldIndex))} {acc' : Accessibility}
    (hb : ∀ x ∈ b, x ∈ modalUniverse φ₀) (hWE : FiveWorldInvE φ₀ b e)
    (hFresh : accFreshInv b acc) (hK : accTargetsKnown b acc)
    (h0 : (0 : WorldIndex) ∈ modalKnownWorlds b)
    (h : modalStepBranchGen modalApplyOneKb5'' b e acc = some (bs, es, acc')) :
    ∀ p ∈ bs.zip es, (∀ x ∈ p.1, x ∈ modalUniverse φ₀) ∧ FiveWorldInvE φ₀ p.1 p.2 := by
  have hW : modalMaxWorld b < modalWorldBound φ₀ :=
    modalMaxWorld_lt_worldBound_of_FiveWorldInv (FiveWorldInvE_imp_FiveWorldInv hWE)
  simp only [modalStepBranchGen] at h
  obtain ⟨sf, hsfmem, hsf⟩ := List.exists_of_findSome?_eq_some h
  by_cases hexp : e.any (· == sf) = true
  · rw [if_pos hexp] at hsf; exact absurd hsf (by simp)
  · rw [if_neg hexp] at hsf
    have hsfform : sf.formula ∈ modalSubfmls φ₀ := modalUniverse_mem_formula_Five (hb sf hsfmem)
    have hgrowth := modalApplyOneKb5''_worldGrowth (φ₀ := φ₀) sf b acc hsfmem hK h0 hsfform
    have houts := modalApplyOneKb5''_outputsSubsetUniverse φ₀ sf b acc hb hsfmem hFresh hW
    unfold FiveWorldInvE at hWE
    rcases hfstc : (modalApplyOneKb5'' sf b acc).fst with nf | brs | nf | _
    · rw [hfstc] at hsf houts hgrowth
      simp only [Option.some.injEq, Prod.mk.injEq] at hsf
      intro p hp
      rw [← hsf.1, ← hsf.2.1] at hp
      simp only [List.zip_cons_cons, List.zip_nil_right, List.mem_singleton] at hp
      subst hp
      dsimp only
      have hbClosure : ∀ x ∈ nf ++ b, x ∈ modalUniverse φ₀ := by
        intro x hx
        simp only [List.mem_append] at hx
        rcases hx with hx | hx
        · exact houts x hx
        · exact hb x hx
      refine ⟨hbClosure, ?_⟩
      unfold FiveWorldInvE
      rcases hgrowth with hknownall | ⟨s, ψ, hnotused, htagmem, hmemnf, hlabelall⟩ |
          ⟨hroot, ψ, hshape, htagmem, hmemnf, hlabelall⟩
      · have hmaxle : modalMaxWorld (nf ++ b) ≤ modalMaxWorld b := by
          apply modalMaxWorld_le_of_forall_label_le_Five
          intro z hz
          simp only [List.mem_append] at hz
          rcases hz with hz | hz
          · exact known_label_le_modalMaxWorld_Five (hknownall z hz)
          · exact label_le_modalMaxWorld hz
        have hN : (usedTagsFiveNonRoot φ₀ b).card ≤ (usedTagsFiveNonRoot φ₀ (nf ++ b)).card :=
          Finset.card_le_card
            (usedTagsFiveNonRoot_mono (fun x hx => List.mem_append_right _ hx))
        have hE : (expandedRootTagsFive φ₀ b e).card ≤
            (expandedRootTagsFive φ₀ (nf ++ b) (e ++ [sf])).card :=
          Finset.card_le_card (expandedRootTagsFive_mono
            (fun x hx => List.mem_append_right _ hx) (fun x hx => List.mem_append_left _ hx))
        calc modalMaxWorld (nf ++ b) ≤ modalMaxWorld b := hmaxle
          _ ≤ (usedTagsFiveNonRoot φ₀ b).card + (expandedRootTagsFive φ₀ b e).card := hWE
          _ ≤ (usedTagsFiveNonRoot φ₀ (nf ++ b)).card +
              (expandedRootTagsFive φ₀ (nf ++ b) (e ++ [sf])).card := Nat.add_le_add hN hE
      · have hmaxeq : modalMaxWorld (nf ++ b) = modalNextWorld b := by
          apply le_antisymm
          · apply modalMaxWorld_le_of_forall_label_le_Five
            intro z hz
            simp only [List.mem_append] at hz
            rcases hz with hz | hz
            · rw [hlabelall z hz]
            · exact le_of_lt (modalNextWorld_gt b z hz)
          · exact label_le_modalMaxWorld (List.mem_append_left _ hmemnf)
        have hNsub : usedTagsFiveNonRoot φ₀ b ⊆ usedTagsFiveNonRoot φ₀ (nf ++ b) :=
          usedTagsFiveNonRoot_mono (fun x hx => List.mem_append_right _ hx)
        have hnewmem : (s, ψ) ∈ usedTagsFiveNonRoot φ₀ (nf ++ b) := by
          simp only [usedTagsFiveNonRoot, Finset.mem_filter]
          refine ⟨htagmem, ?_⟩
          exact List.any_eq_true.mpr
            ⟨⟨s, ψ, modalNextWorld b⟩, List.mem_append_left _ hmemnf,
              by simp [modalNextWorld]⟩
        have hNcard : (usedTagsFiveNonRoot φ₀ b).card + 1 ≤
            (usedTagsFiveNonRoot φ₀ (nf ++ b)).card :=
          Finset.card_lt_card
            ((Finset.ssubset_iff_of_subset hNsub).mpr ⟨(s, ψ), hnewmem, hnotused⟩)
        have hE : (expandedRootTagsFive φ₀ b e).card ≤
            (expandedRootTagsFive φ₀ (nf ++ b) (e ++ [sf])).card :=
          Finset.card_le_card (expandedRootTagsFive_mono
            (fun x hx => List.mem_append_right _ hx) (fun x hx => List.mem_append_left _ hx))
        rw [hmaxeq]
        change modalMaxWorld b + 1 ≤ _
        calc modalMaxWorld b + 1 ≤
              ((usedTagsFiveNonRoot φ₀ b).card + (expandedRootTagsFive φ₀ b e).card) + 1 :=
                Nat.add_le_add_right hWE 1
          _ = ((usedTagsFiveNonRoot φ₀ b).card + 1) + (expandedRootTagsFive φ₀ b e).card := by ring
          _ ≤ (usedTagsFiveNonRoot φ₀ (nf ++ b)).card +
              (expandedRootTagsFive φ₀ (nf ++ b) (e ++ [sf])).card := Nat.add_le_add hNcard hE
      · have hmaxeq : modalMaxWorld (nf ++ b) = modalNextWorld b := by
          apply le_antisymm
          · apply modalMaxWorld_le_of_forall_label_le_Five
            intro z hz
            simp only [List.mem_append] at hz
            rcases hz with hz | hz
            · rw [hlabelall z hz]
            · exact le_of_lt (modalNextWorld_gt b z hz)
          · exact label_le_modalMaxWorld (List.mem_append_left _ hmemnf)
        have hEsub :
            expandedRootTagsFive φ₀ b e ⊆ expandedRootTagsFive φ₀ (nf ++ b) (e ++ [sf]) :=
          expandedRootTagsFive_mono (fun x hx => List.mem_append_right _ hx)
            (fun x hx => List.mem_append_left _ hx)
        have hnotmem : (sf.sign, ψ) ∉ expandedRootTagsFive φ₀ b e := by
          simp only [expandedRootTagsFive, Finset.mem_filter, not_and]
          intro _ hany
          obtain ⟨x, hxmem, hxeq⟩ := List.any_eq_true.mp hany
          simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at hxeq
          obtain ⟨⟨hxlab, hxshape⟩, hxexp⟩ := hxeq
          obtain ⟨y, hymem, hyeq⟩ := List.any_eq_true.mp hxexp
          have hyx : y = x := beq_iff_eq.mp hyeq
          have hlabeq : x.label = sf.label := hxlab.trans hroot.symm
          have hxeqsf : x = sf := by
            rcases hshape with ⟨hs, hf⟩ | ⟨hs, hf⟩
            · rcases hxshape with ⟨⟨hspos, hxs⟩, hxf⟩ | ⟨⟨hsneg, hxs⟩, hxf⟩
              · have hsigneq : x.sign = sf.sign := hxs.trans hs.symm
                have hformeq : x.formula = sf.formula := hxf.trans hf.symm
                calc x = (⟨x.sign, x.formula, x.label⟩ :
                    SignedFormula (Proposition Atom) WorldIndex) := rfl
                  _ = (⟨sf.sign, sf.formula, sf.label⟩ :
                      SignedFormula (Proposition Atom) WorldIndex) := by
                    rw [hsigneq, hformeq, hlabeq]
                  _ = sf := rfl
              · rw [hs] at hsneg; exact absurd hsneg (by decide)
            · rcases hxshape with ⟨⟨hspos, hxs⟩, hxf⟩ | ⟨⟨hsneg, hxs⟩, hxf⟩
              · rw [hs] at hspos; exact absurd hspos (by decide)
              · have hsigneq : x.sign = sf.sign := hxs.trans hs.symm
                have hformeq : x.formula = sf.formula := hxf.trans hf.symm
                calc x = (⟨x.sign, x.formula, x.label⟩ :
                    SignedFormula (Proposition Atom) WorldIndex) := rfl
                  _ = (⟨sf.sign, sf.formula, sf.label⟩ :
                      SignedFormula (Proposition Atom) WorldIndex) := by
                    rw [hsigneq, hformeq, hlabeq]
                  _ = sf := rfl
          have hyeqsf : y = sf := hyx.trans hxeqsf
          exact hexp (hyeqsf ▸ List.any_eq_true.mpr ⟨y, hymem, by simp⟩)
        have hnewmem : (sf.sign, ψ) ∈ expandedRootTagsFive φ₀ (nf ++ b) (e ++ [sf]) := by
          simp only [expandedRootTagsFive, Finset.mem_filter]
          refine ⟨htagmem, List.any_eq_true.mpr ⟨sf, List.mem_append_right _ hsfmem, ?_⟩⟩
          rcases hshape with ⟨hs, hf⟩ | ⟨hs, hf⟩ <;> simp [hroot, hs, hf]
        have hEcard : (expandedRootTagsFive φ₀ b e).card + 1 ≤
            (expandedRootTagsFive φ₀ (nf ++ b) (e ++ [sf])).card :=
          Finset.card_lt_card
            ((Finset.ssubset_iff_of_subset hEsub).mpr ⟨(sf.sign, ψ), hnewmem, hnotmem⟩)
        have hN : (usedTagsFiveNonRoot φ₀ b).card ≤ (usedTagsFiveNonRoot φ₀ (nf ++ b)).card :=
          Finset.card_le_card (usedTagsFiveNonRoot_mono (fun x hx => List.mem_append_right _ hx))
        rw [hmaxeq]
        change modalMaxWorld b + 1 ≤ _
        calc modalMaxWorld b + 1 ≤
              ((usedTagsFiveNonRoot φ₀ b).card + (expandedRootTagsFive φ₀ b e).card) + 1 :=
                Nat.add_le_add_right hWE 1
          _ = (usedTagsFiveNonRoot φ₀ b).card +
              ((expandedRootTagsFive φ₀ b e).card + 1) := by ring
          _ ≤ (usedTagsFiveNonRoot φ₀ (nf ++ b)).card +
              (expandedRootTagsFive φ₀ (nf ++ b) (e ++ [sf])).card := Nat.add_le_add hN hEcard
    · rw [hfstc] at hsf houts hgrowth
      simp only [Option.some.injEq, Prod.mk.injEq] at hsf
      intro p hp
      rw [← hsf.1, ← hsf.2.1] at hp
      obtain ⟨hp1, hp2⟩ := List.of_mem_zip hp
      obtain ⟨br, hbr, hp1eq⟩ := List.mem_map.mp hp1
      obtain ⟨-, -, hp2eq⟩ := List.mem_map.mp hp2
      have hpeq : p = (br ++ b, e ++ [sf]) := by
        obtain ⟨p1, p2⟩ := p
        simp only [Prod.mk.injEq]
        exact ⟨hp1eq.symm, hp2eq.symm⟩
      subst hpeq
      dsimp only
      have hbClosure : ∀ x ∈ br ++ b, x ∈ modalUniverse φ₀ := by
        intro x hx
        simp only [List.mem_append] at hx
        rcases hx with hx | hx
        · exact houts x (List.mem_flatten.mpr ⟨br, hbr, hx⟩)
        · exact hb x hx
      refine ⟨hbClosure, ?_⟩
      unfold FiveWorldInvE
      have hmaxle : modalMaxWorld (br ++ b) ≤ modalMaxWorld b := by
        apply modalMaxWorld_le_of_forall_label_le_Five
        intro z hz
        simp only [List.mem_append] at hz
        rcases hz with hz | hz
        · exact known_label_le_modalMaxWorld_Five (hgrowth z (List.mem_flatten.mpr ⟨br, hbr, hz⟩))
        · exact label_le_modalMaxWorld hz
      have hN : (usedTagsFiveNonRoot φ₀ b).card ≤ (usedTagsFiveNonRoot φ₀ (br ++ b)).card :=
        Finset.card_le_card (usedTagsFiveNonRoot_mono (fun x hx => List.mem_append_right _ hx))
      have hE : (expandedRootTagsFive φ₀ b e).card ≤
          (expandedRootTagsFive φ₀ (br ++ b) (e ++ [sf])).card :=
        Finset.card_le_card (expandedRootTagsFive_mono
          (fun x hx => List.mem_append_right _ hx) (fun x hx => List.mem_append_left _ hx))
      calc modalMaxWorld (br ++ b) ≤ modalMaxWorld b := hmaxle
        _ ≤ (usedTagsFiveNonRoot φ₀ b).card + (expandedRootTagsFive φ₀ b e).card := hWE
        _ ≤ (usedTagsFiveNonRoot φ₀ (br ++ b)).card +
            (expandedRootTagsFive φ₀ (br ++ b) (e ++ [sf])).card := Nat.add_le_add hN hE
    · rw [hfstc] at hsf houts hgrowth
      simp only [Option.some.injEq, Prod.mk.injEq] at hsf
      intro p hp
      rw [← hsf.1, ← hsf.2.1] at hp
      simp only [List.zip_cons_cons, List.zip_nil_right, List.mem_singleton] at hp
      subst hp
      dsimp only
      have hbClosure : ∀ x ∈ nf ++ b, x ∈ modalUniverse φ₀ := by
        intro x hx
        simp only [List.mem_append] at hx
        rcases hx with hx | hx
        · exact houts x hx
        · exact hb x hx
      refine ⟨hbClosure, ?_⟩
      unfold FiveWorldInvE
      have hmaxle : modalMaxWorld (nf ++ b) ≤ modalMaxWorld b := by
        apply modalMaxWorld_le_of_forall_label_le_Five
        intro z hz
        simp only [List.mem_append] at hz
        rcases hz with hz | hz
        · exact known_label_le_modalMaxWorld_Five (hgrowth z hz)
        · exact label_le_modalMaxWorld hz
      have hN : (usedTagsFiveNonRoot φ₀ b).card ≤ (usedTagsFiveNonRoot φ₀ (nf ++ b)).card :=
        Finset.card_le_card (usedTagsFiveNonRoot_mono (fun x hx => List.mem_append_right _ hx))
      have hE : (expandedRootTagsFive φ₀ b e).card ≤
          (expandedRootTagsFive φ₀ (nf ++ b) e).card :=
        Finset.card_le_card (expandedRootTagsFive_mono
          (fun x hx => List.mem_append_right _ hx) (fun x hx => hx))
      calc modalMaxWorld (nf ++ b) ≤ modalMaxWorld b := hmaxle
        _ ≤ (usedTagsFiveNonRoot φ₀ b).card + (expandedRootTagsFive φ₀ b e).card := hWE
        _ ≤ (usedTagsFiveNonRoot φ₀ (nf ++ b)).card +
            (expandedRootTagsFive φ₀ (nf ++ b) e).card := Nat.add_le_add hN hE
    · rw [hfstc] at hsf; simp at hsf

end Cslib.Logic.Modal.Tableau

end
