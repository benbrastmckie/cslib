/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

import Cslib.Init
public import Cslib.Foundations.Logic.Tableau.SignedFormula
public import Cslib.Logics.Modal.Tableau.Defs

/-! # Modal Accessibility Relation and World Helpers

This module defines the `Accessibility` structure for tracking accessibility edges in
modal K tableau branches, together with world-management helpers that support the
K-sound box rule (propagation only to recorded successors).

## Main Definitions

- `Accessibility`: An explicit record of accessibility edges between world indices.
- `Accessibility.empty`: The empty accessibility relation.
- `Accessibility.addEdge`: Add a new accessibility edge.
- `Accessibility.successorsOf`: All successors of a world in the relation.
- `modalNextWorld`: Generate a fresh world index not already used.
- `modalKnownWorlds`: All world indices mentioned in a branch.
- `modalMaxWorld`: The largest world index in a branch.

## Key Design

The `Accessibility` structure is threaded through the tableau algorithm as an accumulating
parameter, analogously to the `TimeOrdering` in the Bimodal tableau. This allows the
box-positive rule to propagate `T(φ)` only to explicitly recorded successors (K-sound),
rather than to all worlds on the branch (which would be S5-unsound).

## References

* [M. Fitting, *Proof Methods for Modal and Intuitionistic Logics*][Fitting1983], Chapter 2
-/

@[expose] public section

namespace Cslib.Logic.Modal.Tableau

open Cslib.Logic.Tableau Cslib.Logic.Modal

variable {Atom : Type*} [DecidableEq Atom] [Hashable Atom]

/-! ## Accessibility Relation -/

/-- A finite accessibility relation between world indices, represented as a list of edges.

The relation is built incrementally: each time a diamond or box-negative rule creates a
fresh successor world, an edge is added to this structure. -/
structure Accessibility where
  /-- The list of accessibility edges as ordered pairs `(w, w')` where `w` can access `w'`. -/
  edges : List (WorldIndex × WorldIndex)

namespace Accessibility

/-- The empty accessibility relation with no edges. -/
def empty : Accessibility := ⟨[]⟩

/-- Add an accessibility edge `w → w'` to the relation. -/
def addEdge (acc : Accessibility) (w w' : WorldIndex) : Accessibility :=
  ⟨(w, w') :: acc.edges⟩

/-- All successors of world `w` in the accessibility relation.

Returns all `w'` such that `w → w'` appears in the edges. -/
def successorsOf (acc : Accessibility) (w : WorldIndex) : List WorldIndex :=
  acc.edges.filterMap fun (src, tgt) => if src == w then some tgt else none

/-- All worlds that appear as either source or target in any edge. -/
def allWorlds (acc : Accessibility) : List WorldIndex :=
  acc.edges.foldl (fun ws (src, tgt) =>
    let ws' := if ws.any (· == src) then ws else src :: ws
    if ws'.any (· == tgt) then ws' else tgt :: ws') []

/-- `true` if the accessibility relation contains the edge `w → w'`. -/
def hasEdge (acc : Accessibility) (w w' : WorldIndex) : Bool :=
  acc.edges.any fun (src, tgt) => src == w && tgt == w'

end Accessibility

/-! ## World Helpers -/

/-- All world indices mentioned in a branch (as labels of signed formulas). -/
def modalKnownWorlds (b : List (SignedFormula (Proposition Atom) WorldIndex)) : List WorldIndex :=
  b.foldl (fun ws sf => if ws.any (· == sf.label) then ws else sf.label :: ws) []

/-- The maximum world index in a branch, defaulting to 0 if the branch is empty. -/
def modalMaxWorld (b : List (SignedFormula (Proposition Atom) WorldIndex)) : WorldIndex :=
  b.foldl (fun mx sf => max mx sf.label) 0

/-- A fresh world index: one more than the maximum in the branch.

This guarantees the fresh world does not appear as a label in `b`. -/
def modalNextWorld (b : List (SignedFormula (Proposition Atom) WorldIndex)) : WorldIndex :=
  modalMaxWorld b + 1

/-- `modalNextWorld b` is strictly greater than every world index in `b`.

This property guarantees that fresh worlds do not collide with existing world labels. -/
lemma modalNextWorld_gt (b : List (SignedFormula (Proposition Atom) WorldIndex))
    (sf : SignedFormula (Proposition Atom) WorldIndex)
    (hmem : sf ∈ b) : sf.label < modalNextWorld b := by
  unfold modalNextWorld modalMaxWorld
  have key : ∀ (xs : List (SignedFormula (Proposition Atom) WorldIndex)) (init : WorldIndex),
      init ≤ xs.foldl (fun mx sf => max mx sf.label) init := by
    intro xs
    induction xs with
    | nil => intro init; simp
    | cons hd tl ih =>
      intro init
      simp only [List.foldl]
      exact Nat.le_trans (Nat.le_max_left _ _) (ih _)
  have key2 : ∀ (xs : List (SignedFormula (Proposition Atom) WorldIndex)) (init : WorldIndex)
      (sf : SignedFormula (Proposition Atom) WorldIndex) (hmem : sf ∈ xs),
      sf.label ≤ xs.foldl (fun mx sf => max mx sf.label) init := by
    intro xs
    induction xs with
    | nil => intro _ _ hmem; simp at hmem
    | cons hd tl ih =>
      intro init sf hmem
      rw [List.mem_cons] at hmem
      simp only [List.foldl]
      cases hmem with
      | inl h => subst h; exact Nat.le_trans (Nat.le_max_right _ _) (key _ _)
      | inr h => exact ih _ _ h
  exact Nat.lt_succ_of_le (key2 b 0 sf hmem)

/-- Every label in a branch is bounded by `modalMaxWorld b`.

This is the membership bound; essentially `key2` from `modalNextWorld_gt`. -/
lemma label_le_modalMaxWorld
    {b : List (SignedFormula (Proposition Atom) WorldIndex)}
    {sf : SignedFormula (Proposition Atom) WorldIndex}
    (h : sf ∈ b) : sf.label ≤ modalMaxWorld b :=
  Nat.lt_succ_iff.mp (modalNextWorld_gt b sf h)

omit [DecidableEq Atom] [Hashable Atom] in
/-- `modalMaxWorld` is monotone under list prepend:
`modalMaxWorld b ≤ modalMaxWorld (xs ++ b)`.

The maximum of a branch only grows as more formulas are prepended. -/
lemma modalMaxWorld_le_append
    (xs b : List (SignedFormula (Proposition Atom) WorldIndex)) :
    modalMaxWorld b ≤ modalMaxWorld (xs ++ b) := by
  simp only [modalMaxWorld, List.foldl_append]
  suffices mono : ∀ (ys : List (SignedFormula (Proposition Atom) WorldIndex))
      (i j : WorldIndex), i ≤ j →
      ys.foldl (fun mx sf => max mx sf.label) i ≤
      ys.foldl (fun mx sf => max mx sf.label) j by
    exact mono b 0 _ (Nat.zero_le _)
  intro ys
  induction ys with
  | nil => intro i j h; simpa
  | cons hd tl ih =>
    intro i j h
    simp only [List.foldl]
    apply ih
    exact Nat.max_le.mpr ⟨Nat.le_trans h (Nat.le_max_left j hd.label), Nat.le_max_right j hd.label⟩

omit [DecidableEq Atom] [Hashable Atom] in
/-- `modalNextWorld` is monotone under list prepend:
`modalNextWorld b ≤ modalNextWorld (xs ++ b)`.

Corollary of `modalMaxWorld_le_append`. -/
lemma modalNextWorld_le_append
    (xs b : List (SignedFormula (Proposition Atom) WorldIndex)) :
    modalNextWorld b ≤ modalNextWorld (xs ++ b) := by
  unfold modalNextWorld
  exact Nat.succ_le_succ (modalMaxWorld_le_append xs b)

/-! ## Box Propagation Helper -/

/-- Collect all box-positive formulas `T(□φ)@w` from a branch for propagation.

Returns a list of `(φ, w)` pairs for all box-positive signed formulas. -/
def boxPositivesOf (b : List (SignedFormula (Proposition Atom) WorldIndex)) :
    List (Proposition Atom × WorldIndex) :=
  b.filterMap fun sf =>
    if sf.sign == .pos then
      match sf.formula with
      | .box φ => some (φ, sf.label)
      | _ => none
    else none

/-- Generate the signed formulas to propagate from `T(□φ)@w` to all successors of `w`.

For each successor `w'` of `w` in `acc`, returns `T(φ)@w'`, filtered to exclude
formulas already present on the branch. This implements the K box-positive rule:
propagation is restricted to RECORDED successors only, not all worlds. -/
def boxPropagation (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (φ : Proposition Atom) (w : WorldIndex) :
    List (SignedFormula (Proposition Atom) WorldIndex) :=
  (acc.successorsOf w).filterMap fun w' =>
    let sf : SignedFormula (Proposition Atom) WorldIndex := ⟨.pos, φ, w'⟩
    if b.any (· == sf) then none else some sf

end Cslib.Logic.Modal.Tableau

end
