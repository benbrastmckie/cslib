/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Modal.Basic
public import Batteries.Data.List.Basic

/-! # Modal K Tableau Loop Induction Helpers

This module collects the generic `List.Forall₂` list helpers needed for both the soundness
and completeness loop inductions, so that `Completeness.lean` can reuse them without
importing the heavier `Soundness.lean`.

## Main Lemmas

- `forall₂_replicate_right`: `Forall₂ R xs (replicate xs.length a) ↔ ∀ x ∈ xs, R x a`.

The `forall₂_of_zip_mem`, `forall₂_append_aux`, `forall₂_drop_aux`, and `forall₂_take_aux`
helpers formerly declared here have been replaced at their call sites by the canonical
Mathlib lemmas `List.forall₂_iff_zip`, `List.rel_append`, `List.forall₂_drop`, and
`List.forall₂_take`.

## Design

`forall₂_replicate_right` was originally `private` in `Soundness.lean`. It is hoisted here
so that both the soundness and completeness loop inductions can share it without
cross-importing the two proof files.

## References

* [M. Fitting, *Proof Methods for Modal and Intuitionistic Logics*][Fitting1983], Chapter 2
-/

@[expose] public section

namespace Cslib.Logic.Modal.Tableau

/-- `Forall₂ R xs (replicate xs.length a)` iff `∀ x ∈ xs, R x a`. -/
lemma forall₂_replicate_right {α β : Type*} {R : α → β → Prop}
    {xs : List α} {a : β} :
    List.Forall₂ R xs (List.replicate xs.length a) ↔ ∀ x ∈ xs, R x a := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.length_cons, List.replicate_succ, List.mem_cons]
    constructor
    · intro hf
      cases hf with
      | cons hx hxs =>
        intro y hy
        rcases hy with rfl | hy
        · exact hx
        · exact ih.mp hxs y hy
    · intro hall
      apply List.Forall₂.cons
      · exact hall x (Or.inl rfl)
      · exact ih.mpr (fun y hy => hall y (Or.inr hy))

end Cslib.Logic.Modal.Tableau

end
