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

- `forall₂_of_zip_mem`: Construct a `Forall₂` from a membership predicate on the zip.
- `forall₂_replicate_right`: `Forall₂ R xs (replicate xs.length a) ↔ ∀ x ∈ xs, R x a`.
- `forall₂_append_aux`: Append two `Forall₂` proofs.
- `forall₂_drop_aux`: Drop from a `Forall₂`.
- `forall₂_take_aux`: Take from a `Forall₂`.

## Design

These helpers were originally `private` in `Soundness.lean`. They are hoisted here so that
both the soundness and completeness loop inductions can share them without cross-importing
the two proof files.

## References

* [M. Fitting, *Proof Methods for Modal and Intuitionistic Logics*][Fitting1983], Chapter 2
-/

@[expose] public section

namespace Cslib.Logic.Modal.Tableau

/-- Construct a `List.Forall₂ R xs ys` from a membership predicate on `xs.zip ys`.

Requires `xs.length = ys.length`. -/
lemma forall₂_of_zip_mem {α β : Type*} {R : α → β → Prop}
    {xs : List α} {ys : List β}
    (hlen : xs.length = ys.length)
    (h : ∀ {x y}, (x, y) ∈ xs.zip ys → R x y) :
    List.Forall₂ R xs ys := by
  induction xs generalizing ys with
  | nil =>
    cases ys with
    | nil => exact List.Forall₂.nil
    | cons y ys => simp at hlen
  | cons x xs ih =>
    cases ys with
    | nil => simp at hlen
    | cons y ys =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
      apply List.Forall₂.cons
      · apply h; simp
      · apply ih hlen
        intro x' y' hm
        apply h; exact .tail _ hm

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

/-- Append two `Forall₂` witnesses. -/
lemma forall₂_append_aux {α β : Type*} {R : α → β → Prop}
    {l1 l2 : List α} {m1 m2 : List β}
    (h1 : List.Forall₂ R l1 m1) (h2 : List.Forall₂ R l2 m2) :
    List.Forall₂ R (l1 ++ l2) (m1 ++ m2) := by
  induction h1 with
  | nil => exact h2
  | cons hx _ ih => exact List.Forall₂.cons hx ih

/-- Drop `n` elements from a `Forall₂` witness. -/
lemma forall₂_drop_aux {α β : Type*} {R : α → β → Prop} :
    ∀ (n : Nat) {l1 : List α} {l2 : List β},
    List.Forall₂ R l1 l2 → List.Forall₂ R (l1.drop n) (l2.drop n)
  | 0, _, _, h => by simpa
  | _ + 1, _, _, .nil => by simp
  | n + 1, _, _, .cons _ h => forall₂_drop_aux n h

/-- Take `n` elements from a `Forall₂` witness. -/
lemma forall₂_take_aux {α β : Type*} {R : α → β → Prop} :
    ∀ (n : Nat) {l1 : List α} {l2 : List β},
    List.Forall₂ R l1 l2 → List.Forall₂ R (l1.take n) (l2.take n)
  | 0, _, _, _ => by simp
  | _ + 1, _, _, .nil => by simp
  | n + 1, _, _, .cons h1 h2 => .cons h1 (forall₂_take_aux n h2)

end Cslib.Logic.Modal.Tableau

end
