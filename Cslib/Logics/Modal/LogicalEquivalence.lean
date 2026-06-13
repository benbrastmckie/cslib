/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

import Cslib.Init
public import Cslib.Logics.Modal.Basic

/-! # Logical Equivalence for Modal Propositions

This file defines a one-hole context for `Proposition`, a fill operation that substitutes a
proposition into the hole, and proves that logical equivalence (agreement of satisfaction across all
models and worlds) is a congruence with respect to contexts.

## Main Definitions

* `Proposition.Context` -- a one-hole context matching the fork's `Proposition` constructors
* `Proposition.Context.fill` -- substitute a proposition into the hole
* `LogicallyEquivalent` -- two propositions are logically equivalent when they are satisfied by
  exactly the same model-world pairs
* `LogicallyEquivalent.congruence` -- logical equivalence is preserved under all contexts

## Design Notes

The `Context` constructors mirror the recursive positions of `Proposition`: `imp` has two
sub-proposition positions (left and right), and `box` has one. The ground constructors `atom` and
`bot` have no sub-propositions, so they do not appear in `Context`.
-/

@[expose] public section

namespace Cslib.Logic.Modal

/-- A one-hole context for `Proposition`. Each constructor corresponds to a recursive position
in `Proposition`: `impL` is the left argument of `imp`, `impR` is the right argument,
`andL`/`andR` are the left/right arguments of `and`, `orL`/`orR` are the left/right arguments
of `or`, and `box` is the argument of `box`. The `hole` constructor marks the position to be
filled. -/
inductive Proposition.Context (Atom : Type u) : Type u where
  /-- The position to substitute. -/
  | hole
  /-- Context in the left argument of `imp`. -/
  | impL (c : Context Atom) (φ : Proposition Atom)
  /-- Context in the right argument of `imp`. -/
  | impR (φ : Proposition Atom) (c : Context Atom)
  /-- Context in the left argument of `and`. -/
  | andL (c : Context Atom) (φ : Proposition Atom)
  /-- Context in the right argument of `and`. -/
  | andR (φ : Proposition Atom) (c : Context Atom)
  /-- Context in the left argument of `or`. -/
  | orL (c : Context Atom) (φ : Proposition Atom)
  /-- Context in the right argument of `or`. -/
  | orR (φ : Proposition Atom) (c : Context Atom)
  /-- Context under `box`. -/
  | box (c : Context Atom)

/-- Fill the hole in a context with a proposition. -/
def Proposition.Context.fill : Proposition.Context Atom → Proposition Atom → Proposition Atom
  | .hole, φ => φ
  | .impL c ψ, φ => c.fill φ → ψ
  | .impR ψ c, φ => ψ → c.fill φ
  | .andL c ψ, φ => c.fill φ ∧ ψ
  | .andR ψ c, φ => ψ ∧ c.fill φ
  | .orL c ψ, φ => c.fill φ ∨ ψ
  | .orR ψ c, φ => ψ ∨ c.fill φ
  | .box c, φ => □(c.fill φ)

/-- Two propositions are logically equivalent when they agree on satisfaction across all models
and worlds. -/
def LogicallyEquivalent.{v} {Atom : Type u} (φ ψ : Proposition Atom) : Prop :=
  ∀ (World : Type v) (m : Model World Atom) (w : World), Satisfies m w φ ↔ Satisfies m w ψ

/-- Logical equivalence is a congruence: if `φ` and `ψ` are logically equivalent, then
`c.fill φ` and `c.fill ψ` are logically equivalent for any context `c`. -/
theorem LogicallyEquivalent.congruence.{v} {Atom : Type u} {φ ψ : Proposition Atom}
    (c : Proposition.Context Atom) (h : LogicallyEquivalent.{v} φ ψ) :
    LogicallyEquivalent.{v} (c.fill φ) (c.fill ψ) := by
  intro World m
  induction c with
  | hole => exact h World m
  | impL c _ ih =>
    intro w
    simp only [Proposition.Context.fill, Satisfies]
    exact ⟨fun hf ha => hf ((ih w).mpr ha), fun hf ha => hf ((ih w).mp ha)⟩
  | impR _ c ih =>
    intro w
    simp only [Proposition.Context.fill, Satisfies]
    exact ⟨fun hf ha => (ih w).mp (hf ha), fun hf ha => (ih w).mpr (hf ha)⟩
  | andL c _ ih =>
    intro w
    simp only [Proposition.Context.fill, Satisfies]
    exact ⟨fun ⟨ha, hb⟩ => ⟨(ih w).mp ha, hb⟩, fun ⟨ha, hb⟩ => ⟨(ih w).mpr ha, hb⟩⟩
  | andR _ c ih =>
    intro w
    simp only [Proposition.Context.fill, Satisfies]
    exact ⟨fun ⟨ha, hb⟩ => ⟨ha, (ih w).mp hb⟩, fun ⟨ha, hb⟩ => ⟨ha, (ih w).mpr hb⟩⟩
  | orL c _ ih =>
    intro w
    simp only [Proposition.Context.fill, Satisfies]
    exact ⟨fun h => h.imp (ih w).mp id, fun h => h.imp (ih w).mpr id⟩
  | orR _ c ih =>
    intro w
    simp only [Proposition.Context.fill, Satisfies]
    exact ⟨fun h => h.imp id (ih w).mp, fun h => h.imp id (ih w).mpr⟩
  | box c ih =>
    intro w
    simp only [Proposition.Context.fill, Satisfies]
    exact ⟨fun hf w' hr => (ih w').mp (hf w' hr),
           fun hf w' hr => (ih w').mpr (hf w' hr)⟩

end Cslib.Logic.Modal
