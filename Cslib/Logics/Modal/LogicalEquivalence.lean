/-
Copyright (c) 2026 Fabrizio Montesi, Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi, Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Modal.Basic
public import Cslib.Foundations.Logic.LogicalEquivalence

/-! # Logical Equivalence for Modal Propositions

This file defines a one-hole context for `Proposition`, a fill operation that substitutes a
proposition into the hole, and the model-class-parametric equivalence `Proposition.Equiv S`,
which is instantiated as an instance of the `LogicalEquivalence` framework
(`Cslib.Foundations.Logic.LogicalEquivalence`).

## Main Definitions

* `Proposition.Context` -- a one-hole context matching the fork's `Proposition` constructors
* `Proposition.Context.fill` -- substitute a proposition into the hole
* `Proposition.Equiv S` -- two propositions are equivalent in the class of models `S`: they agree
  on satisfaction at every model in `S` and every world
* `≡[S]` / `≡` -- notation for `Proposition.Equiv S` / `Proposition.Equiv Set.univ`
* `Satisfies.Context` -- a judgemental context for `Judgement`
* The `LogicalEquivalence (Proposition Atom) (Judgement World Atom) Satisfies.Bundled` instance,
  registering Modal logic K's equivalence with the shared Foundations framework

## Design Notes

The `Context` constructors mirror the recursive positions of `Proposition`: `imp` has two
sub-proposition positions (left and right), and `box` has one. The ground constructors `atom` and
`bot` have no sub-propositions, so they do not appear in `Context`.

`Proposition.Equiv` is parametric in the model class `S`, mirroring the parametricity of
`Proposition.valid` (`Basic.lean`). This lets equivalence be stated relative to any frame class
(e.g. the T/B/4/5/S4/S5 classes from `Cube.lean`), not just the class of all models: `◇□φ ≡[S] □φ`
is an S5 fact that is inexpressible with an equivalence hardwired to all models. The unqualified
`≡` is `Equiv Set.univ`, matching the all-models equivalence used by `Cslib.Logic.HML`.
-/

@[expose] public section

namespace Cslib.Logic.Modal

open scoped InferenceSystem Proposition

/-- A one-hole context for `Proposition`. Each constructor corresponds to a recursive position
in `Proposition`: `impL`/`impR` are the arguments of `imp`, `andL`/`andR` of `and`, `orL`/`orR`
of `or`, `box` is the argument of `box`, and `diamond` is the argument of `diamond`. The `hole`
constructor marks the position to be filled. -/
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
  /-- Context under `diamond`. -/
  | diamond (c : Context Atom)

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
  | .diamond c, φ => ◇(c.fill φ)

instance : HasContext (Proposition Atom) := ⟨Proposition.Context Atom, Proposition.Context.fill⟩

open scoped Proposition.Context

/-- Two propositions `φ₁` and `φ₂` are logically equivalent in the class of models `S` when they
agree on satisfaction at every model in `S` and every world. -/
def Proposition.Equiv (S : Set (Model World Atom)) (φ₁ φ₂ : Proposition Atom) : Prop :=
  ∀ m ∈ S, ∀ w : World, ⇓Modal[m,w ⊨ φ₁ ↔ φ₂]

@[inherit_doc]
scoped notation:50 φ₁ " ≡[" S "] " φ₂ => Proposition.Equiv S φ₁ φ₂

@[inherit_doc]
scoped notation:50 φ₁ " ≡ " φ₂ => Proposition.Equiv Set.univ φ₁ φ₂

/-- Unfolding lemma for `Proposition.Equiv`. -/
@[scoped grind =]
theorem Proposition.equiv_def (S : Set (Model World Atom)) (φ₁ φ₂ : Proposition Atom) :
    (φ₁ ≡[S] φ₂) ↔ (∀ m ∈ S, ∀ w : World, ⇓Modal[m,w ⊨ φ₁ ↔ φ₂]) := Iff.rfl

/-- `Proposition.Equiv` characterised as agreement of satisfaction, splitting the object-level
`↔` into the meta-level `Iff`. -/
@[scoped grind =]
theorem Proposition.equiv_iff (S : Set (Model World Atom)) (φ₁ φ₂ : Proposition Atom) :
    (φ₁ ≡[S] φ₂) ↔ (∀ m ∈ S, ∀ w : World, ⇓Modal[m,w ⊨ φ₁] ↔ ⇓Modal[m,w ⊨ φ₂]) := by
  simp only [Proposition.equiv_def]
  constructor
  · intro h m hm w
    have hh := h m hm w
    simp only [Proposition.iff, Proposition.and_def, Proposition.imp_def,
      Satisfies.and_iff_and, Satisfies.impl_iff_impl] at hh
    rw [derivation_def, derivation_def]
    exact ⟨hh.1, hh.2⟩
  · intro h m hm w
    have hh := h m hm w
    simp only [Proposition.iff, Proposition.and_def, Proposition.imp_def,
      Satisfies.and_iff_and, Satisfies.impl_iff_impl]
    rw [derivation_def, derivation_def] at hh
    exact ⟨hh.1, hh.2⟩

/-- Logically equivalent propositions are valid in the same models: `Equiv` bridges to
`Proposition.valid`. -/
theorem Proposition.equiv_valid (S : Set (Model World Atom)) (φ₁ φ₂ : Proposition Atom)
    (h : φ₁ ≡[S] φ₂) : φ₁.valid S ↔ φ₂.valid S := by
  rw [Proposition.equiv_iff] at h
  simp only [Proposition.valid]
  exact ⟨fun hv m hm w => (h m hm w).mp (hv m hm w), fun hv m hm w => (h m hm w).mpr (hv m hm w)⟩

instance (S : Set (Model World Atom)) : IsEquiv (Proposition Atom) (Proposition.Equiv S) where
  refl a := by rw [Proposition.equiv_iff]; grind
  symm a b h := by rw [Proposition.equiv_iff] at h ⊢; grind
  trans a b c h1 h2 := by rw [Proposition.equiv_iff] at h1 h2 ⊢; grind

instance (S : Set (Model World Atom)) : Congruence (Proposition Atom) (Proposition.Equiv S) where
  elim :
      Covariant (Proposition.Context Atom) (Proposition Atom) (Proposition.Context.fill)
      (Proposition.Equiv S) := by
    intro ctx φ₁ φ₂ heqv
    rw [Proposition.equiv_iff] at heqv ⊢
    intro m hm w
    induction ctx generalizing w with
    | hole => exact heqv m hm w
    | impL c φ ih =>
      simp only [Proposition.Context.fill, derivation_def]
      exact ⟨fun hf ha => hf ((ih w).mpr ha), fun hf ha => hf ((ih w).mp ha)⟩
    | impR φ c ih =>
      simp only [Proposition.Context.fill, derivation_def]
      exact ⟨fun hf ha => (ih w).mp (hf ha), fun hf ha => (ih w).mpr (hf ha)⟩
    | andL c φ ih =>
      simp only [Proposition.Context.fill, derivation_def]
      exact ⟨fun ⟨h1, h2⟩ => ⟨(ih w).mp h1, h2⟩, fun ⟨h1, h2⟩ => ⟨(ih w).mpr h1, h2⟩⟩
    | andR φ c ih =>
      simp only [Proposition.Context.fill, derivation_def]
      exact ⟨fun ⟨h1, h2⟩ => ⟨h1, (ih w).mp h2⟩, fun ⟨h1, h2⟩ => ⟨h1, (ih w).mpr h2⟩⟩
    | orL c φ ih =>
      simp only [Proposition.Context.fill, derivation_def]
      exact ⟨fun h => h.elim (fun h1 => .inl ((ih w).mp h1)) .inr,
        fun h => h.elim (fun h1 => .inl ((ih w).mpr h1)) .inr⟩
    | orR φ c ih =>
      simp only [Proposition.Context.fill, derivation_def]
      exact ⟨fun h => h.elim .inl (fun h2 => .inr ((ih w).mp h2)),
        fun h => h.elim .inl (fun h2 => .inr ((ih w).mpr h2))⟩
    | box c ih =>
      simp only [Proposition.Context.fill, derivation_def]
      exact ⟨fun hf w' hr => (ih w').mp (hf w' hr), fun hf w' hr => (ih w').mpr (hf w' hr)⟩
    | diamond c ih =>
      simp only [Proposition.Context.fill, derivation_def]
      exact ⟨fun ⟨w', hr, hs⟩ => ⟨w', hr, (ih w').mp hs⟩,
        fun ⟨w', hr, hs⟩ => ⟨w', hr, (ih w').mpr hs⟩⟩

/-- Judgemental contexts for Modal logic: a model together with a world, into which a
proposition is placed to form a `Judgement`. -/
structure Satisfies.Context (World Atom : Type*) where
  /-- The model to consider. -/
  m : Model World Atom
  /-- The world to check the proposition against. -/
  w : World

/-- Fills a judgemental context with a proposition. -/
def Satisfies.Context.fill (c : Satisfies.Context World Atom) (φ : Proposition Atom) :
    Judgement World Atom :=
  Modal[c.m, c.w ⊨ φ]

instance judgementalContext : HasHContext (Judgement World Atom) (Proposition Atom) :=
  ⟨Satisfies.Context World Atom, Satisfies.Context.fill⟩

/-- Modal logic K's equivalence, registered as an instance of the `LogicalEquivalence`
framework: equivalence relative to the class of all models (`Proposition.Equiv Set.univ`)
preserves validity of judgements under any judgemental context. -/
instance : LogicalEquivalence (Proposition Atom) (Judgement World Atom) Satisfies.Bundled where
  eqv := Proposition.Equiv Set.univ
  eqvFillValid {φ₁ φ₂ : Proposition Atom} (heqv : φ₁ ≡ φ₂)
      (c : HasHContext.Context (Judgement World Atom) (Proposition Atom))
      (h : Satisfies.Bundled c<[φ₁]) : Satisfies.Bundled c<[φ₂] := by
    rw [Proposition.equiv_iff] at heqv
    have hw := heqv c.m (Set.mem_univ c.m) c.w
    simp only [derivation_def] at hw
    simp only [Satisfies.Bundled, HasHContext.fill, Satisfies.Context.fill] at h ⊢
    exact hw.mp h

end Cslib.Logic.Modal
