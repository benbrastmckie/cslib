/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Init
public import Cslib.Foundations.Logic.Connectives
public import Mathlib.Order.Notation
public import Mathlib.Data.W.Basic
public import Mathlib.Logic.Denumerable

/-! # LTL Formula Type

This module defines the formula type for Linear Temporal Logic with primitives
`{atom, bot, imp, next, untl}`. The primitive `next` operator is kept separate from
`untl`: in full temporal logic, `next φ` is sometimes encoded as `φ U ⊥`, but this
encoding does not hold in all models (it relies on discreteness and non-triviality).
An independent primitive `next` avoids this coupling.

## Main definitions

- `Formula` : Inductive type for LTL formulas with constructors
  `atom`, `bot`, `imp`, `next`, `untl`
- `Formula.someFuture` (◇): `⊤ U φ` — φ holds at some future point
- `Formula.allFuture` (□): `¬◇¬φ` — φ holds at all future points
- `Formula.leadsto` (⇝): `□(p → ◇q)` — liveness: every p-state is eventually followed by q

## Notation

Propositional connectives (scoped to `Cslib.Logic.LTL`):
- `¬` (prefix, 40) : negation (`Formula.neg`)
- `∧` (infix, 36) : conjunction (`Formula.and`)
- `∨` (infix, 35) : disjunction (`Formula.or`)
- `→` (infixr, 25) : implication (`Formula.imp`)
- `↔` (infixr, 20) : biconditional (`Formula.iff`)

Temporal operators (scoped to `Cslib.Logic.LTL`):
- `𝓤` (infix, 40) : until (`Formula.untl`)
- `◯` (prefix, 40) : next-step (`Formula.next`)
- `◇` (prefix, 40) : some future / eventually (`Formula.someFuture`)
- `□` (prefix, 40) : all future / globally (`Formula.allFuture`)
- `⇝` (infix, 20) : leads-to, `□(p → ◇q)` (`Formula.leadsto`)

## Derived Operators

In `untl φ ψ`, the first argument `φ` is the **guard** (holds at all intermediate
points) and the second `ψ` is the **event** (eventually holds at the witness point).
`someFuture φ` is `⊤ U φ` (⊤ is the trivial guard, φ is the event).

## Convention Note

This module uses the **standard (Pnueli) convention** for `untl`: `untl guard event`,
where the guard precedes the event. This matches the classical LTL presentation in
[Pnueli1977] and [VardiWolper1986]:

- `untl φ ψ` means: `φ` holds at all intermediate points, `ψ` holds at the witness.
- `someFuture φ = untl ⊤ φ` (trivial guard, φ is the event).

`Cslib.Logics.Temporal` uses the same **Pnueli convention**: `untl guard event`,
so both logics agree on argument order. The module `Cslib.Logics.LTL.Embedding`
maps LTL `untl` to Temporal `reflexiveUntl` directly, without swapping arguments.

## References

* [A. Pnueli, *The Temporal Logic of Programs*][Pnueli1977]
* [H. Kamp, *Tense Logic and the Theory of Linear Order*][Kamp1968]
* [M. Y. Vardi, P. Wolper,
  *An automata-theoretic approach to automatic program verification*][VardiWolper1986]
-/

@[expose] public section

namespace Cslib.Logic.LTL

/-- LTL formula type. Primitives: atoms, falsum, implication, next-step, and until.

`next` is a primitive constructor and is not derived from `untl`. The encoding
`next φ = φ U ⊥` holds on discrete non-ending sequences but fails in general temporal
models; keeping `next` primitive supports broader model classes. -/
inductive Formula (Atom : Type u) : Type u where
  /-- Atomic proposition. -/
  | atom (p : Atom)
  /-- Falsum / bottom. -/
  | bot
  /-- Implication. -/
  | imp (φ₁ φ₂ : Formula Atom)
  /-- Next-step operator: ◯φ holds at t iff φ holds at t+1. -/
  | next (φ : Formula Atom)
  /-- Until temporal operator: φ₁ U φ₂ (guard U event: φ₁ holds until φ₂). -/
  | untl (φ₁ φ₂ : Formula Atom)
deriving DecidableEq, BEq

-- W-type encoding helpers for the `Encodable (Formula Atom)` instance (internal use only).

/-- Constructor tag type for the W-type encoding: atom tags carry the atom value;
tags `0`–`3` represent `bot`, `imp`, `next`, `untl` respectively. -/
abbrev Formula.wTag (Atom : Type u) := Atom ⊕ Fin 4

/-- Arity function: number of `Formula` sub-formulas for each W-type constructor tag. -/
def Formula.wArity {Atom : Type u} : Formula.wTag Atom → Type
  | .inl _ => Empty  -- atom: zero Formula sub-formulas
  | .inr 0  => Empty  -- bot: zero sub-formulas
  | .inr 1  => Fin 2  -- imp: two sub-formulas
  | .inr 2  => Fin 1  -- next: one sub-formula
  | .inr 3  => Fin 2  -- untl: two sub-formulas

instance {Atom : Type u} (a : Formula.wTag Atom) : Fintype (Formula.wArity a) := by
  match a with
  | .inl _     => exact (show Fintype Empty from inferInstance)
  | .inr ⟨0,_⟩ => exact (show Fintype Empty from inferInstance)
  | .inr ⟨1,_⟩ => exact (show Fintype (Fin 2) from inferInstance)
  | .inr ⟨2,_⟩ => exact (show Fintype (Fin 1) from inferInstance)
  | .inr ⟨3,_⟩ => exact (show Fintype (Fin 2) from inferInstance)

instance {Atom : Type u} (a : Formula.wTag Atom) : Encodable (Formula.wArity a) := by
  match a with
  | .inl _     => exact (show Encodable Empty from inferInstance)
  | .inr ⟨0,_⟩ => exact (show Encodable Empty from inferInstance)
  | .inr ⟨1,_⟩ => exact (show Encodable (Fin 2) from inferInstance)
  | .inr ⟨2,_⟩ => exact (show Encodable (Fin 1) from inferInstance)
  | .inr ⟨3,_⟩ => exact (show Encodable (Fin 2) from inferInstance)

/-- Embed a `Formula` into its W-type representation. -/
def Formula.toW {Atom : Type u} : Formula Atom → WType (Formula.wArity (Atom := Atom))
  | .atom p  => ⟨.inl p, Empty.elim⟩
  | .bot     => ⟨.inr ⟨0, by omega⟩, Empty.elim⟩
  | .imp a b => ⟨.inr ⟨1, by omega⟩, fun i => i.cases (Formula.toW a) (fun _ => Formula.toW b)⟩
  | .next a  => ⟨.inr ⟨2, by omega⟩, fun _ => Formula.toW a⟩
  | .untl a b => ⟨.inr ⟨3, by omega⟩, fun i => i.cases (Formula.toW a) (fun _ => Formula.toW b)⟩

/-- Decode a W-type element back into a `Formula`. Left inverse of `Formula.toW`. -/
def Formula.fromW {Atom : Type u} : WType (Formula.wArity (Atom := Atom)) → Formula Atom
  | ⟨.inl p, _⟩       => .atom p
  | ⟨.inr ⟨0,_⟩, _⟩   => .bot
  | ⟨.inr ⟨1,_⟩, f⟩   => .imp  (Formula.fromW (f ⟨0, by omega⟩)) (Formula.fromW (f ⟨1, by omega⟩))
  | ⟨.inr ⟨2,_⟩, f⟩   => .next (Formula.fromW (f ⟨0, by omega⟩))
  | ⟨.inr ⟨3,_⟩, f⟩   => .untl (Formula.fromW (f ⟨0, by omega⟩)) (Formula.fromW (f ⟨1, by omega⟩))
  | ⟨.inr ⟨n+4,h⟩, _⟩ => absurd h (by omega)

/-- `Formula.fromW` is a left inverse of `Formula.toW`. -/
theorem Formula.fromW_toW {Atom : Type u} (x : Formula Atom) :
    Formula.fromW (Formula.toW x) = x := by
  induction x with
  | atom p    => rfl
  | bot       => rfl
  | imp a b iha ihb   => exact congrArg₂ Formula.imp iha ihb
  | next a ih         => exact congrArg Formula.next ih
  | untl a b iha ihb  => exact congrArg₂ Formula.untl iha ihb

/-- LTL formulas are encodable whenever the atoms are encodable. -/
instance {Atom : Type u} [Encodable Atom] : Encodable (Formula Atom) :=
  Encodable.ofLeftInverse Formula.toW Formula.fromW Formula.fromW_toW

/-- Register `LTL.Formula` as an instance of `LTLConnectives`.

Registered before the derived-connective `abbrev`s so that the
`PropositionalConnectives.neg` / `.top` defaults are in scope
when `Formula.neg` and `Formula.top` are elaborated. -/
instance : LTLConnectives (Formula Atom) where
  bot := .bot
  imp := .imp
  untl := .untl
  next := .next

/-- Bridge lemma: the concrete constructor `Formula.imp` agrees with the `HasImp` projection
supplied by the `LTLConnectives` instance above. Compensates for the local `→` notation bound
to `Formula.imp`, which shadows the scoped `HasImp.imp` notation from `Cslib.Logic`. -/
@[scoped grind =] lemma Formula.imp_def (φ ψ : Formula Atom) : φ.imp ψ = HasImp.imp φ ψ := rfl

/-- Negation: ¬φ := φ → ⊥.

Delegates to the canonical `PropositionalConnectives.neg` default (the repo-wide
derived-connective-defaults convention). -/
abbrev Formula.neg (φ : Formula Atom) : Formula Atom := PropositionalConnectives.neg φ

/-- Verum / top: ⊤ := ⊥ → ⊥.

Delegates to the canonical `PropositionalConnectives.top` default (the repo-wide
derived-connective-defaults convention). -/
abbrev Formula.top : Formula Atom := PropositionalConnectives.top

/-- Disjunction: φ₁ ∨ φ₂ := ¬φ₁ → φ₂ -/
abbrev Formula.or (φ₁ φ₂ : Formula Atom) : Formula Atom :=
  .imp (.imp φ₁ .bot) φ₂

/-- Conjunction: φ₁ ∧ φ₂ := ¬(φ₁ → ¬φ₂) -/
abbrev Formula.and (φ₁ φ₂ : Formula Atom) : Formula Atom :=
  .imp (.imp φ₁ (.imp φ₂ .bot)) .bot

/-- Biconditional: φ₁ ↔ φ₂ := (φ₁ → φ₂) ∧ (φ₂ → φ₁) -/
abbrev Formula.iff (φ₁ φ₂ : Formula Atom) : Formula Atom :=
  (φ₁.imp φ₂).and (φ₂.imp φ₁)

/-- Some future (eventually): ◇φ := ⊤ U φ.
    ⊤ is the trivial guard, φ is the event that eventually holds. -/
abbrev Formula.someFuture (φ : Formula Atom) : Formula Atom :=
  .untl .top φ

/-- All future (globally): □φ := ¬◇¬φ -/
abbrev Formula.allFuture (φ : Formula Atom) : Formula Atom :=
  .neg (.someFuture (.neg φ))

/-- Leads-to: p ⇝ q := □(p → ◇q). A liveness property asserting that
    every state satisfying p is eventually followed by a state satisfying q. -/
abbrev Formula.leadsto (p q : Formula Atom) : Formula Atom :=
  .allFuture (.imp p (.someFuture q))

@[inherit_doc] scoped prefix:40 "¬" => Formula.neg
@[inherit_doc] scoped infix:36 " ∧ " => Formula.and
@[inherit_doc] scoped infix:35 " ∨ " => Formula.or
@[inherit_doc] scoped infixr:20 " ↔ " => Formula.iff
@[inherit_doc] scoped infix:40 " 𝓤 " => Formula.untl
@[inherit_doc] scoped prefix:40 "◯" => Formula.next
@[inherit_doc] scoped prefix:40 "◇" => Formula.someFuture
@[inherit_doc] scoped prefix:40 "□" => Formula.allFuture
@[inherit_doc] scoped infix:20 " ⇝ " => Formula.leadsto

instance : Bot (Formula Atom) := ⟨.bot⟩
instance : Top (Formula Atom) := ⟨.top⟩

/-- LTL formulas are countable whenever the atoms are encodable. -/
instance {Atom : Type u} [Encodable Atom] : Countable (Formula Atom) :=
  Encodable.countable

/-- Iterate `next` on `bot` `n` times, witnessing an injection `ℕ ↪ Formula Atom`. -/
private def iterNext {Atom : Type u} : Nat → Formula Atom
  | 0 => Formula.bot
  | n + 1 => Formula.next (iterNext n)

/-- `Formula Atom` is infinite for every `Atom` (no constraint on `Atom`). -/
instance {Atom : Type u} : Infinite (Formula Atom) :=
  Infinite.of_injective iterNext (by
    intro a b h
    induction a generalizing b with
    | zero => cases b with
      | zero => rfl
      | succ b => simp [iterNext] at h
    | succ a ih => cases b with
      | zero => simp [iterNext] at h
      | succ b => exact congrArg Nat.succ (ih (by simpa [iterNext] using h)))

/-- LTL formulas are denumerable whenever the atoms are encodable. -/
instance {Atom : Type u} [Encodable Atom] : Denumerable (Formula Atom) :=
  Denumerable.ofEncodableOfInfinite (Formula Atom)

end Cslib.Logic.LTL

end
