/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

import Cslib.Init

/-! # Connective Typeclasses for Composable Logics

This module defines a typeclass hierarchy for logical connectives, shared across the four
logic levels (Propositional, Modal, Temporal, Bimodal). Each formula type registers itself
as an instance of the appropriate connective class, enabling polymorphic axiom definitions
and notation.

## Design

The hierarchy adopts a hybrid five constructors `{atom, bot, imp, and, or}`,
following the operator-typeclass direction of fmontesi's PR #607 (one class per operator):
- **Atomic classes**: `HasBot`, `HasImp`, `HasAnd`, `HasOr`, `HasBox`, `HasUntil`, `HasSince`
- **Bundled classes**: `PropositionalConnectives`, `ModalConnectives`,
  `TemporalConnectives`, `BimodalConnectives`

Each concrete formula type duplicates its constructors (Lean 4 cannot extend inductives)
and registers as an instance of the appropriate bundled class.

Conjunction and disjunction are treated as primitives rather than Lukasiewicz-derived
connectives. The classical encodings `and φ ψ := ¬(φ → ¬ψ)` and `or φ ψ := ¬φ → ψ` are
only propositionally equivalent to `∧` and `∨` in classical logic ([Wajsberg1938],
[McKinsey1939]); they fail in intuitionistic and minimal logic. Making `and` and `or`
primitives via `HasAnd`/`HasOr` supports all three logic strengths with a single typeclass
hierarchy.

Negation and verum stay derived: each concrete formula type defines `neg φ := φ → ⊥` and
`top := ⊥ → ⊥` as `abbrev`s, which are valid in minimal, intuitionistic, and classical logic
alike, so no typeclass machinery is needed for them. Biconditional (`iff`) is deferred to
task 173 after `HasAnd` is instantiated on the formula types.

## References

* [I. Johansson, *Der Minimalkalkül, ein reduzierter intuitionistischer Formalismus*][Johansson1937]
* [M. Wajsberg, *Untersuchungen über den Aussagenkalkül von A. Heyting*][Wajsberg1938]
* [J. C. C. McKinsey,
  *Proof of the Independence of the Primitive Symbols of Heyting's Calculus*][McKinsey1939]
* [D. Prawitz, *Natural Deduction: A Proof-Theoretical Study*][Prawitz1965]
* [A. S. Troelstra, D. van Dalen,
  *Constructivism in Mathematics: An Introduction*][TroelstraVanDalen1988]
* [A. Church, *Introduction to Mathematical Logic*][Church1956]
* [A. Heyting, *Die formalen Regeln der intuitionistischen Logik*][Heyting1930]
* [G. Gentzen, *Untersuchungen über das logische Schließen*][Gentzen1935]
* [A. Chagrov, M. Zakharyaschev, *Modal Logic*][ChagrovZakharyaschev1997], Chapter 3
-/

@[expose] public section

namespace Cslib.Logic

/-- A type has a falsum (bottom) connective. -/
class HasBot (F : Type*) where
  /-- The falsum/bottom connective. -/
  bot : F

/-- A type has an implication connective. -/
class HasImp (F : Type*) where
  /-- The implication connective. -/
  imp : F → F → F

/-- A type has a necessity (box) modality.

Box is primitive because the necessitation rule (`if ⊢ φ then ⊢ □φ`) and the K axiom are
pure proof rules on a single connective; with diamond primitive, necessitation becomes the
interaction law `¬◇¬` ([Blackburn2001] Chapter 1 takes the diamond-first alternative).
See [ChagrovZakharyaschev1997] Section 3.1 for the box-first presentation. Box corresponds
to universal quantification over accessible worlds, preserves conjunction, distributes over
implication (axiom K), and is the subject of the necessitation rule. In classical systems,
diamond (possibility) is derived as `¬□¬φ`. Non-classical modal logics (intuitionistic,
minimal) require a separate `HasDia` typeclass, since `□` and `◇` become independent
operators. -/
class HasBox (F : Type*) where
  /-- The necessity/box modality. -/
  box : F → F

/-- A type has an until temporal operator. -/
class HasUntil (F : Type*) where
  /-- The until temporal operator. -/
  untl : F → F → F

/-- A type has a since temporal operator. -/
class HasSince (F : Type*) where
  /-- The since temporal operator. -/
  snce : F → F → F

/-- A type has a next-step temporal operator. -/
class HasNext (F : Type*) where
  /-- The next-step temporal operator. -/
  next : F → F

/-- A type has a conjunction connective. -/
class HasAnd (F : Type*) where
  /-- The conjunction connective. -/
  and : F → F → F

/-- A type has a disjunction connective. -/
class HasOr (F : Type*) where
  /-- The disjunction connective. -/
  or : F → F → F

/-- Propositional connectives: falsum and implication.

`HasAnd` and `HasOr` are defined as standalone atomic classes in this module.
Extending `PropositionalConnectives` to include them is deferred to task 173,
when the four concrete formula types will be updated to provide `and`/`or`
explicitly in their instances. -/
class PropositionalConnectives (F : Type*) extends HasBot F, HasImp F

/-- Modal connectives: propositional connectives plus necessity.

Box is the sole primitive modal operator because necessitation and the K axiom are pure proof
rules on box; with diamond primitive, necessitation becomes the interaction law `¬◇¬`
([Blackburn2001] Chapter 1 takes the diamond-first alternative). See
[ChagrovZakharyaschev1997] Section 3.1 for the box-first presentation. Diamond is derived via
classical negation (`◇φ := ¬□¬φ`) and need not appear in the typeclass. Non-classical modal
logics (intuitionistic, minimal) require extending this class with a primitive `HasDia` once
such systems are formalized in CSLib. -/
class ModalConnectives (F : Type*) extends PropositionalConnectives F, HasBox F

/-- Future temporal connectives: propositional connectives plus until (no since, no next).

This bundle is shared by both `LTLConnectives` (which adds `HasNext`) and
`TemporalConnectives` (which adds `HasSince`). Factoring out the future fragment
allows code generic over future-only temporal logics without committing to past or
next-step operators. -/
class FutureTemporalConnectives (F : Type*) extends PropositionalConnectives F, HasUntil F

/-- LTL connectives: future temporal connectives plus a primitive next-step operator.

Linear Temporal Logic uses `next` as a primitive rather than deriving it from `until`
(the encoding `next φ = φ U ⊥` does not hold in all models). `FutureTemporalConnectives`
provides `bot`, `imp`, and `untl`; this bundle adds `next`. -/
class LTLConnectives (F : Type*) extends FutureTemporalConnectives F, HasNext F

/-- Temporal connectives: propositional connectives plus until and since.

Extends `FutureTemporalConnectives` with the `since` operator, forming the standard
two-sorted temporal signature (future + past). -/
class TemporalConnectives (F : Type*) extends FutureTemporalConnectives F, HasSince F

/-- Bimodal connectives: modal connectives plus until and since.
    Note: we extend `ModalConnectives` and add `HasUntil`/`HasSince` directly
    rather than extending `TemporalConnectives`, to avoid a typeclass diamond. -/
class BimodalConnectives (F : Type*) extends ModalConnectives F, HasUntil F, HasSince F

end Cslib.Logic
