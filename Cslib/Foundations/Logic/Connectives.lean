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

Negation and verum are shared derived connectives: `neg φ := φ → ⊥` and `top := ⊥ → ⊥`
are valid in minimal, intuitionistic, and classical logic alike ([Johansson1937], [Prawitz1965]).
These are provided as **defaulted fields** on `PropositionalConnectives`, giving
a single canonical source for the Lukasiewicz encodings. Each concrete formula type delegates
its local `abbrev`s (`Proposition.neg`, `Formula.neg`, etc.) to these defaults.
Biconditional (`iff`) is deferred until `HasAnd` is instantiated on all the formula types.

## Module Routing

The bundled connective classes serve different logic modules:

| Class | Primitive operators | Logic module |
|-------|---------------------|--------------|
| `FutureTemporalConnectives` | `bot`, `imp`, `untl` | LTL future fragment |
| `LTLConnectives` | `bot`, `imp`, `untl`, `next` | `Cslib.Logics.LTL` |
| `TemporalConnectives` | `bot`, `imp`, `untl`, `snce` | `Cslib.Logics.Temporal` |
| `BimodalConnectives` | `bot`, `imp`, `untl`, `snce`, `box` | `Cslib.Logics.Bimodal` |
| `ModalConnectives` | `bot`, `imp`, `box` | `Cslib.Logics.Modal` |

`HasUntil` is shared across all temporal classes, but the argument order of `untl` differs
by convention: `LTLConnectives` uses `untl guard event` (standard/Pnueli convention), while
`TemporalConnectives` and `BimodalConnectives` use `untl event guard` (Burgess convention).
See `Cslib.Logics.LTL.Embedding` for the explicit bridge between the two conventions.

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
minimal) require a separate `HasDiamond` typeclass, since `□` and `◇` become independent
operators. -/
class HasBox (F : Type*) where
  /-- The necessity/box modality. -/
  box : F → F

/-- A type has a diamond (possibility) modality.

In classical modal logic, diamond is derived from box via `◇φ := ¬□¬φ`. However, in
non-classical (intuitionistic or minimal) modal logics, `□` and `◇` become independent
operators that do not satisfy the classical duality. This typeclass provides a primitive
diamond for systems where this duality fails or where diamond is taken as a separate
primitive alongside box. See `Axioms.AxiomDiaDuality` for the optional duality axiom
connecting `HasBox` and `HasDiamond` instances. -/
class HasDiamond (F : Type*) where
  /-- The possibility/diamond modality. -/
  diamond : F → F

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

/-- Propositional connectives: falsum and implication, with derived negation and verum.

`HasAnd` and `HasOr` are defined as standalone atomic classes in this module rather than
folded into `PropositionalConnectives`, since not every concrete formula type provides
`and`/`or` explicitly yet (`Modal.Proposition` and `PL.Proposition` do; `Temporal.Formula`
and `Bimodal.Formula` do not).

The fields `neg` and `top` carry Lukasiewicz defaults valid in minimal, intuitionistic,
and classical logic ([Johansson1937], [Prawitz1965]). Concrete formula types may delegate
their local `neg`/`top` `abbrev`s to these defaults to avoid copy-pasting the encodings. -/
class PropositionalConnectives (F : Type*) extends HasBot F, HasImp F where
  /-- Negation as Lukasiewicz encoding: ¬φ := φ → ⊥.

  Valid in minimal, intuitionistic, and classical logic ([Johansson1937]). -/
  neg : F → F := fun φ => HasImp.imp φ HasBot.bot
  /-- Verum / top as Lukasiewicz encoding: ⊤ := ⊥ → ⊥.

  Valid in minimal, intuitionistic, and classical logic ([Johansson1937], [Prawitz1965]). -/
  top : F := HasImp.imp (HasBot.bot : F) HasBot.bot

/-- Modal connectives: propositional connectives plus necessity.

Box is the sole primitive modal operator because necessitation and the K axiom are pure proof
rules on box; with diamond primitive, necessitation becomes the interaction law `¬◇¬`
([Blackburn2001] Chapter 1 takes the diamond-first alternative). See
[ChagrovZakharyaschev1997] Section 3.1 for the box-first presentation. Diamond is derived via
classical negation (`◇φ := ¬□¬φ`) and need not appear in the typeclass. Non-classical modal
logics (intuitionistic, minimal) require extending this class with a primitive `HasDiamond` once
such systems are formalized in CSLib. -/
class ModalConnectives (F : Type*) extends PropositionalConnectives F, HasBox F

/-- Future temporal connectives: propositional connectives plus until (no since, no next).

`LTLConnectives` extends this with `HasNext`. Factoring out the future fragment
allows code generic over future-only temporal logics without committing to
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

/-- Bimodal connectives: temporal connectives (primary) plus necessity.

Extends `TemporalConnectives` as the primary parent so that `[BimodalConnectives F]` provides
`[TemporalConnectives F]`, `[FutureTemporalConnectives F]`, and `[PropositionalConnectives F]`
automatically through the inheritance chain. The necessity operator `□` is added as an atomic
mixin via `HasBox`. A priority-100 bridge instance (below) provides `[ModalConnectives F]` for
code that needs the modal fragment. This follows the standard Mathlib mixin pattern:
primary chain for the dominant fragment, bridge for the secondary bundle. -/
class BimodalConnectives (F : Type*) extends TemporalConnectives F, HasBox F

/-- Bridge: any `BimodalConnectives` instance synthesizes `ModalConnectives`.

Priority 100 (below default 1000) avoids interfering with direct `ModalConnectives` instances
while still making `inferInstance : ModalConnectives F` work from `[BimodalConnectives F]`. -/
instance (priority := 100) [BimodalConnectives F] : ModalConnectives F where
  bot := HasBot.bot
  imp := HasImp.imp
  box := HasBox.box

end Cslib.Logic
