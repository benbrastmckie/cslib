/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Propositional.Defs

/-! # Generic Propositional Embedding

This module defines a shared typeclass skeleton `PropositionalEmbedding` and a single generic
structural embedding `PL.Proposition.embed` that factors out the three near-identical
PL-to-target embeddings (`toModal`, `toTemporal`, `toBimodal`).

## Main Definitions

- `PropositionalEmbedding`: Typeclass parameterised by atom and target formula type carrying
  an atom-injection map `atomEmbed`.
- `PL.Proposition.embed`: Generic structural embedding using any `PropositionalEmbedding`
  instance. Structural on `atom`/`bot`/`imp`; Łukasiewicz on `and`/`or`.
- `NativePropositionalEmbedding`: Uninstantiated extension point for future
  intuitionistic-faithful embeddings with native `and`/`or`.

## Encoding Rationale and Classical Scope

The `and` and `or` connectives use the Łukasiewicz encodings into `{bot, imp}`:
- `A ∧ B` maps to `¬(A → ¬B)` = `(A → (B → ⊥)) → ⊥`
- `A ∨ B` maps to `¬A → B` = `(A → ⊥) → B`

These encodings are classically equivalent to `∧` and `∨` but **not** intuitionistically
([Wajsberg1938], [McKinsey1939]); the `embed` skeleton therefore targets classical logics.

**Why not use native `and`/`or`?** The Modal, Temporal, and Bimodal formula types do not have
native `and`/`or` constructors. Only `PL.Proposition` has `HasAnd`/`HasOr` instances (task 173
is deferred). Pushing `and`/`or` into `PropositionalConnectives` would require updating the
four concrete formula types simultaneously and falls outside the scope of this consolidation
(see task 173).

**Intuitionistic lift.** An intuitionistic embedding faithful to native `∧`/`∨` can be provided
in the future by instantiating `NativePropositionalEmbedding` for each target. That extension
point is deliberately uninstantiated here; it is provided as a typed stub so the module
boundary is clear.

## References

* [M. Wajsberg, *Untersuchungen über den Aussagenkalkül von A. Heyting*][Wajsberg1938]
* [J. C. C. McKinsey,
  *Proof of the Independence of the Primitive Symbols of Heyting's Calculus*][McKinsey1939]
* [I. Johansson, *Der Minimalkalkül, ein reduzierter intuitionistischer Formalismus*][Johansson1937]
* [D. Prawitz, *Natural Deduction: A Proof-Theoretical Study*][Prawitz1965]
-/

@[expose] public section

namespace Cslib.Logic

/-- Typeclass recording an atom-injection map from `Atom` into a target formula type `F`.

Together with `[HasBot F] [HasImp F]`, this is exactly the data needed to construct a
classical structural embedding of `PL.Proposition Atom` into `F` via `PL.Proposition.embed`.

**Design**: The typeclass carries only the atom map; `bot` and `imp` are already supplied
by the `PropositionalConnectives` hierarchy. This is the minimal atom-injection class that
makes `embed` typeclass-polymorphic without duplicating existing infrastructure. -/
class PropositionalEmbedding (Atom : Type*) (F : Type*) [HasBot F] [HasImp F] where
  /-- Injection of propositional atoms into the target formula type. -/
  atomEmbed : Atom → F

/-- Generic structural embedding of `PL.Proposition Atom` into any target formula type `F`
equipped with `[HasBot F]`, `[HasImp F]`, and `[PropositionalEmbedding Atom F]`.

- `atom`, `bot`, `imp` map to the corresponding constructors of `F`.
- `and` and `or` use the Łukasiewicz encoding (classically correct, not intuitionistically):
  - `A ∧ B` ↦ `(A → (B → ⊥)) → ⊥`
  - `A ∨ B` ↦ `(A → ⊥) → B`

See the module-level note for the classical-scope limitation. -/
def PL.Proposition.embed [HasBot F] [HasImp F] [PropositionalEmbedding Atom F] :
    PL.Proposition Atom → F
  | .atom p => PropositionalEmbedding.atomEmbed p
  | .bot => HasBot.bot
  | .imp a b => HasImp.imp a.embed b.embed
  | .and a b => HasImp.imp (HasImp.imp a.embed (HasImp.imp b.embed HasBot.bot)) HasBot.bot
  | .or a b => HasImp.imp (HasImp.imp a.embed HasBot.bot) b.embed

/-! ## Equational Lemmas -/

/-- `embed` on atom reduces to the atom injection. -/
@[simp]
theorem PL.Proposition.embed_atom [HasBot F] [HasImp F] [PropositionalEmbedding Atom F]
    (p : Atom) :
    (PL.Proposition.atom p : PL.Proposition Atom).embed (F := F) =
    PropositionalEmbedding.atomEmbed p := rfl

/-- `embed` on bot reduces to `HasBot.bot`. -/
@[simp]
theorem PL.Proposition.embed_bot [HasBot F] [HasImp F] [PropositionalEmbedding Atom F] :
    (PL.Proposition.bot : PL.Proposition Atom).embed (F := F) = HasBot.bot := rfl

/-- `embed` on imp reduces to `HasImp.imp` applied to the embedded subformulas. -/
@[simp]
theorem PL.Proposition.embed_imp [HasBot F] [HasImp F] [PropositionalEmbedding Atom F]
    (a b : PL.Proposition Atom) :
    (PL.Proposition.imp a b).embed (F := F) = HasImp.imp a.embed b.embed := rfl

/-- `embed` on and uses the Łukasiewicz encoding `(A → (B → ⊥)) → ⊥`. -/
@[simp]
theorem PL.Proposition.embed_and [HasBot F] [HasImp F] [PropositionalEmbedding Atom F]
    (a b : PL.Proposition Atom) :
    (PL.Proposition.and a b).embed (F := F) =
    HasImp.imp (HasImp.imp a.embed (HasImp.imp b.embed HasBot.bot)) HasBot.bot := rfl

/-- `embed` on or uses the Łukasiewicz encoding `(A → ⊥) → B`. -/
@[simp]
theorem PL.Proposition.embed_or [HasBot F] [HasImp F] [PropositionalEmbedding Atom F]
    (a b : PL.Proposition Atom) :
    (PL.Proposition.or a b).embed (F := F) =
    HasImp.imp (HasImp.imp a.embed HasBot.bot) b.embed := rfl

/-! ## Extension Point -/

/-- Uninstantiated extension point for a future intuitionistic-faithful embedding.

A type `F` with native `∧`/`∨` constructors (`HasAnd F`, `HasOr F`) could provide a
faithful embedding of `PL.Proposition` that preserves the native `and`/`or` without
Łukasiewicz encoding. This class is deliberately **not instantiated here**: it is provided
as a typed stub to make the extension boundary explicit. Instantiation requires each target
formula type (`Modal.Proposition`, `Temporal.Formula`, `Bimodal.Formula`) to gain primitive
`∧`/`∨` constructors, which is deferred to task 173. -/
class NativePropositionalEmbedding (Atom : Type*) (F : Type*) [HasBot F] [HasImp F]
    [HasAnd F] [HasOr F] where
  /-- Native injection of propositional atoms into the target formula type. -/
  nativeAtomEmbed : Atom → F

end Cslib.Logic
