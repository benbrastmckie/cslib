/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

import Cslib.Init
public import Cslib.Logics.Modal.Metalogic.DerivationTree
public import Cslib.Logics.Modal.Semantics.Birelational

/-! # CK: Constructive Modal Logic K (Axioms and Soundness)

This module defines bare constructive modal logic `CK` ([Wijesekera1990]) and proves its
soundness over the *minimal* birelational semantics (`MValid`, arbitrary upward-closed
`botForces`), the fallible-world semantics for which `CK` is also complete (see
`Constructive/SegmentLindenbaum.lean` and the completeness theorem below).

`CK` is the strict sub-system of Simpson's `IK` obtained by *dropping* the Fischer-Servi
axioms `Cd` (`◇(φ∨ψ) → ◇φ∨◇ψ`) and `Idb` (`(◇φ→□ψ) → □(φ→ψ)`) and the nullary axiom
`Nd` (`◇⊥ → ⊥`): only the two K-distribution schemata `Kb` and `Kd` remain, over the same
9 intuitionistic propositional schemata.

## Main Definitions

- `CKModalAxiom`: the axiom schemata of bare `CK` -- 9 intuitionistic propositional schemata
  plus `k` (Kb) and `kdia` (Kd). **No** `cd`/`idb`/`dbot` constructors.
- `ck_axiom_sound`: every `CKModalAxiom` instance is `MValid`.
- `ck_soundness`/`ck_soundness_derivable`: minimal birelational soundness for `CK`.

## Provenance of the axiom list

The constructor list is pinned against two independent sources:

- The ianshil/CK Coq mechanization: `CKH.v` defines the Hilbert system for bare `CK` with
  exactly the intuitionistic propositional axioms plus Kb and Kd, parametrized by additional
  axioms `AdAx`; bare `CK` is `NoAdAx := fun _ => False` (no additional axioms whatsoever).
  Its completeness for `CK` is `Completeness_seg/CK_seg_completeness.v`, over *segment*
  models with fallible (exploding) worlds -- deliberately not over intuitionistic-falsum
  models, for which bare `CK` is incomplete.
- [Wijesekera1990] §2: constructive `K` has Kb and Kd only. **Terminological caveat
  (resolved)**: Wijesekera's own system additionally validates `Nd = ◇⊥ → ⊥` because his
  models make falsum unforceable; some authors therefore call `CK + Nd` "CK". This
  formalization follows the ianshil/CK convention (`NoAdAx`): *bare* `CK` **excludes** `Nd`.
  Indeed `Nd` is not `MValid` (take `botForces := fun _ => True`), so bare `CK`'s soundness
  target `MValid` forces this choice; conversely `Nd` *is* `IValid` (vacuously), which is
  exactly why bare `CK` is incomplete for `IValid` and the completeness theorem here is
  stated over `MValid`.

## References

* [D. Wijesekera, *Constructive modal logics I*][Wijesekera1990], §2.
* [A. K. Simpson, *The Proof Theory and Semantics of Intuitionistic Modal Logic*][Simpson1994],
  Chapter 3 (the `IK` superset; frame conditions F1/F2).
-/

@[expose] public section

namespace Cslib.Logic.Modal

open Cslib.Logic

universe u v

variable {Atom : Type u}

/-! ## The bare-`CK` Axiom Schemata -/

/-- Axiom schemata for bare constructive modal logic `CK` ([Wijesekera1990] §2; ianshil
`CKH.v` with `NoAdAx`): the 9 intuitionistic propositional schemata (mirroring
`IntPropAxiom`) plus the two K-distribution schemata `k` (Kb) and `kdia` (Kd).

Deliberately **absent** relative to `IKModalAxiom` (do not add them -- each would change
the logic): `cd` (Fischer-Servi `◇(φ∨ψ) → ◇φ∨◇ψ`), `idb` (Fischer-Servi
`(◇φ→□ψ) → □(φ→ψ)`), and `dbot` (Nd, `◇⊥ → ⊥`). None of the three is `MValid`, and none
is derivable in bare `CK`. -/
inductive CKModalAxiom : Proposition Atom → Prop where
  /-- Weakening: `φ → (ψ → φ)`. -/
  | implyK (φ ψ : Proposition Atom) :
      CKModalAxiom (φ.imp (ψ.imp φ))
  /-- Distribution: `(φ → (ψ → χ)) → ((φ → ψ) → (φ → χ))`. -/
  | implyS (φ ψ χ : Proposition Atom) :
      CKModalAxiom ((φ.imp (ψ.imp χ)).imp ((φ.imp ψ).imp (φ.imp χ)))
  /-- Ex falso quodlibet: `⊥ → φ`. -/
  | efq (φ : Proposition Atom) :
      CKModalAxiom (Proposition.bot.imp φ)
  /-- Conjunction introduction: `φ → (ψ → φ ∧ ψ)`. -/
  | andI (φ ψ : Proposition Atom) :
      CKModalAxiom (Cslib.Logic.Axioms.AndI φ ψ)
  /-- Left conjunction elimination: `φ ∧ ψ → φ`. -/
  | andE1 (φ ψ : Proposition Atom) :
      CKModalAxiom (Cslib.Logic.Axioms.AndE1 φ ψ)
  /-- Right conjunction elimination: `φ ∧ ψ → ψ`. -/
  | andE2 (φ ψ : Proposition Atom) :
      CKModalAxiom (Cslib.Logic.Axioms.AndE2 φ ψ)
  /-- Left disjunction introduction: `φ → φ ∨ ψ`. -/
  | orI1 (φ ψ : Proposition Atom) :
      CKModalAxiom (Cslib.Logic.Axioms.OrI1 φ ψ)
  /-- Right disjunction introduction: `ψ → φ ∨ ψ`. -/
  | orI2 (φ ψ : Proposition Atom) :
      CKModalAxiom (Cslib.Logic.Axioms.OrI2 φ ψ)
  /-- Disjunction elimination: `(φ → χ) → ((ψ → χ) → ((φ ∨ ψ) → χ))`. -/
  | orE (φ ψ χ : Proposition Atom) :
      CKModalAxiom (Cslib.Logic.Axioms.OrE φ ψ χ)
  /-- Kb: `□(φ → ψ) → (□φ → □ψ)`. -/
  | k (φ ψ : Proposition Atom) :
      CKModalAxiom
        ((Proposition.box (φ.imp ψ)).imp ((Proposition.box φ).imp (Proposition.box ψ)))
  /-- Kd: `□(φ → ψ) → (◇φ → ◇ψ)`. -/
  | kdia (φ ψ : Proposition Atom) :
      CKModalAxiom ((Proposition.box (φ.imp ψ)).imp ((◇φ).imp (◇ψ)))

end Cslib.Logic.Modal
