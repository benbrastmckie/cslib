/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Propositional.NaturalDeduction.Basic

/-! # Curry-Howard Isomorphism: Simply-Typed Lambda Terms

This file defines the simply-typed lambda calculus `Term` that corresponds to
`Theory.Derivation` via the Curry-Howard isomorphism. The term language is
**intrinsically typed**: `Term (T := T) G A` is a type whose inhabitants are
exactly the terms of type `A` under context `G` relative to theory `T`.

The `Term` type has exactly 11 constructors, mirroring the 11 constructors of
`Theory.Derivation` one-to-one:

| `Theory.Derivation` constructor | `Term` constructor | Curry-Howard correspondence |
|--------------------------------|--------------------|-----------------------------|
| `ax`  | `const` | theory axiom ↔ closed term constant |
| `ass` | `var`   | context assumption ↔ variable |
| `andI`  | `pair` | conjunction intro ↔ pair introduction |
| `andE1` | `fst`  | left conjunction elim ↔ first projection |
| `andE2` | `snd`  | right conjunction elim ↔ second projection |
| `orI1`  | `inl`  | left disjunction intro ↔ left injection |
| `orI2`  | `inr`  | right disjunction intro ↔ right injection |
| `orE`   | `case_` | disjunction elim ↔ case analysis |
| `impI`  | `lam`  | implication intro ↔ lambda abstraction |
| `impE`  | `app`  | implication elim (modus ponens) ↔ function application |
| `efq`   | `efq`  | ex falso quodlibet (⊥ elim) ↔ abort (intuitionistic only) |

## References

* [M. H. B. Sørensen, P. Urzyczyn,
  *Lectures on the Curry-Howard Isomorphism*][SorensenUrzyczyn2006], Section 2.2
-/

@[expose] public section

universe u

namespace Cslib.Logic.PL

open Proposition Theory InferenceSystem

variable {Atom : Type u} [DecidableEq Atom]

/-- A simply-typed lambda term over `Proposition Atom` as the type language.
`Term (T := T) G A` is the type of terms of type `A` in context `G` relative to theory `T`.
This is the intrinsically-typed term language witnessing the Curry-Howard isomorphism with
`Theory.Derivation`: the 11 constructors of `Term` correspond one-to-one with the
11 constructors of `Theory.Derivation`. -/
inductive Theory.Term {T : Theory Atom} : Ctx Atom → Proposition Atom → Type u where
  /-- Constant term corresponding to a theory axiom (mirrors `Derivation.ax`).
  A closed term inhabiting `A` is provided by each axiom `A ∈ T`. -/
  | const {Γ : Ctx Atom} {A : Proposition Atom} (_ : A ∈ T) : Term Γ A
  /-- Variable term corresponding to a context assumption (mirrors `Derivation.ass`).
  A variable of type `A` is provided by each assumption `A ∈ Γ`. -/
  | var {Γ : Ctx Atom} {A : Proposition Atom} (_ : A ∈ Γ) : Term Γ A
  /-- Pair introduction corresponding to conjunction introduction (mirrors `Derivation.andI`).
  A pair `⟨t, s⟩` inhabiting `A ∧ B` is formed from terms `t : A` and `s : B`. -/
  | pair {A B : Proposition Atom} (G : Ctx Atom) :
      Term G A → Term G B → Term G (A ∧ B)
  /-- First projection corresponding to left conjunction elimination (mirrors `Derivation.andE1`).
  The first projection `fst t` of type `A` is extracted from a pair `t : A ∧ B`. -/
  | fst {A B : Proposition Atom} (G : Ctx Atom) :
      Term G (A ∧ B) → Term G A
  /-- Second projection corresponding to right conjunction elimination (mirrors `Derivation.andE2`).
  The second projection `snd t` of type `B` is extracted from a pair `t : A ∧ B`. -/
  | snd {A B : Proposition Atom} (G : Ctx Atom) :
      Term G (A ∧ B) → Term G B
  /-- Left injection corresponding to left disjunction introduction (mirrors `Derivation.orI1`).
  A left injection `inl t` inhabiting `A ∨ B` is formed from a term `t : A`. -/
  | inl {A B : Proposition Atom} (G : Ctx Atom) :
      Term G A → Term G (A ∨ B)
  /-- Right injection corresponding to right disjunction introduction (mirrors `Derivation.orI2`).
  A right injection `inr t` inhabiting `A ∨ B` is formed from a term `t : B`. -/
  | inr {A B : Proposition Atom} (G : Ctx Atom) :
      Term G B → Term G (A ∨ B)
  /-- Case analysis corresponding to disjunction elimination (mirrors `Derivation.orE`).
  A case expression `case_ t s₁ s₂` of type `C` branches on a sum `t : A ∨ B`,
  with `s₁ : C` in context extended by `A` and `s₂ : C` in context extended by `B`. -/
  | case_ {A B C : Proposition Atom} (G : Ctx Atom) :
      Term G (A ∨ B) → Term (insert A G) C → Term (insert B G) C →
      Term G C
  /-- Lambda abstraction corresponding to implication introduction (mirrors `Derivation.impI`).
  A function `lam t` inhabiting `A → B` is formed by abstracting over a term `t : B`
  in a context extended by the assumption `A`. -/
  | lam {A B : Proposition Atom} (Γ : Ctx Atom) :
      Term (insert A Γ) B → Term Γ (A → B)
  /-- Function application corresponding to implication elimination/modus ponens
  (mirrors `Derivation.impE`).
  Applying a function `t : A → B` to an argument `s : A` yields `app t s : B`. -/
  | app {Γ : Ctx Atom} {A B : Proposition Atom} :
      Term Γ (A → B) → Term Γ A → Term Γ B
  /-- Abort term corresponding to ex falso quodlibet / bottom elimination
  (mirrors `Derivation.efq`). Available exactly when the theory is intuitionistic
  (`[IsIntuitionistic T]`). An abort term `efq t` of type `A` is formed from a term `t : ⊥`. -/
  | efq {Γ : Ctx Atom} {A : Proposition Atom} [IsIntuitionistic T] :
      Term Γ ⊥ → Term Γ A

end Cslib.Logic.PL
