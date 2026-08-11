/-
Copyright (c) 2025 Thomas Waring, 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Waring, Benjamin Brast-McKie
-/

module

import Cslib.Init
public import Cslib.Foundations.Logic.Connectives
public import Mathlib.Data.FunLike.Basic
public import Mathlib.Data.Set.Basic
public import Mathlib.Order.TypeTags
public import Aesop.BuiltinRules

/-! # Propositions and theories

## Main definitions

- `Proposition` : the type of propositions over a given type of atom. Primitives are `atom`,
  `bot` (falsum), `imp` (implication), `and` (conjunction), and `or` (disjunction). Negation
  (`neg`), verum (`top`), and biconditional (`iff`) are derived connectives (`abbrev`s). This
  follows natural deduction style ([Gentzen1935], [Prawitz1965], Ch. I sec. 1.2) and the
  constructive mathematics tradition ([Johansson1937], [TroelstraVanDalen1988]) in which `neg A`
  abbreviates `A → ⊥` rather than being taken as primitive.
- `Theory` : set of `Proposition`.
- `IsIntuitionistic` : a theory is intuitionistic if it contains the principle of explosion.
- `IsClassical` : an intuitionistic theory is classical if it further contains double negation
  elimination.
- `Proposition.subst` : replace `atom x` in a `A : Proposition Atom` with `f x`, for a function
  `f : Atom → Proposition Atom'`. This induces a monad structure on `Proposition`, with
  `pure := Proposition.atom`. `Theory` is a functor, by mapping each proposition `A ∈ T` to
  `f <$> A`.
- `Theory.intuitionisticCompletion` : the freely generated intuitionistic theory extending a given
  theory.

## Architecture

Two proof systems are defined for this propositional language:

- **Layer 1 — Natural Deduction** (`NaturalDeduction/Basic.lean`): a `Theory.Derivation` inductive
  with 10 primitive constructors (axiom, assumption, conjunction intro/elim ×2, disjunction
  intro ×2/elim, implication intro/elim). The theory parameter controls logic strength: `MPL`
  (Johansson's minimal logic, [Johansson1937]), `IPL` (intuitionistic), and `CPL` (classical).

- **Layer 2 — Hilbert System** (`ProofSystem/`): an axiom predicate hierarchy
  (`MinPropAxiom` / `IntPropAxiom` / `PropositionalAxiom`) with sequent derivability and a
  Hilbert-style proof-theoretic treatment.

- **Bridge**: `NaturalDeduction/Equivalence.lean` establishes extensional equivalence between the
  two proof systems for all three logic strengths, in both closed-context (`hilbert_iff_nd`,
  `hilbert_iff_nd_min`, `hilbert_iff_nd_int`, `hilbert_iff_nd_cl`) and context-based forms
  (`hilbert_iff_nd_ctx`, `hilbert_iff_nd_ctx_min`, `hilbert_iff_nd_ctx_int`,
  `hilbert_iff_nd_ctx_cl`).

## Notation

We introduce notation for the logical connectives: `⊥ ⊤ ∧ ∨ → ¬` for, respectively, falsum, verum,
conjunction, disjunction, implication and negation.

## References

* [I. Johansson, *Der Minimalkalkül, ein reduzierter intuitionistischer Formalismus*][Johansson1937]
* [G. Gentzen, *Untersuchungen über das logische Schließen*][Gentzen1935]
* [D. Prawitz, *Natural Deduction: A Proof-Theoretical Study*][Prawitz1965]
* [A. S. Troelstra, D. van Dalen,
  *Constructivism in Mathematics: An Introduction*][TroelstraVanDalen1988]
* [A. Church, *Introduction to Mathematical Logic*][Church1956]
* [A. Chagrov, M. Zakharyaschev, *Modal Logic*][ChagrovZakharyaschev1997], Chapter 1
-/

@[expose] public section

universe u

variable {Atom : Type u} [DecidableEq Atom]

namespace Cslib.Logic.PL

/-- Propositions. Primitives are atoms, falsum, implication, conjunction, and disjunction. -/
inductive Proposition (Atom : Type u) : Type u where
  /-- Propositional atoms -/
  | atom (x : Atom)
  /-- Falsum / bottom -/
  | bot
  /-- Implication -/
  | imp (a b : Proposition Atom)
  /-- Conjunction -/
  | and (a b : Proposition Atom)
  /-- Disjunction -/
  | or (a b : Proposition Atom)
deriving DecidableEq, Repr

/-- Negation as a derived connective: ¬A := A → ⊥ -/
abbrev Proposition.neg : Proposition Atom → Proposition Atom := (Proposition.imp · .bot)

/-- Verum / top as a derived connective: ⊤ := ⊥ → ⊥ -/
abbrev Proposition.top : Proposition Atom := .imp .bot .bot

/-- Biconditional as a derived connective: A ↔ B := (A → B) ∧ (B → A) -/
abbrev Proposition.iff (A B : Proposition Atom) : Proposition Atom :=
  (A.imp B).and (B.imp A)

instance : Bot (Proposition Atom) := ⟨.bot⟩
instance : Top (Proposition Atom) := ⟨.top⟩

@[inherit_doc] scoped infix:20 " ↔ " => Proposition.iff
@[inherit_doc] scoped prefix:40 " ¬ " => Proposition.neg

/-- Register `Proposition` as an instance of `PropositionalConnectives`. -/
instance : PropositionalConnectives (Proposition Atom) where
  bot := .bot
  imp := .imp

/-- Register `HasAnd` instance for `Proposition`. -/
instance : HasAnd (Proposition Atom) where
  and := .and

/-- Register `HasOr` instance for `Proposition`. -/
instance : HasOr (Proposition Atom) where
  or := .or

omit [DecidableEq Atom] in
/-- Bridge lemma: the concrete constructor `Proposition.and` agrees with the `HasAnd` projection
supplied by the `HasAnd` instance above. Compensates for the local `∧` notation bound to
`Proposition.and`, which shadows the scoped `HasAnd.and` notation from `Cslib.Logic`. -/
@[scoped grind =] lemma Proposition.and_def (A B : Proposition Atom) :
    A.and B = HasAnd.and A B := rfl

omit [DecidableEq Atom] in
/-- Bridge lemma: the concrete constructor `Proposition.or` agrees with the `HasOr` projection
supplied by the `HasOr` instance above. Compensates for the local `∨` notation bound to
`Proposition.or`, which shadows the scoped `HasOr.or` notation from `Cslib.Logic`. -/
@[scoped grind =] lemma Proposition.or_def (A B : Proposition Atom) :
    A.or B = HasOr.or A B := rfl

omit [DecidableEq Atom] in
/-- Bridge lemma: the concrete constructor `Proposition.imp` agrees with the `HasImp` projection
supplied by the `PropositionalConnectives` instance above. Compensates for the local `→`
notation bound to `Proposition.imp`, which shadows the scoped `HasImp.imp` notation from
`Cslib.Logic`. -/
@[scoped grind =] lemma Proposition.imp_def (A B : Proposition Atom) :
    A.imp B = HasImp.imp A B := rfl

/-- Substitute each atom in a proposition for a proposition, possibly changing the atomic
language. -/
def Proposition.subst {Atom Atom' : Type u} (f : Atom → Proposition Atom') :
    Proposition Atom → Proposition Atom'
  | atom x => f x
  | bot => .bot
  | imp A B => .imp (A.subst f) (B.subst f)
  | and A B => .and (A.subst f) (B.subst f)
  | or A B => .or (A.subst f) (B.subst f)

-- This is probably a lawful monad, but that doesn't seem to be important.
instance : Monad Proposition where
  pure := .atom
  bind A f := A.subst f

/-- Theories are arbitrary sets of propositions. -/
abbrev Theory (Atom) := Set (Proposition Atom)

namespace Theory

/-- Extend a substitution from `Proposition` to `Theory`. -/
protected def subst {Atom Atom' : Type u} (T : Theory Atom) (f : Atom → Proposition Atom') :
    Theory Atom' := T.image (· >>= f)

instance : Functor Theory where
  map f := Set.image (f <$> ·)

/-- The empty theory corresponds to minimal propositional logic. -/
abbrev MPL : Theory (Atom) := ∅

/-- Intuitionistic propositional logic adds the principle of explosion (ex falso quodlibet). -/
abbrev IPL : Theory Atom :=
  Set.range (Proposition.imp ⊥ ·)

/-- Classical logic further adds double negation elimination. -/
abbrev CPL : Theory Atom :=
  Set.range (fun (A : Proposition Atom) ↦ ¬¬A → A)

/-- A theory is intuitionistic if it validates ex falso quodlibet. -/
@[scoped grind]
class IsIntuitionistic (T : Theory Atom) where
  efq (A : Proposition Atom) : (⊥ → A) ∈ T

omit [DecidableEq Atom] in
@[scoped grind =]
theorem isIntuitionisticIff (T : Theory Atom) : IsIntuitionistic T ↔ IPL ⊆ T := by
  constructor
  · rintro h x ⟨y, rfl⟩
    simp only [Proposition.imp_def]
    exact h.efq y
  · intro h
    exact ⟨fun A => h ⟨A, (Proposition.imp_def ⊥ A).symm⟩⟩

/-- A theory is classical if it validates double-negation elimination. -/
@[scoped grind]
class IsClassical (T : Theory Atom) where
  dne (A : Proposition Atom) : (¬¬A → A) ∈ T

omit [DecidableEq Atom] in
@[scoped grind =]
theorem isClassicalIff (T : Theory Atom) : IsClassical T ↔ CPL ⊆ T := by grind

instance instIsIntuitionisticIPL : IsIntuitionistic (Atom := Atom) IPL where
  efq A := Set.mem_range.mpr ⟨A, rfl⟩

instance instIsClassicalCPL : IsClassical (Atom := Atom) CPL where
  dne A := Set.mem_range.mpr ⟨A, rfl⟩

omit [DecidableEq Atom] in
@[scoped grind →]
theorem instIsIntuitionisticExtension {T T' : Theory Atom} [IsIntuitionistic T]
    (h : T ⊆ T') : IsIntuitionistic T' := by grind

omit [DecidableEq Atom] in
@[scoped grind →]
theorem instIsClassicalExtension {T T' : Theory Atom} [IsClassical T] (h : T ⊆ T') :
    IsClassical T' := by grind

/-- Extend a theory T to an intuitionistic theory over a larger atom type by adding the principle
of explosion. The atom type is extended with WithBot to ensure the result is over a strictly
larger language. -/
@[reducible]
def intuitionisticCompletion (T : Theory Atom) : Theory (WithBot Atom) :=
  (WithBot.some <$> T) ∪ IPL

instance instIsIntuitionisticIntuitionisticCompletion (T : Theory Atom) :
    IsIntuitionistic T.intuitionisticCompletion := by grind

end Cslib.Logic.PL.Theory
