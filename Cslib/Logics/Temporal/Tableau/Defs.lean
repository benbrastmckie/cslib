/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

import Cslib.Init
public import Cslib.Logics.Temporal.Syntax.Formula
public import Cslib.Logics.Temporal.Syntax.Subformulas
public import Cslib.Foundations.Logic.Tableau.PropositionalRules

/-! # Temporal Tableau Definitions

This module instantiates the Foundations tableau kernel at
`F = Cslib.Logic.Temporal.Formula Atom` and `L = Nat` (time index),
providing the `Hashable` instance, Lukasiewicz decomposition functions,
and eventuality decomposition functions.

## Time Labels

In temporal logic, the single time-line collapses the bimodal
`Label.{world, time}` pair to a bare `Nat` time index. Each formula
on a branch carries the time point at which it is evaluated.

## Lukasiewicz Encoding

`Temporal.Formula Atom` uses the same Łukasiewicz encoding as `Modal.Proposition Atom`:
- `¬φ := φ → ⊥`
- `φ ∨ ψ := (φ → ⊥) → ψ`
- `φ ∧ ψ := (φ → (ψ → ⊥)) → ⊥`
- `⊤ := ⊥ → ⊥`

Decomposition functions must match these patterns precisely and avoid overlap.

## Pnueli Convention

The internal `Formula.untl` and `Formula.snce` constructors use the Pnueli (guard, event) order:
- `untl guard event` at `t`: ∃ s > t, event at s ∧ guard at all r ∈ (t,s)
- `snce guard event` at `t`: ∃ s < t, event at s ∧ guard at all r ∈ (s,t)
- `someFuture φ = untl ⊤ φ` — ⊤ is the guard, φ is the event
- `somePast φ = snce ⊤ φ` — ⊤ is the guard, φ is the event

This is confirmed by the Satisfies.lean pattern match: `.untl ψ φ` where ψ is the guard
(first arg) and φ is the event (second arg).

Note: the `asUntl?` and `asSnce?` decomposition adapters in this module return
`some (event, guard)` tuples in reversed order for local tableau use. The internal
`untl` constructor is always guard-first (Pnueli).

## References

* [J. Burgess, *Basic Tense Logic*][Burgess1984]
* [D. Gabbay, A. Pnueli, S. Shelah, J. Stavi, *On the temporal analysis of fairness*][GPSS1980]
* [R. Smullyan, *First-Order Logic*][Smullyan1968]
-/

@[expose] public section

namespace Cslib.Logic.Temporal.Tableau

open Cslib.Logic.Tableau Cslib.Logic.Temporal

/-! ## Time Index -/

/-- Time labels for the temporal tableau. Each formula is annotated with the
time point at which it is evaluated. The bimodal `Label.{world,time}` pair
collapses to a bare natural number here since temporal logic has a single
time-line rather than a two-dimensional world-time structure. -/
abbrev TimeIndex := Nat

/-! ## Hashable Instance -/

/-- A hash function for `Formula Atom` using constructor-tag mixing.

Constructor tags: atom=0, bot=1, imp=2, untl=3, snce=4, allFuture=5, allPast=6.
Subformula hashes are combined with `mixHash`. -/
def temporalFormulaHash [Hashable Atom] : Formula Atom → UInt64
  | .atom x => mixHash 0 (hash x)
  | .bot => 1
  | .imp a b => mixHash (mixHash 2 (temporalFormulaHash a)) (temporalFormulaHash b)
  | .untl a b => mixHash (mixHash 3 (temporalFormulaHash a)) (temporalFormulaHash b)
  | .snce a b => mixHash (mixHash 4 (temporalFormulaHash a)) (temporalFormulaHash b)
  | .allFuture a => mixHash 5 (temporalFormulaHash a)
  | .allPast a => mixHash 6 (temporalFormulaHash a)

/-- `Hashable` instance for `Formula Atom`, required by `SignedFormula` and `Branch`
when the formula type is `Formula Atom`. -/
instance instHashableTemporalFormula [Hashable Atom] :
    Hashable (Formula Atom) where
  hash := temporalFormulaHash

/-! ## Fuel Measure -/

/-- Fuel bound for the temporal tableau loop.

Based on the structural complexity of the initial formula. The bound is
conservative: `(4 * n + 4) * (n + 2) + 2` where `n = complexity φ`,
following the modal K precedent. Each new time point can trigger at most
`4 * n` expansion steps; the quadratic term bounds the total. -/
def soundFuel (φ : Formula Atom) : Nat :=
  let n := φ.complexity
  (4 * n + 4) * (n + 2) + 2

/-! ## Lukasiewicz Decomposition Functions -/

/-- Decompose `φ` as negation `¬ψ = ψ → ⊥`; returns `some ψ` or `none`. -/
def tempNegOf? (φ : Formula Atom) : Option (Formula Atom) :=
  match φ with
  | .imp a .bot => some a
  | _ => none

/-- `tempNegOf?` decomposes Lukasiewicz negation. -/
@[simp]
lemma tempNegOf?_neg (a : Formula Atom) : tempNegOf? (.imp a .bot) = some a := rfl

/-- `tempNegOf?` returns `none` for atoms. -/
@[simp]
lemma tempNegOf?_atom (p : Atom) : tempNegOf? (.atom p) = none := rfl

/-- `tempNegOf?` returns `none` for bot. -/
@[simp]
lemma tempNegOf?_bot : tempNegOf? (.bot : Formula Atom) = none := rfl

/-- Decompose `φ` as disjunction `ψ₁ ∨ ψ₂ = (ψ₁ → ⊥) → ψ₂`;
returns `some (ψ₁, ψ₂)` or `none`. -/
def tempOrOf? (φ : Formula Atom) : Option (Formula Atom × Formula Atom) :=
  match φ with
  | .imp (.imp a .bot) b => some (a, b)
  | _ => none

/-- `tempOrOf?` decomposes Lukasiewicz disjunction. -/
@[simp]
lemma tempOrOf?_or (a b : Formula Atom) :
    tempOrOf? (Formula.imp (Formula.imp a Formula.bot) b) = some (a, b) := rfl

/-- `tempOrOf?` returns `none` for atoms. -/
@[simp]
lemma tempOrOf?_atom (p : Atom) : tempOrOf? (.atom p) = none := rfl

/-- Decompose `φ` as conjunction `ψ₁ ∧ ψ₂ = (ψ₁ → (ψ₂ → ⊥)) → ⊥`;
returns `some (ψ₁, ψ₂)` or `none`. -/
def tempAndOf? (φ : Formula Atom) : Option (Formula Atom × Formula Atom) :=
  match φ with
  | .imp (.imp a (.imp b .bot)) .bot => some (a, b)
  | _ => none

/-- `tempAndOf?` decomposes Lukasiewicz conjunction. -/
@[simp]
lemma tempAndOf?_and (a b : Formula Atom) :
    tempAndOf? (.imp (.imp a (.imp b .bot)) .bot) = some (a, b) := rfl

/-- `tempAndOf?` returns `none` for atoms. -/
@[simp]
lemma tempAndOf?_atom (p : Atom) : tempAndOf? (.atom p) = none := rfl

/-- Decompose `φ` as proper implication `ψ₁ → ψ₂`, excluding encoded connectives:
negation (`ψ₁ → ⊥`) and disjunction (`(ψ₁ → ⊥) → ψ₂`); returns `some (ψ₁, ψ₂)` or `none`.

Conjunction `(ψ₁ → (ψ₂ → ⊥)) → ⊥` has consequent `⊥`, so it is already excluded. -/
def tempImpOf? (φ : Formula Atom) : Option (Formula Atom × Formula Atom) :=
  match φ with
  | .imp a b =>
    match b with
    | .bot => none  -- Exclude negation and conjunction-encoded (conseq = ⊥)
    | _ =>
      match a with
      | .imp _ .bot => none  -- Exclude disjunction (antecedent is negation)
      | _ => some (a, b)
  | _ => none

/-- `tempImpOf?` returns `none` for negation (`ψ → ⊥`). -/
@[simp]
lemma tempImpOf?_neg (a : Formula Atom) :
    tempImpOf? (Formula.imp a Formula.bot) = none := rfl

/-- `tempImpOf?` returns `none` for Lukasiewicz disjunction. -/
@[simp]
lemma tempImpOf?_or (a b : Formula Atom) :
    tempImpOf? (Formula.imp (Formula.imp a Formula.bot) b) = none := by
  cases b <;> simp [tempImpOf?]

/-- `tempImpOf?` decomposes proper implication when consequent is not `⊥`
and antecedent is not a negation. -/
lemma tempImpOf?_imp {a b : Formula Atom} (h1 : b ≠ Formula.bot)
    (h2 : ∀ c : Formula Atom, a ≠ Formula.imp c Formula.bot) :
    tempImpOf? (Formula.imp a b) = some (a, b) := by
  cases hb : b with
  | bot => exact absurd hb h1
  | _ =>
    cases ha : a with
    | imp c d =>
      cases hd : d with
      | bot => exact absurd (ha ▸ hd ▸ rfl) (h2 c)
      | _ => simp [tempImpOf?]
    | _ => simp [tempImpOf?]

/-! ## Temporal Decomposition Functions -/

/-- Decompose `φ` as a positive until `T(ψ U χ)`:
`untl ψ_guard χ_event` in Pnueli (guard, event) order.
Returns `some (event, guard)` — note the reversed tuple order for local tableau use.

The internal `untl a b` constructor stores guard=a, event=b (Pnueli).
This adapter returns `(event, guard)` = `(b, a)` as a convenience for tableau rules
that pattern-match on the existential witness (event) first. -/
def asUntl? (φ : Formula Atom) : Option (Formula Atom × Formula Atom) :=
  match φ with
  | .untl guard event => some (event, guard)
  | _ => none

/-- `asUntl?` decomposes until formulas returning `(event, guard)`. -/
@[simp]
lemma asUntl?_untl (guard event : Formula Atom) :
    asUntl? (Formula.untl guard event) = some (event, guard) := rfl

/-- `asUntl?` returns `none` for non-until formulas. -/
@[simp]
lemma asUntl?_atom (p : Atom) :
    asUntl? (.atom p) = (none : Option (Formula Atom × Formula Atom)) := rfl

/-- Decompose `φ` as a positive since `T(ψ S χ)`:
returns `some (event, guard)` where `snce guard event` is the internal form. -/
def asSnce? (φ : Formula Atom) : Option (Formula Atom × Formula Atom) :=
  match φ with
  | .snce guard event => some (event, guard)
  | _ => none

/-- `asSnce?` decomposes since formulas returning `(event, guard)`. -/
@[simp]
lemma asSnce?_snce (guard event : Formula Atom) :
    asSnce? (Formula.snce guard event) = some (event, guard) := rfl

/-- Decompose `φ` as some-future: `𝐅ψ = ⊤ U ψ = untl (⊤) ψ` in Lean form.

Recall: `Formula.someFuture φ = .untl .top φ` where `.top = .imp .bot .bot`.
So `𝐅ψ` is stored as `untl (.imp .bot .bot) ψ`. -/
def asSomeFuture? (φ : Formula Atom) : Option (Formula Atom) :=
  match φ with
  | .untl (.imp .bot .bot) event => some event
  | _ => none

/-- `asSomeFuture?` decomposes some-future formulas. -/
@[simp]
lemma asSomeFuture?_someFuture (ψ : Formula Atom) :
    asSomeFuture? (Formula.someFuture ψ) = some ψ := rfl

/-- `asSomeFuture?` returns `none` for atoms. -/
@[simp]
lemma asSomeFuture?_atom (p : Atom) : asSomeFuture? (.atom p) = none := rfl

/-- Decompose `φ` as some-past: `𝐏ψ = ⊤ S ψ = snce (⊤) ψ` in Lean form.

Recall: `Formula.somePast φ = .snce .top φ` where `.top = .imp .bot .bot`. -/
def asSomePast? (φ : Formula Atom) : Option (Formula Atom) :=
  match φ with
  | .snce (.imp .bot .bot) event => some event
  | _ => none

/-- `asSomePast?` decomposes some-past formulas. -/
@[simp]
lemma asSomePast?_somePast (ψ : Formula Atom) :
    asSomePast? (Formula.somePast ψ) = some ψ := rfl

/-- `asSomePast?` returns `none` for atoms. -/
@[simp]
lemma asSomePast?_atom (p : Atom) : asSomePast? (.atom p) = none := rfl

/-- Decompose `φ` as all-future: `𝐆ψ`, a primitive constructor since task #180. The classical
equivalence `𝐆ψ ↔ ¬𝐅¬ψ` is recovered only as an axiom-backed theorem
(`Axiom.allFuture_to_classic`/`classic_to_allFuture`), not definitionally, so this adapter
pattern-matches the constructor directly rather than the old `¬𝐅¬` Lukasiewicz encoding. -/
def asAllFuture? (φ : Formula Atom) : Option (Formula Atom) :=
  match φ with
  | .allFuture ψ => some ψ
  | _ => none

/-- `asAllFuture?` decomposes all-future formulas. -/
@[simp]
lemma asAllFuture?_allFuture (ψ : Formula Atom) :
    asAllFuture? (Formula.allFuture ψ) = some ψ := rfl

/-- `asAllFuture?` returns `none` for atoms. -/
@[simp]
lemma asAllFuture?_atom (p : Atom) : asAllFuture? (.atom p) = none := rfl

/-- Decompose `φ` as all-past: `𝐇ψ`, a primitive constructor since task #180. The classical
equivalence `𝐇ψ ↔ ¬𝐏¬ψ` is recovered only as an axiom-backed theorem
(`Axiom.allPast_to_classic`/`classic_to_allPast`), not definitionally, so this adapter
pattern-matches the constructor directly rather than the old `¬𝐏¬` Lukasiewicz encoding. -/
def asAllPast? (φ : Formula Atom) : Option (Formula Atom) :=
  match φ with
  | .allPast ψ => some ψ
  | _ => none

/-- `asAllPast?` decomposes all-past formulas. -/
@[simp]
lemma asAllPast?_allPast (ψ : Formula Atom) :
    asAllPast? (Formula.allPast ψ) = some ψ := rfl

/-- `asAllPast?` returns `none` for atoms. -/
@[simp]
lemma asAllPast?_atom (p : Atom) : asAllPast? (.atom p) = none := rfl

/-! ## Subformula Count (for termination) -/

/-- Subformula count for fuel: number of distinct subformulas of `φ`. -/
def subformulaCount [DecidableEq Atom] (φ : Formula Atom) : Nat :=
  Formula.subformulaCount φ

/-! ## Basic Examples -/

/-- Example: negation decomposes correctly. -/
example (a : Formula Atom) : tempNegOf? (Formula.neg a) = some a := rfl

/-- Example: someFuture decomposes correctly. -/
example (a : Formula Atom) : asSomeFuture? (𝐅a) = some a := rfl

/-- Example: allFuture decomposes correctly. -/
example (a : Formula Atom) : asAllFuture? (𝐆a) = some a := rfl

end Cslib.Logic.Temporal.Tableau

end
