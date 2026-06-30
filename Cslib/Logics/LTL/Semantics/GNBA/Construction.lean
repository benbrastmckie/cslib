/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.LTL.Semantics.GNBA.Atoms
public import Cslib.Computability.Automata.NA.Basic
public import Mathlib.Tactic.NormNum

/-! # GNBA Construction — States, Transitions, and NBA Conversion

This module builds the GNBA for an LTL formula and converts it to an NBA via the
cycling-counter (degeneralization) construction.

## Contents

- `Formula.GNBAState`: the atom-subtype state space
- `Formula.gnbaTr`: the one-step transition relation
- `Formula.gnbaStart`: the set of initial states
- `Formula.untlSubformulas`, `Formula.gnbaAcceptSet`: acceptance bookkeeping
- `Formula.gnbaNBA`: the NBA obtained via cycling-counter degeneralization
-/

@[expose] public section

namespace Cslib.Logic.LTL

variable {Atom : Type*}

open Cslib.Automata NA

/-! ### GNBA state type -/

/-- The GNBA state type: the subtype of `Set (Formula Atom)` satisfying `Formula.IsAtom φ`.

Atoms are maximally consistent subsets of the Fischer-Ladner closure, and they form the
state space of the GNBA tableau construction for formula `φ`. -/
def Formula.GNBAState (φ : Formula Atom) : Type _ :=
  { B : Set (Formula Atom) // Formula.IsAtom φ B }

/-- The GNBA state type is finite, since atoms are subsets of the finite closure of `φ`. -/
instance Formula.gnbaStateFinite (φ : Formula Atom) : Finite (Formula.GNBAState φ) :=
  Set.finite_coe_iff.mpr (Formula.atoms_finite φ)

/-! ### GNBA transition relation -/

/-- The GNBA transition relation for formula `φ`.

`Formula.gnbaTr φ B a B'` holds when the atom `B'` is a valid one-step successor of `B`
under input letter `a : Set Atom`. The three conditions are:
1. **Letter consistency**: for each `atom p ∈ φ.closure`, `atom p ∈ B ↔ p ∈ a`.
2. **Next-step consistency**: for each `next ψ ∈ φ.closure`, `next ψ ∈ B ↔ ψ ∈ B'`.
3. **Until expansion**: for each `untl ψ₁ ψ₂ ∈ φ.closure`,
   `untl ψ₁ ψ₂ ∈ B ↔ (ψ₂ ∈ B ∨ (ψ₁ ∈ B ∧ untl ψ₁ ψ₂ ∈ B'))`.

Together these conditions encode that `B` and `B'` are atom states connected by a valid
tableau transition step labelled by `a`. -/
def Formula.gnbaTr (φ : Formula Atom) (B : Formula.GNBAState φ) (a : Set Atom)
    (B' : Formula.GNBAState φ) : Prop :=
  (∀ p : Atom, Formula.atom p ∈ Formula.closure φ →
    (Formula.atom p ∈ B.val ↔ p ∈ a)) ∧
  (∀ ψ : Formula Atom, Formula.next ψ ∈ Formula.closure φ →
    (Formula.next ψ ∈ B.val ↔ ψ ∈ B'.val)) ∧
  (∀ ψ₁ ψ₂ : Formula Atom, Formula.untl ψ₁ ψ₂ ∈ Formula.closure φ →
    (Formula.untl ψ₁ ψ₂ ∈ B.val ↔
      (ψ₂ ∈ B.val ∨ (ψ₁ ∈ B.val ∧ Formula.untl ψ₁ ψ₂ ∈ B'.val))))

/-! ### GNBA initial states -/

/-- The GNBA initial states: atoms `B` with `φ ∈ B.val`.

A run is required to start in an atom that contains the formula `φ` itself.
This encodes the requirement that the initial time-step satisfies `φ`. -/
def Formula.gnbaStart (φ : Formula Atom) : Set (Formula.GNBAState φ) :=
  { B | φ ∈ B.val }

/-! ### Until subformulas and acceptance sets -/

/-- The Until subformulas of `φ.closure`: formulas of the form `untl ψ₁ ψ₂` in the closure.

These are exactly the subformulas whose acceptance must be tracked in the GNBA.
For each such subformula, a separate acceptance set ensures that every Until obligation
is eventually fulfilled. -/
def Formula.untlSubformulas (φ : Formula Atom) : Set (Formula Atom) :=
  { χ ∈ Formula.closure φ | ∃ ψ₁ ψ₂, χ = Formula.untl ψ₁ ψ₂ }

/-- The Until subformulas form a finite set, being a subset of the finite closure. -/
lemma Formula.untlSubformulas_finite (φ : Formula Atom) :
    Set.Finite (Formula.untlSubformulas φ) :=
  (Formula.closure_finite φ).subset (Set.sep_subset _ _)

/-- The GNBA acceptance set for a given Until subformula `χ`.

A state `B` is accepting for `χ` when either `χ ∉ B.val` (the Until formula is not
"active" or "pending") or `χ = untl ψ₁ ψ₂` and `ψ₂ ∈ B.val` (the eventuality `ψ₂`
has been fulfilled in this step).

By including states where `χ ∉ B.val`, runs that eventually stop requiring `χ` are still
accepted, ensuring progress for all active Until obligations. -/
def Formula.gnbaAcceptSet (φ : Formula Atom) (χ : Formula Atom) :
    Set (Formula.GNBAState φ) :=
  { B | χ ∉ B.val ∨ ∃ ψ₁ ψ₂, χ = Formula.untl ψ₁ ψ₂ ∧ ψ₂ ∈ B.val }

/-! ### Enumeration of Until subformulas -/

/-- A `Finset` containing all Until subformulas of `φ.closure`.

Converts the finite set `Formula.untlSubformulas φ` to a `Finset` for use in
the cycling counter construction of the GNBA-to-NBA conversion. -/
noncomputable def Formula.untlFinset (φ : Formula Atom) : Finset (Formula Atom) :=
  (Formula.untlSubformulas_finite φ).toFinset

/-- The number of Until subformulas (acceptance conditions) in `φ.closure`. -/
noncomputable def Formula.gnbaK (φ : Formula Atom) : ℕ :=
  (Formula.untlFinset φ).card

/-! ### GNBA-to-NBA conversion -/

/-- NBA state type for the cycling counter construction.

The NBA state is a pair `(B, i)` where `B : GNBAState φ` is a GNBA state and
`i : Fin (gnbaK φ).succ` is the cycling counter tracking which acceptance condition
must be checked next. The counter ranges from `0` to `gnbaK φ` (inclusive). -/
def Formula.GNBANBAState (φ : Formula Atom) : Type _ :=
  Formula.GNBAState φ × Fin (Formula.gnbaK φ).succ

/-- The NBA state type is finite: it is a product of two finite types. -/
instance Formula.gnbaNBAStateFinite (φ : Formula Atom) :
    Finite (Formula.GNBANBAState φ) := by
  unfold Formula.GNBANBAState
  haveI : Finite (Formula.GNBAState φ) :=
    Set.finite_coe_iff.mpr (Formula.atoms_finite φ)
  haveI : Finite (Fin (Formula.gnbaK φ).succ) := Finite.of_fintype _
  exact Finite.instProd

open Classical in
/-- The NBA for formula `φ`, obtained from the GNBA via the cycling counter construction
(Baier-Katoen Lemma 4.56 / degeneralization construction).

The NBA state type is `GNBANBAState φ = GNBAState φ × Fin (gnbaK φ).succ`. A run
`(B₀, 0), (B₁, i₁), (B₂, i₂), ...` in the NBA corresponds to a run `B₀, B₁, B₂, ...`
in the GNBA, with the counter tracking which GNBA acceptance condition must be satisfied next.

The counter `i : Fin (gnbaK φ + 1)` ranges from `0` to `gnbaK φ` (inclusive). Values
`0, ..., gnbaK φ - 1` indicate which acceptance condition must be satisfied next. The value
`gnbaK φ` is the **accepting value**: it is reached only after all `gnbaK φ` acceptance
conditions have been satisfied in sequence in the current cycle, and immediately resets to 0.

The transition from `(B, i)` to `(B', j)` requires:
- The GNBA transition `gnbaTr φ B a B'` holds.
- Counter advance:
  - If `gnbaK φ = 0` (no Until subformulas): `j.val = 0`.
  - If `i.val < gnbaK φ`: let `χ = untlFinset[i.val]`. If `B ∈ gnbaAcceptSet φ χ`,
    then `j.val = i.val + 1` (advance); otherwise `j = i` (stay).
  - If `i.val = gnbaK φ` (accepting state): `j.val = 0` (reset to start new cycle).

Acceptance: a state `(B, i)` is accepting when `i.val = gnbaK φ`. The accepting value is
reached only after all `gnbaK φ` acceptance conditions have been visited in order, ensuring
all Until eventualities are fulfilled.

The correctness of this construction -- that the NBA language equals
`Formula.gnbaOmegaLanguage φ` -- is proved in `Formula.gnba_language_eq`. -/
noncomputable def Formula.gnbaNBA (φ : Formula Atom) :
    NA.Buchi (Formula.GNBANBAState φ) (Set Atom) where
  Tr := fun ⟨B, i⟩ a ⟨B', j⟩ =>
    Formula.gnbaTr φ B a B' ∧
    if h : Formula.gnbaK φ = 0 then
      j.val = 0
    else if hi : i.val < Formula.gnbaK φ then
      let χ := (Formula.untlFinset φ).toList.get
          ⟨i.val, by rwa [Finset.length_toList, ← Formula.gnbaK]⟩
      if B ∈ Formula.gnbaAcceptSet φ χ then
        j.val = i.val + 1
      else
        j = i
    else
      -- i.val = gnbaK φ: reset to 0
      j.val = 0
  start := { s | s.1 ∈ Formula.gnbaStart φ ∧ s.2.val = 0 }
  accept := { s | s.2.val = Formula.gnbaK φ }

end Cslib.Logic.LTL

end
