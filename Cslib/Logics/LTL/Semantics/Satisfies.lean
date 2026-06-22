/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.LTL.Syntax.Formula
public import Cslib.Foundations.Data.OmegaSequence.Defs
public import Mathlib.Data.Finset.Attr
public import Mathlib.Tactic.Attr.Core
public import Mathlib.Tactic.Finiteness.Attr
public import Mathlib.Tactic.SetLike
public import Mathlib.Tactic.ToAdditive

/-! # LTL Satisfaction over Omega-Words

This module defines a basic satisfaction relation for LTL formulas over omega-words
of states. A `State` type is equipped with a valuation `v : Atom → State → Prop`
that determines which atomic propositions hold at each state. An omega-word is an
`ωSequence State`, and satisfaction is evaluated at the first state of the sequence,
with temporal operators moving along the sequence via `head` and `tail`.

The semantics follow the standard Kripke/Pnueli definition of LTL over ω-sequences.
Connection to `OmegaExecution` from the LTS library is deferred to future work.

## Main definitions

- `Satisfies v w φ` : formula `φ` holds at the first state of omega-word `w`
  under valuation `v`
- `Valid v φ` : `φ` holds at the first state of every omega-word under `v`
- `Satisfiable φ` : `φ` holds at the first state of some omega-word under some
  valuation

## References

* [A. Pnueli, *The Temporal Logic of Programs*][Pnueli1977]
* [M. Y. Vardi, P. Wolper,
  *An automata-theoretic approach to automatic program verification*][VardiWolper1986]
-/

@[expose] public section

namespace Cslib.Logic.LTL

variable {Atom State : Type*}

/-- Satisfaction relation for LTL over omega-words of states.

`Satisfies v w φ` means formula `φ` holds at the first state of the omega-word `w`,
where `v : Atom → State → Prop` determines which atoms hold at each state.

The `untl` case: `φ U ψ` holds at the current state when there exists a future
position `j` where ψ holds (the event), and φ holds at all intermediate positions
`k < j` (the guard). -/
def Satisfies (v : Atom → State → Prop) (w : ωSequence State) : Formula Atom → Prop
  | .atom p => v p w.head
  | .bot => False
  | .imp φ ψ => Satisfies v w φ → Satisfies v w ψ
  | .next φ => Satisfies v w.tail φ
  | .untl φ ψ => ∃ j, Satisfies v (w.drop j) ψ ∧ ∀ k < j, Satisfies v (w.drop k) φ

/-- A formula holds at the first state of every omega-word under the given valuation. -/
def Valid (v : Atom → State → Prop) (φ : Formula Atom) : Prop :=
  ∀ (w : ωSequence State), Satisfies v w φ

/-- A formula is satisfiable: it holds at the first state of some omega-word
  under some valuation. -/
def Satisfiable (φ : Formula Atom) : Prop :=
  ∃ (v : Atom → State → Prop) (w : ωSequence State), Satisfies v w φ

namespace Satisfies

/-! ## Constructor Lemmas -/

/-- Truth of an atom is determined by the valuation at the first state of the word. -/
@[simp]
theorem atom_iff (v : Atom → State → Prop) (w : ωSequence State) (p : Atom) :
    Satisfies v w (.atom p) ↔ v p w.head :=
  Iff.rfl

/-- Bot (⊥) is false everywhere. -/
@[simp]
theorem bot_iff (v : Atom → State → Prop) (w : ωSequence State) :
    Satisfies v w .bot ↔ False :=
  Iff.rfl

/-- Truth of implication is material conditional. -/
@[simp]
theorem imp_iff (v : Atom → State → Prop) (w : ωSequence State)
    (φ ψ : Formula Atom) :
    Satisfies v w (.imp φ ψ) ↔
      (Satisfies v w φ → Satisfies v w ψ) :=
  Iff.rfl

/-- Next: φ holds at the next state (the tail of the omega-word). -/
@[simp]
theorem next_iff (v : Atom → State → Prop) (w : ωSequence State)
    (φ : Formula Atom) :
    Satisfies v w (.next φ) ↔ Satisfies v w.tail φ :=
  Iff.rfl

/-- Until: φ U ψ holds iff ψ eventually holds, with φ as the guard at all intermediate steps.

  In `untl φ ψ`, `φ` is the guard (holds at all intermediate positions k < j) and
  `ψ` is the event (holds at witness position j). -/
@[simp]
theorem untl_iff (v : Atom → State → Prop) (w : ωSequence State)
    (φ ψ : Formula Atom) :
    Satisfies v w (.untl φ ψ) ↔
      ∃ j, Satisfies v (w.drop j) ψ ∧ ∀ k < j, Satisfies v (w.drop k) φ :=
  Iff.rfl

/-! ## Derived Connective Lemmas -/

/-- Bot (⊥) is not satisfiable at any word. -/
theorem bot_false (v : Atom → State → Prop) (w : ωSequence State) :
    ¬ Satisfies v w .bot :=
  id

/-- Negation: ¬φ holds iff φ does not hold. -/
theorem neg_iff (v : Atom → State → Prop) (w : ωSequence State)
    (φ : Formula Atom) :
    Satisfies v w (¬φ) ↔ ¬ Satisfies v w φ := by
  simp only [Satisfies]

/-- Top (⊤) is satisfiable everywhere. -/
theorem top_true (v : Atom → State → Prop) (w : ωSequence State) :
    Satisfies v w Formula.top := by
  intro h
  exact h

/-! ## Temporal Operator Lemmas -/

/-- Some future (◇φ): φ eventually holds at some future position. -/
theorem someFuture_iff (v : Atom → State → Prop) (w : ωSequence State)
    (φ : Formula Atom) :
    Satisfies v w (◇φ) ↔ ∃ j, Satisfies v (w.drop j) φ := by
  simp only [Satisfies]
  constructor
  · rintro ⟨j, hevent, _⟩
    exact ⟨j, hevent⟩
  · rintro ⟨j, hj⟩
    exact ⟨j, hj, fun _ _ => id⟩

/-- All future (□φ): φ holds at every future position. -/
theorem allFuture_iff (v : Atom → State → Prop) (w : ωSequence State)
    (φ : Formula Atom) :
    Satisfies v w (□φ) ↔ ∀ j, Satisfies v (w.drop j) φ := by
  simp only [Satisfies]
  constructor
  · intro h j
    by_contra hns
    exact h ⟨j, hns, fun _ _ => id⟩
  · intro h ⟨j, hevent, _⟩
    exact hevent (h j)

end Satisfies

end Cslib.Logic.LTL

end
