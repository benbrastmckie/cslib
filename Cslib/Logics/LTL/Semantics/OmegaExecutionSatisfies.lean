/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.LTL.Semantics.Satisfies
public import Cslib.Foundations.Semantics.LTS.OmegaExecution

/-! # LTL Satisfaction over LTS OmegaExecutions

This module bridges LTL satisfaction (defined over omega-words `w : ωSequence State` with
valuation `v : Atom → State → Prop`) to the `LTS.OmegaExecution` infrastructure in
`Cslib.Foundations`.

The key ingredient is a *labeling function* `labeling : State → (Atom → Prop)` that assigns
to each LTS state the set of atomic propositions that hold in that state. Given a labeling, an
omega-execution `ss : ωSequence State` induces a valuation
`fun p s => labeling s p : Atom → State → Prop`.

## Main definitions

- `SatisfiesExec labeling ss φ` : LTL satisfaction lifted through a labeling function

## Main theorems

- `satisfiesExec_iff` : `SatisfiesExec` agrees with `Satisfies` when `v = fun p s => labeling s p`
- `satisfiesExec_atom` : atom case unfolds to `labeling ss.head p`
- `satisfiesExec_next` : next case shifts to the tail of `ss`
- `satisfiesExec_untl` : until case unfolds correctly with `drop`

## References

* [A. Pnueli, *The Temporal Logic of Programs*][Pnueli1977]
* [M. Y. Vardi, P. Wolper,
  *An automata-theoretic approach to automatic program verification*][VardiWolper1986]
-/

@[expose] public section

namespace Cslib.Logic.LTL

open ωSequence

variable {Atom State Label : Type*}

/-- LTL satisfaction lifted through a labeling function.

`SatisfiesExec labeling ss φ` holds iff the formula `φ` is satisfied at the head of
the omega-word `ss` using the valuation induced by `labeling`: atom `p` holds at state
`s` iff `labeling s p` holds. -/
def SatisfiesExec (labeling : State → (Atom → Prop))
    (ss : ωSequence State) (φ : Formula Atom) : Prop :=
  Satisfies (fun p s => labeling s p) ss φ

/-- `SatisfiesExec` unfolds to `Satisfies` with the induced valuation. -/
theorem satisfiesExec_iff {labeling : State → (Atom → Prop)} {ss : ωSequence State}
    {φ : Formula Atom} :
    SatisfiesExec labeling ss φ ↔ Satisfies (fun p s => labeling s p) ss φ :=
  Iff.rfl

/-- The atom case: `SatisfiesExec labeling ss (atom p) ↔ labeling ss.head p`. -/
theorem satisfiesExec_atom {labeling : State → (Atom → Prop)} {ss : ωSequence State}
    {p : Atom} :
    SatisfiesExec labeling ss (.atom p) ↔ labeling ss.head p :=
  Iff.rfl

/-- The bot case: `SatisfiesExec labeling ss bot ↔ False`. -/
theorem satisfiesExec_bot {labeling : State → (Atom → Prop)} {ss : ωSequence State} :
    SatisfiesExec labeling ss .bot ↔ False :=
  Iff.rfl

/-- The imp case: unfolds to an implication of `SatisfiesExec`. -/
theorem satisfiesExec_imp {labeling : State → (Atom → Prop)} {ss : ωSequence State}
    {φ ψ : Formula Atom} :
    SatisfiesExec labeling ss (.imp φ ψ) ↔
      (SatisfiesExec labeling ss φ → SatisfiesExec labeling ss ψ) :=
  Iff.rfl

/-- The next case: `SatisfiesExec labeling ss (next φ) ↔ SatisfiesExec labeling ss.tail φ`. -/
theorem satisfiesExec_next {labeling : State → (Atom → Prop)} {ss : ωSequence State}
    {φ : Formula Atom} :
    SatisfiesExec labeling ss (.next φ) ↔ SatisfiesExec labeling ss.tail φ :=
  Iff.rfl

/-- The until case: unfolds using `drop`. -/
theorem satisfiesExec_untl {labeling : State → (Atom → Prop)} {ss : ωSequence State}
    {φ ψ : Formula Atom} :
    SatisfiesExec labeling ss (.untl φ ψ) ↔
      ∃ j, SatisfiesExec labeling (ss.drop j) ψ ∧
        ∀ k < j, SatisfiesExec labeling (ss.drop k) φ :=
  Iff.rfl

/-- If `v p s = labeling s p` for all `p` and `s`, then `Satisfies v ss φ` is equivalent to
`SatisfiesExec labeling ss φ`. -/
theorem satisfiesExec_of_val_eq {labeling : State → (Atom → Prop)} {ss : ωSequence State}
    {v : Atom → State → Prop} (heq : ∀ p s, v p s = labeling s p)
    {φ : Formula Atom} :
    Satisfies v ss φ ↔ SatisfiesExec labeling ss φ := by
  simp only [SatisfiesExec]
  have hv : v = fun p s => labeling s p := funext (fun p => funext (fun s => heq p s))
  subst hv
  rfl

end Cslib.Logic.LTL

end
