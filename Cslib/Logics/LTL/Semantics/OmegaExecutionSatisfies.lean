/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.LTL.Semantics.Satisfies
public import Cslib.Foundations.Semantics.LTS.OmegaExecution

/-! # LTL Satisfaction over LTS OmegaExecutions

This module bridges LTL satisfaction (defined over abstract valuations `v : ℕ → (Atom → Prop)`)
to the `LTS.OmegaExecution` infrastructure in `Cslib.Foundations`.

The key ingredient is a *labeling function* `labeling : State → (Atom → Prop)` that assigns
to each LTS state the set of atomic propositions that hold in that state. Given a labeling, an
omega-execution `ss : ωSequence State` induces a valuation `fun n => labeling (ss n)`.

## Main definitions

- `SatisfiesExec labeling ss i φ` : LTL satisfaction lifted through a labeling function

## Main theorems

- `satisfiesExec_iff` : `SatisfiesExec` agrees with `Satisfies` when `v = labeling ∘ ss`
- `satisfiesExec_atom` : atom case unfolds to `labeling (ss i) p`
- `satisfiesExec_next` : next case shifts the time index
- `satisfiesExec_untl` : until case unfolds correctly

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

`SatisfiesExec labeling ss i φ` holds iff the formula `φ` is satisfied at time `i` in
the omega-word induced by `ss` via `labeling`: the valuation assigns atom `p` to hold at
time `n` iff `p ∈ labeling (ss n)` (in the Prop sense: `labeling (ss n) p` holds). -/
def SatisfiesExec (labeling : State → (Atom → Prop))
    (ss : ωSequence State) (i : ℕ) (φ : Formula Atom) : Prop :=
  Satisfies (fun n => labeling (ss n)) i φ

/-- `SatisfiesExec` unfolds to `Satisfies` with the induced valuation. -/
theorem satisfiesExec_iff {labeling : State → (Atom → Prop)} {ss : ωSequence State}
    {i : ℕ} {φ : Formula Atom} :
    SatisfiesExec labeling ss i φ ↔ Satisfies (fun n => labeling (ss n)) i φ :=
  Iff.rfl

/-- The atom case: `SatisfiesExec labeling ss i (atom p) ↔ labeling (ss i) p`. -/
theorem satisfiesExec_atom {labeling : State → (Atom → Prop)} {ss : ωSequence State}
    {i : ℕ} {p : Atom} :
    SatisfiesExec labeling ss i (.atom p) ↔ labeling (ss i) p :=
  Iff.rfl

/-- The bot case: `SatisfiesExec labeling ss i bot ↔ False`. -/
theorem satisfiesExec_bot {labeling : State → (Atom → Prop)} {ss : ωSequence State}
    {i : ℕ} :
    SatisfiesExec labeling ss i .bot ↔ False :=
  Iff.rfl

/-- The imp case: unfolds to an implication of `SatisfiesExec`. -/
theorem satisfiesExec_imp {labeling : State → (Atom → Prop)} {ss : ωSequence State}
    {i : ℕ} {φ ψ : Formula Atom} :
    SatisfiesExec labeling ss i (.imp φ ψ) ↔
      (SatisfiesExec labeling ss i φ → SatisfiesExec labeling ss i ψ) :=
  Iff.rfl

/-- The next case: `SatisfiesExec labeling ss i (next φ) ↔ SatisfiesExec labeling ss (i+1) φ`. -/
theorem satisfiesExec_next {labeling : State → (Atom → Prop)} {ss : ωSequence State}
    {i : ℕ} {φ : Formula Atom} :
    SatisfiesExec labeling ss i (.next φ) ↔ SatisfiesExec labeling ss (i + 1) φ :=
  Iff.rfl

/-- The until case: unfolds using the Burgess convention. -/
theorem satisfiesExec_untl {labeling : State → (Atom → Prop)} {ss : ωSequence State}
    {i : ℕ} {ψ φ : Formula Atom} :
    SatisfiesExec labeling ss i (.untl ψ φ) ↔
      ∃ j ≥ i, SatisfiesExec labeling ss j φ ∧
        ∀ k, i ≤ k → k < j → SatisfiesExec labeling ss k ψ :=
  Iff.rfl

/-- If `v n = labeling (ss n)` for all `n`, then `Satisfies v i φ` is equivalent to
`SatisfiesExec labeling ss i φ`. -/
theorem satisfiesExec_of_val_eq {labeling : State → (Atom → Prop)} {ss : ωSequence State}
    {v : ℕ → (Atom → Prop)} (heq : ∀ n, v n = labeling (ss n))
    {i : ℕ} {φ : Formula Atom} :
    Satisfies v i φ ↔ SatisfiesExec labeling ss i φ := by
  simp only [SatisfiesExec]
  have hv : v = fun n => labeling (ss n) := funext heq
  subst hv
  rfl

end Cslib.Logic.LTL

end
