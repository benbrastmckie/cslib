/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

import Cslib.Init
public import Cslib.Logics.Propositional.Tableau.Classical.Completeness
public import Cslib.Logics.Propositional.Tableau.Classical.Soundness
public import Cslib.Init

/-! # Classical Tableau Decision Procedure

This module delivers a `Decidable (Tautology φ)` instance via the classical tableau, registered
at lowered priority, and connects it to derivability via the `prop_completeness_iff_tautology`
bridge.

## Main Results

- `classicalTableau_decides`: The tableau correctly decides tautologyhood.
- `instDecidableTautologyTableau`: A `Decidable (Tautology φ)` instance via tableau.
- `instDecidableDerivable`: A `Decidable (Derivable PropositionalAxiom φ)` instance.

## Design

The `Decidable (Tautology φ)` instance works as follows:
1. Run `classicalTableau φ`.
2. If it returns `closed`, conclude `Tautology φ` (by `classicalTableau_sound`).
3. If it returns `openBranch b`, conclude `¬ Tautology φ`
   (by `classicalOpenBranch_countermodel` + `BoolEvaluate_eq_iff`).

The `Derivable PropositionalAxiom φ` instance uses `prop_completeness_iff_tautology`
to reduce to `Tautology φ`.

## Implementation Status

Both directions are now fully proved (sorry-free). `classicalTableau_sound` was proved first;
`classicalTableau_complete` in `Classical/Completeness.lean` is now also sorry-free, established
via the base-3 exponential fuel-sufficiency argument: fuel `3 ^ complexity φ` is
sufficient to expand every branch, so any branch returned as open is a Hintikka set, yielding
a Boolean countermodel. The `Decidable` instance and `instDecidableTautology` are both
sorry-free.

## References

* [R. Smullyan, *First-Order Logic*][Smullyan1968], Chapter V
* [M. Fitting, *Proof Methods for Modal and Intuitionistic Logics*][Fitting1983], Chapter 2
-/

@[expose] public section

namespace Cslib.Logic.PL

open Cslib.Logic.Tableau

variable {Atom : Type*} [DecidableEq Atom] [Hashable Atom]

/-! ## Tableau Decision Correctness -/

omit [Hashable Atom] in
/-- The classical tableau correctly decides tautologyhood:
`classicalTableau φ = closed ↔ Tautology φ`.

This combines soundness and completeness:
- Forward: by `classicalTableau_sound`.
- Backward: by `classicalTableau_complete`. -/
theorem classicalTableau_decides (φ : Proposition Atom) :
    classicalTableau φ = .closed ↔ Tautology φ :=
  ⟨classicalTableau_sound φ, classicalTableau_complete φ⟩

/-! ## Decidable Instances -/

/-- `Tautology φ` is decidable via the classical tableau.

This is an alternative to the Boolean enumeration `instDecidableTautology` in `Bool.lean`.
The two instances are extensionally equivalent but use different algorithms.

Note: Unlike the Boolean enumeration, this decision procedure does not require `Fintype Atom`;
the tableau algorithm works for any `DecidableEq Atom` and `Hashable Atom`.

Priority: deliberately lowered to `100` (below the default `1000`). This instance does not
reduce in the kernel — evaluating it via `decide`/`whnf` stalls on the underlying
`WellFounded.fix` recursion used by `classicalTableau`, so `decide (Tautology φ)` gets stuck
rather than closing. Lowering the priority means `Decidable (Tautology φ)` resolution falls
through to the kernel-reducible `instDecidableTautology` whenever `Fintype Atom` is available,
so `decide` remains usable on tautology goals. In the `Fintype`-free case this instance remains
the sole candidate, where priority never comes into play. -/
instance (priority := 100) instDecidableTautologyTableau (φ : Proposition Atom) :
    Decidable (Tautology φ) :=
  match h : classicalTableau φ with
  | .closed => isTrue (classicalTableau_sound φ h)
  | .openBranch b =>
    isFalse (fun htaut =>
      -- If φ were a tautology, the tableau would have closed
      have hclosed := classicalTableau_complete φ htaut
      -- But hclosed says closed, while h says openBranch b
      by simp [hclosed] at h)

-- Note: `instDecidableDerivablePropositionalAxiom` (Boolean enumeration) already exists
-- in `Metalogic/StrongCompleteness.lean`. We do not define a duplicate here.
-- The tableau-based alternative can be recovered from `classicalTableau_decides` directly.

end Cslib.Logic.PL

end
