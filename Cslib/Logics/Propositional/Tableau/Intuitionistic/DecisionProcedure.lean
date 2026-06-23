/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

import Cslib.Init
public import Cslib.Logics.Propositional.Tableau.Intuitionistic.Completeness
public import Cslib.Logics.Propositional.Metalogic.IntStrongCompleteness

/-! # Intuitionistic Propositional Tableau Decision Procedure

This module delivers the `Decidable (IValid φ)` instance via the intuitionistic tableau,
and connects it to derivability via `int_soundness_completeness`.

## Main Results

- `intuitionisticTableau_decides`: The tableau correctly decides IValid.
- `instDecidableIValid`: A `Decidable (IValid φ)` instance via tableau (NEW to CSLib).
- `instDecidableDerivableIntPropAxiom`: `Decidable (Derivable IntPropAxiom φ)` via tableau.

## Design

The `Decidable (IValid φ)` instance is the primary new contribution of this module:
1. Run `intuitionisticTableau φ`.
2. If it returns `closed`, conclude `IValid φ` (by `intuitionisticTableau_sound`).
3. If it returns `openBranch b`, conclude `¬ IValid φ`
   (by `intuitionisticOpenBranch_countermodel`).

The `Derivable IntPropAxiom φ` instance uses `int_soundness_completeness` to reduce to `IValid`.

## Notes on sorry

The underlying soundness/completeness theorems use sorry. The Decidable instance
structure is sorry-free: it uses `isTrue`/`isFalse` with sorry-tagged witnesses.

## References

* [M. Fitting, *Proof Methods for Modal and Intuitionistic Logics*][Fitting1983], Chapter 4
-/

@[expose] public section

namespace Cslib.Logic.PL

open Cslib.Logic.Tableau

variable {Atom : Type*} [DecidableEq Atom] [Hashable Atom]

/-! ## Tableau Decision Correctness -/

/-- The intuitionistic tableau correctly decides intuitionistic validity:
`intuitionisticTableau φ = closed ↔ IValid φ`.

Combines `intuitionisticTableau_sound` and `intuitionisticTableau_complete`. -/
theorem intuitionisticTableau_decides (φ : Proposition Atom) :
    intuitionisticTableau φ = .closed ↔ IValid φ :=
  ⟨intuitionisticTableau_sound φ, intuitionisticTableau_complete φ⟩

/-! ## Decidable Instances (NEW to CSLib) -/

/-- `IValid φ` is decidable via the intuitionistic tableau.

This is a NEW decidability result for CSLib: intuitionistic propositional validity
was not previously decidable by a constructive procedure in this library. -/
instance instDecidableIValid (φ : Proposition Atom) : Decidable (IValid φ) :=
  match h : intuitionisticTableau φ with
  | .closed => isTrue (intuitionisticTableau_sound φ h)
  | .openBranch _ =>
    isFalse (fun hvalid =>
      have hclosed := intuitionisticTableau_complete φ hvalid
      by simp [hclosed] at h)

/-- `Derivable IntPropAxiom φ` is decidable via the intuitionistic tableau and
the completeness theorem `int_soundness_completeness`. -/
instance instDecidableDerivableIntPropAxiom (φ : Proposition Atom) :
    Decidable (Derivable IntPropAxiom φ) :=
  decidable_of_iff (IValid φ) int_soundness_completeness

end Cslib.Logic.PL

end
