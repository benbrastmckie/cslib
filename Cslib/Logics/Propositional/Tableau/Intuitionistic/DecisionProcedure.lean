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

`intuitionisticTableau_sound` is now sorry-free. The completeness direction
(`intuitionisticTableau_complete` in `Intuitionistic/Completeness.lean`) still rests on
three deferred sorries in the completeness development. The parametric `truthLemma` in
`Intuitionistic/Scheme.lean` (forcing ↔ membership, all connectives) is now sorry-free — it
gained an explicit `hpers` (positive-persistence) hypothesis and is unconditionally true over
any frame carrying it. The remaining sorries are:
- the open-branch countermodel structural property in `Intuitionistic/Scheme.lean`
- the `IValid → forcing` bridge in `Intuitionistic/Completeness.lean` (uses the
  parametric `truthLemma`)
- the `MValid → forcing` bridge in `Minimal/Completeness.lean` (reuses `truthLemma minScheme`)

The `Decidable` instance (`instDecidableDerivableIntPropAxiom`) carries the soundness branch
clean and the countermodel branch with the deferred completeness `sorryAx`. This is not a
regression introduced here; the sorry-taint pre-dates this task.

## Two Decision Routes — Distinct Roles

CSLib contains **two independent decision procedures** for `Derivable IntPropAxiom φ`:

### Route 1 (Tableau — this module, canonical registered instance)
- **Module**: `Tableau/Intuitionistic/DecisionProcedure.lean`
- **Mechanism**: Constructive signed-tableau proof-search/countermodel. Decides via
  `instDecidableIValid` composed with `int_soundness_completeness`.
- **Axiom profile**: Carries the deferred completeness `sorryAx` (see above). Will become
  sorry-free once the deferred completeness sorries are filled.
- **Exposed as**: `instDecidableDerivableIntPropAxiom` — the **sole registered `Decidable`
  instance** for `Derivable IntPropAxiom φ`.
- **Role**: Canonical extension-facing instance; feeds the modal/temporal/bimodal extensions.

### Route 2 (FMP — sorry-free, named def, not a registered instance)
- **Module**: `Metalogic/IntDecidability.lean`
- **Mechanism**: Finite model property via `Σ`-bounded finite canonical Kripke model.
- **Axiom profile**: `{propext, Classical.choice, Quot.sound}` — **sorry-free**.
- **Exposed as**: `decidableDerivableIntPropAxiomFMP` (`noncomputable def`). Also see
  `int_fmp` (FMP biconditional) and `int_fin_truth_lemma`.
- **Role**: Independent theoretical result, useful as a correctness witness. Not a registered
  instance; does not compete with `instDecidableDerivableIntPropAxiom` for resolution.

The two routes have disjoint carrier types (signed-branch worlds vs `IntFinWorld`) and
independent proof lineages. Factoring a common truth-lemma abstraction is explicitly deferred.
See also `instDecidableDerivableMinPropAxiom` / `decidableDerivableMinPropAxiomFMP` for the
analogous Minimal propositional decidability pair.

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
