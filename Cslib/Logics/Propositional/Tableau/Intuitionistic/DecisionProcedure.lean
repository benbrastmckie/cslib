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

- `intuitionisticTableau_decides`: The tableau correctly decides `IValid.{_, 0}`.
- `instDecidableIValid`: A `Decidable (IValid.{_, 0} φ)` instance via tableau (NEW to CSLib).
- `instDecidableDerivableIntPropAxiom`: `Decidable (Derivable IntPropAxiom φ)` via tableau, at
  `IValid`'s original, unpinned universe (routed through `ivalid_universe_invariant`).
- `ivalid_descend` / `ivalid_universe_invariant`: `IValid` is invariant under the universe
  `World` is quantified over -- the bridge that lets the `Type 0` pin above cost nothing.

## Design

The `Decidable (IValid φ)` instance is the primary new contribution of this module:
1. Run `intuitionisticTableau φ`.
2. If it returns `closed`, conclude `IValid φ` (by `intuitionisticTableau_sound`).
3. If it returns `openBranch b`, conclude `¬ IValid φ`
   (by `intuitionisticOpenBranch_countermodel`).

The `Derivable IntPropAxiom φ` instance uses `int_soundness_completeness` to reduce to `IValid`.

## Notes on sorry

This module is now sorry-free, and so is everything it depends on. `intuitionisticTableau_sound`
is sorry-free. The completeness direction (`intuitionisticTableau_complete` in
`Intuitionistic/Completeness.lean`) is now ALSO sorry-free: `openBranch_countermodel`'s
upward-closure conjunct (`Intuitionistic/Scheme.lean`) is discharged (the AUGMENTED `augSets`
witness carries positive persistence post-repair), so the `IValid.{_, 0} φ → forcing` bridge no
longer defers anything. The parametric `truthLemma` in `Intuitionistic/Scheme.lean` (forcing ↔
membership, all connectives) is likewise sorry-free — it gained an explicit `hpers`
(positive-persistence) hypothesis and is unconditionally true over any frame carrying it.

The `Decidable` instance (`instDecidableDerivableIntPropAxiom`) is now sorry-free end to end.

## Two Decision Routes — Distinct Roles

CSLib contains **two independent decision procedures** for `Derivable IntPropAxiom φ`:

### Route 1 (Tableau — this module, canonical registered instance)
- **Module**: `Tableau/Intuitionistic/DecisionProcedure.lean`
- **Mechanism**: Constructive signed-tableau proof-search/countermodel. Decides via
  `instDecidableIValid` composed with `int_soundness_completeness`.
- **Axiom profile**: `{propext, Classical.choice, Quot.sound}` — **sorry-free** (see "Notes on
  sorry" above).
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

/-- The intuitionistic tableau correctly decides intuitionistic validity (at universe `0`):
`intuitionisticTableau φ = closed ↔ IValid.{_, 0} φ`.

Combines `intuitionisticTableau_sound` and `intuitionisticTableau_complete`. -/
theorem intuitionisticTableau_decides (φ : Proposition Atom) :
    intuitionisticTableau φ = .closed ↔ IValid.{_, 0} φ :=
  ⟨intuitionisticTableau_sound φ, intuitionisticTableau_complete φ⟩

/-! ## Decidable Instances (NEW to CSLib) -/

/-- `IValid.{_, 0} φ` is decidable via the intuitionistic tableau.

This is a NEW decidability result for CSLib: intuitionistic propositional validity
was not previously decidable by a constructive procedure in this library. -/
instance instDecidableIValid (φ : Proposition Atom) : Decidable (IValid.{_, 0} φ) :=
  match h : intuitionisticTableau φ with
  | .closed => isTrue (intuitionisticTableau_sound φ h)
  | .openBranch _ =>
    isFalse (fun hvalid =>
      have hclosed := intuitionisticTableau_complete φ hvalid
      by simp [hclosed] at h)

/-! ## Universe Invariance of `IValid`

`IValid.{u, v} φ` quantifies `World : Type v`, but `intuitionisticTableau_complete`'s countermodel
frame is built from `Nat : Type 0` — so applying it needs `IValid` pinned at universe `0`. The two
theorems below establish that this pin costs nothing: `IValid` is invariant under the choice of
`World`'s universe, in both directions. The forward direction (`Type 0 → Type v`) is free --
complete at `0`, then apply the universe-polymorphic `intuitionisticTableau_sound` at `v`. The
reverse direction (`Type v → Type 0`) needs an explicit transport: `ivalid_descend` lifts an
arbitrary `Type 0` model through `ULift` into a `Type v` model witnessing the same `IForces`
behaviour (by induction on `φ`, since `IForces` only ever inspects `val` pointwise -- `IValid`'s
`bot_forces` is fixed to `fun _ => False`, needing no transport of its own), then pulls the
`Type v`-validity witness back down along `ULift.down`. Mirrors
`Minimal/DecisionProcedure.lean`'s `mvalid_descend` / `mvalid_universe_invariant` for `MValid`,
simplified by `IValid` carrying no separate `bot_forces` argument to transport. -/

omit [DecidableEq Atom] [Hashable Atom] in
/-- Validity over `Type v` worlds descends to validity over `Type 0` worlds. Proved by lifting
an arbitrary `Type 0` model through `ULift` (`Preorder.lift ULift.down`) into a `Type v` model,
applying the `Type v` validity hypothesis there, and transporting the resulting forcing fact back
down along `ULift.down` by induction on `φ` (forcing only ever inspects `val` pointwise, so it
commutes with any bijection on worlds). -/
theorem ivalid_descend {φ : Proposition Atom} (h : IValid.{_, v} φ) : IValid.{_, 0} φ := by
  intro World _inst val vuc w
  letI : Preorder (ULift.{v, 0} World) := Preorder.lift ULift.down
  have key : ∀ (ψ : Proposition Atom) (x : ULift.{v, 0} World),
      IForces (fun (W : ULift.{v, 0} World) p => val W.down p)
        (fun (_ : ULift.{v, 0} World) => False) x ψ ↔
      IForces val (fun _ => False) x.down ψ := by
    intro ψ
    induction ψ with
    | atom p => intro x; exact Iff.rfl
    | bot => intro x; exact Iff.rfl
    | imp a b iha ihb =>
      intro x
      constructor
      · intro hf y hy hya
        exact (ihb ⟨y⟩).mp (hf ⟨y⟩ hy ((iha ⟨y⟩).mpr hya))
      · intro hf y hy hya
        exact (ihb y).mpr (hf y.down hy ((iha y).mp hya))
    | and a b iha ihb => intro x; exact and_congr (iha x) (ihb x)
    | or a b iha ihb => intro x; exact or_congr (iha x) (ihb x)
  exact (key φ ⟨w⟩).mp
    (h (ULift.{v, 0} World) (fun W p => val W.down p) (fun p hle hv => vuc p hle hv) ⟨w⟩)

/-- `IValid` is invariant under the universe at which `World` is quantified: validity over
`Type 0` worlds and validity over arbitrary `Type v` worlds coincide. The forward direction is
free (complete at `0`, then apply the universe-polymorphic `intuitionisticTableau_sound` at `v`);
the reverse direction is `ivalid_descend`'s `ULift` transport. This is what lets
`instDecidableDerivableIntPropAxiom` below keep its original, universe-unpinned public statement
even though `intuitionisticTableau_decides`/`instDecidableIValid` are now pinned to `Type 0`. -/
theorem ivalid_universe_invariant (φ : Proposition Atom) :
    IValid.{_, v} φ ↔ IValid.{_, 0} φ :=
  ⟨ivalid_descend, fun h => intuitionisticTableau_sound φ (intuitionisticTableau_complete φ h)⟩

/-- `Derivable IntPropAxiom φ` is decidable via the intuitionistic tableau and the completeness
theorem `int_soundness_completeness`. Routes through `ivalid_universe_invariant` so this
instance's public statement stays at `IValid`'s original, unpinned universe even though
`instDecidableIValid` above is now pinned to `Type 0`. -/
instance instDecidableDerivableIntPropAxiom (φ : Proposition Atom) :
    Decidable (Derivable IntPropAxiom φ) :=
  letI : Decidable (IValid φ) :=
    decidable_of_iff (IValid.{_, 0} φ) (ivalid_universe_invariant φ).symm
  decidable_of_iff (IValid φ) int_soundness_completeness

end Cslib.Logic.PL

end
