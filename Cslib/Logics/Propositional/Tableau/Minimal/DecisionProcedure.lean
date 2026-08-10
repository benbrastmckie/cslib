/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

import Cslib.Init
public import Cslib.Logics.Propositional.Tableau.Minimal.Completeness
public import Cslib.Logics.Propositional.Metalogic.MinStrongCompleteness

/-! # Minimal Propositional Tableau Decision Procedure

This module delivers the `Decidable (MValid φ)` instance via the minimal propositional
tableau and connects it to derivability via `min_soundness_completeness`.

## Main Results

- `minimalTableau_sound`: Proved (sorry-free) in `Minimal.Soundness`. If
  `minimalTableau φ = closed`, then `MValid φ`.
- `minimalTableau_complete`: In `Minimal.Completeness`; `MValid.{_, 0} φ` implies
  `minimalTableau φ = closed`. Sorry-free (see "Notes on sorry" below for what still carries
  `sorryAx` one level down).
- `minimalTableau_decides`: Biconditional combining soundness and completeness, at `MValid.{_,0}`.
- `instDecidableMValid`: A `Decidable (MValid.{_, 0} φ)` instance via tableau (NEW to CSLib).
- `instDecidableDerivableMinPropAxiom`: `Decidable (Derivable MinPropAxiom φ)` via tableau, at
  `MValid`'s original, unpinned universe (routed through `mvalid_universe_invariant`).
- `mvalid_descend` / `mvalid_universe_invariant`: `MValid` is invariant under the universe
  `World` is quantified over -- the bridge that lets the `Type 0` pin above cost nothing.

## Design

The minimal tableau reuses the intuitionistic expansion (`intExpandBranches`) but
substitutes `isMinimallyClosed` (all complementary T(φ)/F(φ) pairs) instead of the
intuitionistic T(⊥)-only closure. This ensures that branches with T(⊥)/F(⊥) also close.

The key difference between intuitionistic and minimal:
- **Intuitionistic**: `botForces = fun _ => False` (⊥ never holds).
- **Minimal**: `botForces w = T(⊥) is on b at world w` (⊥ can hold at some worlds).

Soundness and completeness proofs are in the dedicated `Soundness.lean` and
`Completeness.lean` modules respectively.

## Notes on sorry

`minimalTableau_sound` is sorry-free. The completeness direction
(`minimalTableau_complete` in `Minimal/Completeness.lean`) is now ALSO sorry-free: the old
`MValid → forcing` bridge sorry is discharged, since `minOpenBranch_countermodel` now supplies
both of `MValid`'s upward-closure conjuncts together (see `Minimal/Completeness.lean`'s "Notes
on sorry" for the full disposition and the statement-shape defect this closure depended on
fixing). The parametric `truthLemma` in `Intuitionistic/Scheme.lean` (which the minimal tableau
reuses as `truthLemma minScheme`) is likewise sorry-free — it gained an explicit `hpers`
(positive-persistence) hypothesis and is unconditionally true over any frame carrying it. The
one remaining sorry in this dependency chain is:
- the open-branch countermodel structural property in `Intuitionistic/Scheme.lean`
  (`openBranch_countermodel`'s existential itself — genuinely open, not refuted)

The `Decidable` instance (`instDecidableDerivableMinPropAxiom`) carries the soundness branch
clean and the countermodel branch with `openBranch_countermodel`'s deferred `sorryAx`. This
sorry-taint is pre-existing and will be resolved once that one remaining sorry is filled.

## Two Decision Routes — Distinct Roles

CSLib contains **two independent decision procedures** for `Derivable MinPropAxiom φ`:

### Route 1 (Tableau — this module, canonical registered instance)
- **Module**: `Tableau/Minimal/DecisionProcedure.lean`
- **Mechanism**: Constructive signed-tableau proof-search/countermodel. Reuses the
  intuitionistic expansion (`intExpandBranches`) with `isMinimallyClosed` closure predicate.
  Decides via `instDecidableMValid` composed with `min_soundness_completeness`.
- **Axiom profile**: Carries the deferred completeness `sorryAx` (see above). Will become
  sorry-free once the one remaining completeness sorry (`openBranch_countermodel`'s existential
  in `Intuitionistic/Scheme.lean`) is filled.
- **Exposed as**: `instDecidableDerivableMinPropAxiom` — the **sole registered `Decidable`
  instance** for `Derivable MinPropAxiom φ`.
- **Role**: Canonical extension-facing instance for minimal propositional logic.

### Route 2 (FMP — sorry-free, named def, not a registered instance)
- **Module**: `Metalogic/MinDecidability.lean`
- **Mechanism**: Finite model property via `Σ`-bounded finite canonical Kripke model
  (`MinFinWorld φ`). Unlike the intuitionistic FMP, minimal worlds may contain `⊥`.
- **Axiom profile**: `{propext, Classical.choice, Quot.sound}` — **sorry-free**.
- **Exposed as**: `decidableDerivableMinPropAxiomFMP` (`noncomputable def`). Also see
  `min_fmp` (FMP biconditional) and `min_fin_truth_lemma`.
- **Role**: Independent theoretical result, useful as a correctness witness. Not a registered
  instance; does not compete with `instDecidableDerivableMinPropAxiom` for resolution.

The two routes have disjoint carrier types (signed-branch worlds vs `MinFinWorld`) and
independent proof lineages. Factoring a common truth-lemma abstraction is explicitly deferred.
See also `instDecidableDerivableIntPropAxiom` / `decidableDerivableIntPropAxiomFMP` for the
analogous Intuitionistic propositional decidability pair.

## References

* [M. Fitting, *Proof Methods for Modal and Intuitionistic Logics*][Fitting1983], Chapter 4
-/

@[expose] public section

namespace Cslib.Logic.PL

open Cslib.Logic.Tableau

variable {Atom : Type*} [DecidableEq Atom] [Hashable Atom]

/-! ## Decision Theorem -/

/-- The minimal tableau correctly decides minimal validity:
`minimalTableau φ = closed ↔ MValid φ`.

Combines `minimalTableau_sound` (from `Minimal.Soundness`) and `minimalTableau_complete`
(from `Minimal.Completeness`) into a single biconditional. -/
theorem minimalTableau_decides (φ : Proposition Atom) :
    minimalTableau φ = .closed ↔ MValid.{_, 0} φ :=
  ⟨minimalTableau_sound φ, minimalTableau_complete φ⟩

/-! ## Decidable Instances (NEW to CSLib) -/

/-- `MValid φ` is decidable via the minimal tableau.

This is a NEW decidability result for CSLib: minimal propositional validity was not
previously decidable by a constructive procedure in this library. -/
instance instDecidableMValid (φ : Proposition Atom) : Decidable (MValid.{_, 0} φ) :=
  match h : minimalTableau φ with
  | .closed => isTrue (minimalTableau_sound φ h)
  | .openBranch _ =>
    isFalse (fun hvalid =>
      have hclosed := minimalTableau_complete φ hvalid
      by simp [hclosed] at h)

/-! ## Universe Invariance of `MValid`

`MValid.{u, v} φ` quantifies `World : Type v`, but `minimalTableau_complete`'s countermodel
frame is built from `Nat : Type 0` — so applying it needs `MValid` pinned at universe `0`. The
two theorems below establish that this pin costs nothing: `MValid` is invariant under the choice
of `World`'s universe, in both directions. The forward direction (`Type 0 → Type v`) is free —
complete at `0`, then apply the universe-polymorphic `minimalTableau_sound` at `v`. The reverse
direction (`Type v → Type 0`) needs an explicit transport: `mvalid_descend` lifts an arbitrary
`Type 0` model through `ULift` into a `Type v` model witnessing the same `IForces` behaviour (by
induction on `φ`, since `IForces` only ever inspects `val`/`bot_forces` pointwise), then pulls
the `Type v`-validity witness back down along `ULift.down`. -/

omit [DecidableEq Atom] [Hashable Atom] in
/-- Validity over `Type v` worlds descends to validity over `Type 0` worlds. Proved by lifting
an arbitrary `Type 0` model through `ULift` (`Preorder.lift ULift.down`) into a `Type v` model,
applying the `Type v` validity hypothesis there, and transporting the resulting forcing fact back
down along `ULift.down` by induction on `φ` (forcing only ever inspects `val`/`bot_forces`
pointwise, so it commutes with any bijection on worlds). -/
theorem mvalid_descend {φ : Proposition Atom} (h : MValid.{_, v} φ) : MValid.{_, 0} φ := by
  intro World _inst val bot_forces vuc buc w
  letI : Preorder (ULift.{v, 0} World) := Preorder.lift ULift.down
  have key : ∀ (ψ : Proposition Atom) (x : ULift.{v, 0} World),
      IForces (fun (W : ULift.{v, 0} World) p => val W.down p)
        (fun (W : ULift.{v, 0} World) => bot_forces W.down) x ψ ↔
      IForces val bot_forces x.down ψ := by
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
    (h (ULift.{v, 0} World) (fun W p => val W.down p) (fun W => bot_forces W.down)
      (fun p hle hv => vuc p hle hv) (fun hle hb => buc hle hb) ⟨w⟩)

/-- `MValid` is invariant under the universe at which `World` is quantified: validity over
`Type 0` worlds and validity over arbitrary `Type v` worlds coincide. The forward direction is
free (complete at `0`, then apply the universe-polymorphic `minimalTableau_sound` at `v`); the
reverse direction is `mvalid_descend`'s `ULift` transport. This is what lets
`instDecidableDerivableMinPropAxiom` below keep its original, universe-unpinned public statement
even though `minimalTableau_decides`/`instDecidableMValid` are now pinned to `Type 0`. -/
theorem mvalid_universe_invariant (φ : Proposition Atom) :
    MValid.{_, v} φ ↔ MValid.{_, 0} φ :=
  ⟨mvalid_descend, fun h => minimalTableau_sound φ (minimalTableau_complete φ h)⟩

/-- `Derivable MinPropAxiom φ` is decidable via the minimal tableau and the completeness
theorem `min_soundness_completeness`. Routes through `mvalid_universe_invariant` so this
instance's public statement stays at `MValid`'s original, unpinned universe even though
`instDecidableMValid` above is now pinned to `Type 0`. -/
instance instDecidableDerivableMinPropAxiom (φ : Proposition Atom) :
    Decidable (Derivable MinPropAxiom φ) :=
  letI : Decidable (MValid φ) :=
    decidable_of_iff (MValid.{_, 0} φ) (mvalid_universe_invariant φ).symm
  decidable_of_iff (MValid φ) min_soundness_completeness

end Cslib.Logic.PL

end
