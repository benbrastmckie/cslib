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
- `minimalTableau_complete`: In `Minimal.Completeness`; `MValid φ` implies
  `minimalTableau φ = closed`. Rests on the deferred completeness sorries (see "Notes on sorry"
  below).
- `minimalTableau_decides`: Biconditional combining soundness and completeness.
- `instDecidableMValid`: A `Decidable (MValid φ)` instance via tableau (NEW to CSLib).
- `instDecidableDerivableMinPropAxiom`: `Decidable (Derivable MinPropAxiom φ)` via tableau.

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
(`minimalTableau_complete` in `Minimal/Completeness.lean`) rests on the deferred completeness
sorries. The parametric `truthLemma` in `Intuitionistic/Scheme.lean` (which the minimal tableau
reuses as `truthLemma minScheme`) is now sorry-free — it gained an explicit `hpers`
(positive-persistence) hypothesis and is unconditionally true over any frame carrying it. The
remaining sorries are:
- the open-branch countermodel structural property in `Intuitionistic/Scheme.lean`
- the `MValid → forcing` bridge in `Minimal/Completeness.lean` (uses `truthLemma minScheme`)

The `Decidable` instance (`instDecidableDerivableMinPropAxiom`) carries the soundness branch
clean and the countermodel branch with the deferred completeness `sorryAx`. This sorry-taint is
pre-existing and will be resolved once the deferred completeness sorries are filled.

## Two Decision Routes — Distinct Roles

CSLib contains **two independent decision procedures** for `Derivable MinPropAxiom φ`:

### Route 1 (Tableau — this module, canonical registered instance)
- **Module**: `Tableau/Minimal/DecisionProcedure.lean`
- **Mechanism**: Constructive signed-tableau proof-search/countermodel. Reuses the
  intuitionistic expansion (`intExpandBranches`) with `isMinimallyClosed` closure predicate.
  Decides via `instDecidableMValid` composed with `min_soundness_completeness`.
- **Axiom profile**: Carries the deferred completeness `sorryAx` (see above). Will become
  sorry-free once the deferred completeness sorries are filled.
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
    minimalTableau φ = .closed ↔ MValid φ :=
  ⟨minimalTableau_sound φ, minimalTableau_complete φ⟩

/-! ## Decidable Instances (NEW to CSLib) -/

/-- `MValid φ` is decidable via the minimal tableau.

This is a NEW decidability result for CSLib: minimal propositional validity was not
previously decidable by a constructive procedure in this library. -/
instance instDecidableMValid (φ : Proposition Atom) : Decidable (MValid φ) :=
  match h : minimalTableau φ with
  | .closed => isTrue (minimalTableau_sound φ h)
  | .openBranch _ =>
    isFalse (fun hvalid =>
      have hclosed := minimalTableau_complete φ hvalid
      by simp [hclosed] at h)

/-- `Derivable MinPropAxiom φ` is decidable via the minimal tableau and the completeness
theorem `min_soundness_completeness`. -/
instance instDecidableDerivableMinPropAxiom (φ : Proposition Atom) :
    Decidable (Derivable MinPropAxiom φ) :=
  decidable_of_iff (MValid φ) min_soundness_completeness

end Cslib.Logic.PL

end
