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

- `minimalTableau_sound`: Proved in `Minimal.Soundness`. If `minimalTableau φ = closed`,
  then `MValid φ`.
- `minimalTableau_complete`: Proved in `Minimal.Completeness`. If `MValid φ`,
  then `minimalTableau φ = closed`.
- `minimalTableau_decides`: Biconditional combining soundness and completeness.
- `instDecidableMValid`: A `Decidable (MValid φ)` instance via tableau (NEW to CSLib).
- `instDecidableDerivableMinPropAxiom`: `Decidable (Derivable MinPropAxiom φ)` via tableau.

## Design

The minimal tableau reuses the intuitionistic expansion (`intExpandBranches`) but
substitutes `isMinimallyClosed` (all complementary T(φ)/F(φ) pairs) instead of the
atom-only `MinimalClosure` instance. This ensures that branches with T(⊥)/F(⊥) also close.

The key difference between intuitionistic and minimal:
- **Intuitionistic**: `botForces = fun _ => False` (⊥ never holds).
- **Minimal**: `botForces w = T(⊥) is on b at world w` (⊥ can hold at some worlds).

Soundness and completeness proofs are in the dedicated `Soundness.lean` and
`Completeness.lean` modules respectively.

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
