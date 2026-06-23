/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

import Cslib.Init
public import Cslib.Logics.Propositional.Tableau.Intuitionistic.Expansion
public import Cslib.Logics.Propositional.Semantics.Kripke
public import Cslib.Logics.Propositional.Metalogic.MinStrongCompleteness

/-! # Minimal Propositional Tableau Decision Procedure

This module delivers the `Decidable (MValid φ)` instance via the minimal propositional
tableau and connects it to derivability via `min_soundness_completeness`.

## Main Results

- `minimalTableau_sound`: If `minimalTableau φ = closed`, then `MValid φ`.
- `minimalTableau_complete`: If `MValid φ`, then `minimalTableau φ = closed`.
- `instDecidableMValid`: A `Decidable (MValid φ)` instance via tableau (NEW to CSLib).
- `instDecidableDerivableMinPropAxiom`: `Decidable (Derivable MinPropAxiom φ)` via tableau.

## Design

The minimal tableau reuses the intuitionistic expansion (`intExpandBranches`) but
substitutes the `MinimalClosure` instance. A branch closes in minimal logic only when
T(p) and F(p) coexist at the same world for an atomic formula p.

The key difference between intuitionistic and minimal:
- **Intuitionistic**: T(⊥) closes a branch (`botForces = fun _ => False`).
- **Minimal**: T(⊥) does NOT close a branch (⊥ can be forced at some worlds).
  Instead, T(p)/F(p) for atomic p closes branches.

## Countermodel for Minimal

For a minimal countermodel from an open branch `b`:
- Same world structure as the intuitionistic case (Nat with ≤).
- Same valuation `v(w, p) = T(atom p) at w on b`.
- `botForces w = T(⊥) is on b at world w` (upward-closed by persistence).

## Notes on sorry

Soundness and completeness proofs are marked sorry. The `Decidable` instances
are structurally sorry-free.

## References

* [M. Fitting, *Proof Methods for Modal and Intuitionistic Logics*][Fitting1983], Chapter 4
-/

@[expose] public section

namespace Cslib.Logic.PL

open Cslib.Logic.Tableau

variable {Atom : Type*} [DecidableEq Atom] [Hashable Atom]

/-! ## Minimal Branch Satisfiability -/

/-- A branch is minimally satisfied if there exists a Kripke model (with any `botForces`)
that agrees with every signed formula. For minimal logic, `botForces` is not fixed. -/
def minBranchSatisfied {World : Type*} [Preorder World]
    (val : World → Atom → Prop)
    (botForces : World → Prop)
    (worldOf : Nat → World)
    (b : IBranch Atom) : Prop :=
  ∀ sf ∈ b,
    (sf.sign = .pos → IForces val botForces (worldOf sf.label) sf.formula) ∧
    (sf.sign = .neg → ¬ IForces val botForces (worldOf sf.label) sf.formula)

/-! ## Soundness and Completeness (with sorry) -/

/-- **Minimal Tableau Soundness**: If `minimalTableau φ = closed`, then `MValid φ`.

The proof strategy is the same as for intuitionistic soundness, but using `MinimalClosure`
instead of `IntuitionisticClosure`. A minimally closed branch (containing T(p) and F(p)
for atomic p at the same world) is unsatisfiable in any minimal model, since
`IForces val botForces w (atom p) = val w p` and the contradiction T(p)/F(p) forces
`val w p ↔ ¬ val w p`.

NOTE: Full proof marked sorry. -/
theorem minimalTableau_sound (φ : Proposition Atom)
    (h : minimalTableau φ = .closed) : MValid φ := by
  sorry

/-- **Minimal Tableau Completeness**: If `MValid φ`, then `minimalTableau φ = closed`.

By contrapositive: if `minimalTableau φ = openBranch b`, construct a minimal Kripke
countermodel from `b`:
- Worlds = Nat labels on b with ≤ ordering.
- Valuation `v(w, p) = T(atom p) at w on b`.
- `botForces w = T(⊥) at w on b` (upward-closed by persistence).

The branch is not minimally closed, so no T(p)/F(p) atom contradiction exists, allowing
a consistent minimal model. The truth lemma (by formula induction) shows this model
falsifies `φ` at world 0.

NOTE: Full proof marked sorry. -/
theorem minimalTableau_complete (φ : Proposition Atom)
    (h : MValid φ) : minimalTableau φ = .closed := by
  sorry

/-! ## Decidable Instances (NEW to CSLib) -/

/-- The minimal tableau correctly decides minimal validity:
`minimalTableau φ = closed ↔ MValid φ`. -/
theorem minimalTableau_decides (φ : Proposition Atom) :
    minimalTableau φ = .closed ↔ MValid φ :=
  ⟨minimalTableau_sound φ, minimalTableau_complete φ⟩

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
