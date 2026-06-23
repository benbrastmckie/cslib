/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

import Cslib.Init

public import Cslib.Logics.Propositional.Semantics.Algebra.Completeness
public import Cslib.Logics.Propositional.Semantics.Algebra.Soundness
public import Cslib.Logics.Propositional.Semantics.Algebra.Bridge
public import Cslib.Logics.Propositional.NaturalDeduction.Equivalence
public import Cslib.Logics.Propositional.Metalogic.StrongCompleteness

/-! # Hilbert-Level Algebraic Completeness for Propositional Logic

This module composes two bridges to produce Hilbert-level algebraic completeness
for all three propositional logic tiers:

- **MPL** (Minimal Propositional Logic): `Derivable MinPropAxiom φ ↔ GHAValid φ`
- **IPL** (Intuitionistic Propositional Logic): `Derivable IntPropAxiom φ ↔ HAValid φ`
- **CPL** (Classical Propositional Logic): `Derivable PropositionalAxiom φ ↔ BAValid φ`

## Proof Strategy

Each direction uses a different route:

**Soundness (→)**: Algebraic soundness for `DerivationTree`, proved in
`Semantics.Algebra.Soundness`. The Hilbert system is sound w.r.t. the respective algebra class.

**Completeness (←)**:

For MPL: `GHAValid φ` → `DerivableIn (∅ : Theory Atom) φ` (by `MPL.alg_complete`) →
`DerivableIn (AxiomTheory MinPropAxiom) (∅ ⊢ φ)` (theory monotonicity, since
`∅ ⊆ AxiomTheory MinPropAxiom`) → `Derivable MinPropAxiom φ` (by `hilbert_iff_nd_min`).

For IPL: `HAValid φ` → `DerivableIn (IPL : Theory Atom) φ` (by `IPL.alg_complete`) →
`DerivableIn (AxiomTheory IntPropAxiom) (∅ ⊢ φ)` (theory monotonicity via EFQ membership) →
`Derivable IntPropAxiom φ` (by `hilbert_iff_nd_int`).

For CPL: `BAValid φ` → `Tautology φ` (via `Bool` as Boolean algebra and bridge lemmas) →
`Derivable PropositionalAxiom φ` (by `prop_completeness_iff_tautology`).

## References

* [A. Rasiowa, *An Algebraic Approach to Non-Classical Logics*][Rasiowa1974]
-/

@[expose] public section

namespace Cslib.Logic.PL

open Cslib.Logic
open InferenceSystem
open Theory

universe u

/-! ## Bridge Lemma: IPL ⊆ AxiomTheory IntPropAxiom -/

/-- Every formula in `IPL` (of the form `⊥ → A`) belongs to `AxiomTheory IntPropAxiom`,
since `IntPropAxiom (⊥ → A)` holds via the `efq` constructor.
This subset inclusion enables theory monotonicity in the IPL completeness argument. -/
lemma ipl_subset_axiomTheory_int {Atom : Type u} :
    (IPL : Theory Atom) ⊆ AxiomTheory (@IntPropAxiom Atom) := by
  intro φ hφ
  simp only [IPL, Set.mem_range] at hφ
  obtain ⟨A, rfl⟩ := hφ
  exact mem_axiomTheory.mpr (IntPropAxiom.efq A)

/-! ## MPL: Hilbert ↔ GHAValid -/

/-- **Hilbert-level algebraic completeness for MPL**.
A formula `φ` is derivable in the minimal Hilbert system (`Derivable MinPropAxiom φ`)
if and only if it is valid in every Generalized Heyting Algebra (`GHAValid φ`).

- **Soundness (→)**: `min_alg_soundness_derivable`
- **Completeness (←)**: routes through ND algebraic completeness (`MPL.alg_complete`)
  and the Hilbert–ND equivalence (`hilbert_iff_nd_min`). -/
set_option linter.unusedDecidableInType false in
theorem MPL.hilbert_alg_complete {Atom : Type u} [DecidableEq Atom] {φ : PL.Proposition Atom} :
    Derivable MinPropAxiom φ ↔ GHAValid φ := by
  constructor
  · exact min_alg_soundness_derivable
  · intro h
    -- Step 1: GHAValid → DerivableIn (∅) via MPL.alg_complete.
    -- Use `rw` to convert the goal, then apply GHAValid at the fixed universe u.
    have hND : DerivableIn (∅ : Theory Atom) φ := by
      rw [MPL.alg_complete]
      intro H _ v bot_val
      exact h (H := H) v bot_val
    -- Step 2: Convert bare-formula derivability to sequent form (definitional equality).
    have hNDseq : DerivableIn (∅ : Theory Atom) ((∅ : Ctx Atom) ⊢ φ) :=
      DerivableIn.iff_derivableIn_empty.mp hND
    -- Step 3: Theory monotonicity: ∅ ⊆ AxiomTheory MinPropAxiom.
    have hNDmin : DerivableIn (AxiomTheory (@MinPropAxiom Atom)) ((∅ : Ctx Atom) ⊢ φ) :=
      hNDseq.weakTheory (Set.empty_subset _)
    -- Step 4: Hilbert–ND equivalence.
    exact hilbert_iff_nd_min.mpr hNDmin

/-! ## IPL: Hilbert ↔ HAValid -/

/-- **Hilbert-level algebraic completeness for IPL**.
A formula `φ` is derivable in the intuitionistic Hilbert system (`Derivable IntPropAxiom φ`)
if and only if it is valid in every Heyting Algebra (`HAValid φ`).

- **Soundness (→)**: `int_alg_soundness_derivable`
- **Completeness (←)**: routes through `IPL.alg_complete` and `hilbert_iff_nd_int`. -/
set_option linter.unusedDecidableInType false in
theorem IPL.hilbert_alg_complete {Atom : Type u} [DecidableEq Atom] {φ : PL.Proposition Atom} :
    Derivable IntPropAxiom φ ↔ HAValid φ := by
  constructor
  · exact int_alg_soundness_derivable
  · intro h
    -- Step 1: HAValid → DerivableIn (IPL) via IPL.alg_complete.
    -- Use `rw` to convert the goal, then apply HAValid at the fixed universe u.
    have hND : DerivableIn (IPL : Theory Atom) φ := by
      rw [IPL.alg_complete]
      intro H _ v
      exact h (H := H) v
    -- Step 2: Convert bare-formula derivability to sequent form (definitional equality).
    have hNDseq : DerivableIn (IPL : Theory Atom) ((∅ : Ctx Atom) ⊢ φ) :=
      DerivableIn.iff_derivableIn_empty.mp hND
    -- Step 3: Theory monotonicity: IPL ⊆ AxiomTheory IntPropAxiom.
    have hNDint : DerivableIn (AxiomTheory (@IntPropAxiom Atom)) ((∅ : Ctx Atom) ⊢ φ) :=
      hNDseq.weakTheory ipl_subset_axiomTheory_int
    -- Step 4: Hilbert–ND equivalence.
    exact hilbert_iff_nd_int.mpr hNDint

/-! ## CPL: Hilbert ↔ BAValid -/

/-- `BAValid φ` implies `Tautology φ`.

Proof: instantiate `BAValid` at `Bool` (a BooleanAlgebra) using `Classical.propDecidable`
for decidability of the base valuation. The algebraic Bool evaluation is then converted
to `BoolEvaluate` and back to `Evaluate` via `boolEvaluateEq` and `Evaluate_eq_BoolEvaluate`. -/
lemma baValid_implies_tautology {Atom : Type u} {φ : PL.Proposition Atom}
    (h : BAValid φ) : Tautology φ := by
  intro v
  -- Use Classical decidability to treat v as a BoolValuation
  haveI : ∀ a : Atom, Decidable (v a) := fun _ => Classical.propDecidable _
  -- Convert goal to BoolEvaluate form, then apply BAValid at Bool.
  -- The `rw [boolEvaluateEq]` step rewires the goal to `AlgEvaluate ... false φ = true`,
  -- which provides the Bool type context needed for `h Bool ...` to unify at universe 0.
  rw [Evaluate_eq_BoolEvaluate]
  show BoolEvaluate (fun a => decide (v a)) φ = true
  rw [boolEvaluateEq]
  exact h Bool (fun a => decide (v a))

/-- **Hilbert-level algebraic completeness for CPL**.
A formula `φ` is derivable in the classical Hilbert system (`Derivable PropositionalAxiom φ`)
if and only if it is valid in every Boolean Algebra (`BAValid φ`).

- **Soundness (→)**: `prop_alg_soundness_derivable`
- **Completeness (←)**: converts `BAValid` to `Tautology` (via `Bool` as a Boolean algebra),
  then applies `prop_completeness_iff_tautology`. -/
set_option linter.unusedDecidableInType false in
theorem CPL.hilbert_alg_complete {Atom : Type u} [DecidableEq Atom] {φ : PL.Proposition Atom} :
    Derivable PropositionalAxiom φ ↔ BAValid φ := by
  constructor
  · exact prop_alg_soundness_derivable
  · intro h
    exact prop_completeness_iff_tautology.mp (baValid_implies_tautology h)

end Cslib.Logic.PL
