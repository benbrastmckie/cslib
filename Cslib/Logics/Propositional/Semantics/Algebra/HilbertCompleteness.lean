/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Propositional.Semantics.Algebra.HilbertLindenbaum
public import Cslib.Logics.Propositional.Semantics.Algebra.Soundness

/-! # Hilbert-Level Algebraic Completeness for Propositional Logic

This module proves Hilbert-level algebraic completeness for all three propositional
logic tiers using the **Hilbert Lindenbaum algebra** directly:

- **MPL** (Minimal Propositional Logic): `Derivable MinPropAxiom φ ↔ GHAValid φ`
- **IPL** (Intuitionistic Propositional Logic): `Derivable IntPropAxiom φ ↔ HAValid φ`
- **CPL** (Classical Propositional Logic): `Derivable PropositionalAxiom φ ↔ BAValid φ`

## Proof Strategy

Each direction uses a different route:

**Soundness (→)**: Algebraic soundness for `DerivationTree`, proved in
`Semantics.Algebra.Soundness`. The Hilbert system is sound w.r.t. the respective algebra class.

**Completeness (←)**: Uses the Hilbert Lindenbaum algebra directly.
Given validity in every algebra of the appropriate class, instantiate at the
`HilbertLindenbaumAlgebra Axioms` with the canonical valuation `canonicalV Axioms` and
the canonical bottom `canonicalBotVal Axioms`. The truth lemma `canonicalV_spec` then
identifies the algebraic value with the equivalence class, and `hilbertLindenbaumMk_eq_top_iff`
extracts `Derivable Axioms φ`.

## References

* [A. Rasiowa, *An Algebraic Approach to Non-Classical Logics*][Rasiowa1974]
-/

@[expose] public section

namespace Cslib.Logic.PL

open Proposition

universe u

/-! ## MPL: Hilbert ↔ GHAValid -/

/-- **Hilbert-level algebraic completeness for MPL**.
A formula `φ` is derivable in the minimal Hilbert system (`Derivable MinPropAxiom φ`)
if and only if it is valid in every Generalized Heyting Algebra (`GHAValid φ`).

Soundness uses `min_alg_soundness_derivable`. Completeness instantiates `GHAValid` at the
Hilbert Lindenbaum algebra for `MinPropAxiom`, applies the truth lemma `canonicalV_spec`,
and extracts derivability via `hilbertLindenbaumMk_eq_top_iff`. -/
theorem MPL.hilbert_alg_complete {Atom : Type u} {φ : PL.Proposition Atom} :
    Derivable (@MinPropAxiom Atom) φ ↔ GHAValid.{u, u} φ := by
  constructor
  · exact min_alg_soundness_derivable
  · intro h
    -- Instantiate GHAValid at the Hilbert Lindenbaum algebra for MinPropAxiom.
    -- Both universe levels are u (atom universe), matching HilbertLindenbaumAlgebra.
    have hLind : AlgEvaluate (canonicalV (@MinPropAxiom Atom))
        (canonicalBotVal (@MinPropAxiom Atom)) φ = ⊤ :=
      h (HilbertLindenbaumAlgebra (@MinPropAxiom Atom))
        (canonicalV (@MinPropAxiom Atom)) (canonicalBotVal (@MinPropAxiom Atom))
    rw [canonicalV_spec] at hLind
    exact hilbertLindenbaumMk_eq_top_iff.mp hLind

/-! ## IPL: Hilbert ↔ HAValid -/

/-- **Hilbert-level algebraic completeness for IPL**.
A formula `φ` is derivable in the intuitionistic Hilbert system (`Derivable IntPropAxiom φ`)
if and only if it is valid in every Heyting Algebra (`HAValid φ`).

Soundness uses `int_alg_soundness_derivable`. Completeness instantiates `HAValid` at the
Hilbert Lindenbaum algebra for `IntPropAxiom` (carrying `hilbertLindenbaumIntHA`), applies
the truth lemma, and extracts derivability via `hilbertLindenbaumMk_eq_top_iff`. -/
theorem IPL.hilbert_alg_complete {Atom : Type u} {φ : PL.Proposition Atom} :
    Derivable (@IntPropAxiom Atom) φ ↔ HAValid.{u, u} φ := by
  constructor
  · exact int_alg_soundness_derivable
  · intro h
    -- Instantiate HAValid at the Hilbert Lindenbaum algebra for IntPropAxiom.
    -- In hilbertLindenbaumIntHA, ⊥ = [⊥] = canonicalBotVal (definitional equality).
    have hLind : AlgEvaluate (canonicalV (@IntPropAxiom Atom))
        (canonicalBotVal (@IntPropAxiom Atom)) φ = ⊤ := by
      have hLind' := h (HilbertLindenbaumAlgebra (@IntPropAxiom Atom))
        (canonicalV (@IntPropAxiom Atom))
      rwa [show (⊥ : HilbertLindenbaumAlgebra (@IntPropAxiom Atom)) =
        canonicalBotVal (@IntPropAxiom Atom) from rfl] at hLind'
    rw [canonicalV_spec] at hLind
    exact hilbertLindenbaumMk_eq_top_iff.mp hLind

/-! ## CPL: Hilbert ↔ BAValid -/

/-- **Hilbert-level algebraic completeness for CPL**.
A formula `φ` is derivable in the classical Hilbert system (`Derivable PropositionalAxiom φ`)
if and only if it is valid in every Boolean Algebra (`BAValid φ`).

Soundness uses `prop_alg_soundness_derivable`. Completeness instantiates `BAValid` at the
Hilbert Lindenbaum algebra for `PropositionalAxiom` (carrying `hilbertLindenbaumClBA`), applies
the truth lemma, and extracts derivability via `hilbertLindenbaumMk_eq_top_iff`. -/
theorem CPL.hilbert_alg_complete {Atom : Type u} {φ : PL.Proposition Atom} :
    Derivable (@PropositionalAxiom Atom) φ ↔ BAValid.{u, u} φ := by
  constructor
  · exact prop_alg_soundness_derivable
  · intro h
    -- Instantiate BAValid at the Hilbert Lindenbaum algebra for PropositionalAxiom.
    -- In hilbertLindenbaumClBA, ⊥ = [⊥] = canonicalBotVal (definitional equality).
    have hLind : AlgEvaluate (canonicalV (@PropositionalAxiom Atom))
        (canonicalBotVal (@PropositionalAxiom Atom)) φ = ⊤ := by
      have hLind' := h (HilbertLindenbaumAlgebra (@PropositionalAxiom Atom))
        (canonicalV (@PropositionalAxiom Atom))
      rwa [show (⊥ : HilbertLindenbaumAlgebra (@PropositionalAxiom Atom)) =
        canonicalBotVal (@PropositionalAxiom Atom) from rfl] at hLind'
    rw [canonicalV_spec] at hLind
    exact hilbertLindenbaumMk_eq_top_iff.mp hLind

end Cslib.Logic.PL
