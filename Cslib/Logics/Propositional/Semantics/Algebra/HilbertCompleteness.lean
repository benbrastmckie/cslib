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

/-! ## Theory-Parametric Completeness -/

/-- **Theory-Parametric Hilbert-Level Algebraic Completeness**.
A formula `φ` is derivable from axioms `Axioms` if and only if every GHA valuation that
models the axiom theory (`v ⊨[bot_val] AxiomTheory Axioms`) satisfies `φ`.

**Forward (soundness)**: Apply `alg_theory_soundness` with empty context and the supplied
`AlgTValid` hypothesis.

**Backward (completeness)**: Instantiate at the Hilbert Lindenbaum algebra, using
`canonicalV_algTValid` to discharge the `AlgTValid` premise, then extract derivability via
`canonicalV_spec` and `hilbertLindenbaumMk_eq_top_iff`.

Universe note: `{Atom : Type u}` and `(H : Type u)` are pinned to the same universe level
`u` to match the `HilbertLindenbaumAlgebra` construction; using `Type _` causes
universe-metavariable mismatches. -/
theorem hilbert_alg_complete_theory {Atom : Type u}
    (Axioms : PL.Proposition Atom → Prop) [MinimalAxioms Axioms]
    {φ : PL.Proposition Atom} :
    Derivable Axioms φ ↔
    ∀ (H : Type u) [GeneralizedHeytingAlgebra H] (v : Atom → H) (bot_val : H),
      v ⊨[bot_val] AxiomTheory Axioms → AlgEvaluate v bot_val φ = ⊤ := by
  constructor
  · intro ⟨d⟩ H _ v bot_val hT
    exact alg_theory_soundness d v bot_val hT (fun _ h => nomatch h)
  · intro h
    -- Instantiate at the Hilbert Lindenbaum algebra with the canonical valuation.
    have hLind : AlgEvaluate (canonicalV Axioms) (canonicalBotVal Axioms) φ = ⊤ :=
      h (HilbertLindenbaumAlgebra Axioms) (canonicalV Axioms) (canonicalBotVal Axioms)
        (canonicalV_algTValid Axioms)
    rw [canonicalV_spec] at hLind
    exact hilbertLindenbaumMk_eq_top_iff.mp hLind

/-! ## MPL: Hilbert ↔ GHAValid -/

/-- **Hilbert-level algebraic completeness for MPL**.
A formula `φ` is derivable in the minimal Hilbert system (`Derivable MinPropAxiom φ`)
if and only if it is valid in every Generalized Heyting Algebra (`GHAValid φ`).

Recovered as a corollary of `hilbert_alg_complete_theory`.

- **Forward**: Apply `hilbert_alg_complete_theory.mp` at `bot_val = ⊥`, discharging
  `AlgTValid` via `min_alg_axiom_sound` (which proves each axiom evaluates to `⊤`).
- **Backward**: Instantiate `GHAValid` at the Hilbert Lindenbaum algebra for `MinPropAxiom`,
  apply `canonicalV_spec`, and extract derivability via `hilbertLindenbaumMk_eq_top_iff`.

**Terminal-interface note**: this theorem is a load-bearing *internal input* to
`CanAlgComplete` (`CanAlgComplete.lean`), which is the single documented terminal interface
for fragment algebraic completeness — see `canAlgCompleteIsBotFree`. It stays public (20+
use-sites, including `Foundations/Logic/ProofSystem.lean`); only its role in the completeness
stack is being reclassified here, not its visibility, name, or signature. -/
theorem MPL.hilbert_alg_completeness {Atom : Type u} {φ : PL.Proposition Atom} :
    Derivable (@MinPropAxiom Atom) φ ↔ GHAValid.{u, u} φ := by
  constructor
  · intro hd H _ v bot_val
    exact (hilbert_alg_complete_theory (@MinPropAxiom Atom)).mp hd H v bot_val
      (fun ψ hψ => by
        simp only [AxiomTheory, Set.mem_setOf_eq] at hψ
        exact min_alg_axiom_sound hψ H v bot_val)
  · intro h
    -- Instantiate GHAValid at the Hilbert Lindenbaum algebra for MinPropAxiom.
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

Recovered as a corollary of `hilbert_alg_complete_theory`.

- **Forward**: Apply `hilbert_alg_complete_theory.mp` at `bot_val = ⊥`, discharging
  `AlgTValid` via `int_alg_axiom_sound`.
- **Backward**: Instantiate `HAValid` at the Hilbert Lindenbaum algebra for `IntPropAxiom`
  (carrying `hilbertLindenbaumIntHA`); use the `rfl` bridge `⊥ = canonicalBotVal _`. -/
theorem IPL.hilbert_alg_completeness {Atom : Type u} {φ : PL.Proposition Atom} :
    Derivable (@IntPropAxiom Atom) φ ↔ HAValid.{u, u} φ := by
  constructor
  · intro hd H _ v
    exact (hilbert_alg_complete_theory (@IntPropAxiom Atom)).mp hd H v ⊥
      (fun ψ hψ => by
        simp only [AxiomTheory, Set.mem_setOf_eq] at hψ
        exact int_alg_axiom_sound hψ H v)
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

Recovered as a corollary of `hilbert_alg_complete_theory`.

- **Forward**: Apply `hilbert_alg_complete_theory.mp` at `bot_val = ⊥`, discharging
  `AlgTValid` via `prop_alg_axiom_sound`.
- **Backward**: Instantiate `BAValid` at the Hilbert Lindenbaum algebra for
  `PropositionalAxiom` (carrying `hilbertLindenbaumClBA`); use the `rfl` bridge
  `⊥ = canonicalBotVal _`. -/
theorem CPL.hilbert_alg_completeness {Atom : Type u} {φ : PL.Proposition Atom} :
    Derivable (@PropositionalAxiom Atom) φ ↔ BAValid.{u, u} φ := by
  constructor
  · intro hd H _ v
    exact (hilbert_alg_complete_theory (@PropositionalAxiom Atom)).mp hd H v ⊥
      (fun ψ hψ => by
        simp only [AxiomTheory, Set.mem_setOf_eq] at hψ
        exact prop_alg_axiom_sound hψ H v)
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
