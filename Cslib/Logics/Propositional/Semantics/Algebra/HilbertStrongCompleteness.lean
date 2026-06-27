/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Propositional.Semantics.Algebra.HilbertLindenbaumRel
public import Cslib.Logics.Propositional.Semantics.Algebra.Soundness

/-! # Algebraic Strong Completeness for the Hilbert System

This module proves **strong (context/theory) algebraic completeness** for the Hilbert system:
a formula is set-derivable from a context `Γ` if and only if it is forced (evaluates to `⊤`)
in every Generalized Heyting Algebra that models the axiom theory and satisfies every formula
in `Γ`.

## Main Results

- `hilbert_alg_strong_complete_theory`: The pointwise-⊤ iff theorem:
  ```
  SetDerivable Axioms Γ φ ↔
    ∀ (H : Type u) [GeneralizedHeytingAlgebra H] (v : Atom → H) (bot_val : H),
      v ⊨[bot_val] AxiomTheory Axioms →
      SatisfiesTheory (AlgEvaluate v bot_val) Γ →
      AlgEvaluate v bot_val φ = ⊤
  ```

- `hilbert_alg_strong_complete_theory_empty`: Recovery lemma showing that the `Γ = ∅`
  case recovers `hilbert_alg_complete_theory` (regression guard).

## Proof Strategy

**Forward (soundness)**: Unfold `SetDerivable` to extract `L ⊆ Γ` and a `DerivationTree`
over `L`, then apply `alg_theory_soundness`. The `SatisfiesTheory` hypothesis over `Γ`
restricts to `L` via the subset.

**Backward (completeness)**: Instantiate the hypothesis at the `RelLindenbaumAlgebra Axioms Γ`
with the relativized canonical valuation `relCanonicalV Γ` and bottom value
`relCanonicalBotVal Γ`. The axiom-theory premise is discharged via `relCanonicalV_algTValid`,
and the `SatisfiesTheory Γ` premise via `relCanonicalV_satisfiesΓ` (the key property:
every `ψ ∈ Γ` evaluates to `⊤` in the relativized algebra). The truth lemma
`relCanonicalV_spec` converts the result to `relMk Γ φ = ⊤`, and `relMk_eq_top_iff`
yields `SetDerivable Axioms Γ φ`.

## Universe Note

`{Atom : Type u}` and algebras `(H : Type u)` are pinned to the same universe level `u`,
matching `HilbertLindenbaum.lean` and `RelLindenbaumAlgebra`. Using `Type _` causes
universe-metavariable mismatches with the quotient construction.

## References

* [A. Rasiowa, *An Algebraic Approach to Non-Classical Logics*][Rasiowa1974]
-/

@[expose] public section

namespace Cslib.Logic.PL

open Proposition

universe u

/-! ## Strong Completeness -/

/-- **Algebraic Strong (Context-Parametric) Completeness for the Hilbert System**.

A formula `φ` is set-derivable from context `Γ` using axioms `Axioms` if and only if,
in every Generalized Heyting Algebra `H` that models the axiom theory and whose evaluation
satisfies every formula in `Γ`, `φ` evaluates to `⊤`.

This is the **pointwise-⊤ biconditional** form of strong completeness.

**Universe note**: `H` and `Atom` range over the same universe `u` to match the
`RelLindenbaumAlgebra` and `HilbertLindenbaumAlgebra` quotient constructions.

**Proof**:
- Forward: unfold `SetDerivable`, apply `alg_theory_soundness` using `SatisfiesTheory` over
  the finite witness list.
- Backward: instantiate at `RelLindenbaumAlgebra Axioms Γ` with `relCanonicalV Γ` and
  `relCanonicalBotVal Γ`; discharge premises via `relCanonicalV_algTValid` and
  `relCanonicalV_satisfiesΓ`; conclude via `relCanonicalV_spec` and `relMk_eq_top_iff`. -/
theorem hilbert_alg_strong_complete_theory {Atom : Type u}
    (Axioms : PL.Proposition Atom → Prop) [MinimalAxioms Axioms]
    {Γ : Set (PL.Proposition Atom)} {φ : PL.Proposition Atom} :
    SetDerivable Axioms Γ φ ↔
    ∀ (H : Type u) [GeneralizedHeytingAlgebra H] (v : Atom → H) (bot_val : H),
      v ⊨[bot_val] AxiomTheory Axioms →
      SatisfiesTheory (AlgEvaluate v bot_val) Γ →
      AlgEvaluate v bot_val φ = ⊤ := by
  constructor
  · -- Forward: soundness direction
    -- Unfold SetDerivable to get a finite list witness L ⊆ Γ and a derivation tree over L.
    intro ⟨L, hL_sub, ⟨d⟩⟩ H _ v bot_val hT hΓ
    -- Apply alg_theory_soundness with the context function built from hΓ restricted to L.
    exact alg_theory_soundness d v bot_val hT (fun ψ hψ => hΓ ψ (hL_sub ψ hψ))
  · -- Backward: completeness direction via the relativized Lindenbaum algebra
    intro h
    -- Instantiate h at RelLindenbaumAlgebra Axioms Γ with the relativized canonical valuation.
    have hTop : AlgEvaluate
        (relCanonicalV Γ) (relCanonicalBotVal Γ (Axioms := Axioms)) φ = ⊤ :=
      h (RelLindenbaumAlgebra Axioms Γ) (relCanonicalV Γ) (relCanonicalBotVal Γ)
        (relCanonicalV_algTValid Γ) relCanonicalV_satisfiesΓ
    -- Apply the truth lemma: AlgEvaluate (relCanonicalV Γ) ... φ = relMk Γ φ
    rw [relCanonicalV_spec] at hTop
    -- relMk Γ φ = ⊤ ↔ SetDerivable Axioms Γ φ
    exact relMk_eq_top_iff.mp hTop

/-! ## Recovery of Weak Completeness -/

/-- **Recovery Lemma**: the `Γ = ∅` case of `hilbert_alg_strong_complete_theory`
recovers `hilbert_alg_complete_theory` (the weak/empty-context completeness theorem in
`HilbertCompleteness.lean`).

When `Γ = ∅`, the `SatisfiesTheory (AlgEvaluate v bot_val) ∅` premise is vacuously true,
and `SetDerivable Axioms ∅ φ` collapses to `Derivable Axioms φ` via `SetDerivable_empty_iff`.
This certifies that the strong completeness theorem is a genuine extension of the
weak-completeness result (regression guard). -/
lemma hilbert_alg_strong_complete_theory_empty {Atom : Type u}
    (Axioms : PL.Proposition Atom → Prop) [MinimalAxioms Axioms]
    {φ : PL.Proposition Atom} :
    Derivable Axioms φ ↔
    ∀ (H : Type u) [GeneralizedHeytingAlgebra H] (v : Atom → H) (bot_val : H),
      v ⊨[bot_val] AxiomTheory Axioms →
      AlgEvaluate v bot_val φ = ⊤ := by
  rw [← SetDerivable_empty_iff]
  rw [hilbert_alg_strong_complete_theory Axioms]
  constructor
  · -- Forward: the Γ = ∅ case, SatisfiesTheory _ ∅ is vacuous so we can drop it
    intro h H _ v bot_val hT
    exact h H v bot_val hT (fun _ hA => hA.elim)
  · -- Backward: add the vacuous SatisfiesTheory ∅ premise
    intro h H _ v bot_val hT _
    exact h H v bot_val hT

end Cslib.Logic.PL

end
