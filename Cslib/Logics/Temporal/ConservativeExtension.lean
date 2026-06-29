/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Foundations.Logic.Metalogic.ConservativityLift
public import Cslib.Logics.Temporal.FromPropositional
public import Cslib.Logics.Temporal.Semantics.Satisfies
public import Cslib.Logics.Temporal.Metalogic.Soundness
public import Cslib.Logics.Propositional.Metalogic.StrongCompleteness
public import Cslib.Logics.Propositional.Semantics.Bool
public import Mathlib.Algebra.Order.Ring.Int

/-! # Temporal BX as a Conservative Extension of Classical Propositional Logic

This module proves that Temporal BX is a conservative extension of CPL: any propositional
formula `φ` that is derivable in BX (as `φ.toTemporal`) is already derivable in CPL.

## Main Theorems

- `temporal_satisfies_toTemporal_iff_evaluate`: Semantic bridge between Temporal satisfaction
  of propositional translations and PL evaluation.
- `temporal_conservative_extension`: BX is a conservative extension of CPL.

## References

* Standard conservativity result for temporal logics over their propositional fragment.
-/

@[expose] public section

namespace Cslib.Logic

open Temporal Cslib.Logic.Temporal PL

/-- **Semantic Bridge Lemma**: Temporal satisfaction of `φ.toTemporal` at any point `t` in
any temporal model `M` is equivalent to propositional evaluation of `φ` under the valuation
`M.valuation t`.

Proof: Structural induction on `φ`. The `and`/`or` cases follow by classical logic since
`toTemporal` encodes these using the Lukasiewicz convention (`Temporal.Formula` has no native
`and`/`or` constructors; the encoding is classically sound though not intuitionistically). -/
theorem temporal_satisfies_toTemporal_iff_evaluate
    {D : Type*} [LinearOrder D] {Atom : Type*}
    (M : TemporalModel D Atom) (t : D)
    (φ : PL.Proposition Atom) :
    Satisfies M t φ.toTemporal ↔ PL.Evaluate (M.valuation t) φ :=
  evaluate_iff_of_classicalBridge PL.Proposition.toTemporal (Satisfies M t) (M.valuation t)
    (fun _ => Iff.rfl) id (fun _ _ => Iff.rfl) (fun _ _ => Iff.rfl) (fun _ _ => Iff.rfl) φ

/-- **Temporal BX Conservative Extension over CPL**:

If the temporal translation `φ.toTemporal` is BX-derivable, then `φ` is CPL-derivable.

Proof: BX soundness (on `ℤ` as a linear order with no max/min) gives temporal satisfaction
of `φ.toTemporal`; the semantic bridge gives tautologyhood of `φ`; CPL completeness gives
derivability. -/
theorem temporal_conservative_extension {Atom : Type*} {φ : PL.Proposition Atom}
    (h : Temporal.ThDerivable φ.toTemporal) :
    Derivable PropositionalAxiom φ :=
  conservative_over_cpl
    (Tgt := Temporal.Formula Atom)
    (emb := PL.Proposition.toTemporal)
    (sat := fun v ψ => Satisfies (TemporalModel.constant v) (0 : ℤ) ψ)
    (bridge := fun v =>
      temporal_satisfies_toTemporal_iff_evaluate (TemporalModel.constant v) 0 φ)
    (h_sat := fun v => soundness_thderivable h (TemporalModel.constant v) 0)

end Cslib.Logic

end
