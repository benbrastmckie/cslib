/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Modal.FromPropositional
public import Cslib.Logics.Modal.Metalogic.Systems.B.Soundness
public import Cslib.Logics.Propositional.Metalogic.StrongCompleteness

/-! # Modal B as a Conservative Extension of Classical Propositional Logic

This module proves that Modal B is a conservative extension of Classical Propositional Logic
(CPL): any propositional formula `φ` that is derivable in B (as `φ.toModal`) is already
derivable in CPL.

The proof uses the universal model `(Unit, fun _ _ => True, fun _ => v)`, which satisfies
all B frame conditions (symmetry: `fun _ _ _ => trivial`). Since `φ.toModal` contains no box
operators, satisfaction is determined entirely by the valuation, giving CPL tautologyhood
of `φ` and hence CPL derivability by completeness.

## Main Theorem

- `b_conservative_extension`: If `φ.toModal` is B-derivable then `φ` is CPL-derivable.

## References

* Standard result in modal logic: see [Blackburn2001] Chapter 4.
-/

@[expose] public section

namespace Cslib.Logic

open PL Cslib.Logic.Modal

/-- **Modal B Conservative Extension over CPL**:

If the modal translation `φ.toModal` is derivable in B, then `φ` is derivable
in Classical Propositional Logic.

Proof: construct the universal model `(Unit, fun _ _ => True, fun _ => v)`.
Symmetry holds vacuously (`fun _ _ _ => trivial`). B soundness gives satisfaction
of `φ.toModal` at the single world; the bridge lemma converts this to `Evaluate v φ`;
CPL completeness then gives CPL derivability. -/
theorem b_conservative_extension {Atom : Type*} {φ : PL.Proposition Atom}
    (h : Derivable (@BAxiom Atom) φ.toModal) :
    PL.Derivable PropositionalAxiom φ := by
  apply prop_completeness; intro v
  let m : Modal.Model Unit Atom := ⟨fun _ _ => True, fun _ => v⟩
  obtain ⟨d⟩ := h
  exact (modal_satisfies_toModal_iff_evaluate m () φ).mp
    (b_soundness d m (fun _ _ _ => trivial) () (fun _ h => nomatch h))

end Cslib.Logic

end
