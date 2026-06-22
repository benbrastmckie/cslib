/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Modal.FromPropositional
public import Cslib.Logics.Modal.Metalogic.Systems.D5.Soundness
public import Cslib.Logics.Propositional.Metalogic.StrongCompleteness

/-! # Modal D5 as a Conservative Extension of Classical Propositional Logic

This module proves that Modal D5 is a conservative extension of Classical Propositional Logic
(CPL): any propositional formula `φ` that is derivable in D5 (as `φ.toModal`) is already
derivable in CPL.

The proof uses the universal model `(Unit, fun _ _ => True, fun _ => v)`, which satisfies
all D5 frame conditions. Seriality holds via `fun w => ⟨w, trivial⟩` and Euclideanness
holds vacuously. Since `φ.toModal` contains no box operators, satisfaction is determined
entirely by the valuation, giving CPL tautologyhood of `φ` and hence CPL derivability
by completeness.

## Main Theorem

- `d5_conservative_extension`: If `φ.toModal` is D5-derivable then `φ` is CPL-derivable.

## References

* Standard result in modal logic: see [Blackburn2001] Chapter 4.
-/

@[expose] public section

namespace Cslib.Logic

open PL Cslib.Logic.Modal

/-- **Modal D5 Conservative Extension over CPL**:

If the modal translation `φ.toModal` is derivable in D5, then `φ` is derivable
in Classical Propositional Logic.

Proof: construct the universal model `(Unit, fun _ _ => True, fun _ => v)`.
Seriality holds via `fun w => ⟨w, trivial⟩` and Euclideanness holds vacuously.
D5 soundness gives satisfaction of `φ.toModal` at the single world; the bridge lemma
converts this to `Evaluate v φ`; CPL completeness then gives CPL derivability. -/
theorem d5_conservative_extension {Atom : Type*} {φ : PL.Proposition Atom}
    (h : Derivable (@D5Axiom Atom) φ.toModal) :
    PL.Derivable PropositionalAxiom φ := by
  apply prop_completeness; intro v
  let m : Modal.Model Unit Atom := ⟨fun _ _ => True, fun _ => v⟩
  obtain ⟨d⟩ := h
  exact (modal_satisfies_toModal_iff_evaluate m () φ).mp
    (d5_soundness d m ⟨fun w => ⟨w, trivial⟩⟩ (fun _ _ _ _ _ => trivial)
      () (fun _ h => nomatch h))

end Cslib.Logic

end
