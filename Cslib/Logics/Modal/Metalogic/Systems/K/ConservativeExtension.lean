/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Modal.FromPropositional
public import Cslib.Logics.Modal.Metalogic.Systems.K.Soundness
public import Cslib.Logics.Propositional.Metalogic.StrongCompleteness

/-! # Modal K as a Conservative Extension of Classical Propositional Logic

This module proves that Modal K is a conservative extension of Classical Propositional Logic
(CPL): any propositional formula `φ` that is derivable in K (as `φ.toModal`) is already
derivable in CPL.

The proof composes three existing results:
1. K Soundness: K-derivable formulas are valid on all Kripke frames.
2. Semantic coherence: validity of `φ.toModal` implies propositional tautologyhood of `φ`.
3. CPL Completeness: propositional tautologies are CPL-derivable.

## Main Theorem

- `modal_conservative_extension`: If `φ.toModal` is K-derivable then `φ` is CPL-derivable.

## References

* Standard result in modal logic: see [Blackburn2001] Chapter 1.
-/

@[expose] public section

namespace Cslib.Logic

open PL Cslib.Logic.Modal

/-- **Modal K Conservative Extension over CPL**:

If the modal translation `φ.toModal` is derivable in K, then `φ` is derivable
in Classical Propositional Logic.

Proof: K soundness gives validity of `φ.toModal`; the semantic bridge lemma
`toModal_valid_implies_tautology` gives that `φ` is a tautology; CPL completeness
then gives CPL derivability of `φ`. -/
theorem modal_conservative_extension {Atom : Type*} {φ : PL.Proposition Atom}
    (h : Derivable (@KAxiom Atom) φ.toModal) :
    PL.Derivable PropositionalAxiom φ :=
  prop_completeness (toModal_valid_implies_tautology
    (fun _ m w => k_soundness_derivable h m w))

end Cslib.Logic

end
