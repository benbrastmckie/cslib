/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

import Cslib.Init
public import Cslib.Logics.Propositional.ProofSystem.FragmentAxioms
public import Cslib.Logics.Propositional.Metalogic.Soundness
public import Cslib.Logics.Propositional.Semantics.Algebra.ConjImpConservative

/-! # Completeness of the Classical Implicational Fragment CPL⟨→,⊤⟩

This module proves that the classical implicational fragment CPL⟨→,⊤⟩ — axiomatized by
K (weakening), S (distribution), and Peirce's law — is complete for tautologies that
involve only implication and truth (i.e., imp-top-only formulas). The proof follows
the Kalmár / Tarski–Bernays truth-assignment method.

## Strategy

The proof proceeds in stages building toward `classicalImp_completeness`:

1. **Soundness** (`classicalImp_soundness`): every CPL⟨→,⊤⟩-derivable formula is a
   tautology. Routes through `ClassicalImpAxiom.toPropAxiom` and CPL soundness.

2. **Derived rules**: identity (`classicalImp_imp_self`), composition (`classicalImp_imp_trans`),
   and the Peirce-driven case lemma (`classicalImp_peirce_mp`) needed by the truth lemma.

3. **Literal context** (`litCtx`): a List-based Kalmár literal context keyed on a Boolean
   assignment, with atom `p` contributing `atom p` if true or `atom p → goal` if false.

4. **Kalmár truth lemma** (`classicalImp_kalmar`): for imp-top-only `φ`, the literal
   context derives either `φ` (if true) or `φ → goal` (if false).

5. **Completeness** (`classicalImp_completeness`): iterate atom elimination over the literal
   context to conclude `Derivable ClassicalImpAxiom φ` from `Tautology φ`.

6. **Conservativity** (`cpl_conservative_over_imp`): CPL is conservative over CPL⟨→,⊤⟩
   for imp-top-only formulas.

## References

* Tarski–Bernays axiomatization of the classical implicational calculus.
* Kalmár completeness method (falsum-surrogate variant).
* See also: `Cslib/Logics/Propositional/Semantics/Algebra/ImpConservative.lean` for the
  analogous intuitionistic conservativity result. -/

@[expose] public section

namespace Cslib.Logic.PL

variable {Atom : Type*}

/-! ## Soundness -/

/-- Soundness for the classical implicational fragment: every `ClassicalImpAxiom`-derivable
formula is a tautology. Routes through `ClassicalImpAxiom.toPropAxiom` and CPL soundness. -/
theorem classicalImp_soundness {φ : PL.Proposition Atom}
    (h : Derivable ClassicalImpAxiom φ) : Tautology φ := by
  obtain ⟨d⟩ := h
  exact prop_soundness_tautology ⟨liftDerivationTree (fun ψ hψ => hψ.toPropAxiom) d⟩

end Cslib.Logic.PL
