/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Modal.FromPropositional
public import Cslib.Logics.Modal.Metalogic.DerivationTree
public import Cslib.Logics.Propositional.Metalogic.StrongCompleteness

/-! # Parametric Modal Conservative Extension over CPL

This module provides a single parametric theorem
`modal_conservative_extension_param` that captures the shared proof skeleton used by
all 15 per-system conservative-extension results. Each system-specific theorem is
obtained by supplying a satisfaction callback that discharges the system's
frame-condition hypotheses against the universal `Unit` model.

The universal model `⟨fun _ _ => True, fun _ => v⟩ : Modal.Model Unit Atom` has a
single world, an always-true accessibility relation, and valuations inherited from CPL.
Every frame condition (reflexivity, transitivity, symmetry, Euclideanness, seriality)
holds vacuously on this model, so each `*_soundness` wrapper can be called with trivial
discharge terms.

## Main Theorem

- `modal_conservative_extension_param`: Parametric conservative-extension theorem.
  Takes any derivability hypothesis and a satisfaction callback that witnesses
  `φ.toModal` at the universal model for any CPL valuation.

## References

* Standard result in modal logic: see [Blackburn2001] Chapter 1.
-/

@[expose] public section

namespace Cslib.Logic

open PL Cslib.Logic.Modal

/-- **Parametric Modal Conservative Extension over CPL**:

If `φ.toModal` is derivable in any modal system whose axioms are sound at the
universal `Unit` model, then `φ` is derivable in Classical Propositional Logic.

The callback `h_sat` witnesses, for each CPL valuation `v`, that `φ.toModal` is
satisfied at the single world `()` of the universal model
`⟨fun _ _ => True, fun _ => v⟩`. This is exactly the term produced by calling
`<sys>_soundness d _ <frame-conditions> () (fun _ h => nomatch h)` in each
system instantiation. -/
theorem modal_conservative_extension_param {Atom : Type*}
    {Axioms : Modal.Proposition Atom → Prop} {φ : PL.Proposition Atom}
    (_ : Derivable Axioms φ.toModal)
    (h_sat : ∀ (v : Atom → Prop),
      Modal.Satisfies (⟨fun _ _ => True, fun _ => v⟩ : Modal.Model Unit Atom) () φ.toModal) :
    PL.Derivable PropositionalAxiom φ := by
  apply prop_completeness; intro v
  exact (modal_satisfies_toModal_iff_evaluate
    (⟨fun _ _ => True, fun _ => v⟩ : Modal.Model Unit Atom) () φ).mp (h_sat v)

end Cslib.Logic

end
