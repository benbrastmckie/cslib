/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Modal.FromPropositional
public import Cslib.Logics.Modal.Metalogic.ConservativeExtension
public import Cslib.Logics.Modal.Metalogic.Systems.KB5.Soundness
public import Cslib.Logics.Propositional.Metalogic.StrongCompleteness

/-! # Modal KB5 as a Conservative Extension of CPL -/

@[expose] public section

namespace Cslib.Logic

open PL Cslib.Logic.Modal

/-- Modal KB5 is a conservative extension of CPL: if `φ.toModal` is KB5-derivable then `φ` is
CPL-derivable. Instantiates `modal_conservative_extension_param` with `kb5_soundness`
(symmetry: `fun _ _ _ => trivial`, Euclideanness: `fun _ _ _ _ _ => trivial`). -/
theorem kb5_conservative_extension {Atom : Type*} {φ : PL.Proposition Atom}
    (h : Derivable (@KB5Axiom Atom) φ.toModal) :
    PL.Derivable PropositionalAxiom φ :=
  modal_conservative_extension_param h fun _ => by
    obtain ⟨d⟩ := h
    exact kb5_soundness d _ (fun _ _ _ => trivial) (fun _ _ _ _ _ => trivial)
      () (fun _ h => nomatch h)

end Cslib.Logic

end
