/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Modal.FromPropositional
public import Cslib.Logics.Modal.Metalogic.ConservativeExtension
public import Cslib.Logics.Modal.Metalogic.Systems.S4.Soundness
public import Cslib.Logics.Propositional.Metalogic.StrongCompleteness

/-! # Modal S4 as a Conservative Extension of CPL -/

@[expose] public section

namespace Cslib.Logic

open PL Cslib.Logic.Modal

/-- Modal S4 is a conservative extension of CPL: if `φ.toModal` is S4-derivable then `φ` is
CPL-derivable. Instantiates `modal_conservative_extension_param` with `s4_soundness`
(reflexivity: `fun _ => trivial`, transitivity: `fun _ _ _ _ _ => trivial`). -/
theorem s4_conservative_over_cpl {Atom : Type*} {φ : PL.Proposition Atom}
    (h : Derivable (@S4Axiom Atom) φ.toModal) :
    PL.Derivable PropositionalAxiom φ :=
  modal_conservative_extension_param h fun _ => by
    obtain ⟨d⟩ := h
    exact s4_soundness d _ (fun _ => trivial) (fun _ _ _ _ _ => trivial)
      () (fun _ h => nomatch h)

end Cslib.Logic

end
