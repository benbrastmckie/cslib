/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Modal.FromPropositional
public import Cslib.Logics.Modal.Metalogic.ConservativeExtension
public import Cslib.Logics.Modal.Metalogic.Systems.D5.Soundness
public import Cslib.Logics.Propositional.Metalogic.StrongCompleteness

/-! # Modal D5 as a Conservative Extension of CPL -/

@[expose] public section

namespace Cslib.Logic

open PL Cslib.Logic.Modal

/-- Modal D5 is a conservative extension of CPL: if `φ.toModal` is D5-derivable then `φ` is
CPL-derivable. Instantiates `modal_conservative_extension_param` with `d5_soundness`
(seriality: `⟨fun w => ⟨w, trivial⟩⟩`, Euclideanness: `fun _ _ _ _ _ => trivial`). -/
theorem d5_conservative_over_cpl {Atom : Type*} {φ : PL.Proposition Atom}
    (h : Derivable (@D5Axiom Atom) φ.toModal) :
    PL.Derivable PropositionalAxiom φ :=
  modal_conservative_extension_param h fun _ => by
    obtain ⟨d⟩ := h
    exact d5_soundness d _ ⟨fun w => ⟨w, trivial⟩⟩ (fun _ _ _ _ _ => trivial)
      () (fun _ h => nomatch h)

end Cslib.Logic

end
