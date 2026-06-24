/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Modal.FromPropositional
public import Cslib.Logics.Modal.Metalogic.ConservativeExtension
public import Cslib.Logics.Modal.Metalogic.Systems.D.Soundness
public import Cslib.Logics.Propositional.Metalogic.StrongCompleteness

/-! # Modal D as a Conservative Extension of CPL -/

@[expose] public section

namespace Cslib.Logic

open PL Cslib.Logic.Modal

/-- Modal D is a conservative extension of CPL: if `φ.toModal` is D-derivable then `φ` is
CPL-derivable. Instantiates `modal_conservative_extension_param` with `d_soundness`
(seriality: `⟨fun w => ⟨w, trivial⟩⟩`). -/
theorem d_conservative_extension {Atom : Type*} {φ : PL.Proposition Atom}
    (h : Derivable (@DAxiom Atom) φ.toModal) :
    PL.Derivable PropositionalAxiom φ :=
  modal_conservative_extension_param h fun _ => by
    obtain ⟨d⟩ := h
    exact d_soundness d _ ⟨fun w => ⟨w, trivial⟩⟩ () (fun _ h => nomatch h)

end Cslib.Logic

end
