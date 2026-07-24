/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Modal.FromPropositional
public import Cslib.Logics.Modal.Metalogic.ConservativeExtension
public import Cslib.Logics.Modal.Metalogic.Systems.T.Soundness
public import Cslib.Logics.Propositional.Metalogic.StrongCompleteness

/-! # Modal T as a Conservative Extension of CPL -/

@[expose] public section

namespace Cslib.Logic

open PL Cslib.Logic.Modal

/-- Modal T is a conservative extension of CPL: if `φ.toModal` is T-derivable then `φ` is
CPL-derivable. Instantiates `modal_conservative_extension_param` with `t_soundness`
(reflexivity: `fun _ => trivial`). -/
theorem t_conservative_over_cpl {Atom : Type*} {φ : PL.Proposition Atom}
    (h : Derivable (@TAxiom Atom) φ.toModal) :
    PL.Derivable PropositionalAxiom φ :=
  modal_conservative_extension_param h fun _ => by
    obtain ⟨d⟩ := h
    exact t_soundness d _ (fun _ => trivial) () (fun _ h => nomatch h)

end Cslib.Logic

end
