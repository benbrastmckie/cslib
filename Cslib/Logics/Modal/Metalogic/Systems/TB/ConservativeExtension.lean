/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Modal.FromPropositional
public import Cslib.Logics.Modal.Metalogic.ConservativeExtension
public import Cslib.Logics.Modal.Metalogic.Systems.TB.Soundness
public import Cslib.Logics.Propositional.Metalogic.StrongCompleteness

/-! # Modal TB as a Conservative Extension of CPL -/

@[expose] public section

namespace Cslib.Logic

open PL Cslib.Logic.Modal

/-- Modal TB is a conservative extension of CPL: if `φ.toModal` is TB-derivable then `φ` is
CPL-derivable. Instantiates `modal_conservative_extension_param` with `tb_soundness`
(reflexivity: `fun _ => trivial`, symmetry: `fun _ _ _ => trivial`). -/
theorem tb_conservative_extension {Atom : Type*} {φ : PL.Proposition Atom}
    (h : Derivable (@TBAxiom Atom) φ.toModal) :
    PL.Derivable PropositionalAxiom φ :=
  modal_conservative_extension_param h fun _ => by
    obtain ⟨d⟩ := h
    exact tb_soundness d _ (fun _ => trivial) (fun _ _ _ => trivial) () (fun _ h => nomatch h)

end Cslib.Logic

end
