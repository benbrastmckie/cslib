/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Modal.FromPropositional
public import Cslib.Logics.Modal.Metalogic.ConservativeExtension
public import Cslib.Logics.Modal.Metalogic.Systems.DB.Soundness
public import Cslib.Logics.Propositional.Metalogic.StrongCompleteness

/-! # Modal DB as a Conservative Extension of CPL -/

@[expose] public section

namespace Cslib.Logic

open PL Cslib.Logic.Modal

/-- Modal DB is a conservative extension of CPL: if `φ.toModal` is DB-derivable then `φ` is
CPL-derivable. Instantiates `modal_conservative_extension_param` with `db_soundness`
(seriality: `⟨fun w => ⟨w, trivial⟩⟩`, symmetry: `fun _ _ _ => trivial`). -/
theorem db_conservative_over_cpl {Atom : Type*} {φ : PL.Proposition Atom}
    (h : Derivable (@DBAxiom Atom) φ.toModal) :
    PL.Derivable PropositionalAxiom φ :=
  modal_conservative_extension_param h fun _ => by
    obtain ⟨d⟩ := h
    exact db_soundness d _ ⟨fun w => ⟨w, trivial⟩⟩ (fun _ _ _ => trivial)
      () (fun _ h => nomatch h)

end Cslib.Logic

end
