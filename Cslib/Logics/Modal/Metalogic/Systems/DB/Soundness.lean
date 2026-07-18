/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Modal.Metalogic.Soundness
public import Cslib.Logics.Modal.ProofSystem.Instances

/-! # Soundness Theorem for Modal Logic DB (KDB)

This module proves soundness for modal logic DB over serial + symmetric Kripke
frames. DB = K + D + B, combining the seriality axiom (D) with the symmetry
axiom (B), but without axiom T.

## Main Results

- `db_axiom_sound`: Each of the 7 DBAxiom schemata is valid over serial,
  symmetric frames.
- `db_soundness`: If `Gamma |- phi` via `DerivationTree DBAxiom`, then `phi` is
  satisfied at every world of every serial, symmetric model where `Gamma` is
  satisfied.
## References

* Blackburn, de Rijke, Venema, "Modal Logic" (2002), Definition 4.9, Table 4.1
* Cslib/Logics/Modal/Basic.lean -- `Satisfies.d` for semantic validity of D axiom
* Cslib/Logics/Modal/Basic.lean -- `Satisfies.b` for semantic validity of B axiom
-/

@[expose] public section

namespace Cslib.Logic.Modal

open Cslib.Logic

variable {Atom : Type*}

/-! ## DB Axiom Soundness -/

/-- Every axiom of DB is valid over serial, symmetric frames. -/
theorem db_axiom_sound {World : Type*} {φ : Proposition Atom}
    (h_ax : DBAxiom φ) (m : Model World Atom)
    (h_serial : Relation.Serial m.r)
    (h_symm : ∀ w₁ w₂, m.r w₁ w₂ → m.r w₂ w₁)
    (w : World) : Satisfies m w φ := by
  cases h_ax with
  | implyK φ ψ => exact Satisfies.implyK_axiom m w φ ψ
  | implyS φ ψ χ => exact Satisfies.implyS_axiom m w φ ψ χ
  | efq φ => exact Satisfies.efq_axiom m w φ
  | peirce φ ψ => exact Satisfies.peirce_axiom m w φ ψ
  | modalK φ ψ => exact Satisfies.modalK_axiom m w φ ψ
  | modalD φ => exact Satisfies.modalD_axiom m h_serial w φ
  | modalB φ => exact Satisfies.modalB_axiom m h_symm w φ
  | andI φ ψ => exact Satisfies.andI_axiom m w φ ψ
  | andE1 φ ψ => exact Satisfies.andE1_axiom m w φ ψ
  | andE2 φ ψ => exact Satisfies.andE2_axiom m w φ ψ
  | orI1 φ ψ => exact Satisfies.orI1_axiom m w φ ψ
  | orI2 φ ψ => exact Satisfies.orI2_axiom m w φ ψ
  | orE φ ψ χ => exact Satisfies.orE_axiom m w φ ψ χ
  | diaDualityFwd φ => exact Satisfies.diaDualityFwd_axiom m w φ
  | diaDualityBack φ => exact Satisfies.diaDualityBack_axiom m w φ


/-! ## DB Soundness Theorems -/

/-- DB soundness: every derivable formula from context is valid over serial,
symmetric models. -/
theorem db_soundness {World : Type*}
    {Γ : List (Proposition Atom)} {φ : Proposition Atom}
    (d : DerivationTree (@DBAxiom Atom) Γ φ)
    (m : Model World Atom)
    (h_serial : Relation.Serial m.r)
    (h_symm : ∀ w₁ w₂, m.r w₁ w₂ → m.r w₂ w₁)
    (w : World)
    (h_ctx : ∀ ψ ∈ Γ, Satisfies m w ψ) : Satisfies m w φ :=
  soundness d m (fun _ h_ax w => db_axiom_sound h_ax m h_serial h_symm w) w h_ctx

end Cslib.Logic.Modal
