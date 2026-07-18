/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Modal.Metalogic.Soundness
public import Cslib.Logics.Modal.ProofSystem.Instances

/-! # Soundness Theorem for Modal Logic D5 (KD5)

This module proves soundness for modal logic D5 over serial + Euclidean Kripke
frames. D5 = K + D + 5, combining the seriality axiom (D) with the Euclideanness
axiom (5), but without axiom T.

## Main Results

- `d5_axiom_sound`: Each of the 7 D5Axiom schemata is valid over serial,
  Euclidean frames.
- `d5_soundness`: If `Gamma |- phi` via `DerivationTree D5Axiom`, then `phi` is
  satisfied at every world of every serial, Euclidean model where `Gamma` is
  satisfied.
## References

* Blackburn, de Rijke, Venema, "Modal Logic" (2002), Definition 4.9, Table 4.1
* Cslib/Logics/Modal/Basic.lean -- `Satisfies.d` for semantic validity of D axiom
* Cslib/Logics/Modal/Basic.lean -- `Satisfies.five` for semantic validity of axiom 5
-/

@[expose] public section

namespace Cslib.Logic.Modal

open Cslib.Logic

variable {Atom : Type*}

/-! ## D5 Axiom Soundness -/

/-- Every axiom of D5 is valid over serial, Euclidean frames. -/
theorem d5_axiom_sound {World : Type*} {φ : Proposition Atom}
    (h_ax : D5Axiom φ) (m : Model World Atom)
    (h_serial : Relation.Serial m.r)
    (h_eucl : ∀ w₁ w₂ w₃, m.r w₁ w₂ → m.r w₁ w₃ → m.r w₂ w₃)
    (w : World) : Satisfies m w φ := by
  cases h_ax with
  | implyK φ ψ => exact Satisfies.implyK_axiom m w φ ψ
  | implyS φ ψ χ => exact Satisfies.implyS_axiom m w φ ψ χ
  | efq φ => exact Satisfies.efq_axiom m w φ
  | peirce φ ψ => exact Satisfies.peirce_axiom m w φ ψ
  | modalK φ ψ => exact Satisfies.modalK_axiom m w φ ψ
  | modalD φ => exact Satisfies.modalD_axiom m h_serial w φ
  | modalFive φ => exact Satisfies.modalFive_axiom m h_eucl w φ
  | andI φ ψ => exact Satisfies.andI_axiom m w φ ψ
  | andE1 φ ψ => exact Satisfies.andE1_axiom m w φ ψ
  | andE2 φ ψ => exact Satisfies.andE2_axiom m w φ ψ
  | orI1 φ ψ => exact Satisfies.orI1_axiom m w φ ψ
  | orI2 φ ψ => exact Satisfies.orI2_axiom m w φ ψ
  | orE φ ψ χ => exact Satisfies.orE_axiom m w φ ψ χ
  | diaDualityFwd φ => exact Satisfies.diaDualityFwd_axiom m w φ
  | diaDualityBack φ => exact Satisfies.diaDualityBack_axiom m w φ


/-! ## D5 Soundness Theorems -/

/-- D5 soundness: every derivable formula from context is valid over serial,
Euclidean models. -/
theorem d5_soundness {World : Type*}
    {Γ : List (Proposition Atom)} {φ : Proposition Atom}
    (d : DerivationTree (@D5Axiom Atom) Γ φ)
    (m : Model World Atom)
    (h_serial : Relation.Serial m.r)
    (h_eucl : ∀ w₁ w₂ w₃, m.r w₁ w₂ → m.r w₁ w₃ → m.r w₂ w₃)
    (w : World)
    (h_ctx : ∀ ψ ∈ Γ, Satisfies m w ψ) : Satisfies m w φ :=
  soundness d m (fun _ h_ax w => d5_axiom_sound h_ax m h_serial h_eucl w) w h_ctx

end Cslib.Logic.Modal
