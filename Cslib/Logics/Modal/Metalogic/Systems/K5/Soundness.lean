/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Modal.Metalogic.Soundness
public import Cslib.Logics.Modal.ProofSystem.Instances

/-! # Soundness Theorem for Modal Logic K5

This module proves soundness for modal logic K5 (K + axiom 5) over Euclidean
Kripke frames.

## Main Results

- `k5_axiom_sound`: Each of the 6 K5Axiom schemata is valid over Euclidean frames.
- `k5_soundness`: If `Gamma |- phi` via `DerivationTree K5Axiom`, then `phi` is
  satisfied at every world of every Euclidean model where `Gamma` is satisfied.
## References

* Blackburn, de Rijke, Venema, "Modal Logic" (2002), Definition 4.9, Table 4.1
* Cslib/Logics/Modal/Basic.lean -- `Satisfies.five` for semantic validity of axiom 5
-/

@[expose] public section

namespace Cslib.Logic.Modal

open Cslib.Logic

variable {Atom : Type*}

/-! ## K5 Axiom Soundness -/

/-- Every axiom of K5 is valid over Euclidean frames. -/
theorem k5_axiom_sound {World : Type*} {φ : Proposition Atom}
    (h_ax : K5Axiom φ) (m : Model World Atom)
    (h_eucl : ∀ w₁ w₂ w₃, m.r w₁ w₂ → m.r w₁ w₃ → m.r w₂ w₃)
    (w : World) : Satisfies m w φ := by
  cases h_ax with
  | implyK φ ψ => exact Satisfies.implyK_axiom m w φ ψ
  | implyS φ ψ χ => exact Satisfies.implyS_axiom m w φ ψ χ
  | efq φ => exact Satisfies.efq_axiom m w φ
  | peirce φ ψ => exact Satisfies.peirce_axiom m w φ ψ
  | modalK φ ψ => exact Satisfies.modalK_axiom m w φ ψ
  | modalFive φ =>
    intro h_diam w' hr h_box_neg_w'
    exact h_diam (fun w'' hr' h_phi =>
      h_box_neg_w' w'' (h_eucl w w' w'' hr hr') h_phi)
  | andI φ ψ => exact Satisfies.andI_axiom m w φ ψ
  | andE1 φ ψ => exact Satisfies.andE1_axiom m w φ ψ
  | andE2 φ ψ => exact Satisfies.andE2_axiom m w φ ψ
  | orI1 φ ψ => exact Satisfies.orI1_axiom m w φ ψ
  | orI2 φ ψ => exact Satisfies.orI2_axiom m w φ ψ
  | orE φ ψ χ => exact Satisfies.orE_axiom m w φ ψ χ
  | diaDualityFwd φ => exact Satisfies.diaDualityFwd_axiom m w φ
  | diaDualityBack φ => exact Satisfies.diaDualityBack_axiom m w φ


/-! ## K5 Soundness Theorems -/

/-- K5 soundness: every derivable formula from context is valid over Euclidean models. -/
theorem k5_soundness {World : Type*}
    {Γ : List (Proposition Atom)} {φ : Proposition Atom}
    (d : DerivationTree (@K5Axiom Atom) Γ φ)
    (m : Model World Atom)
    (h_eucl : ∀ w₁ w₂ w₃, m.r w₁ w₂ → m.r w₁ w₃ → m.r w₂ w₃)
    (w : World)
    (h_ctx : ∀ ψ ∈ Γ, Satisfies m w ψ) : Satisfies m w φ :=
  soundness d m (fun _ h_ax w => k5_axiom_sound h_ax m h_eucl w) w h_ctx

end Cslib.Logic.Modal
