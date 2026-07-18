/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Modal.Metalogic.Soundness
public import Cslib.Logics.Modal.ProofSystem.Instances

/-! # Soundness Theorem for Modal Logic T

This module proves soundness for modal logic T: every formula derivable from
`TAxiom` is valid on reflexive frames.

## Main Results

- `t_axiom_sound`: Each of the 6 T axiom schemata is valid over reflexive frames.
- `t_soundness`: If `Gamma |- phi` via `DerivationTree TAxiom`, then `phi` is
  satisfied at every world of every reflexive model where all of `Gamma` is satisfied.
## References

* Blackburn, de Rijke, Venema - Modal Logic (Ch. 4, Definition 4.9, Table 4.1)
* Cslib/Logics/Modal/Metalogic/Soundness.lean -- parameterized soundness theorem
-/

@[expose] public section

namespace Cslib.Logic.Modal

open Cslib.Logic

variable {Atom : Type*}

/-! ## T Axiom Soundness (BRV Definition 4.9 for T) -/

/-- Every axiom of T is valid over reflexive frames. -/
theorem t_axiom_sound {World : Type*} {φ : Proposition Atom}
    (h_ax : TAxiom φ) (m : Model World Atom)
    (h_refl : ∀ w, m.r w w)
    (w : World) : Satisfies m w φ := by
  cases h_ax with
  | implyK φ ψ => exact Satisfies.implyK_axiom m w φ ψ
  | implyS φ ψ χ => exact Satisfies.implyS_axiom m w φ ψ χ
  | efq φ => exact Satisfies.efq_axiom m w φ
  | peirce φ ψ => exact Satisfies.peirce_axiom m w φ ψ
  | modalK φ ψ => exact Satisfies.modalK_axiom m w φ ψ
  | modalT φ => exact Satisfies.modalT_axiom m h_refl w φ
  | andI φ ψ => exact Satisfies.andI_axiom m w φ ψ
  | andE1 φ ψ => exact Satisfies.andE1_axiom m w φ ψ
  | andE2 φ ψ => exact Satisfies.andE2_axiom m w φ ψ
  | orI1 φ ψ => exact Satisfies.orI1_axiom m w φ ψ
  | orI2 φ ψ => exact Satisfies.orI2_axiom m w φ ψ
  | orE φ ψ χ => exact Satisfies.orE_axiom m w φ ψ χ
  | diaDualityFwd φ => exact Satisfies.diaDualityFwd_axiom m w φ
  | diaDualityBack φ => exact Satisfies.diaDualityBack_axiom m w φ


/-! ## T Soundness Theorems -/

/-- **T Soundness**: If `Gamma |- phi` via `DerivationTree TAxiom`, then `phi` is
satisfied at every world of every reflexive model where all of `Gamma` is satisfied. -/
theorem t_soundness {World : Type*}
    {Γ : List (Proposition Atom)} {φ : Proposition Atom}
    (d : DerivationTree (@TAxiom Atom) Γ φ)
    (m : Model World Atom)
    (h_refl : ∀ w, m.r w w)
    (w : World)
    (h_ctx : ∀ ψ ∈ Γ, Satisfies m w ψ) : Satisfies m w φ :=
  soundness d m (fun _ h_ax w => t_axiom_sound h_ax m h_refl w) w h_ctx

end Cslib.Logic.Modal
