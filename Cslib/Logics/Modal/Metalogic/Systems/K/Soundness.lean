/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Modal.Metalogic.Soundness
public import Cslib.Logics.Modal.ProofSystem.Instances

/-! # Soundness Theorem for Modal Logic K

This module proves soundness for modal logic K: every formula derivable from
`KAxiom` is valid on all frames (no frame conditions needed).

## Main Results

- `k_axiom_sound`: Each of the 5 K axiom schemata is valid over all frames.
- `k_soundness`: If `Gamma |- phi` via `DerivationTree KAxiom`, then `phi` is
  satisfied at every world where all of `Gamma` is satisfied.
- `k_soundness_derivable`: If `phi` is K-derivable, then `phi` is valid on all frames.

## References

* Blackburn, de Rijke, Venema - Modal Logic (Ch. 4, Definition 4.9)
* Cslib/Logics/Modal/Metalogic/Soundness.lean -- parameterized soundness theorem
-/

@[expose] public section

namespace Cslib.Logic.Modal

open Cslib.Logic

variable {Atom : Type*}

/-! ## K Axiom Soundness (BRV Definition 4.9 for K) -/

/-- Every axiom of K is valid over all frames (no frame conditions needed). -/
theorem k_axiom_sound {World : Type*} {φ : Proposition Atom}
    (h_ax : KAxiom φ) (m : Model World Atom)
    (w : World) : Satisfies m w φ := by
  cases h_ax with
  | implyK φ ψ => exact Satisfies.implyK_axiom m w φ ψ
  | implyS φ ψ χ => exact Satisfies.implyS_axiom m w φ ψ χ
  | efq φ => exact Satisfies.efq_axiom m w φ
  | peirce φ ψ => exact Satisfies.peirce_axiom m w φ ψ
  | modalK φ ψ => exact Satisfies.modalK_axiom m w φ ψ
  | andI φ ψ => exact Satisfies.andI_axiom m w φ ψ
  | andE1 φ ψ => exact Satisfies.andE1_axiom m w φ ψ
  | andE2 φ ψ => exact Satisfies.andE2_axiom m w φ ψ
  | orI1 φ ψ => exact Satisfies.orI1_axiom m w φ ψ
  | orI2 φ ψ => exact Satisfies.orI2_axiom m w φ ψ
  | orE φ ψ χ => exact Satisfies.orE_axiom m w φ ψ χ
  | diaDualityFwd φ => exact Satisfies.diaDualityFwd_axiom m w φ
  | diaDualityBack φ => exact Satisfies.diaDualityBack_axiom m w φ


/-! ## K Soundness Theorems -/

/-- **K Soundness**: If `Gamma |- phi` via `DerivationTree KAxiom`, then `phi` is
satisfied at every world where all of `Gamma` is satisfied. -/
theorem k_soundness {World : Type*}
    {Γ : List (Proposition Atom)} {φ : Proposition Atom}
    (d : DerivationTree (@KAxiom Atom) Γ φ)
    (m : Model World Atom)
    (w : World)
    (h_ctx : ∀ ψ ∈ Γ, Satisfies m w ψ) : Satisfies m w φ :=
  soundness d m (fun _ h_ax w => k_axiom_sound h_ax m w) w h_ctx

/-- **K Soundness for derivable formulas**: If `phi` is K-derivable from the empty
context, then `phi` is satisfied at every world of every model. -/
theorem k_soundness_derivable {World : Type*}
    {φ : Proposition Atom} (h : Derivable (@KAxiom Atom) φ)
    (m : Model World Atom)
    (w : World) : Satisfies m w φ :=
  soundness_derivable h m (fun _ h_ax w => k_axiom_sound h_ax m w) w

end Cslib.Logic.Modal
