/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Modal.Metalogic.Soundness
public import Cslib.Logics.Modal.ProofSystem.Instances

/-! # Soundness Theorem for Modal Logic KB5

This module proves soundness for modal logic KB5 (= K + B + 5): every formula
derivable from `KB5Axiom` is valid on symmetric + Euclidean frames.

KB5 has 7 axiom schemata -- the 4 propositional axioms, the K distribution axiom,
the B symmetry axiom (`φ → □◇φ`), and the 5 Euclidean axiom (`◇φ → □◇φ`).
The frame class for KB5 is symmetric + Euclidean.

## Main Results

- `kb5_axiom_sound`: Each of the 7 KB5 axiom schemata is valid over symmetric,
  Euclidean frames.
- `kb5_soundness`: If `Gamma |- phi` via `DerivationTree KB5Axiom`, then `phi` is
  satisfied at every world where all of `Gamma` is satisfied, on symmetric,
  Euclidean frames.
## References

* Blackburn, de Rijke, Venema - Modal Logic (Ch. 4, Definition 4.9)
* Cslib/Logics/Modal/Metalogic/Soundness.lean -- parameterized soundness theorem
-/

@[expose] public section

namespace Cslib.Logic.Modal

open Cslib.Logic

variable {Atom : Type*}

/-! ## KB5 Axiom Soundness (BRV Definition 4.9 for KB5) -/

/-- Every axiom of KB5 is valid over symmetric, Euclidean frames.

Axiom B (`φ → □◇φ`) uses symmetry (Blackburn Theorem 4.28, clause 2);
axiom 5 (`◇φ → □◇φ`) uses Euclideanness.
Propositional axioms and K are valid on all frames. -/
theorem kb5_axiom_sound {World : Type*} {φ : Proposition Atom}
    (h_ax : KB5Axiom φ) (m : Model World Atom)
    (h_symm : ∀ w₁ w₂, m.r w₁ w₂ → m.r w₂ w₁)
    (h_eucl : ∀ w₁ w₂ w₃, m.r w₁ w₂ → m.r w₁ w₃ → m.r w₂ w₃)
    (w : World) : Satisfies m w φ := by
  cases h_ax with
  | implyK φ ψ => exact Satisfies.implyK_axiom m w φ ψ
  | implyS φ ψ χ => exact Satisfies.implyS_axiom m w φ ψ χ
  | efq φ => exact Satisfies.efq_axiom m w φ
  | peirce φ ψ => exact Satisfies.peirce_axiom m w φ ψ
  | modalK φ ψ => exact Satisfies.modalK_axiom m w φ ψ
  | modalB φ => exact Satisfies.modalB_axiom m h_symm w φ
  | modalFive φ => exact Satisfies.modalFive_axiom m h_eucl w φ
  | andI φ ψ => exact Satisfies.andI_axiom m w φ ψ
  | andE1 φ ψ => exact Satisfies.andE1_axiom m w φ ψ
  | andE2 φ ψ => exact Satisfies.andE2_axiom m w φ ψ
  | orI1 φ ψ => exact Satisfies.orI1_axiom m w φ ψ
  | orI2 φ ψ => exact Satisfies.orI2_axiom m w φ ψ
  | orE φ ψ χ => exact Satisfies.orE_axiom m w φ ψ χ
  | diaDualityFwd φ => exact Satisfies.diaDualityFwd_axiom m w φ
  | diaDualityBack φ => exact Satisfies.diaDualityBack_axiom m w φ


/-! ## KB5 Soundness Theorems -/

/-- **KB5 Soundness**: If `Gamma |- phi` via `DerivationTree KB5Axiom`, then `phi` is
satisfied at every world where all of `Gamma` is satisfied, on symmetric,
Euclidean frames. -/
theorem kb5_soundness {World : Type*}
    {Γ : List (Proposition Atom)} {φ : Proposition Atom}
    (d : DerivationTree (@KB5Axiom Atom) Γ φ)
    (m : Model World Atom)
    (h_symm : ∀ w₁ w₂, m.r w₁ w₂ → m.r w₂ w₁)
    (h_eucl : ∀ w₁ w₂ w₃, m.r w₁ w₂ → m.r w₁ w₃ → m.r w₂ w₃)
    (w : World)
    (h_ctx : ∀ ψ ∈ Γ, Satisfies m w ψ) : Satisfies m w φ :=
  soundness d m (fun _ h_ax w => kb5_axiom_sound h_ax m h_symm h_eucl w) w h_ctx

end Cslib.Logic.Modal
