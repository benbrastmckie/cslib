/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Modal.Metalogic.Soundness
public import Cslib.Logics.Modal.ProofSystem.Instances

/-! # Soundness Theorem for Modal Logic K4

This module proves soundness for modal logic K4 (= K + axiom 4): every formula
derivable from `K4Axiom` is valid on transitive frames.

K4 has 6 axiom schemata -- the same as S4 minus the T axiom (`□φ → φ`).
The frame class for K4 is transitive (Blackburn et al. Table 4.1, p.195).

## Main Results

- `k4_axiom_sound`: Each of the 6 K4 axiom schemata is valid over transitive
  frames (Blackburn Definition 4.9, Table 4.1).
- `k4_soundness`: If `Gamma |- phi` via `DerivationTree K4Axiom`, then `phi` is
  satisfied at every world where all of `Gamma` is satisfied, on transitive frames.
## References

* Blackburn, de Rijke, Venema - Modal Logic (Ch. 4, Definition 4.9, Table 4.1)
* Cslib/Logics/Modal/Metalogic/Soundness.lean -- parameterized soundness theorem
-/

@[expose] public section

namespace Cslib.Logic.Modal

open Cslib.Logic

variable {Atom : Type*}

/-! ## K4 Axiom Soundness (BRV Definition 4.9 for K4) -/

/-- Every axiom of K4 is valid over transitive frames.

Axiom 4 (`□φ → □□φ`) uses transitivity (Blackburn Theorem 4.27).
Propositional axioms and K are valid on all frames. -/
theorem k4_axiom_sound {World : Type*} {φ : Proposition Atom}
    (h_ax : K4Axiom φ) (m : Model World Atom)
    (h_trans : ∀ w₁ w₂ w₃, m.r w₁ w₂ → m.r w₂ w₃ → m.r w₁ w₃)
    (w : World) : Satisfies m w φ := by
  cases h_ax with
  | implyK φ ψ => exact Satisfies.implyK_axiom m w φ ψ
  | implyS φ ψ χ => exact Satisfies.implyS_axiom m w φ ψ χ
  | efq φ => exact Satisfies.efq_axiom m w φ
  | peirce φ ψ => exact Satisfies.peirce_axiom m w φ ψ
  | modalK φ ψ => exact Satisfies.modalK_axiom m w φ ψ
  | modalFour φ =>
    intro h_box w₁ hr₁ w₂ hr₂
    exact h_box w₂ (h_trans w w₁ w₂ hr₁ hr₂)

/-! ## K4 Soundness Theorems -/

/-- **K4 Soundness**: If `Gamma |- phi` via `DerivationTree K4Axiom`, then `phi` is
satisfied at every world where all of `Gamma` is satisfied, on transitive frames. -/
theorem k4_soundness {World : Type*}
    {Γ : List (Proposition Atom)} {φ : Proposition Atom}
    (d : DerivationTree (@K4Axiom Atom) Γ φ)
    (m : Model World Atom)
    (h_trans : ∀ w₁ w₂ w₃, m.r w₁ w₂ → m.r w₂ w₃ → m.r w₁ w₃)
    (w : World)
    (h_ctx : ∀ ψ ∈ Γ, Satisfies m w ψ) : Satisfies m w φ :=
  soundness d m (fun _ h_ax w => k4_axiom_sound h_ax m h_trans w) w h_ctx

end Cslib.Logic.Modal
