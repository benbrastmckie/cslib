/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Modal.Metalogic.Soundness
public import Cslib.Logics.Modal.ProofSystem.Instances

/-! # Soundness Theorem for Modal Logic S5

This module proves soundness for modal logic S5: every formula derivable from
`ModalAxiom` is valid on S5 frames (reflexive, transitive, Euclidean).

## Main Results

- `s5_axiom_sound`: Each of the 8 S5 axiom schemata is valid over S5 frames.
- `s5_soundness`: If `Gamma |- phi` via `DerivationTree ModalAxiom`, then `phi` is
  satisfied at every world of every S5 model where all of `Gamma` is satisfied.
- `s5_soundness_derivable`: If `phi` is S5-derivable, then `phi` is valid on all
  S5 frames.

## References

* Blackburn, de Rijke, Venema - Modal Logic (Ch. 4, Definition 4.9)
* Cslib/Logics/Modal/Metalogic/Soundness.lean -- parameterized soundness theorem
-/

@[expose] public section

namespace Cslib.Logic.Modal

open Cslib.Logic

variable {Atom : Type*}

/-! ## S5 Axiom Soundness -/

/-- Every axiom of S5 is valid over S5 frames (reflexive, transitive, Euclidean). -/
theorem s5_axiom_sound {World : Type*} {φ : Proposition Atom}
    (h_ax : ModalAxiom φ) (m : Model World Atom)
    (h_refl : ∀ w, m.r w w)
    (h_trans : ∀ w₁ w₂ w₃, m.r w₁ w₂ → m.r w₂ w₃ → m.r w₁ w₃)
    (h_eucl : ∀ w₁ w₂ w₃, m.r w₁ w₂ → m.r w₁ w₃ → m.r w₂ w₃)
    (w : World) : Satisfies m w φ := by
  cases h_ax with
  | implyK φ ψ =>
    intro hφ _
    exact hφ
  | implyS φ ψ χ =>
    intro h₁ h₂ h₃
    exact h₁ h₃ (h₂ h₃)
  | efq φ =>
    intro h
    exact absurd h id
  | peirce φ ψ =>
    intro h
    by_contra h_not
    exact h_not (h (fun hφ => absurd hφ h_not))
  | modalK φ ψ =>
    intro h_box_imp h_box_phi w' hr
    exact h_box_imp w' hr (h_box_phi w' hr)
  | modalT φ =>
    intro h_box
    exact h_box w (h_refl w)
  | modalFour φ =>
    intro h_box w₁ hr₁ w₂ hr₂
    exact h_box w₂ (h_trans w w₁ w₂ hr₁ hr₂)
  | modalB φ =>
    intro hφ w' hr h_box_neg
    have h_symm : m.r w' w := h_eucl w w' w hr (h_refl w)
    exact h_box_neg w h_symm hφ

/-! ## S5 Soundness Theorems -/

/-- **S5 Soundness**: If `Gamma |- phi` via `DerivationTree ModalAxiom`, then `phi` is
satisfied at every world of every S5 model where all of `Gamma` is satisfied. -/
theorem s5_soundness {World : Type*}
    {Γ : List (Proposition Atom)} {φ : Proposition Atom}
    (d : DerivationTree (@ModalAxiom Atom) Γ φ)
    (m : Model World Atom)
    (h_refl : ∀ w, m.r w w)
    (h_trans : ∀ w₁ w₂ w₃, m.r w₁ w₂ → m.r w₂ w₃ → m.r w₁ w₃)
    (h_eucl : ∀ w₁ w₂ w₃, m.r w₁ w₂ → m.r w₁ w₃ → m.r w₂ w₃)
    (w : World)
    (h_ctx : ∀ ψ ∈ Γ, Satisfies m w ψ) : Satisfies m w φ :=
  soundness d m (fun _ h_ax w => s5_axiom_sound h_ax m h_refl h_trans h_eucl w) w h_ctx

end Cslib.Logic.Modal
