/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Modal.Metalogic.Soundness
public import Cslib.Logics.Modal.ProofSystem.Instances

/-! # Soundness Theorem for Modal Logic D4 (KD4)

This module proves soundness for modal logic D4 over serial + transitive Kripke
frames. D4 = K + D + 4, combining the seriality axiom (D) with the transitivity
axiom (4), but without axiom T.

## Main Results

- `d4_axiom_sound`: Each of the 7 D4Axiom schemata is valid over serial,
  transitive frames.
- `d4_soundness`: If `Gamma |- phi` via `DerivationTree D4Axiom`, then `phi` is
  satisfied at every world of every serial, transitive model where `Gamma` is
  satisfied.
- `d4_soundness_derivable`: Soundness for derivable formulas (empty context).

## References

* Blackburn, de Rijke, Venema, "Modal Logic" (2002), Definition 4.9, Table 4.1
* Cslib/Logics/Modal/Basic.lean -- `Satisfies.d` for semantic validity of D axiom
* Cslib/Logics/Modal/Basic.lean -- `Satisfies.four` for semantic validity of 4 axiom
-/

@[expose] public section

namespace Cslib.Logic.Modal

open Cslib.Logic

variable {Atom : Type*}

/-! ## D4 Axiom Soundness -/

/-- Every axiom of D4 is valid over serial, transitive frames. -/
theorem d4_axiom_sound {World : Type*} {φ : Proposition Atom}
    (h_ax : D4Axiom φ) (m : Model World Atom)
    (h_serial : Relation.Serial m.r)
    (h_trans : ∀ w₁ w₂ w₃, m.r w₁ w₂ → m.r w₂ w₃ → m.r w₁ w₃)
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
  | modalD φ =>
    -- D axiom: □φ → ◇φ where ◇φ = (□(φ → ⊥)) → ⊥
    -- By seriality, obtain witness w' with m.r w w'
    intro h_box h_box_neg
    obtain ⟨w', hr⟩ := h_serial.serial w
    exact h_box_neg w' hr (h_box w' hr)
  | modalFour φ =>
    -- 4 axiom: □φ → □□φ
    -- By transitivity
    intro h_box w₁ hr₁ w₂ hr₂
    exact h_box w₂ (h_trans w w₁ w₂ hr₁ hr₂)
  | andI φ ψ =>
    intro hφ hψ
    exact ⟨hφ, hψ⟩
  | andE1 φ ψ =>
    intro ⟨hφ, _⟩
    exact hφ
  | andE2 φ ψ =>
    intro ⟨_, hψ⟩
    exact hψ
  | orI1 φ ψ =>
    intro hφ
    exact Or.inl hφ
  | orI2 φ ψ =>
    intro hψ
    exact Or.inr hψ
  | orE φ ψ χ =>
    intro h₁ h₂ h₃
    exact h₃.elim h₁ h₂

/-! ## D4 Soundness Theorems -/

/-- D4 soundness: every derivable formula from context is valid over serial,
transitive models. -/
theorem d4_soundness {World : Type*}
    {Γ : List (Proposition Atom)} {φ : Proposition Atom}
    (d : DerivationTree (@D4Axiom Atom) Γ φ)
    (m : Model World Atom)
    (h_serial : Relation.Serial m.r)
    (h_trans : ∀ w₁ w₂ w₃, m.r w₁ w₂ → m.r w₂ w₃ → m.r w₁ w₃)
    (w : World)
    (h_ctx : ∀ ψ ∈ Γ, Satisfies m w ψ) : Satisfies m w φ :=
  soundness d m (fun _ h_ax w => d4_axiom_sound h_ax m h_serial h_trans w) w h_ctx

/-- D4 soundness for derivable formulas (empty context). -/
theorem d4_soundness_derivable {World : Type*}
    {φ : Proposition Atom} (h : Derivable (@D4Axiom Atom) φ)
    (m : Model World Atom)
    (h_serial : Relation.Serial m.r)
    (h_trans : ∀ w₁ w₂ w₃, m.r w₁ w₂ → m.r w₂ w₃ → m.r w₁ w₃)
    (w : World) : Satisfies m w φ :=
  soundness_derivable h m
    (fun _ h_ax w => d4_axiom_sound h_ax m h_serial h_trans w) w

end Cslib.Logic.Modal
