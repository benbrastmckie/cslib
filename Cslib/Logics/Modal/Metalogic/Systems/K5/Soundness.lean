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
- `k5_soundness_derivable`: Soundness for derivable formulas (empty context).

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
  | modalFive φ =>
    intro h_diam w' hr h_box_neg_w'
    exact h_diam (fun w'' hr' h_phi =>
      h_box_neg_w' w'' (h_eucl w w' w'' hr hr') h_phi)

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

/-- K5 soundness for derivable formulas (empty context). -/
theorem k5_soundness_derivable {World : Type*}
    {φ : Proposition Atom} (h : Derivable (@K5Axiom Atom) φ)
    (m : Model World Atom)
    (h_eucl : ∀ w₁ w₂ w₃, m.r w₁ w₂ → m.r w₁ w₃ → m.r w₂ w₃)
    (w : World) : Satisfies m w φ :=
  soundness_derivable h m (fun _ h_ax w => k5_axiom_sound h_ax m h_eucl w) w

end Cslib.Logic.Modal
