/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Modal.Metalogic.Soundness
public import Cslib.Logics.Modal.ProofSystem.Instances

/-! # Soundness Theorem for Modal Logic K45

This module proves soundness for modal logic K45 (= K + 4 + 5): every formula derivable
from `K45Axiom` is valid on transitive, Euclidean frames.

K45 has 7 axiom schemata -- the same as S4 but with axiom 5 (`◇φ → □◇φ`) replacing
axiom T (`□φ → φ`). The frame class for K45 is transitive + Euclidean
(Blackburn et al. Table 4.1, p.195).

## Main Results

- `k45_axiom_sound`: Each of the 7 K45 axiom schemata is valid over transitive,
  Euclidean frames (Blackburn Definition 4.9, Table 4.1).
- `k45_soundness`: If `Gamma |- phi` via `DerivationTree K45Axiom`, then `phi` is
  satisfied at every world where all of `Gamma` is satisfied, on transitive,
  Euclidean frames.
## References

* Blackburn, de Rijke, Venema - Modal Logic (Ch. 4, Definition 4.9, Table 4.1)
* Cslib/Logics/Modal/Metalogic/Soundness.lean -- parameterized soundness theorem
-/

@[expose] public section

namespace Cslib.Logic.Modal

open Cslib.Logic

variable {Atom : Type*}

/-! ## K45 Axiom Soundness (BRV Definition 4.9 for K45) -/

/-- Every axiom of K45 is valid over transitive, Euclidean frames.

Axiom 4 (`□φ → □□φ`) uses transitivity (Blackburn Theorem 4.27);
axiom 5 (`◇φ → □◇φ`) uses Euclideanness (Blackburn Table 4.1).
Propositional axioms and K are valid on all frames. -/
theorem k45_axiom_sound {World : Type*} {φ : Proposition Atom}
    (h_ax : K45Axiom φ) (m : Model World Atom)
    (h_trans : ∀ w₁ w₂ w₃, m.r w₁ w₂ → m.r w₂ w₃ → m.r w₁ w₃)
    (h_eucl : ∀ w₁ w₂ w₃, m.r w₁ w₂ → m.r w₁ w₃ → m.r w₂ w₃)
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
  | modalFive φ =>
    intro hdiam v hrv hbox_neg_v
    apply hdiam
    intro u hru hsat
    exact hbox_neg_v u (h_eucl w v u hrv hru) hsat
  | andI φ ψ => exact Satisfies.andI_axiom m w φ ψ
  | andE1 φ ψ => exact Satisfies.andE1_axiom m w φ ψ
  | andE2 φ ψ => exact Satisfies.andE2_axiom m w φ ψ
  | orI1 φ ψ => exact Satisfies.orI1_axiom m w φ ψ
  | orI2 φ ψ => exact Satisfies.orI2_axiom m w φ ψ
  | orE φ ψ χ => exact Satisfies.orE_axiom m w φ ψ χ
  | diaDualityFwd φ => exact Satisfies.diaDualityFwd_axiom m w φ
  | diaDualityBack φ => exact Satisfies.diaDualityBack_axiom m w φ


/-! ## K45 Soundness Theorems -/

/-- **K45 Soundness**: If `Gamma |- phi` via `DerivationTree K45Axiom`, then `phi` is
satisfied at every world where all of `Gamma` is satisfied, on transitive,
Euclidean frames. -/
theorem k45_soundness {World : Type*}
    {Γ : List (Proposition Atom)} {φ : Proposition Atom}
    (d : DerivationTree (@K45Axiom Atom) Γ φ)
    (m : Model World Atom)
    (h_trans : ∀ w₁ w₂ w₃, m.r w₁ w₂ → m.r w₂ w₃ → m.r w₁ w₃)
    (h_eucl : ∀ w₁ w₂ w₃, m.r w₁ w₂ → m.r w₁ w₃ → m.r w₂ w₃)
    (w : World)
    (h_ctx : ∀ ψ ∈ Γ, Satisfies m w ψ) : Satisfies m w φ :=
  soundness d m (fun _ h_ax w => k45_axiom_sound h_ax m h_trans h_eucl w) w h_ctx

end Cslib.Logic.Modal
