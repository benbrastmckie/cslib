/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Modal.Metalogic.Soundness
public import Cslib.Logics.Modal.ProofSystem.Instances

/-! # Soundness Theorem for Modal Logic S4

This module proves soundness for modal logic S4 (= KT4): every formula derivable from
`S4Axiom` is valid on reflexive, transitive frames.

S4 has 7 axiom schemata -- the same as S5 minus the B axiom (`p → □◇p`).
The frame class for S4 is reflexive + transitive (Blackburn et al. Table 4.1, p.195).

## Main Results

- `s4_axiom_sound`: Each of the 7 S4 axiom schemata is valid over reflexive,
  transitive frames (Blackburn Definition 4.9, Table 4.1).
- `s4_soundness`: If `Gamma |- phi` via `DerivationTree S4Axiom`, then `phi` is
  satisfied at every world where all of `Gamma` is satisfied, on reflexive,
  transitive frames.
## References

* Blackburn, de Rijke, Venema - Modal Logic (Ch. 4, Definition 4.9, Table 4.1)
* Cslib/Logics/Modal/Metalogic/Soundness.lean -- parameterized soundness theorem
-/

@[expose] public section

namespace Cslib.Logic.Modal

open Cslib.Logic

variable {Atom : Type*}

/-! ## S4 Axiom Soundness (BRV Definition 4.9 for S4) -/

/-- Every axiom of S4 is valid over reflexive, transitive frames.

Axiom T (`□φ → φ`) uses reflexivity (Blackburn Theorem 4.28, clause 1);
axiom 4 (`□φ → □□φ`) uses transitivity (Blackburn Theorem 4.27).
Propositional axioms and K are valid on all frames. -/
theorem s4_axiom_sound {World : Type*} {φ : Proposition Atom}
    (h_ax : S4Axiom φ) (m : Model World Atom)
    (h_refl : ∀ w, m.r w w)
    (h_trans : ∀ w₁ w₂ w₃, m.r w₁ w₂ → m.r w₂ w₃ → m.r w₁ w₃)
    (w : World) : Satisfies m w φ := by
  cases h_ax with
  | implyK φ ψ => exact Satisfies.implyK_axiom m w φ ψ
  | implyS φ ψ χ => exact Satisfies.implyS_axiom m w φ ψ χ
  | efq φ => exact Satisfies.efq_axiom m w φ
  | peirce φ ψ => exact Satisfies.peirce_axiom m w φ ψ
  | modalK φ ψ => exact Satisfies.modalK_axiom m w φ ψ
  | modalT φ => exact Satisfies.modalT_axiom m h_refl w φ
  | modalFour φ => exact Satisfies.modalFour_axiom m h_trans w φ
  | andI φ ψ => exact Satisfies.andI_axiom m w φ ψ
  | andE1 φ ψ => exact Satisfies.andE1_axiom m w φ ψ
  | andE2 φ ψ => exact Satisfies.andE2_axiom m w φ ψ
  | orI1 φ ψ => exact Satisfies.orI1_axiom m w φ ψ
  | orI2 φ ψ => exact Satisfies.orI2_axiom m w φ ψ
  | orE φ ψ χ => exact Satisfies.orE_axiom m w φ ψ χ
  | diaDualityFwd φ => exact Satisfies.diaDualityFwd_axiom m w φ
  | diaDualityBack φ => exact Satisfies.diaDualityBack_axiom m w φ


/-! ## S4 Soundness Theorems -/

/-- **S4 Soundness**: If `Gamma |- phi` via `DerivationTree S4Axiom`, then `phi` is
satisfied at every world where all of `Gamma` is satisfied, on reflexive,
transitive frames. -/
theorem s4_soundness {World : Type*}
    {Γ : List (Proposition Atom)} {φ : Proposition Atom}
    (d : DerivationTree (@S4Axiom Atom) Γ φ)
    (m : Model World Atom)
    (h_refl : ∀ w, m.r w w)
    (h_trans : ∀ w₁ w₂ w₃, m.r w₁ w₂ → m.r w₂ w₃ → m.r w₁ w₃)
    (w : World)
    (h_ctx : ∀ ψ ∈ Γ, Satisfies m w ψ) : Satisfies m w φ :=
  soundness d m (fun _ h_ax w => s4_axiom_sound h_ax m h_refl h_trans w) w h_ctx

end Cslib.Logic.Modal
