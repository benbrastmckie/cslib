/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Modal.Metalogic.Soundness
public import Cslib.Logics.Modal.ProofSystem.Instances
public import Cslib.Logics.Modal.Metalogic.SchemaSoundness
public import Cslib.Logics.Modal.ProofSystem.SchemaBridges
public import Mathlib.Tactic.FinCases

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

Routed through `unionSound`: `s4Tags` carries two differentiators (`modalT`, `modalFour`),
discharged by `h_refl`/`h_trans`; the 13 core-tag obligations discharge by `trivial`. -/
theorem s4_axiom_sound {World : Type*} {φ : Proposition Atom}
    (h_ax : S4Axiom φ) (m : Model World Atom)
    (h_refl : ∀ w, m.r w w)
    (h_trans : ∀ w₁ w₂ w₃, m.r w₁ w₂ → m.r w₂ w₃ → m.r w₁ w₃)
    (w : World) : Satisfies m w φ :=
  unionSound s4Tags m
    (fun t ht => by fin_cases ht <;> first | trivial | exact h_refl | exact h_trans)
    (schemaUnion_s4Tags_iff_S4Axiom.mpr h_ax) w


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
