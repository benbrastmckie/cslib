/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Modal.Metalogic.Soundness
public import Cslib.Logics.Modal.Metalogic.SchemaSoundness
public import Mathlib.Tactic.FinCases

/-! # Soundness Theorem for Modal Logic S5

This module proves soundness for modal logic S5: every formula derivable from
`S5Axiom` is valid on S5 frames (reflexive, transitive, Euclidean).

## Main Results

- `s5_axiom_sound`: Each of the 8 S5 axiom schemata is valid over S5 frames.
- `s5_soundness`: If `Gamma |- phi` via `DerivationTree S5Axiom`, then `phi` is
  satisfied at every world of every S5 model where all of `Gamma` is satisfied.
## References

* Blackburn, de Rijke, Venema - Modal Logic (Ch. 4, Definition 4.9)
* Cslib/Logics/Modal/Metalogic/Soundness.lean -- parameterized soundness theorem
-/

@[expose] public section

namespace Cslib.Logic.Modal

open Cslib.Logic

variable {Atom : Type*}

/-! ## S5 Axiom Soundness -/

/-- Every axiom of S5 is valid over S5 frames (reflexive, transitive, Euclidean).

Routed through `unionSound`: `s5Tags` carries three differentiators (`modalT`, `modalFour`,
`modalB`). `modalT`/`modalFour` discharge directly from `h_refl`/`h_trans`; `modalB`
(symmetry) is not a direct hypothesis here (S5 = T+4+B, not T+4+B+5, so no `h_symm` parameter
exists) — it is derived from `h_refl` and `h_eucl` inline (`m.r w₂ w₁` from `m.r w₁ w₂` via
Euclideanness at `w₁, w₂, w₁` with the reflexivity witness `m.r w₁ w₁`). -/
theorem s5_axiom_sound {World : Type*} {φ : Proposition Atom}
    (h_ax : S5Axiom φ) (m : Model World Atom)
    (h_refl : ∀ w, m.r w w)
    (h_trans : ∀ w₁ w₂ w₃, m.r w₁ w₂ → m.r w₂ w₃ → m.r w₁ w₃)
    (h_eucl : ∀ w₁ w₂ w₃, m.r w₁ w₂ → m.r w₁ w₃ → m.r w₂ w₃)
    (w : World) : Satisfies m w φ :=
  have h_symm : ∀ w₁ w₂, m.r w₁ w₂ → m.r w₂ w₁ :=
    fun w₁ w₂ hr => h_eucl w₁ w₂ w₁ hr (h_refl w₁)
  unionSound s5Tags m (fun t ht => by fin_cases ht <;> trivial)
    h_ax w


/-! ## S5 Soundness Theorems -/

/-- **S5 Soundness**: If `Gamma |- phi` via `DerivationTree S5Axiom`, then `phi` is
satisfied at every world of every S5 model where all of `Gamma` is satisfied. -/
theorem s5_soundness {World : Type*}
    {Γ : List (Proposition Atom)} {φ : Proposition Atom}
    (d : DerivationTree (@S5Axiom Atom) Γ φ)
    (m : Model World Atom)
    (h_refl : ∀ w, m.r w w)
    (h_trans : ∀ w₁ w₂ w₃, m.r w₁ w₂ → m.r w₂ w₃ → m.r w₁ w₃)
    (h_eucl : ∀ w₁ w₂ w₃, m.r w₁ w₂ → m.r w₁ w₃ → m.r w₂ w₃)
    (w : World)
    (h_ctx : ∀ ψ ∈ Γ, Satisfies m w ψ) : Satisfies m w φ :=
  soundness d m (fun _ h_ax w => s5_axiom_sound h_ax m h_refl h_trans h_eucl w) w h_ctx

end Cslib.Logic.Modal
