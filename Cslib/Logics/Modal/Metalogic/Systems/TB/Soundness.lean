/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Modal.Metalogic.Soundness
public import Cslib.Logics.Modal.ProofSystem.Instances
public import Cslib.Logics.Modal.Metalogic.SchemaSoundness
public import Mathlib.Tactic.FinCases

/-! # Soundness Theorem for Modal Logic TB

This module proves soundness for modal logic TB (= KTB): every formula derivable from
`TBAxiom` is valid on reflexive, symmetric frames.

TB has 7 axiom schemata -- the same as S4 but with axiom B (`φ → □◇φ`) replacing
axiom 4 (`□φ → □□φ`). The frame class for TB is reflexive + symmetric
(Blackburn et al. Table 4.1).

## Main Results

- `tb_axiom_sound`: Each of the 7 TB axiom schemata is valid over reflexive,
  symmetric frames (Blackburn Definition 4.9, Table 4.1).
- `tb_soundness`: If `Gamma |- phi` via `DerivationTree TBAxiom`, then `phi` is
  satisfied at every world where all of `Gamma` is satisfied, on reflexive,
  symmetric frames.
## References

* Blackburn, de Rijke, Venema - Modal Logic (Ch. 4, Definition 4.9, Table 4.1)
* Cslib/Logics/Modal/Metalogic/Soundness.lean -- parameterized soundness theorem
-/

@[expose] public section

namespace Cslib.Logic.Modal

open Cslib.Logic

variable {Atom : Type*}

/-! ## TB Axiom Soundness (BRV Definition 4.9 for TB) -/

/-- Every axiom of TB is valid over reflexive, symmetric frames.

Routed through `unionSound`: `tbTags` carries two differentiators (`modalT`, `modalB`),
discharged by `h_refl`/`h_symm`; the 13 core-tag obligations discharge by `trivial`. -/
theorem tb_axiom_sound {World : Type*} {φ : Proposition Atom}
    (h_ax : TBAxiom φ) (m : Model World Atom)
    (h_refl : ∀ w, m.r w w)
    (h_symm : ∀ w₁ w₂, m.r w₁ w₂ → m.r w₂ w₁)
    (w : World) : Satisfies m w φ :=
  unionSound tbTags m (fun t ht => by fin_cases ht <;> trivial)
    h_ax w


/-! ## TB Soundness Theorems -/

/-- **TB Soundness**: If `Gamma |- phi` via `DerivationTree TBAxiom`, then `phi` is
satisfied at every world where all of `Gamma` is satisfied, on reflexive,
symmetric frames. -/
theorem tb_soundness {World : Type*}
    {Γ : List (Proposition Atom)} {φ : Proposition Atom}
    (d : DerivationTree (@TBAxiom Atom) Γ φ)
    (m : Model World Atom)
    (h_refl : ∀ w, m.r w w)
    (h_symm : ∀ w₁ w₂, m.r w₁ w₂ → m.r w₂ w₁)
    (w : World)
    (h_ctx : ∀ ψ ∈ Γ, Satisfies m w ψ) : Satisfies m w φ :=
  soundness d m (fun _ h_ax w => tb_axiom_sound h_ax m h_refl h_symm w) w h_ctx

end Cslib.Logic.Modal
