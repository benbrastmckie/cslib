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

/-- Every axiom of D4 is valid over serial, transitive frames.

Routed through `unionSound`: `d4Tags` carries two differentiators (`modalD`, `modalFour`),
discharged by `h_serial`/`h_trans`; the 13 core-tag obligations discharge by `trivial`. -/
theorem d4_axiom_sound {World : Type*} {φ : Proposition Atom}
    (h_ax : D4Axiom φ) (m : Model World Atom)
    (h_serial : Relation.Serial m.r)
    (h_trans : ∀ w₁ w₂ w₃, m.r w₁ w₂ → m.r w₂ w₃ → m.r w₁ w₃)
    (w : World) : Satisfies m w φ :=
  unionSound d4Tags m (fun t ht => by fin_cases ht <;> trivial)
    h_ax w


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

end Cslib.Logic.Modal
