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

/-! # Soundness Theorem for Modal Logic D45 (KD45)

This module proves soundness for modal logic D45 over serial + transitive +
Euclidean Kripke frames. D45 = K + D + 4 + 5, combining the seriality axiom (D)
with the transitivity axiom (4) and the Euclideanness axiom (5), but without
axiom T.

## Main Results

- `d45_axiom_sound`: Each of the 8 D45Axiom schemata is valid over serial,
  transitive, Euclidean frames.
- `d45_soundness`: If `Gamma |- phi` via `DerivationTree D45Axiom`, then `phi` is
  satisfied at every world of every serial, transitive, Euclidean model where
  `Gamma` is satisfied.
## References

* Blackburn, de Rijke, Venema, "Modal Logic" (2002), Definition 4.9, Table 4.1
* Cslib/Logics/Modal/Basic.lean -- `Satisfies.d` for semantic validity of D axiom
* Cslib/Logics/Modal/Basic.lean -- `Satisfies.four` for semantic validity of 4 axiom
* Cslib/Logics/Modal/Basic.lean -- `Satisfies.five` for semantic validity of 5 axiom
-/

@[expose] public section

namespace Cslib.Logic.Modal

open Cslib.Logic

variable {Atom : Type*}

/-! ## D45 Axiom Soundness -/

/-- Every axiom of D45 is valid over serial, transitive, Euclidean frames.

Routed through `unionSound`: `d45Tags` carries three differentiators (`modalD`, `modalFour`,
`modalFive`), discharged by `h_serial`/`h_trans`/`h_eucl`; the 13 core-tag obligations
discharge by `trivial`. -/
theorem d45_axiom_sound {World : Type*} {φ : Proposition Atom}
    (h_ax : D45Axiom φ) (m : Model World Atom)
    (h_serial : Relation.Serial m.r)
    (h_trans : ∀ w₁ w₂ w₃, m.r w₁ w₂ → m.r w₂ w₃ → m.r w₁ w₃)
    (h_eucl : ∀ w₁ w₂ w₃, m.r w₁ w₂ → m.r w₁ w₃ → m.r w₂ w₃)
    (w : World) : Satisfies m w φ :=
  unionSound d45Tags m (fun t ht => by fin_cases ht <;> trivial)
    h_ax w


/-! ## D45 Soundness Theorems -/

/-- D45 soundness: every derivable formula from context is valid over serial,
transitive, Euclidean models. -/
theorem d45_soundness {World : Type*}
    {Γ : List (Proposition Atom)} {φ : Proposition Atom}
    (d : DerivationTree (@D45Axiom Atom) Γ φ)
    (m : Model World Atom)
    (h_serial : Relation.Serial m.r)
    (h_trans : ∀ w₁ w₂ w₃, m.r w₁ w₂ → m.r w₂ w₃ → m.r w₁ w₃)
    (h_eucl : ∀ w₁ w₂ w₃, m.r w₁ w₂ → m.r w₁ w₃ → m.r w₂ w₃)
    (w : World)
    (h_ctx : ∀ ψ ∈ Γ, Satisfies m w ψ) : Satisfies m w φ :=
  soundness d m (fun _ h_ax w => d45_axiom_sound h_ax m h_serial h_trans h_eucl w) w h_ctx

end Cslib.Logic.Modal
