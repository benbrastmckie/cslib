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

/-! # Soundness Theorem for Modal Logic DB (KDB)

This module proves soundness for modal logic DB over serial + symmetric Kripke
frames. DB = K + D + B, combining the seriality axiom (D) with the symmetry
axiom (B), but without axiom T.

## Main Results

- `db_axiom_sound`: Each of the 7 DBAxiom schemata is valid over serial,
  symmetric frames.
- `db_soundness`: If `Gamma |- phi` via `DerivationTree DBAxiom`, then `phi` is
  satisfied at every world of every serial, symmetric model where `Gamma` is
  satisfied.
## References

* Blackburn, de Rijke, Venema, "Modal Logic" (2002), Definition 4.9, Table 4.1
* Cslib/Logics/Modal/Basic.lean -- `Satisfies.d` for semantic validity of D axiom
* Cslib/Logics/Modal/Basic.lean -- `Satisfies.b` for semantic validity of B axiom
-/

@[expose] public section

namespace Cslib.Logic.Modal

open Cslib.Logic

variable {Atom : Type*}

/-! ## DB Axiom Soundness -/

/-- Every axiom of DB is valid over serial, symmetric frames.

Routed through `unionSound`: `dbTags` carries two differentiators (`modalD`, `modalB`),
discharged by `h_serial`/`h_symm`; the 13 core-tag obligations discharge by `trivial`. -/
theorem db_axiom_sound {World : Type*} {φ : Proposition Atom}
    (h_ax : DBAxiom φ) (m : Model World Atom)
    (h_serial : Relation.Serial m.r)
    (h_symm : ∀ w₁ w₂, m.r w₁ w₂ → m.r w₂ w₁)
    (w : World) : Satisfies m w φ :=
  unionSound dbTags m (fun t ht => by fin_cases ht <;> trivial)
    (schemaUnion_dbTags_iff_DBAxiom.mpr h_ax) w


/-! ## DB Soundness Theorems -/

/-- DB soundness: every derivable formula from context is valid over serial,
symmetric models. -/
theorem db_soundness {World : Type*}
    {Γ : List (Proposition Atom)} {φ : Proposition Atom}
    (d : DerivationTree (@DBAxiom Atom) Γ φ)
    (m : Model World Atom)
    (h_serial : Relation.Serial m.r)
    (h_symm : ∀ w₁ w₂, m.r w₁ w₂ → m.r w₂ w₁)
    (w : World)
    (h_ctx : ∀ ψ ∈ Γ, Satisfies m w ψ) : Satisfies m w φ :=
  soundness d m (fun _ h_ax w => db_axiom_sound h_ax m h_serial h_symm w) w h_ctx

end Cslib.Logic.Modal
