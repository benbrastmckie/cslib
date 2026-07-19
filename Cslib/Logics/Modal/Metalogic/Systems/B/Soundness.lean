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

/-! # Soundness Theorem for Modal Logic B (KB)

This module proves soundness for modal logic B over symmetric Kripke frames.

## Main Results

- `b_axiom_sound`: Each of the 6 BAxiom schemata is valid over symmetric frames.
- `b_soundness`: If `Gamma |- phi` via `DerivationTree BAxiom`, then `phi` is
  satisfied at every world of every symmetric model where `Gamma` is satisfied.
## References

* Blackburn, de Rijke, Venema, "Modal Logic" (2002), Definition 4.9, Table 4.1
* Cslib/Logics/Modal/Basic.lean -- `Satisfies.b` for semantic validity of B axiom
-/

@[expose] public section

namespace Cslib.Logic.Modal

open Cslib.Logic

variable {Atom : Type*}

/-! ## B Axiom Soundness -/

/-- Every axiom of B is valid over symmetric frames.

Routed through `unionSound`: `bTags` carries exactly one differentiator (`modalB`), discharged
by `h_symm`; the 13 core-tag obligations discharge by `trivial`. -/
theorem b_axiom_sound {World : Type*} {φ : Proposition Atom}
    (h_ax : BAxiom φ) (m : Model World Atom)
    (h_symm : ∀ w₁ w₂, m.r w₁ w₂ → m.r w₂ w₁)
    (w : World) : Satisfies m w φ :=
  unionSound bTags m (fun t ht => by fin_cases ht <;> trivial)
    (schemaUnion_bTags_iff_BAxiom.mpr h_ax) w


/-! ## B Soundness Theorems -/

/-- B soundness: every derivable formula from context is valid over symmetric models. -/
theorem b_soundness {World : Type*}
    {Γ : List (Proposition Atom)} {φ : Proposition Atom}
    (d : DerivationTree (@BAxiom Atom) Γ φ)
    (m : Model World Atom)
    (h_symm : ∀ w₁ w₂, m.r w₁ w₂ → m.r w₂ w₁)
    (w : World)
    (h_ctx : ∀ ψ ∈ Γ, Satisfies m w ψ) : Satisfies m w φ :=
  soundness d m (fun _ h_ax w => b_axiom_sound h_ax m h_symm w) w h_ctx

end Cslib.Logic.Modal
