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

/-! # Soundness Theorem for Modal Logic T

This module proves soundness for modal logic T: every formula derivable from
`TAxiom` is valid on reflexive frames.

## Main Results

- `t_axiom_sound`: Each of the 6 T axiom schemata is valid over reflexive frames.
- `t_soundness`: If `Gamma |- phi` via `DerivationTree TAxiom`, then `phi` is
  satisfied at every world of every reflexive model where all of `Gamma` is satisfied.
## References

* Blackburn, de Rijke, Venema - Modal Logic (Ch. 4, Definition 4.9, Table 4.1)
* Cslib/Logics/Modal/Metalogic/Soundness.lean -- parameterized soundness theorem
-/

@[expose] public section

namespace Cslib.Logic.Modal

open Cslib.Logic

variable {Atom : Type*}

/-! ## T Axiom Soundness (BRV Definition 4.9 for T) -/

/-- Every axiom of T is valid over reflexive frames.

Routed through `unionSound`: `tTags` carries exactly one differentiator (`modalT`), discharged
by `h_refl`; the 13 core-tag obligations discharge by `trivial`. -/
theorem t_axiom_sound {World : Type*} {φ : Proposition Atom}
    (h_ax : TAxiom φ) (m : Model World Atom)
    (h_refl : ∀ w, m.r w w)
    (w : World) : Satisfies m w φ :=
  unionSound tTags m (fun t ht => by fin_cases ht <;> trivial)
    (schemaUnion_tTags_iff_TAxiom.mpr h_ax) w


/-! ## T Soundness Theorems -/

/-- **T Soundness**: If `Gamma |- phi` via `DerivationTree TAxiom`, then `phi` is
satisfied at every world of every reflexive model where all of `Gamma` is satisfied. -/
theorem t_soundness {World : Type*}
    {Γ : List (Proposition Atom)} {φ : Proposition Atom}
    (d : DerivationTree (@TAxiom Atom) Γ φ)
    (m : Model World Atom)
    (h_refl : ∀ w, m.r w w)
    (w : World)
    (h_ctx : ∀ ψ ∈ Γ, Satisfies m w ψ) : Satisfies m w φ :=
  soundness d m (fun _ h_ax w => t_axiom_sound h_ax m h_refl w) w h_ctx

end Cslib.Logic.Modal
