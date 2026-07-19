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

Routed through `unionSound`: `k45Tags` carries two differentiators (`modalFour`,
`modalFive`), discharged by `h_trans`/`h_eucl`; the 13 core-tag obligations discharge by
`trivial`. -/
theorem k45_axiom_sound {World : Type*} {φ : Proposition Atom}
    (h_ax : K45Axiom φ) (m : Model World Atom)
    (h_trans : ∀ w₁ w₂ w₃, m.r w₁ w₂ → m.r w₂ w₃ → m.r w₁ w₃)
    (h_eucl : ∀ w₁ w₂ w₃, m.r w₁ w₂ → m.r w₁ w₃ → m.r w₂ w₃)
    (w : World) : Satisfies m w φ :=
  unionSound k45Tags m (fun t ht => by fin_cases ht <;> trivial)
    h_ax w


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
