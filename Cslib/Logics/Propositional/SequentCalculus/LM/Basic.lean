/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

import Cslib.Init
public import Cslib.Logics.Propositional.SequentCalculus.LJ.Basic

/-! # Minimal Propositional Sequent Calculus LM

This file gives the mirror-symmetric surface name `LMProof` for the minimal-strength sequent
calculus, together with the key structural fact that the gated `botL` rule is unconstructible at
minimal strength.

The minimal sequent calculus is **not** a new rule inductive: it is `SeqProof` (defined generically
over a theory `T` in `LJ/Basic.lean`) instantiated at `T = MPL = ∅`. Since `MPL` admits no
`IsIntuitionistic` instance, the gated `botL` constructor is structurally unconstructible, so
`SeqProofMinimal := SeqProof MPL` is exactly "LJ minus ex falso" — the minimal calculus LM.

## Main Definitions

- `LMProof`: discoverability alias for `SeqProofMinimal` (`= SeqProof MPL`), mirroring the naming
  of `LJProof` (`= SeqProof IPL`).
- `not_isIntuitionistic_mpl`: `MPL` is not intuitionistic, so `botL` cannot be constructed at `MPL`.

## References

* [S. Negri, J. von Plato, *Structural Proof Theory*][NegriVonPlato2001], Ch. 3
-/

@[expose] public section

universe u

namespace Cslib.Logic.PL

open Proposition Theory

variable {Atom : Type u} [DecidableEq Atom]

/-- Minimal-strength single-conclusion sequent-calculus proof trees, the LM calculus. Mirror-
symmetric discoverability alias for `SeqProofMinimal := SeqProof MPL` (defined in `LJ/Basic.lean`).
Since `MPL` admits no `IsIntuitionistic` instance, the gated `botL` rule is structurally
unconstructible, so `LMProof` is exactly the `botL`-free minimal calculus. -/
abbrev LMProof (seq : @Sequent Atom) : Type u := SeqProofMinimal seq

omit [DecidableEq Atom] in
/-- The minimal theory `MPL = ∅` is not intuitionistic: it does not contain the explosion axiom
`⊥ → A` for every `A`. Consequently the gated `botL` constructor of `SeqProof MPL` (= `LMProof`)
is structurally unconstructible, since it requires an `IsIntuitionistic MPL` instance. -/
theorem not_isIntuitionistic_mpl : ¬ Theory.IsIntuitionistic (MPL : Theory Atom) := by
  intro h
  have := (Theory.isIntuitionisticIff (MPL : Theory Atom)).mp h
  have hmem : (⊥ → ⊥ : Proposition Atom) ∈ (Theory.IPL : Theory Atom) := ⟨⊥, rfl⟩
  exact absurd (this hmem) (by simp)

end Cslib.Logic.PL
