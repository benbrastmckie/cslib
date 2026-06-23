/-
Copyright (c) 2026 Fabrizio Montesi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi
-/

module

public import Cslib.Init

/-! # Inference Systems

This module defines the core abstractions for inference systems in CSLib.

## Key Definitions

- `InferenceSystem S α`: A typeclass that associates a tag type `S` with a derivation functor
  over a value type `α`. The notation `S⇓a` represents a derivation of `a` in system `S`.
- `InferenceSystem.Default`: An opaque tag used as the canonical inference system for types
  that carry a single natural notion of derivability.
- `HasInferenceSystem`: An abbreviation for `InferenceSystem Default`, enabling the shorthand
  notation `⇓a` when only one inference system is in scope.
- `DerivableIn S a`: A proposition asserting that `a` is derivable in `S`; defined as
  `Nonempty (S⇓a)` to avoid computational content in proof terms.
- `Derivable a`: Shorthand for `DerivableIn Default a`.

## Notation

- `S⇓a`: A derivation of `a` in system `S` (scoped notation).
- `⇓a`: A derivation of `a` in the default system (scoped notation).
-/

@[expose] public section

namespace Cslib.Logic

/--
The notation typeclass for inference systems.
This enables the notation `S⇓a`, where `S` is a tag for the inference system and `a : α`
is a derivable value.
-/
class InferenceSystem (S : Type*) (α : Type*) where
  /--
  `S⇓a` is a derivation of `a`, that is, a witness that `a` is derivable in the system `S`.
  The meaning of this notation is type-dependent.
  -/
  derivation (a : α) : Sort v

/-- Default tag for inference system instances. `⇓a` is short for `Default⇓a`. -/
opaque InferenceSystem.Default : Type := Empty

/-- Class for types (`α`) that have a canonical inference system. -/
abbrev HasInferenceSystem := InferenceSystem InferenceSystem.Default

namespace InferenceSystem

@[inherit_doc] scoped notation S:90 "⇓" a:90 => InferenceSystem.derivation S a

/-- Rewrites the conclusion of a proof into an equal one. -/
@[scoped grind =]
def rwConclusion [InferenceSystem S α] {Γ Δ : α} (h : Γ = Δ) (p : S⇓Γ) : S⇓Δ :=
  h ▸ p

/-- `a` is derivable in `S` if it is the conclusion of some derivation. -/
def DerivableIn S [InferenceSystem S α] (a : α) := Nonempty (S⇓a)

/-- `a : α` is derivable in the default inference system for `α`. -/
abbrev Derivable [InferenceSystem Default α] := DerivableIn Default (α := α)

/-- Shows derivability from a derivation. -/
theorem DerivableIn.fromDerivation [InferenceSystem S α] {a : α} (d : S⇓a) : DerivableIn S a :=
  Nonempty.intro d

/-- Coercion from a derivation `S⇓a` to `DerivableIn S a`. Wraps `DerivableIn.fromDerivation`. -/
instance [InferenceSystem S α] {a : α} : Coe (S⇓a) (DerivableIn S a) := ⟨DerivableIn.fromDerivation⟩

/-- Extracts (noncomputably) a derivation from the fact that a conclusion is derivable. -/
noncomputable def DerivableIn.toDerivation [InferenceSystem S α] {a : α} (d : DerivableIn S a) :
    S⇓a :=
  Classical.choice d

/-- Noncomputable coercion from `DerivableIn S a` to `S⇓a`, extracting a derivation via
`Classical.choice`. Wraps `DerivableIn.toDerivation`. -/
noncomputable instance [InferenceSystem S α] {a : α} : Coe (DerivableIn S a) (S⇓a) :=
  ⟨DerivableIn.toDerivation⟩

@[inherit_doc] scoped notation "⇓" a:90 => InferenceSystem.derivation Default a

end InferenceSystem

end Cslib.Logic
