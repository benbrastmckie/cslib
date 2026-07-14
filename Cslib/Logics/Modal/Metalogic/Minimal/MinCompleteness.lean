/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

import Cslib.Init
public import Cslib.Logics.Modal.Metalogic.Minimal.MinTruthLemma
public import Cslib.Logics.Modal.Metalogic.Minimal.MK

/-! # Completeness of `MK`

This module proves `mk_completeness` (any `MValid` formula is derivable from `MKModalAxiom`)
and packages the soundness-completeness biconditional `mk_soundness_completeness`.

Unlike `IK`'s `ivalid_completeness`/`mvalid_completeness` (`Intuitionistic/Completeness.lean`),
which `by_cases` on the consistency of `cl ∅` and use `efq` in the inconsistent branch, `MK`
completeness is **single-branch**: quasi-prime worlds carry no consistency predicate, so there
is no inconsistent case to split on. The contrapositive proof extends `cl ∅` directly by
`quasi_prime_exclusion` (via `min_head_realization`), exactly as the propositional
`min_strong_completeness` (`MinStrongCompleteness.lean`) does at `Γ = ∅`.

## Main Definitions

- `mk_completeness`: `MValid φ → Derivable MKModalAxiom φ`.
- `mk_soundness_completeness`: `MValid φ ↔ Derivable MKModalAxiom φ`.

## References

* [A. K. Simpson, *The Proof Theory and Semantics of Intuitionistic Modal Logic*][Simpson1994],
  Chapter 3.
* [A. Chagrov, M. Zakharyaschev, *Modal Logic*][ChagrovZakharyaschev1997], Theorem 2.43.
-/

@[expose] public section

namespace Cslib.Logic.Modal

open Cslib.Logic

universe u

variable {Atom : Type u}

/-! ## Completeness -/

/-- **Completeness for `MK`**: any `MValid` formula is derivable from `MKModalAxiom`.
Single-branch (no consistency case split, `Role C` of the research report's `efq` analysis):
by contrapositive, `min_head_realization` extends `cl ∅` to a quasi-prime theory `T` omitting
`φ`; instantiate `MValid` at the canonical model (`canonicalR`, `min_canonical_f1`/
`min_canonical_f2`, `canonicalVal`, `minBotForces`) rooted at `⟨T, hT⟩`, apply
`min_canonical_truth_lemma`, and contradict `φ ∉ T`. -/
theorem mk_completeness {φ : Proposition Atom} (h_valid : MValid.{u, u} φ) :
    Derivable MKModalAxiom φ := by
  by_contra h_not_deriv
  obtain ⟨T, hT_qp, hT_excl⟩ := min_head_realization h_not_deriv
  let w0 : MinCanonicalPrimeWorld Atom := ⟨T, hT_qp⟩
  have h_forces : BForces canonicalR canonicalVal minBotForces w0 φ :=
    h_valid (MinCanonicalPrimeWorld Atom) canonicalR
      (fun {w w' v} hww' hwv => min_canonical_f1 hww' hwv)
      (fun {w v v'} hwv hvv' => min_canonical_f2 hwv hvv')
      canonicalVal minBotForces
      (fun {_ _} p hw hv => canonicalVal_upward_closed p hw hv)
      (fun {_ _} hw hbf => minBotForces_upward_closed hw hbf) w0
  exact hT_excl ((min_canonical_truth_lemma φ w0).mp h_forces)

/-- **Soundness-completeness biconditional for `MK`**: `φ` is `MValid` iff `φ` is derivable
from `MKModalAxiom`. -/
theorem mk_soundness_completeness {φ : Proposition Atom} :
    MValid.{u, u} φ ↔ Derivable MKModalAxiom φ :=
  ⟨mk_completeness, mk_soundness_derivable⟩

end Cslib.Logic.Modal
