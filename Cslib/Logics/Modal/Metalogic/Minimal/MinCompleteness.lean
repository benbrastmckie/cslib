/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

import Cslib.Init
public import Cslib.Logics.Modal.Metalogic.Minimal.MinExtension
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
Instantiation of the `Axioms`-generic `mkvalidFC_completeness` at `Axioms := MKModalAxiom` and the
trivial frame condition `FC := (fun {_} _ => True)`: `h_canonFC` is discharged by `trivial` (the
trivial `FC` holds of any relation), and the `MValid` hypothesis is converted to `MValidFC`-form
via `mvalid_iff_mvalidFC_true`. The 12 anonymous-constructor lambdas supply `MKModalAxiom`'s 12
core schemata (`.implyK` … `.idb`), mirroring `mt_completeness`'s instantiation
(`MT.lean`). -/
theorem mk_completeness {φ : Proposition Atom} (h_valid : MValid.{u, u} φ) :
    Derivable MKModalAxiom φ :=
  mkvalidFC_completeness (fun {_} _ => True)
    (fun φ ψ => .implyK φ ψ) (fun φ ψ χ => .implyS φ ψ χ)
    (fun φ ψ => .andI φ ψ) (fun φ ψ => .andE1 φ ψ) (fun φ ψ => .andE2 φ ψ)
    (fun φ ψ => .orI1 φ ψ) (fun φ ψ => .orI2 φ ψ) (fun φ ψ χ => .orE φ ψ χ)
    (fun φ ψ => .k φ ψ) (fun φ ψ => .kdia φ ψ) (fun φ ψ => .cd φ ψ) (fun φ ψ => .idb φ ψ)
    trivial
    (mvalid_iff_mvalidFC_true.mp h_valid)

/-- **Soundness-completeness biconditional for `MK`**: `φ` is `MValid` iff `φ` is derivable
from `MKModalAxiom`. -/
theorem mk_soundness_completeness {φ : Proposition Atom} :
    MValid.{u, u} φ ↔ Derivable MKModalAxiom φ :=
  ⟨mk_completeness, mk_soundness_derivable⟩

end Cslib.Logic.Modal
