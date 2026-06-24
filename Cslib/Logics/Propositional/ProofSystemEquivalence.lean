/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

import Cslib.Init
public import Cslib.Logics.Propositional.SequentCalculus.LK.Completeness
public import Cslib.Logics.Propositional.SequentCalculus.LJ.Completeness
public import Mathlib.Data.List.TFAE
import Mathlib.Tactic.TFAE

@[expose] public section

/-! # Proof System Equivalences for Propositional Logic

This module collects three-way equivalences between the Hilbert-style proof system,
natural deduction (ND), and sequent calculus for classical (CPL) and intuitionistic (IPL)
propositional logic, stated as `List.TFAE` theorems. For minimal logic (MPL), only a
two-way Hilbert–ND equivalence is available (no minimal sequent calculus exists in CSLib).

## Main Results

- `cplProofSystemsTfae`: CPL three-way equivalence (Hilbert, ND, LK), context-based.
- `cplProofSystemsTfaeClosed`: CPL three-way equivalence at the empty context.
- `iplProofSystemsTfae`: IPL three-way equivalence (Hilbert, ND, LJ), context-based.
- `iplProofSystemsTfaeClosed`: IPL three-way equivalence at the empty context.
- `mplHilbertIffNd`: MPL two-way equivalence (Hilbert ↔ ND), context-based.

## Dependencies

The proofs are purely compositional, relying on existing bridge theorems:
- `hilbert_iff_nd_ctx_cl`, `nd_iff_lk` (LK completeness)
- `hilbert_iff_nd_ctx_int`, `nd_iff_lj` (LJ completeness)
- `hilbert_iff_nd_ctx_min` (ND equivalence)
-/

namespace Cslib.Logic.PL

open InferenceSystem

variable {Atom : Type*} [DecidableEq Atom]

/-! ## Classical Propositional Logic (CPL) -/

/-- **CPL Three-Way Equivalence** (context-based): For any context `Γ` and formula `φ`,
the following are equivalent:
1. Hilbert derivability: `Deriv PropositionalAxiom Γ.toList φ`
2. ND derivability: `DerivableIn (AxiomTheory PropositionalAxiom) (Γ ⊢ φ)`
3. LK provability: `Nonempty (LKProof (Γ ⊢ₛ {φ}))`

Proved by composing `hilbert_iff_nd_ctx_cl` (1 ↔ 2) and `nd_iff_lk` (2 ↔ 3). -/
theorem cplProofSystemsTfae (Γ : Ctx Atom) (φ : PL.Proposition Atom) :
    [Deriv PropositionalAxiom Γ.toList φ,
     DerivableIn (AxiomTheory (@PropositionalAxiom Atom) : Theory Atom) (Γ ⊢ φ),
     Nonempty (LKProof (Γ ⊢ₛ ({φ} : Finset _)))].TFAE := by
  tfae_have 1 ↔ 2 := hilbert_iff_nd_ctx_cl
  tfae_have 2 ↔ 3 := nd_iff_lk
  tfae_finish

/-- **CPL Three-Way Equivalence** (closed): At the empty context, the following are equivalent:
1. Hilbert derivability: `Derivable PropositionalAxiom φ`
2. ND derivability: `DerivableIn (AxiomTheory PropositionalAxiom) (∅ ⊢ φ)`
3. LK provability: `Nonempty (LKProof (∅ ⊢ₛ {φ}))`

Obtained from `cplProofSystemsTfae` at `Γ = ∅` via `Finset.toList_empty`. -/
theorem cplProofSystemsTfaeClosed (φ : PL.Proposition Atom) :
    [Derivable PropositionalAxiom φ,
     DerivableIn (AxiomTheory (@PropositionalAxiom Atom) : Theory Atom)
       ((∅ : Ctx Atom) ⊢ φ),
     Nonempty (LKProof ((∅ : Ctx Atom) ⊢ₛ ({φ} : Finset _)))].TFAE := by
  have h := cplProofSystemsTfae (∅ : Ctx Atom) φ
  simp only [Finset.toList_empty] at h
  exact h

/-! ## Intuitionistic Propositional Logic (IPL) -/

/-- **IPL Three-Way Equivalence** (context-based): For any context `Γ` and formula `φ`,
the following are equivalent:
1. Hilbert derivability: `Deriv IntPropAxiom Γ.toList φ`
2. ND derivability: `DerivableIn (AxiomTheory IntPropAxiom) (Γ ⊢ φ)`
3. LJ provability: `Nonempty (LJProof (Γ ⊢ φ))`

Proved by composing `hilbert_iff_nd_ctx_int` (1 ↔ 2) and `nd_iff_lj` (2 ↔ 3). -/
theorem iplProofSystemsTfae (Γ : Ctx Atom) (φ : PL.Proposition Atom) :
    [Deriv IntPropAxiom Γ.toList φ,
     DerivableIn (AxiomTheory (@IntPropAxiom Atom) : Theory Atom) (Γ ⊢ φ),
     Nonempty (LJProof (Γ ⊢ φ))].TFAE := by
  tfae_have 1 ↔ 2 := hilbert_iff_nd_ctx_int
  tfae_have 2 ↔ 3 := nd_iff_lj
  tfae_finish

/-- **IPL Three-Way Equivalence** (closed): At the empty context, the following are equivalent:
1. Hilbert derivability: `Derivable IntPropAxiom φ`
2. ND derivability: `DerivableIn (AxiomTheory IntPropAxiom) (∅ ⊢ φ)`
3. LJ provability: `Nonempty (LJProof (∅ ⊢ φ))`

Obtained from `iplProofSystemsTfae` at `Γ = ∅` via `Finset.toList_empty`. -/
theorem iplProofSystemsTfaeClosed (φ : PL.Proposition Atom) :
    [Derivable IntPropAxiom φ,
     DerivableIn (AxiomTheory (@IntPropAxiom Atom) : Theory Atom)
       ((∅ : Ctx Atom) ⊢ φ),
     Nonempty (LJProof ((∅ : Ctx Atom) ⊢ φ))].TFAE := by
  have h := iplProofSystemsTfae (∅ : Ctx Atom) φ
  simp only [Finset.toList_empty] at h
  exact h

/-! ## Minimal Propositional Logic (MPL) -/

/-- **MPL Two-Way Equivalence** (context-based): For any context `Γ` and formula `φ`,
Hilbert derivability with `MinPropAxiom` from `Γ.toList` is equivalent to ND derivability
under `AxiomTheory MinPropAxiom` from `Γ`.

No minimal sequent calculus (LM) exists in CSLib, so only a two-way equivalence is available.
This re-exports `hilbert_iff_nd_ctx_min` for discoverability. -/
theorem mplHilbertIffNd {Γ : Ctx Atom} {φ : PL.Proposition Atom} :
    Deriv MinPropAxiom Γ.toList φ ↔
    DerivableIn (AxiomTheory (@MinPropAxiom Atom) : Theory Atom) (Γ ⊢ φ) :=
  hilbert_iff_nd_ctx_min

end Cslib.Logic.PL

end
