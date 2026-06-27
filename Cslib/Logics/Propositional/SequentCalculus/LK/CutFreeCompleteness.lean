/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

import Cslib.Init
public import Cslib.Logics.Propositional.SequentCalculus.LK.CutElimination
public import Cslib.Logics.Propositional.SequentCalculus.LK.Completeness

/-! # Cut-Free Completeness of LK for Classical Propositional Logic

This module combines LK completeness (`lk_iff_tautology`) with Gentzen's Hauptsatz
(`LKProof.cutElim`) to give a direct cut-free completeness result: every tautology has a
cut-free LK proof.

References:
* [G. Gentzen, *Untersuchungen über das logische Schließen*][Gentzen1935], §3
* [S. Negri, J. von Plato, *Structural Proof Theory*][NegriVonPlato2001], Ch. 3 -/

@[expose] public section

universe u

namespace Cslib.Logic.PL

variable {Atom : Type u} [DecidableEq Atom]

/-- Every classical propositional tautology has a cut-free LK proof (cut-free completeness).

This is the composition of `lk_iff_tautology.mp` (completeness: tautology → LK proof) and
`LKProof.cutElim` (Gentzen's Hauptsatz: every LK proof can be transformed into a cut-free
LK proof). -/
theorem lkCutFreeCompleteness {φ : Proposition Atom} (h : Tautology φ) :
    Nonempty (CutFreeLKProof (∅ ⊢ₛ ({φ} : Finset _))) :=
  let ⟨d⟩ := lk_iff_tautology.mp h
  d.cutElim

/-- A formula is a tautology if and only if it has a cut-free LK proof from the empty context.

This strengthens `lk_iff_tautology` by replacing ordinary LK proofs with cut-free proofs in
the forward direction. The backward direction follows because any cut-free LK proof is in
particular an LK proof. -/
theorem lkCutFreeIffTautology {φ : Proposition Atom} :
    Tautology φ ↔ Nonempty (CutFreeLKProof (∅ ⊢ₛ ({φ} : Finset _))) :=
  ⟨lkCutFreeCompleteness, fun ⟨d⟩ => lk_iff_tautology.mpr ⟨d.val⟩⟩

end Cslib.Logic.PL

end
