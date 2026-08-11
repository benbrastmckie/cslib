/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Propositional.SequentCalculus.LJ.CutElimination
public import Cslib.Logics.Propositional.SequentCalculus.LJ.Completeness

/-! # Cut-Free Completeness of LJ for Intuitionistic Propositional Logic

This module combines LJ completeness (`lj_iff_ivalid`) with Gentzen's Hauptsatz
(`LJProof.cutElim`) to give a direct cut-free completeness result: every intuitionistically
valid formula has a cut-free LJ proof.

Mirrors `LK/CutFreeCompleteness.lean`'s `lkCutFreeCompleteness` / `lkCutFreeIffTautology`, with
one difference: `lj_iff_ivalid` carries an explicit `IValid.{u, u}` universe pin, which is
carried through both statements here rather than erased.

References:
* [G. Gentzen, *Untersuchungen über das logische Schließen*][Gentzen1935], §3
* [S. Negri, J. von Plato, *Structural Proof Theory*][NegriVonPlato2001], Ch. 3 -/

@[expose] public section

universe u

namespace Cslib.Logic.PL

variable {Atom : Type u} [DecidableEq Atom]

/-- Every intuitionistically valid formula has a cut-free LJ proof (cut-free completeness).

This is the composition of `lj_iff_ivalid.mp` (completeness: `IValid.{u, u} φ` → LJ proof) and
`LJProof.cutElim` (Gentzen's Hauptsatz: every LJ proof can be transformed into a cut-free
LJ proof). -/
theorem ljCutFreeCompleteness {φ : Proposition Atom} (h : IValid.{u, u} φ) :
    Nonempty (CutFreeLJProof (∅ ⊢ φ)) :=
  let ⟨d⟩ := lj_iff_ivalid.mp h
  d.cutElim

/-- A formula is intuitionistically valid if and only if it has a cut-free LJ proof from the
empty context.

This strengthens `lj_iff_ivalid` by replacing ordinary LJ proofs with cut-free proofs in the
forward direction. The backward direction follows because any cut-free LJ proof is in
particular an LJ proof. -/
theorem ljCutFreeIffIValid {φ : Proposition Atom} :
    IValid.{u, u} φ ↔ Nonempty (CutFreeLJProof (∅ ⊢ φ)) :=
  ⟨ljCutFreeCompleteness, fun ⟨d⟩ => lj_iff_ivalid.mpr ⟨d.val⟩⟩

end Cslib.Logic.PL

end
