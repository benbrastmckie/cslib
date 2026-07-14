/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Modal.Metalogic.Minimal.MK
public import Cslib.Logics.Modal.Metalogic.Minimal.MT
public import Cslib.Logics.Modal.Metalogic.Minimal.MS4
public import Cslib.Logics.Modal.Metalogic.Minimal.MS5

/-! # Axiom Subsumption Lemmas for the Minimal-Base Modal Cube

This module proves the three direct-edge axiom subsumption lemmas for the minimal-base
modal cube `MK → MT → MS4 → MS5`, mirroring the classical `AxiomSubsumption.lean`
template (`InterSystem/AxiomSubsumption.lean`). Each lemma is a mechanical `match`
case-split: every constructor of the weaker axiom predicate maps to the same-named
constructor of the stronger axiom predicate, since `MTModalAxiom`/`MS4ModalAxiom`/
`MS5ModalAxiom` are each defined as the previous rung's constructors verbatim plus new
ones (see `MT.lean`/`MS4.lean`/`MS5.lean` module docstrings).

**Framing**: these are same-language edges within the minimal propositional base, so the
converse is false (e.g. `MT` proves `□φ → φ`, which is not `MK`-derivable). The results
here and their `Derivable`-level corollaries in `MinimalLatticeMonotonicity.lean` are
**monotonicity**, not conservativity.

## Coverage

- `MKModalAxiom_implies_MTModalAxiom`
- `MTModalAxiom_implies_MS4ModalAxiom`
- `MS4ModalAxiom_implies_MS5ModalAxiom`
-/

@[expose] public section

namespace Cslib.Logic.Modal

variable {Atom : Type*}

/-- Every `MKModalAxiom` instance is an `MTModalAxiom` instance: `MT` extends `MK` by adding
the `tBox`/`tDia` schemata verbatim, leaving `MK`'s 12 constructors unchanged. -/
lemma MKModalAxiom_implies_MTModalAxiom {φ : Proposition Atom} (h : MKModalAxiom φ) :
    MTModalAxiom φ :=
  match h with
  | .implyK φ ψ => .implyK φ ψ
  | .implyS φ ψ χ => .implyS φ ψ χ
  | .andI φ ψ => .andI φ ψ
  | .andE1 φ ψ => .andE1 φ ψ
  | .andE2 φ ψ => .andE2 φ ψ
  | .orI1 φ ψ => .orI1 φ ψ
  | .orI2 φ ψ => .orI2 φ ψ
  | .orE φ ψ χ => .orE φ ψ χ
  | .k φ ψ => .k φ ψ
  | .kdia φ ψ => .kdia φ ψ
  | .cd φ ψ => .cd φ ψ
  | .idb φ ψ => .idb φ ψ

/-- Every `MTModalAxiom` instance is an `MS4ModalAxiom` instance: `MS4` extends `MT` by
adding the `fourBox`/`fourDia` schemata verbatim, leaving `MT`'s 14 constructors unchanged. -/
lemma MTModalAxiom_implies_MS4ModalAxiom {φ : Proposition Atom} (h : MTModalAxiom φ) :
    MS4ModalAxiom φ :=
  match h with
  | .implyK φ ψ => .implyK φ ψ
  | .implyS φ ψ χ => .implyS φ ψ χ
  | .andI φ ψ => .andI φ ψ
  | .andE1 φ ψ => .andE1 φ ψ
  | .andE2 φ ψ => .andE2 φ ψ
  | .orI1 φ ψ => .orI1 φ ψ
  | .orI2 φ ψ => .orI2 φ ψ
  | .orE φ ψ χ => .orE φ ψ χ
  | .k φ ψ => .k φ ψ
  | .kdia φ ψ => .kdia φ ψ
  | .cd φ ψ => .cd φ ψ
  | .idb φ ψ => .idb φ ψ
  | .tBox φ => .tBox φ
  | .tDia φ => .tDia φ

/-- Every `MS4ModalAxiom` instance is an `MS5ModalAxiom` instance: `MS5` extends `MS4` by
adding the `bBox`/`bDia` schemata verbatim, leaving `MS4`'s 16 constructors unchanged. -/
lemma MS4ModalAxiom_implies_MS5ModalAxiom {φ : Proposition Atom} (h : MS4ModalAxiom φ) :
    MS5ModalAxiom φ :=
  match h with
  | .implyK φ ψ => .implyK φ ψ
  | .implyS φ ψ χ => .implyS φ ψ χ
  | .andI φ ψ => .andI φ ψ
  | .andE1 φ ψ => .andE1 φ ψ
  | .andE2 φ ψ => .andE2 φ ψ
  | .orI1 φ ψ => .orI1 φ ψ
  | .orI2 φ ψ => .orI2 φ ψ
  | .orE φ ψ χ => .orE φ ψ χ
  | .k φ ψ => .k φ ψ
  | .kdia φ ψ => .kdia φ ψ
  | .cd φ ψ => .cd φ ψ
  | .idb φ ψ => .idb φ ψ
  | .tBox φ => .tBox φ
  | .tDia φ => .tDia φ
  | .fourBox φ => .fourBox φ
  | .fourDia φ => .fourDia φ

end Cslib.Logic.Modal

end
