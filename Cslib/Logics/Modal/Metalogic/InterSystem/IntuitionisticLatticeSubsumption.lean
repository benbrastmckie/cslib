/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Modal.Metalogic.Intuitionistic.IK
public import Cslib.Logics.Modal.Metalogic.Intuitionistic.IT
public import Cslib.Logics.Modal.Metalogic.Intuitionistic.IS4
public import Cslib.Logics.Modal.Metalogic.Intuitionistic.IS5

/-! # Axiom Subsumption Lemmas for the Intuitionistic-Base Modal Cube

This module proves the three direct-edge axiom subsumption lemmas for the
intuitionistic-base modal cube `IK → IT → IS4 → IS5`, mirroring the classical
`AxiomSubsumption.lean` template (`InterSystem/AxiomSubsumption.lean`). Each lemma is a
mechanical `match` case-split: every constructor of the weaker axiom predicate maps to
the same-named constructor of the stronger axiom predicate, since `ITModalAxiom`/
`IS4ModalAxiom`/`IS5ModalAxiom` are each defined as the previous rung's constructors
verbatim plus new ones (see `IT.lean`/`IS4.lean`/`IS5.lean` module docstrings).

**Framing**: these are same-language edges within the intuitionistic propositional base, so
the converse is false (e.g. `IT` proves `□φ → φ`, which is not `IK`-derivable). The results
here and their `Derivable`-level corollaries in `IntuitionisticLatticeMonotonicity.lean` are
**monotonicity**, not conservativity.

## Coverage

- `IKModalAxiom_implies_ITModalAxiom`
- `ITModalAxiom_implies_IS4ModalAxiom`
- `IS4ModalAxiom_implies_IS5ModalAxiom`
-/

@[expose] public section

namespace Cslib.Logic.Modal

variable {Atom : Type*}

/-- Every `IKModalAxiom` instance is an `ITModalAxiom` instance: `IT` extends `IK` by
adding the `tBox`/`tDia` schemata verbatim, leaving `IK`'s 14 constructors unchanged. -/
lemma IKModalAxiom_implies_ITModalAxiom {φ : Proposition Atom} (h : IKModalAxiom φ) :
    ITModalAxiom φ :=
  match h with
  | .implyK φ ψ => .implyK φ ψ
  | .implyS φ ψ χ => .implyS φ ψ χ
  | .efq φ => .efq φ
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
  | .dbot => .dbot

/-- Every `ITModalAxiom` instance is an `IS4ModalAxiom` instance: `IS4` extends `IT` by
adding the `fourBox`/`fourDia` schemata verbatim, leaving `IT`'s 16 constructors unchanged. -/
lemma ITModalAxiom_implies_IS4ModalAxiom {φ : Proposition Atom} (h : ITModalAxiom φ) :
    IS4ModalAxiom φ :=
  match h with
  | .implyK φ ψ => .implyK φ ψ
  | .implyS φ ψ χ => .implyS φ ψ χ
  | .efq φ => .efq φ
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
  | .dbot => .dbot
  | .tBox φ => .tBox φ
  | .tDia φ => .tDia φ

/-- Every `IS4ModalAxiom` instance is an `IS5ModalAxiom` instance: `IS5` extends `IS4` by
adding the `bBox`/`bDia` schemata verbatim, leaving `IS4`'s 18 constructors unchanged. -/
lemma IS4ModalAxiom_implies_IS5ModalAxiom {φ : Proposition Atom} (h : IS4ModalAxiom φ) :
    IS5ModalAxiom φ :=
  match h with
  | .implyK φ ψ => .implyK φ ψ
  | .implyS φ ψ χ => .implyS φ ψ χ
  | .efq φ => .efq φ
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
  | .dbot => .dbot
  | .tBox φ => .tBox φ
  | .tDia φ => .tDia φ
  | .fourBox φ => .fourBox φ
  | .fourDia φ => .fourDia φ

end Cslib.Logic.Modal

end
