/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Modal.Metalogic.Constructive.CK
public import Cslib.Logics.Modal.Metalogic.Constructive.CT
public import Cslib.Logics.Modal.Metalogic.Constructive.CS4
public import Cslib.Logics.Modal.Metalogic.Constructive.CS5

/-! # Axiom Subsumption Lemmas for the Constructive-Base Modal Cube

This module proves the three direct-edge axiom subsumption lemmas for the
constructive-base modal cube `CK → CT → CS4 → CS5`, mirroring the classical
`AxiomSubsumption.lean` template (`InterSystem/AxiomSubsumption.lean`). Each lemma is a
mechanical `match` case-split: every constructor of the weaker axiom predicate maps to
the same-named constructor of the stronger axiom predicate, since `CTModalAxiom`/
`CS4ModalAxiom`/`CS5ModalAxiom` are each defined as the previous rung's constructors
verbatim plus new ones (see `CT.lean`/`CS4.lean`/`CS5.lean` module docstrings).

**Note (task 501/508 independence)**: this module is purely syntactic (`cases`/`match` on the
axiom predicates); it does not depend on `CKValidFC`/`ckvalidFC_completeness` in any way, and is
therefore entirely independent of `CS4`/`CS5` semantic completeness (`CS4` completeness is now
established, task 508; `CS5` completeness remains open — see `CS5.lean`'s module docstring for
the mechanized obstruction). Neither status affects the syntactic derivability monotonicity
proved here.

**Framing**: these are same-language edges within the constructive propositional base, so
the converse is false (e.g. `CT` proves `□φ → φ`, which is not `CK`-derivable). The results
here and their `Derivable`-level corollaries in `ConstructiveLatticeMonotonicity.lean` are
**monotonicity**, not conservativity.

## Coverage

- `CKModalAxiom_implies_CTModalAxiom`
- `CTModalAxiom_implies_CS4ModalAxiom`
- `CS4ModalAxiom_implies_CS5ModalAxiom`
-/

@[expose] public section

namespace Cslib.Logic.Modal

variable {Atom : Type*}

/-- Every `CKModalAxiom` instance is a `CTModalAxiom` instance: `CT` extends `CK` by
adding the `tBox`/`tDia` schemata verbatim, leaving `CK`'s 11 constructors unchanged. -/
lemma CKModalAxiom_implies_CTModalAxiom {φ : Proposition Atom} (h : CKModalAxiom φ) :
    CTModalAxiom φ :=
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

/-- Every `CTModalAxiom` instance is a `CS4ModalAxiom` instance: `CS4` extends `CT` by
adding the `fourBox`/`fourDia` schemata verbatim, leaving `CT`'s 13 constructors unchanged. -/
lemma CTModalAxiom_implies_CS4ModalAxiom {φ : Proposition Atom} (h : CTModalAxiom φ) :
    CS4ModalAxiom φ :=
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
  | .tBox φ => .tBox φ
  | .tDia φ => .tDia φ

/-- Every `CS4ModalAxiom` instance is a `CS5ModalAxiom` instance: `CS5` extends `CS4` by
adding the `bBox`/`bDia` schemata verbatim, leaving `CS4`'s 15 constructors unchanged. -/
lemma CS4ModalAxiom_implies_CS5ModalAxiom {φ : Proposition Atom} (h : CS4ModalAxiom φ) :
    CS5ModalAxiom φ :=
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
  | .tBox φ => .tBox φ
  | .tDia φ => .tDia φ
  | .fourBox φ => .fourBox φ
  | .fourDia φ => .fourDia φ

end Cslib.Logic.Modal

end
