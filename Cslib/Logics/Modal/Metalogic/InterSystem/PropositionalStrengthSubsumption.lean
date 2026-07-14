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
public import Cslib.Logics.Modal.Metalogic.Constructive.CK
public import Cslib.Logics.Modal.Metalogic.Constructive.CT
public import Cslib.Logics.Modal.Metalogic.Constructive.CS4
public import Cslib.Logics.Modal.Metalogic.Constructive.CS5
public import Cslib.Logics.Modal.Metalogic.Intuitionistic.IS5

/-! # Cross-Base Propositional-Strength Subsumption into the Intuitionistic Base

This module proves the cross-base axiom subsumption lemmas embedding the minimal and
constructive propositional bases into the intuitionistic base, at every rung of the modal
cube: `MK/CK → IK`, `MT/CT → IT`, `MS4/CS4 → IS4`, `MS5/CS5 → IS5`.

Each embedding is mechanical: `IKModalAxiom` is `MKModalAxiom`'s 12 constructors plus `efq`
and `dbot` (see `IK.lean`'s module docstring: "`k1`-`k5`" = `{k, kdia, cd, idb, dbot}`), and
also literally contains all of `CKModalAxiom`'s 11 constructors (`CK` = `IK` minus `cd`,
`idb`, `dbot`). The per-rung modal extensions (`tBox`/`tDia`, `fourBox`/`fourDia`,
`bBox`/`bDia`) are named identically across all three bases, so the embeddings lift
rung-by-rung without any new machinery.

## MK/CK Incomparability

`MKModalAxiom` and `CKModalAxiom` are **incomparable**: `MK` has the Fischer-Servi
constructors `cd`/`idb` (and `kdia`) but no `efq`; `CK` has `efq` but no `cd`/`idb`. Neither
embeds into the other. Both embed into `IK`, which is exactly `MK`'s modal constructors
(`k`/`kdia`/`cd`/`idb`) united with `CK`'s propositional constructor (`efq`), plus `dbot`
(present in neither weaker base).

## Coverage

- `MKModalAxiom_implies_IKModalAxiom`, `CKModalAxiom_implies_IKModalAxiom`
- `MTModalAxiom_implies_ITModalAxiom`, `CTModalAxiom_implies_ITModalAxiom`
- `MS4ModalAxiom_implies_IS4ModalAxiom`, `CS4ModalAxiom_implies_IS4ModalAxiom`
- `MS5ModalAxiom_implies_IS5ModalAxiom`, `CS5ModalAxiom_implies_IS5ModalAxiom`

**Framing**: these are same-*modal*-language, different-*propositional*-base edges, so the
converse is false (e.g. classical-style Peirce-style principles or `efq` are not derivable
from the weaker propositional base). These are **monotonicity** results, not conservativity;
see `PropositionalStrengthMonotonicity.lean` for the `Derivable`-level corollaries.
-/

@[expose] public section

namespace Cslib.Logic.Modal

variable {Atom : Type*}

/-! ## Into `IK` -/

/-- Every `MKModalAxiom` instance is an `IKModalAxiom` instance: `IK` extends `MK`'s 12
constructors verbatim with `efq` and `dbot`. -/
lemma MKModalAxiom_implies_IKModalAxiom {φ : Proposition Atom} (h : MKModalAxiom φ) :
    IKModalAxiom φ :=
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

/-- Every `CKModalAxiom` instance is an `IKModalAxiom` instance: `IK` extends `CK`'s 11
constructors verbatim with `cd`, `idb`, and `dbot`. -/
lemma CKModalAxiom_implies_IKModalAxiom {φ : Proposition Atom} (h : CKModalAxiom φ) :
    IKModalAxiom φ :=
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

/-! ## Into `IT` -/

/-- Every `MTModalAxiom` instance is an `ITModalAxiom` instance. -/
lemma MTModalAxiom_implies_ITModalAxiom {φ : Proposition Atom} (h : MTModalAxiom φ) :
    ITModalAxiom φ :=
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

/-- Every `CTModalAxiom` instance is an `ITModalAxiom` instance. -/
lemma CTModalAxiom_implies_ITModalAxiom {φ : Proposition Atom} (h : CTModalAxiom φ) :
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
  | .tBox φ => .tBox φ
  | .tDia φ => .tDia φ

/-! ## Into `IS4` -/

/-- Every `MS4ModalAxiom` instance is an `IS4ModalAxiom` instance. -/
lemma MS4ModalAxiom_implies_IS4ModalAxiom {φ : Proposition Atom} (h : MS4ModalAxiom φ) :
    IS4ModalAxiom φ :=
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

/-- Every `CS4ModalAxiom` instance is an `IS4ModalAxiom` instance. -/
lemma CS4ModalAxiom_implies_IS4ModalAxiom {φ : Proposition Atom} (h : CS4ModalAxiom φ) :
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
  | .tBox φ => .tBox φ
  | .tDia φ => .tDia φ
  | .fourBox φ => .fourBox φ
  | .fourDia φ => .fourDia φ

/-! ## Into `IS5` -/

/-- Every `MS5ModalAxiom` instance is an `IS5ModalAxiom` instance. -/
lemma MS5ModalAxiom_implies_IS5ModalAxiom {φ : Proposition Atom} (h : MS5ModalAxiom φ) :
    IS5ModalAxiom φ :=
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
  | .bBox φ => .bBox φ
  | .bDia φ => .bDia φ

/-- Every `CS5ModalAxiom` instance is an `IS5ModalAxiom` instance. -/
lemma CS5ModalAxiom_implies_IS5ModalAxiom {φ : Proposition Atom} (h : CS5ModalAxiom φ) :
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
  | .tBox φ => .tBox φ
  | .tDia φ => .tDia φ
  | .fourBox φ => .fourBox φ
  | .fourDia φ => .fourDia φ
  | .bBox φ => .bBox φ
  | .bDia φ => .bDia φ

end Cslib.Logic.Modal

end
