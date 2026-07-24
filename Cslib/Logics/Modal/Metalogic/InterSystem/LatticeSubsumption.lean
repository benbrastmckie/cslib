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
public import Cslib.Logics.Modal.Metalogic.Minimal.MK
public import Cslib.Logics.Modal.Metalogic.Minimal.MT
public import Cslib.Logics.Modal.Metalogic.Minimal.MS4
public import Cslib.Logics.Modal.Metalogic.Minimal.MS5
public import Cslib.Logics.Modal.Metalogic.Intuitionistic.IK
public import Cslib.Logics.Modal.Metalogic.Intuitionistic.IT
public import Cslib.Logics.Modal.Metalogic.Intuitionistic.IS4
public import Cslib.Logics.Modal.Metalogic.Intuitionistic.IS5

/-! # Axiom Subsumption Lemmas for the Same-Base Modal Cubes

This module proves the direct-edge axiom subsumption lemmas for each of the three
same-language-base modal cubes -- constructive (`CK → CT → CS4 → CS5`), minimal
(`MK → MT → MS4 → MS5`), and intuitionistic (`IK → IT → IS4 → IS5`) -- mirroring the
classical `AxiomSubsumption.lean` template (`InterSystem/AxiomSubsumption.lean`). Each lemma
is a mechanical constructor case-split: every constructor of the weaker axiom predicate maps
to the same-named constructor of the stronger axiom predicate, since each rung's `S5Axiom`
is defined as the previous rung's constructors verbatim plus new ones (see each track's
`T`/`S4`/`S5` module docstrings). The three tracks are proved together in a single module since
they are structurally parallel and have no cross-base dependency (see
`PropositionalStrengthSubsumption.lean` for the cross-base embeddings).

**Independence from semantic completeness**: this module is purely syntactic (`cases` on the
axiom predicates); it does not depend on `CKValidFC`/`ckvalidFC_completeness` in any way, and is
therefore entirely independent of `CS4`/`CS5` semantic completeness (`CS4` completeness is
established; `CS5` completeness remains open -- see `CS5.lean`'s module docstring for the
mechanized obstruction). Neither status affects the syntactic derivability monotonicity proved
here.

**Framing**: these are same-language edges within each propositional base, so the converse is
false in each case (e.g. `CT` proves `□φ → φ`, which is not `CK`-derivable). The results here
and their `Derivable`-level corollaries in `LatticeMonotonicity.lean` are **monotonicity**, not
conservativity.

## Coverage

- Constructive: `CKModalAxiom_implies_CTModalAxiom`, `CTModalAxiom_implies_CS4ModalAxiom`,
  `CS4ModalAxiom_implies_CS5ModalAxiom`
- Minimal: `MKModalAxiom_implies_MTModalAxiom`, `MTModalAxiom_implies_MS4ModalAxiom`,
  `MS4ModalAxiom_implies_MS5ModalAxiom`
- Intuitionistic: `IKModalAxiom_implies_ITModalAxiom`, `ITModalAxiom_implies_IS4ModalAxiom`,
  `IS4ModalAxiom_implies_IS5ModalAxiom`
-/

@[expose] public section

namespace Cslib.Logic.Modal

variable {Atom : Type*}

/-! ## Constructive base -/

/-- Every `CKModalAxiom` instance is a `CTModalAxiom` instance: `CT` extends `CK` by
adding the `tBox`/`tDia` schemata verbatim, leaving `CK`'s 11 constructors unchanged. -/
lemma CKModalAxiom_implies_CTModalAxiom {φ : Proposition Atom} (h : CKModalAxiom φ) :
    CTModalAxiom φ := by
  cases h <;> constructor

/-- Every `CTModalAxiom` instance is a `CS4ModalAxiom` instance: `CS4` extends `CT` by
adding the `fourBox`/`fourDia` schemata verbatim, leaving `CT`'s 13 constructors unchanged. -/
lemma CTModalAxiom_implies_CS4ModalAxiom {φ : Proposition Atom} (h : CTModalAxiom φ) :
    CS4ModalAxiom φ := by
  cases h <;> constructor

/-- Every `CS4ModalAxiom` instance is a `CS5ModalAxiom` instance: `CS5` extends `CS4` by
adding the `bBox`/`bDia` schemata verbatim, leaving `CS4`'s 15 constructors unchanged. -/
lemma CS4ModalAxiom_implies_CS5ModalAxiom {φ : Proposition Atom} (h : CS4ModalAxiom φ) :
    CS5ModalAxiom φ := by
  cases h <;> constructor

/-! ## Minimal base -/

/-- Every `MKModalAxiom` instance is an `MTModalAxiom` instance: `MT` extends `MK` by adding
the `tBox`/`tDia` schemata verbatim, leaving `MK`'s 12 constructors unchanged. -/
lemma MKModalAxiom_implies_MTModalAxiom {φ : Proposition Atom} (h : MKModalAxiom φ) :
    MTModalAxiom φ := by
  cases h <;> constructor

/-- Every `MTModalAxiom` instance is an `MS4ModalAxiom` instance: `MS4` extends `MT` by
adding the `fourBox`/`fourDia` schemata verbatim, leaving `MT`'s 14 constructors unchanged. -/
lemma MTModalAxiom_implies_MS4ModalAxiom {φ : Proposition Atom} (h : MTModalAxiom φ) :
    MS4ModalAxiom φ := by
  cases h <;> constructor

/-- Every `MS4ModalAxiom` instance is an `MS5ModalAxiom` instance: `MS5` extends `MS4` by
adding the `bBox`/`bDia` schemata verbatim, leaving `MS4`'s 16 constructors unchanged. -/
lemma MS4ModalAxiom_implies_MS5ModalAxiom {φ : Proposition Atom} (h : MS4ModalAxiom φ) :
    MS5ModalAxiom φ := by
  cases h <;> constructor

/-! ## Intuitionistic base -/

/-- Every `IKModalAxiom` instance is an `ITModalAxiom` instance: `IT` extends `IK` by
adding the `tBox`/`tDia` schemata verbatim, leaving `IK`'s 14 constructors unchanged. -/
lemma IKModalAxiom_implies_ITModalAxiom {φ : Proposition Atom} (h : IKModalAxiom φ) :
    ITModalAxiom φ := by
  cases h <;> constructor

/-- Every `ITModalAxiom` instance is an `IS4ModalAxiom` instance: `IS4` extends `IT` by
adding the `fourBox`/`fourDia` schemata verbatim, leaving `IT`'s 16 constructors unchanged. -/
lemma ITModalAxiom_implies_IS4ModalAxiom {φ : Proposition Atom} (h : ITModalAxiom φ) :
    IS4ModalAxiom φ := by
  cases h <;> constructor

/-- Every `IS4ModalAxiom` instance is an `IS5ModalAxiom` instance: `IS5` extends `IS4` by
adding the `bBox`/`bDia` schemata verbatim, leaving `IS4`'s 18 constructors unchanged. -/
lemma IS4ModalAxiom_implies_IS5ModalAxiom {φ : Proposition Atom} (h : IS4ModalAxiom φ) :
    IS5ModalAxiom φ := by
  cases h <;> constructor

end Cslib.Logic.Modal

end
