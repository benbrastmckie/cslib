/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Modal.Metalogic.InterSystem.IntToClassical
public import Cslib.Logics.Modal.Metalogic.InterSystem.IntuitionisticLatticeMonotonicity
public import Cslib.Logics.Modal.Metalogic.InterSystem.PropositionalStrengthMonotonicity
public import Cslib.Logics.Modal.Metalogic.Systems.K.ConservativeExtension

/-! # Capstone: Modularity Across the Propositional-Strength × Modal-Axiom Lattice

This module is the capstone synthesis of task 484. It does not prove any new mathematics;
it consolidates the monotonicity results of `MinimalLatticeMonotonicity.lean`,
`IntuitionisticLatticeMonotonicity.lean`, `ConstructiveLatticeMonotonicity.lean`,
`PropositionalStrengthMonotonicity.lean`, and the classical `Conservativity.lean` into a
single documented lattice map, and re-exposes the already-proved Axis-C
modal-over-propositional conservative extension (`modal_conservative_extension`,
`Systems/K/ConservativeExtension.lean`) under this module for discoverability.

## The Three-Axis Framing

Everything in `Cslib/Logics/Modal/Metalogic/` derives theorems through **one** shared
framework, `Derivable Axioms φ := Nonempty (DerivationTree Axioms [] φ)` over
`Proposition Atom`, parameterized by an axiom predicate `Axioms : Proposition Atom → Prop`.
Three genuinely different kinds of lattice edge live inside this one framework, and they
have different Lean shapes:

**Axis A — the modal-axiom lattice** (K/T/S4/S5/D/B/K4/K5/…, within one fixed propositional
base). Edges here are **monotonicity only**: `Derivable Weak φ → Derivable Strong φ`, proved
by axiom-predicate inclusion via the generic `Derivable_mono` lift
(`InterSystem/Lifting.lean:66`). The same-language **converse is false** — e.g. `T` proves
`□φ → φ`, which is not `K`-derivable; classical `K` proves Peirce's law, which is not
`intuitionistic`-derivable. Classical Axis-A edges: `AxiomSubsumption.lean` +
`Conservativity.lean` (24 edges). Minimal/Intuitionistic/Constructive Axis-A edges:
`MinimalLatticeMonotonicity.lean`, `IntuitionisticLatticeMonotonicity.lean`,
`ConstructiveLatticeMonotonicity.lean` (task 484, Phases 1-3).

**Axis B — propositional strength** (minimal ⊆ constructive/intuitionistic ⊆ classical,
within one fixed modal system). Edges here are also **monotonicity only**, into the
intuitionistic base: `MKModalAxiom_implies_IKModalAxiom`, `CKModalAxiom_implies_IKModalAxiom`,
and per-rung analogues (`PropositionalStrengthMonotonicity.lean`, task 484 Phase 4). The
converse is again false (classical-only principles like Peirce's law are not derivable from
the weaker propositional bases). `MKModalAxiom` and `CKModalAxiom` are themselves
**incomparable** (`MK` has the Fischer-Servi constructors `cd`/`idb` but no `efq`; `CK` has
`efq` but no `cd`/`idb`); both embed into `IK`, which is exactly their union plus `dbot`.
The Intuitionistic → Classical edge (`IK → K`) is the *one* genuinely hard direction on this
axis (report Phase 3 / plan Phases 6-7), because intuitionistic `IK` uses a **primitive**
diamond with Fischer-Servi axioms while classical `K` uses the **dual** diamond
(`◇ = ¬□¬`) — not a syntactic rename, requiring the new generalized
`Derivable_of_axiom_derivable` lift plus per-axiom classical derivations.

**Axis C — modal-over-propositional** (a modal system vs. its underlying CPL/IPL/MPL). This
is the **only** axis with a genuine conservativity **converse**:
`modal_conservative_extension_param` (`Metalogic/ConservativeExtension.lean:54`) shows that
if `φ.toModal` is derivable in any modal system sound at the universal `Unit` model, then
`φ` is derivable in the underlying propositional logic — i.e. the modal system proves no
*new* propositional theorems. All 15 classical per-system instances already exist
(`Systems/*/ConservativeExtension.lean`); `axisC_k_conservative_over_cpl` below re-exposes
the `K` instance under this module. PL-level fragment conservativity (Glivenko, bot-free)
is a related but separate, already-complete result (`HilbertConservativeGlivenko.lean`).

## Naming Discipline

Axes A and B lemmas are named with `_mono` / `_implies_` suffixes throughout this codebase
(e.g. `kDerivable_implies_tDerivable`, `mkDerivable_implies_ikDerivable`). The word
"conservative"/"conservativity" is reserved for genuine Axis-C results and PL fragments; it
never appears as the name of an Axis-A or Axis-B lemma, because those edges' same-language
converses are false.

## Consolidated Lattice Statement (Sample Composites)

The theorems below are direct compositions of the Phase 1-4 monotonicity lemmas —
no new proof content, only chaining across axes to witness "modularity": a formula
derivable in the *weakest* corner of the lattice (`MK`/`CK`) is derivable at any point
reachable by monotone edges, including the *strongest* same-language corner (`IS5`).
-/

@[expose] public section

namespace Cslib.Logic.Modal

variable {Atom : Type*} {φ : Proposition Atom}

/-! ## Cross-Axis Composites (Axis B then Axis A) -/

/-- `MK`-derivable formulas are `IS5`-derivable: chain Axis B (`MK → IK`) then Axis A
(`IK → IT → IS4 → IS5`). Witnesses modularity: the two axes compose freely. -/
theorem mkDerivable_implies_is5Derivable (h : Derivable (@MKModalAxiom Atom) φ) :
    Derivable (@IS5ModalAxiom Atom) φ :=
  ikDerivable_implies_is5Derivable (mkDerivable_implies_ikDerivable h)

/-- `CK`-derivable formulas are `IS5`-derivable: chain Axis B (`CK → IK`) then Axis A
(`IK → IT → IS4 → IS5`). -/
theorem ckDerivable_implies_is5Derivable (h : Derivable (@CKModalAxiom Atom) φ) :
    Derivable (@IS5ModalAxiom Atom) φ :=
  ikDerivable_implies_is5Derivable (ckDerivable_implies_ikDerivable h)

/-- `MT`-derivable formulas are `IS5`-derivable: chain Axis B (`MT → IT`) then Axis A
(`IT → IS4 → IS5`). -/
theorem mtDerivable_implies_is5Derivable (h : Derivable (@MTModalAxiom Atom) φ) :
    Derivable (@IS5ModalAxiom Atom) φ :=
  itDerivable_implies_is5Derivable (mtDerivable_implies_itDerivable h)

/-- `CT`-derivable formulas are `IS5`-derivable: chain Axis B (`CT → IT`) then Axis A
(`IT → IS4 → IS5`). -/
theorem ctDerivable_implies_is5Derivable (h : Derivable (@CTModalAxiom Atom) φ) :
    Derivable (@IS5ModalAxiom Atom) φ :=
  itDerivable_implies_is5Derivable (ctDerivable_implies_itDerivable h)

/-! ## Cross-Axis Composites Into the Classical Column (Axis B then Int->Classical) -/

/-- `MK`-derivable formulas are `K`-derivable: chain Axis B (`MK → IK`) then the
`IK → K` Int→Classical bridge. -/
theorem mkDerivable_implies_kDerivable (h : Derivable (@MKModalAxiom Atom) φ) :
    Derivable (@KAxiom Atom) φ :=
  ikDerivable_implies_kDerivable (mkDerivable_implies_ikDerivable h)

/-- `MT`-derivable formulas are `T`-derivable: chain Axis B (`MT → IT`) then the
`IT → T` Int→Classical bridge. -/
theorem mtDerivable_implies_tDerivable (h : Derivable (@MTModalAxiom Atom) φ) :
    Derivable (@TAxiom Atom) φ :=
  itDerivable_implies_tDerivable (mtDerivable_implies_itDerivable h)

/-- `MS4`-derivable formulas are `S4`-derivable: chain Axis B (`MS4 → IS4`) then the
`IS4 → S4` Int→Classical bridge. -/
theorem ms4Derivable_implies_s4Derivable (h : Derivable (@MS4ModalAxiom Atom) φ) :
    Derivable (@S4Axiom Atom) φ :=
  is4Derivable_implies_s4Derivable (ms4Derivable_implies_is4Derivable h)

/-- `MS5`-derivable formulas are `S5`-derivable (classical target is `ModalAxiom`): chain
Axis B (`MS5 → IS5`) then the `IS5 → S5` Int→Classical bridge. -/
theorem ms5Derivable_implies_s5Derivable (h : Derivable (@MS5ModalAxiom Atom) φ) :
    Derivable (@ModalAxiom Atom) φ :=
  is5Derivable_implies_s5Derivable (ms5Derivable_implies_is5Derivable h)

/-- `CK`-derivable formulas are `K`-derivable: chain Axis B (`CK → IK`) then the
`IK → K` Int→Classical bridge. -/
theorem ckDerivable_implies_kDerivable (h : Derivable (@CKModalAxiom Atom) φ) :
    Derivable (@KAxiom Atom) φ :=
  ikDerivable_implies_kDerivable (ckDerivable_implies_ikDerivable h)

/-- `CT`-derivable formulas are `T`-derivable: chain Axis B (`CT → IT`) then the
`IT → T` Int→Classical bridge. -/
theorem ctDerivable_implies_tDerivable (h : Derivable (@CTModalAxiom Atom) φ) :
    Derivable (@TAxiom Atom) φ :=
  itDerivable_implies_tDerivable (ctDerivable_implies_itDerivable h)

/-- `CS4`-derivable formulas are `S4`-derivable: chain Axis B (`CS4 → IS4`) then the
`IS4 → S4` Int→Classical bridge. -/
theorem cs4Derivable_implies_s4Derivable (h : Derivable (@CS4ModalAxiom Atom) φ) :
    Derivable (@S4Axiom Atom) φ :=
  is4Derivable_implies_s4Derivable (cs4Derivable_implies_is4Derivable h)

/-- `CS5`-derivable formulas are `S5`-derivable (classical target is `ModalAxiom`): chain
Axis B (`CS5 → IS5`) then the `IS5 → S5` Int→Classical bridge. -/
theorem cs5Derivable_implies_s5Derivable (h : Derivable (@CS5ModalAxiom Atom) φ) :
    Derivable (@ModalAxiom Atom) φ :=
  is5Derivable_implies_s5Derivable (cs5Derivable_implies_is5Derivable h)

/-! ## Axis C: Reused Conservativity (Not Reproved) -/

/-- **Axis C reuse**: modal `K` is a conservative extension of CPL — re-exposed here from
`Systems/K/ConservativeExtension.lean` under the modularity synthesis for discoverability.
The proof is the reused Axis-C result verbatim (`modal_conservative_extension`); this module
does not reprove it. -/
theorem axisC_k_conservative_over_cpl {φ : PL.Proposition Atom}
    (h : Derivable (@KAxiom Atom) φ.toModal) :
    PL.Derivable PL.PropositionalAxiom φ :=
  modal_conservative_extension h

end Cslib.Logic.Modal

end
