/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Modal.Metalogic.InterSystem.Lifting
public import Cslib.Logics.Modal.Metalogic.InterSystem.PropositionalStrengthSubsumption

/-! # Cross-Base Propositional-Strength Derivability Monotonicity into the Intuitionistic Base

This module instantiates the generic `Derivable_mono` lemma (`InterSystem/Lifting.lean:66`)
with the axiom subsumption lemmas from `PropositionalStrengthSubsumption.lean` to produce
named derivability monotonicity theorems embedding the minimal and constructive bases into
the intuitionistic base, at every rung of the modal cube.

**Framing**: same-modal-language, different-propositional-base edges — **monotonicity**, not
conservativity (the converse is false: `IK` proves `efq`-consequences and `dbot`, neither of
which is `MK`- or `CK`-derivable). Genuine conservativity is reserved for the
modal-over-propositional axis (see `Metalogic/ConservativeExtension.lean`), reused (not
reproved) in `Modularity.lean`.

**MK/CK incomparability**: `MKModalAxiom` and `CKModalAxiom` are incomparable (see
`PropositionalStrengthSubsumption.lean`'s module docstring), so there is no
`mkDerivable_implies_ckDerivable` or converse — both embed into `IK` independently.
-/

@[expose] public section

namespace Cslib.Logic.Modal

variable {Atom : Type*} {φ : Proposition Atom}

/-! ## Into `IK` -/

/-- `MK`-derivable formulas are `IK`-derivable. -/
theorem mkDerivable_implies_ikDerivable (h : Derivable (@MKModalAxiom Atom) φ) :
    Derivable (@IKModalAxiom Atom) φ :=
  Derivable_mono (fun _ => MKModalAxiom_implies_IKModalAxiom) h

/-- `CK`-derivable formulas are `IK`-derivable. -/
theorem ckDerivable_implies_ikDerivable (h : Derivable (@CKModalAxiom Atom) φ) :
    Derivable (@IKModalAxiom Atom) φ :=
  Derivable_mono (fun _ => CKModalAxiom_implies_IKModalAxiom) h

/-! ## Into `IT` -/

/-- `MT`-derivable formulas are `IT`-derivable. -/
theorem mtDerivable_implies_itDerivable (h : Derivable (@MTModalAxiom Atom) φ) :
    Derivable (@ITModalAxiom Atom) φ :=
  Derivable_mono (fun _ => MTModalAxiom_implies_ITModalAxiom) h

/-- `CT`-derivable formulas are `IT`-derivable. -/
theorem ctDerivable_implies_itDerivable (h : Derivable (@CTModalAxiom Atom) φ) :
    Derivable (@ITModalAxiom Atom) φ :=
  Derivable_mono (fun _ => CTModalAxiom_implies_ITModalAxiom) h

/-! ## Into `IS4` -/

/-- `MS4`-derivable formulas are `IS4`-derivable. -/
theorem ms4Derivable_implies_is4Derivable (h : Derivable (@MS4ModalAxiom Atom) φ) :
    Derivable (@IS4ModalAxiom Atom) φ :=
  Derivable_mono (fun _ => MS4ModalAxiom_implies_IS4ModalAxiom) h

/-- `CS4`-derivable formulas are `IS4`-derivable. -/
theorem cs4Derivable_implies_is4Derivable (h : Derivable (@CS4ModalAxiom Atom) φ) :
    Derivable (@IS4ModalAxiom Atom) φ :=
  Derivable_mono (fun _ => CS4ModalAxiom_implies_IS4ModalAxiom) h

/-! ## Into `IS5` -/

/-- `MS5`-derivable formulas are `IS5`-derivable. -/
theorem ms5Derivable_implies_is5Derivable (h : Derivable (@MS5ModalAxiom Atom) φ) :
    Derivable (@IS5ModalAxiom Atom) φ :=
  Derivable_mono (fun _ => MS5ModalAxiom_implies_IS5ModalAxiom) h

/-- `CS5`-derivable formulas are `IS5`-derivable. -/
theorem cs5Derivable_implies_is5Derivable (h : Derivable (@CS5ModalAxiom Atom) φ) :
    Derivable (@IS5ModalAxiom Atom) φ :=
  Derivable_mono (fun _ => CS5ModalAxiom_implies_IS5ModalAxiom) h

end Cslib.Logic.Modal

end
