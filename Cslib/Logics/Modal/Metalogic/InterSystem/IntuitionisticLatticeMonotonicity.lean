/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Modal.Metalogic.InterSystem.Lifting
public import Cslib.Logics.Modal.Metalogic.InterSystem.LatticeSubsumption

/-! # Derivability Monotonicity for the Intuitionistic-Base Modal Cube

This module instantiates the generic `Derivable_mono` lemma (`InterSystem/Lifting.lean:66`)
with the axiom subsumption lemmas from `IntuitionisticLatticeSubsumption.lean` to produce
named derivability monotonicity theorems for the intuitionistic-base modal cube
`IK → IT → IS4 → IS5`, plus the corresponding frame-condition inclusion lemmas witnessing
module composition.

**Framing**: these are **monotonicity** results (`_implies_` naming), not conservativity —
the same-language converse is false on this axis (e.g. `IT` proves `□φ → φ`, not
`IK`-provable). Genuine conservativity is reserved for the modal-over-propositional axis
(see `Metalogic/ConservativeExtension.lean`) and is reused, not reproved, in `Modularity.lean`.
-/

@[expose] public section

namespace Cslib.Logic.Modal

variable {Atom : Type*} {φ : Proposition Atom}

/-! ## Derivability Monotonicity -/

/-- `IK`-derivable formulas are `IT`-derivable. -/
theorem ikDerivable_implies_itDerivable (h : Derivable (@IKModalAxiom Atom) φ) :
    Derivable (@ITModalAxiom Atom) φ :=
  Derivable_mono (fun _ => IKModalAxiom_implies_ITModalAxiom) h

/-- `IT`-derivable formulas are `IS4`-derivable. -/
theorem itDerivable_implies_is4Derivable (h : Derivable (@ITModalAxiom Atom) φ) :
    Derivable (@IS4ModalAxiom Atom) φ :=
  Derivable_mono (fun _ => ITModalAxiom_implies_IS4ModalAxiom) h

/-- `IS4`-derivable formulas are `IS5`-derivable. -/
theorem is4Derivable_implies_is5Derivable (h : Derivable (@IS4ModalAxiom Atom) φ) :
    Derivable (@IS5ModalAxiom Atom) φ :=
  Derivable_mono (fun _ => IS4ModalAxiom_implies_IS5ModalAxiom) h

/-- `IK`-derivable formulas are `IS4`-derivable (transitive chain). -/
theorem ikDerivable_implies_is4Derivable (h : Derivable (@IKModalAxiom Atom) φ) :
    Derivable (@IS4ModalAxiom Atom) φ :=
  itDerivable_implies_is4Derivable (ikDerivable_implies_itDerivable h)

/-- `IK`-derivable formulas are `IS5`-derivable (transitive chain). -/
theorem ikDerivable_implies_is5Derivable (h : Derivable (@IKModalAxiom Atom) φ) :
    Derivable (@IS5ModalAxiom Atom) φ :=
  is4Derivable_implies_is5Derivable (ikDerivable_implies_is4Derivable h)

/-- `IT`-derivable formulas are `IS5`-derivable (transitive chain). -/
theorem itDerivable_implies_is5Derivable (h : Derivable (@ITModalAxiom Atom) φ) :
    Derivable (@IS5ModalAxiom Atom) φ :=
  is4Derivable_implies_is5Derivable (itDerivable_implies_is4Derivable h)

/-! ## Frame-Condition Inclusions -/

/-- `IS5`'s frame condition (reflexive-transitive-symmetric) includes `IS4`'s
(reflexive-transitive). -/
lemma is5FC_implies_is4FC {World : Type*} {r : World → World → Prop} (h : is5FC r) :
    is4FC r :=
  ⟨h.1, h.2.1⟩

/-- `IS4`'s frame condition (reflexive-transitive) includes `IT`'s (reflexive). -/
lemma is4FC_implies_itFC {World : Type*} {r : World → World → Prop} (h : is4FC r) :
    itFC r :=
  h.1

/-- `IS5`'s frame condition includes `IT`'s (transitive chain). -/
lemma is5FC_implies_itFC {World : Type*} {r : World → World → Prop} (h : is5FC r) :
    itFC r :=
  is4FC_implies_itFC (is5FC_implies_is4FC h)

end Cslib.Logic.Modal

end
