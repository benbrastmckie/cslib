/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Modal.Metalogic.InterSystem.Lifting
public import Cslib.Logics.Modal.Metalogic.InterSystem.LatticeSubsumption

/-! # Derivability Monotonicity for the Constructive-Base Modal Cube

This module instantiates the generic `Derivable_mono` lemma (`InterSystem/Lifting.lean:66`)
with the axiom subsumption lemmas from `ConstructiveLatticeSubsumption.lean` to produce
named derivability monotonicity theorems for the constructive-base modal cube
`CK → CT → CS4 → CS5`, plus the corresponding frame-condition inclusion lemmas witnessing
module composition.

**Note (task 501 independence)**: like `ConstructiveLatticeSubsumption.lean`, this module is
purely syntactic and does not depend on `ckvalidFC_completeness`; it is independent of the
CS4/CS5 completeness blocker tracked in task 501.

**Framing**: these are **monotonicity** results (`_implies_` naming), not conservativity —
the same-language converse is false on this axis (e.g. `CT` proves `□φ → φ`, not
`CK`-provable). Genuine conservativity is reserved for the modal-over-propositional axis
(see `Metalogic/ConservativeExtension.lean`) and is reused, not reproved, in `Modularity.lean`.
-/

@[expose] public section

namespace Cslib.Logic.Modal

variable {Atom : Type*} {φ : Proposition Atom}

/-! ## Derivability Monotonicity -/

/-- `CK`-derivable formulas are `CT`-derivable. -/
theorem ckDerivable_implies_ctDerivable (h : Derivable (@CKModalAxiom Atom) φ) :
    Derivable (@CTModalAxiom Atom) φ :=
  Derivable_mono (fun _ => CKModalAxiom_implies_CTModalAxiom) h

/-- `CT`-derivable formulas are `CS4`-derivable. -/
theorem ctDerivable_implies_cs4Derivable (h : Derivable (@CTModalAxiom Atom) φ) :
    Derivable (@CS4ModalAxiom Atom) φ :=
  Derivable_mono (fun _ => CTModalAxiom_implies_CS4ModalAxiom) h

/-- `CS4`-derivable formulas are `CS5`-derivable. -/
theorem cs4Derivable_implies_cs5Derivable (h : Derivable (@CS4ModalAxiom Atom) φ) :
    Derivable (@CS5ModalAxiom Atom) φ :=
  Derivable_mono (fun _ => CS4ModalAxiom_implies_CS5ModalAxiom) h

/-- `CK`-derivable formulas are `CS4`-derivable (transitive chain). -/
theorem ckDerivable_implies_cs4Derivable (h : Derivable (@CKModalAxiom Atom) φ) :
    Derivable (@CS4ModalAxiom Atom) φ :=
  ctDerivable_implies_cs4Derivable (ckDerivable_implies_ctDerivable h)

/-- `CK`-derivable formulas are `CS5`-derivable (transitive chain). -/
theorem ckDerivable_implies_cs5Derivable (h : Derivable (@CKModalAxiom Atom) φ) :
    Derivable (@CS5ModalAxiom Atom) φ :=
  cs4Derivable_implies_cs5Derivable (ckDerivable_implies_cs4Derivable h)

/-- `CT`-derivable formulas are `CS5`-derivable (transitive chain). -/
theorem ctDerivable_implies_cs5Derivable (h : Derivable (@CTModalAxiom Atom) φ) :
    Derivable (@CS5ModalAxiom Atom) φ :=
  cs4Derivable_implies_cs5Derivable (ctDerivable_implies_cs4Derivable h)

/-! ## Frame-Condition Inclusions -/

/-- `CS5`'s frame condition (reflexive, ≤-composed-transitive, ≤-composed-symmetric)
includes `CS4`'s (reflexive, ≤-composed-transitive). -/
lemma cs5FC_implies_cs4FC {World : Type*} [Preorder World] {r : World → World → Prop}
    (h : cs5FC r) : cs4FC r :=
  ⟨h.1, h.2.1⟩

/-- `CS4`'s frame condition (reflexive, ≤-composed-transitive) includes `CT`'s (reflexive). -/
lemma cs4FC_implies_ctFC {World : Type*} [Preorder World] {r : World → World → Prop}
    (h : cs4FC r) : ctFC r :=
  h.1

/-- `CS5`'s frame condition includes `CT`'s (transitive chain). -/
lemma cs5FC_implies_ctFC {World : Type*} [Preorder World] {r : World → World → Prop}
    (h : cs5FC r) : ctFC r :=
  cs4FC_implies_ctFC (cs5FC_implies_cs4FC h)

end Cslib.Logic.Modal

end
