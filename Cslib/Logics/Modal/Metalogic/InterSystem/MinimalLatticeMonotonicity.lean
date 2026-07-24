/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Modal.Metalogic.InterSystem.Lifting
public import Cslib.Logics.Modal.Metalogic.InterSystem.LatticeSubsumption

/-! # Derivability Monotonicity for the Minimal-Base Modal Cube

This module instantiates the generic `Derivable_mono` lemma (`InterSystem/Lifting.lean:66`)
with the axiom subsumption lemmas from `MinimalLatticeSubsumption.lean` to produce named
derivability monotonicity theorems for the minimal-base modal cube `MK → MT → MS4 → MS5`,
plus the corresponding frame-condition inclusion lemmas witnessing module composition.

**Framing**: these are **monotonicity** results (`_implies_` naming), not conservativity —
the same-language converse is false on this axis (e.g. `MT` proves `□φ → φ`, not `MK`-provable).
Genuine conservativity is reserved for the modal-over-propositional axis (see
`Metalogic/ConservativeExtension.lean`) and is reused, not reproved, in `Modularity.lean`.
-/

@[expose] public section

namespace Cslib.Logic.Modal

variable {Atom : Type*} {φ : Proposition Atom}

/-! ## Derivability Monotonicity -/

/-- `MK`-derivable formulas are `MT`-derivable. -/
theorem mkDerivable_implies_mtDerivable (h : Derivable (@MKModalAxiom Atom) φ) :
    Derivable (@MTModalAxiom Atom) φ :=
  Derivable_mono (fun _ => MKModalAxiom_implies_MTModalAxiom) h

/-- `MT`-derivable formulas are `MS4`-derivable. -/
theorem mtDerivable_implies_ms4Derivable (h : Derivable (@MTModalAxiom Atom) φ) :
    Derivable (@MS4ModalAxiom Atom) φ :=
  Derivable_mono (fun _ => MTModalAxiom_implies_MS4ModalAxiom) h

/-- `MS4`-derivable formulas are `MS5`-derivable. -/
theorem ms4Derivable_implies_ms5Derivable (h : Derivable (@MS4ModalAxiom Atom) φ) :
    Derivable (@MS5ModalAxiom Atom) φ :=
  Derivable_mono (fun _ => MS4ModalAxiom_implies_MS5ModalAxiom) h

/-- `MK`-derivable formulas are `MS4`-derivable (transitive chain). -/
theorem mkDerivable_implies_ms4Derivable (h : Derivable (@MKModalAxiom Atom) φ) :
    Derivable (@MS4ModalAxiom Atom) φ :=
  mtDerivable_implies_ms4Derivable (mkDerivable_implies_mtDerivable h)

/-- `MK`-derivable formulas are `MS5`-derivable (transitive chain). -/
theorem mkDerivable_implies_ms5Derivable (h : Derivable (@MKModalAxiom Atom) φ) :
    Derivable (@MS5ModalAxiom Atom) φ :=
  ms4Derivable_implies_ms5Derivable (mkDerivable_implies_ms4Derivable h)

/-- `MT`-derivable formulas are `MS5`-derivable (transitive chain). -/
theorem mtDerivable_implies_ms5Derivable (h : Derivable (@MTModalAxiom Atom) φ) :
    Derivable (@MS5ModalAxiom Atom) φ :=
  ms4Derivable_implies_ms5Derivable (mtDerivable_implies_ms4Derivable h)

/-! ## Frame-Condition Inclusions -/

/-- `MS5`'s frame condition (reflexive-transitive-symmetric) includes `MS4`'s
(reflexive-transitive). -/
lemma ms5FC_implies_ms4FC {World : Type*} {r : World → World → Prop} (h : ms5FC r) :
    ms4FC r :=
  ⟨h.1, h.2.1⟩

/-- `MS4`'s frame condition (reflexive-transitive) includes `MT`'s (reflexive). -/
lemma ms4FC_implies_mtFC {World : Type*} {r : World → World → Prop} (h : ms4FC r) :
    mtFC r :=
  h.1

/-- `MS5`'s frame condition includes `MT`'s (transitive chain). -/
lemma ms5FC_implies_mtFC {World : Type*} {r : World → World → Prop} (h : ms5FC r) :
    mtFC r :=
  ms4FC_implies_mtFC (ms5FC_implies_ms4FC h)

end Cslib.Logic.Modal

end
