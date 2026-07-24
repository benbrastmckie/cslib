/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Modal.Metalogic.InterSystem.Lifting
public import Cslib.Logics.Modal.Metalogic.InterSystem.LatticeSubsumption

/-! # Derivability Monotonicity for the Same-Base Modal Cubes

This module instantiates the generic `Derivable_mono` lemma (`InterSystem/Lifting.lean:66`)
with the axiom subsumption lemmas from `LatticeSubsumption.lean` to produce named
derivability monotonicity theorems for each of the three same-language-base modal cubes --
constructive (`CK → CT → CS4 → CS5`), minimal (`MK → MT → MS4 → MS5`), and intuitionistic
(`IK → IT → IS4 → IS5`) -- plus the corresponding frame-condition inclusion lemmas witnessing
module composition. The three tracks are proved together in a single module since they are
structurally parallel and have no cross-base dependency (see
`PropositionalStrengthMonotonicity.lean` for the cross-base corollaries).

**Independence from semantic completeness**: like `LatticeSubsumption.lean`, this module is
purely syntactic and does not depend on `ckvalidFC_completeness`; it is independent of the
`CS4`/`CS5` semantic completeness status.

**Framing**: these are **monotonicity** results (`_implies_` naming), not conservativity --
the same-language converse is false on this axis (e.g. `CT`/`MT`/`IT` each prove `□φ → φ`,
not derivable one rung down). Genuine conservativity is reserved for the modal-over-propositional
axis (see `Metalogic/ConservativeExtension.lean`) and is reused, not reproved, in
`Modularity.lean`.
-/

@[expose] public section

namespace Cslib.Logic.Modal

variable {Atom : Type*} {φ : Proposition Atom}

/-! ## Constructive base -/

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

/-! ## Minimal base -/

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

/-! ## Intuitionistic base -/

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
