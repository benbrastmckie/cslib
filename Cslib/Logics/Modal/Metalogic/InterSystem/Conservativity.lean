/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Modal.Metalogic.InterSystem.Lifting
public import Cslib.Logics.Modal.Metalogic.InterSystem.AxiomSubsumption

/-! # Derivability Monotonicity Theorems for the Modal Cube

This module instantiates the generic `Derivable_mono` lemma with the axiom subsumption
lemmas from `AxiomSubsumption.lean` to produce named derivability monotonicity theorems
for all provable direct edges of the modal cube.

## Key Theorem

For each edge "X extends Y" (X is stronger, Y is weaker) in the modal cube where the
axiom predicate of Y is syntactically subsumed by the axiom predicate of X, we prove:

```
y_derivable_implies_x_derivable : Derivable YAxiom φ → Derivable XAxiom φ
```

## Coverage

All 24 direct syntactic-subsumption edges of the modal cube are covered:

**From K (weakest)**: K → T, K → D, K → B, K → K4, K → K5
**From D**: D → D4, D → D5, D → DB
**From T**: T → S4, T → TB
**From B (KB)**: B → TB, B → DB, B → KB5
**From K4**: K4 → S4, K4 → D4, K4 → K45
**From K5**: K5 → D5, K5 → K45, K5 → KB5
**From K45**: K45 → D45
**From D4**: D4 → D45
**From D5**: D5 → D45
**Into S5**: S4 → S5, TB → S5

## Notes

The edge KB5 → S5 is not covered by syntactic subsumption (S5 does not include
axiom 5 literally, but derives it from T + 4 + B). Three transitive chain theorems
are provided for key paths through the cube.

## References

See `AxiomSubsumption.lean` for the per-edge subsumption lemmas and `Lifting.lean`
for the generic `liftDerivation` and `Derivable_mono` foundations.
-/

@[expose] public section

namespace Cslib.Logic.Modal

variable {Atom : Type*} {φ : Proposition Atom}

/-! ## From K (Weakest System) -/

/-- K-derivable formulas are T-derivable: T extends K by adding the T axiom (reflexivity). -/
theorem kDerivable_implies_tDerivable (h : Derivable (@KAxiom Atom) φ) :
    Derivable (@TAxiom Atom) φ :=
  Derivable_mono (fun _ => KAxiom_implies_TAxiom) h

/-- K-derivable formulas are D-derivable: D extends K by adding the D axiom (seriality). -/
theorem kDerivable_implies_dDerivable (h : Derivable (@KAxiom Atom) φ) :
    Derivable (@DAxiom Atom) φ :=
  Derivable_mono (fun _ => KAxiom_implies_DAxiom) h

/-- K-derivable formulas are B (KB)-derivable: B extends K by adding the B axiom (symmetry). -/
theorem kDerivable_implies_bDerivable (h : Derivable (@KAxiom Atom) φ) :
    Derivable (@BAxiom Atom) φ :=
  Derivable_mono (fun _ => KAxiom_implies_BAxiom) h

/-- K-derivable formulas are K4-derivable: K4 extends K by adding the 4 axiom (transitivity). -/
theorem kDerivable_implies_k4Derivable (h : Derivable (@KAxiom Atom) φ) :
    Derivable (@K4Axiom Atom) φ :=
  Derivable_mono (fun _ => KAxiom_implies_K4Axiom) h

/-- K-derivable formulas are K5-derivable: K5 extends K by adding the 5 axiom (Euclideanness). -/
theorem kDerivable_implies_k5Derivable (h : Derivable (@KAxiom Atom) φ) :
    Derivable (@K5Axiom Atom) φ :=
  Derivable_mono (fun _ => KAxiom_implies_K5Axiom) h

/-! ## From D -/

/-- D-derivable formulas are D4-derivable: D4 extends D by adding the 4 axiom (transitivity). -/
theorem dDerivable_implies_d4Derivable (h : Derivable (@DAxiom Atom) φ) :
    Derivable (@D4Axiom Atom) φ :=
  Derivable_mono (fun _ => DAxiom_implies_D4Axiom) h

/-- D-derivable formulas are D5-derivable: D5 extends D by adding the 5 axiom (Euclideanness). -/
theorem dDerivable_implies_d5Derivable (h : Derivable (@DAxiom Atom) φ) :
    Derivable (@D5Axiom Atom) φ :=
  Derivable_mono (fun _ => DAxiom_implies_D5Axiom) h

/-- D-derivable formulas are DB-derivable: DB extends D by adding the B axiom (symmetry). -/
theorem dDerivable_implies_dbDerivable (h : Derivable (@DAxiom Atom) φ) :
    Derivable (@DBAxiom Atom) φ :=
  Derivable_mono (fun _ => DAxiom_implies_DBAxiom) h

/-! ## From T -/

/-- T-derivable formulas are S4-derivable: S4 extends T by adding the 4 axiom (transitivity). -/
theorem tDerivable_implies_s4Derivable (h : Derivable (@TAxiom Atom) φ) :
    Derivable (@S4Axiom Atom) φ :=
  Derivable_mono (fun _ => TAxiom_implies_S4Axiom) h

/-- T-derivable formulas are TB-derivable: TB extends T by adding the B axiom (symmetry). -/
theorem tDerivable_implies_tbDerivable (h : Derivable (@TAxiom Atom) φ) :
    Derivable (@TBAxiom Atom) φ :=
  Derivable_mono (fun _ => TAxiom_implies_TBAxiom) h

/-! ## From B (KB) -/

/-- B (KB)-derivable formulas are TB-derivable: TB extends B by adding the T axiom (reflexivity). -/
theorem bDerivable_implies_tbDerivable (h : Derivable (@BAxiom Atom) φ) :
    Derivable (@TBAxiom Atom) φ :=
  Derivable_mono (fun _ => BAxiom_implies_TBAxiom) h

/-- B (KB)-derivable formulas are DB-derivable: DB extends B by adding the D axiom (seriality). -/
theorem bDerivable_implies_dbDerivable (h : Derivable (@BAxiom Atom) φ) :
    Derivable (@DBAxiom Atom) φ :=
  Derivable_mono (fun _ => BAxiom_implies_DBAxiom) h

/-- B (KB)-derivable formulas are KB5-derivable: KB5 extends B by adding the 5 axiom
(Euclideanness). -/
theorem bDerivable_implies_kb5Derivable (h : Derivable (@BAxiom Atom) φ) :
    Derivable (@KB5Axiom Atom) φ :=
  Derivable_mono (fun _ => BAxiom_implies_KB5Axiom) h

/-! ## From K4 -/

/-- K4-derivable formulas are S4-derivable: S4 extends K4 by adding the T axiom (reflexivity). -/
theorem k4Derivable_implies_s4Derivable (h : Derivable (@K4Axiom Atom) φ) :
    Derivable (@S4Axiom Atom) φ :=
  Derivable_mono (fun _ => K4Axiom_implies_S4Axiom) h

/-- K4-derivable formulas are D4-derivable: D4 extends K4 by adding the D axiom (seriality). -/
theorem k4Derivable_implies_d4Derivable (h : Derivable (@K4Axiom Atom) φ) :
    Derivable (@D4Axiom Atom) φ :=
  Derivable_mono (fun _ => K4Axiom_implies_D4Axiom) h

/-- K4-derivable formulas are K45-derivable: K45 extends K4 by adding the 5 axiom
(Euclideanness). -/
theorem k4Derivable_implies_k45Derivable (h : Derivable (@K4Axiom Atom) φ) :
    Derivable (@K45Axiom Atom) φ :=
  Derivable_mono (fun _ => K4Axiom_implies_K45Axiom) h

/-! ## From K5 -/

/-- K5-derivable formulas are D5-derivable: D5 extends K5 by adding the D axiom (seriality). -/
theorem k5Derivable_implies_d5Derivable (h : Derivable (@K5Axiom Atom) φ) :
    Derivable (@D5Axiom Atom) φ :=
  Derivable_mono (fun _ => K5Axiom_implies_D5Axiom) h

/-- K5-derivable formulas are K45-derivable: K45 extends K5 by adding the 4 axiom (transitivity). -/
theorem k5Derivable_implies_k45Derivable (h : Derivable (@K5Axiom Atom) φ) :
    Derivable (@K45Axiom Atom) φ :=
  Derivable_mono (fun _ => K5Axiom_implies_K45Axiom) h

/-- K5-derivable formulas are KB5-derivable: KB5 extends K5 by adding the B axiom (symmetry). -/
theorem k5Derivable_implies_kb5Derivable (h : Derivable (@K5Axiom Atom) φ) :
    Derivable (@KB5Axiom Atom) φ :=
  Derivable_mono (fun _ => K5Axiom_implies_KB5Axiom) h

/-! ## From K45 -/

/-- K45-derivable formulas are D45-derivable: D45 extends K45 by adding the D axiom (seriality). -/
theorem k45Derivable_implies_d45Derivable (h : Derivable (@K45Axiom Atom) φ) :
    Derivable (@D45Axiom Atom) φ :=
  Derivable_mono (fun _ => K45Axiom_implies_D45Axiom) h

/-! ## From D4 and D5 -/

/-- D4-derivable formulas are D45-derivable: D45 extends D4 by adding the 5 axiom
(Euclideanness). -/
theorem d4Derivable_implies_d45Derivable (h : Derivable (@D4Axiom Atom) φ) :
    Derivable (@D45Axiom Atom) φ :=
  Derivable_mono (fun _ => D4Axiom_implies_D45Axiom) h

/-- D5-derivable formulas are D45-derivable: D45 extends D5 by adding the 4 axiom (transitivity). -/
theorem d5Derivable_implies_d45Derivable (h : Derivable (@D5Axiom Atom) φ) :
    Derivable (@D45Axiom Atom) φ :=
  Derivable_mono (fun _ => D5Axiom_implies_D45Axiom) h

/-! ## Into S5 -/

/-- S4-derivable formulas are S5-derivable: S5 extends S4 by adding the B axiom (symmetry). -/
theorem s4Derivable_implies_s5Derivable (h : Derivable (@S4Axiom Atom) φ) :
    Derivable (@ModalAxiom Atom) φ :=
  Derivable_mono (fun _ => S4Axiom_implies_ModalAxiom) h

/-- TB-derivable formulas are S5-derivable: S5 extends TB by adding the 4 axiom (transitivity). -/
theorem tbDerivable_implies_s5Derivable (h : Derivable (@TBAxiom Atom) φ) :
    Derivable (@ModalAxiom Atom) φ :=
  Derivable_mono (fun _ => TBAxiom_implies_ModalAxiom) h

/-! ## Transitive Chain Theorems -/

/-- K-derivable formulas are S5-derivable via the chain K → T → S4 → S5. -/
theorem kDerivable_implies_s5Derivable (h : Derivable (@KAxiom Atom) φ) :
    Derivable (@ModalAxiom Atom) φ :=
  h |> kDerivable_implies_tDerivable |> tDerivable_implies_s4Derivable
    |> s4Derivable_implies_s5Derivable

/-- K-derivable formulas are D45-derivable via the chain K → D → D4 → D45. -/
theorem kDerivable_implies_d45Derivable (h : Derivable (@KAxiom Atom) φ) :
    Derivable (@D45Axiom Atom) φ :=
  h |> kDerivable_implies_dDerivable |> dDerivable_implies_d4Derivable
    |> d4Derivable_implies_d45Derivable

/-- D-derivable formulas are D45-derivable via the chain D → D4 → D45. -/
theorem dDerivable_implies_d45Derivable (h : Derivable (@DAxiom Atom) φ) :
    Derivable (@D45Axiom Atom) φ :=
  h |> dDerivable_implies_d4Derivable |> d4Derivable_implies_d45Derivable

end Cslib.Logic.Modal

end
