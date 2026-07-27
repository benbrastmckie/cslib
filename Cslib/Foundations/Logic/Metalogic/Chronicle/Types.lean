/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

import Cslib.Init
public import Cslib.Foundations.Logic.Metalogic.Chronicle.ChronicleInterface
public import Mathlib.Data.Finset.Attr
public import Mathlib.Data.Finset.Defs

/-! # Chronicle Types — Shared Bimodal/Temporal Chronicle Data Structures

Generic version of the ~95%-shared `ChronicleTypes` layer (DCS infrastructure,
r-relations, r-maximality, Burgess content relations, the `Chronicle` structure,
conditions c0-c5', `ValidChronicle`, C3 consequences, `ChronicleInvariant`, and basic
subset/intersection theorems), parameterized by a `ChronicleInterface F` value.
Both `Logics/Bimodal/.../Chronicle/ChronicleTypes.lean` and
`Logics/Temporal/.../Chronicle/ChronicleTypes.lean` instantiate this module and
re-export its declarations under their existing names.

## References

* Ported from
  `Cslib/Logics/Bimodal/Metalogic/BXCanonical/Chronicle/ChronicleTypes.lean` and
  `Cslib/Logics/Temporal/Metalogic/Chronicle/ChronicleTypes.lean`.
* Burgess 1982: "Axioms for tense logic II: Time periods"
-/

set_option linter.style.emptyLine false
set_option linter.dupNamespace false

@[expose] public section

namespace Cslib.Logic.Metalogic.Chronicle

attribute [local instance] Classical.propDecidable

variable {F : Type*}

/-! ## Adjacency Predicate

Formula-independent: shared verbatim by both trees, no `ChronicleInterface` needed. -/

/-- Two rationals are adjacent in `dom` if they are consecutive elements with no point
between them. -/
def Adjacent (dom : Finset Rat) (x y : Rat) : Prop :=
  x ∈ dom ∧ y ∈ dom ∧ x < y ∧ ∀ z ∈ dom, ¬(x < z ∧ z < y)

/-! ## Deductively Closed Sets (DCS) -/

/-- A set is deductively closed (consistent + closed under derivation) w.r.t. `I`. -/
def SetDeductivelyClosed (I : ChronicleInterface F) (Omega : Set F) : Prop :=
  CISetConsistent I Omega ∧ CIClosedUnderDerivation I Omega

/-- Every MCS is deductively closed. -/
theorem mcs_is_dcs (I : ChronicleInterface F) {Omega : Set F}
    (h : CISetMaximalConsistent I Omega) :
    SetDeductivelyClosed I Omega :=
  ⟨h.1, fun _ _ hL hd => I.mcsClosedUnderDerivation h hL hd⟩

/-- A CUD set contains all theorems. -/
theorem cud_contains_theorems (I : ChronicleInterface F) {Omega : Set F}
    (h : CIClosedUnderDerivation I Omega)
    {phi : F} (hd : I.Deriv [] phi) : phi ∈ Omega :=
  h [] phi (fun _ h => absurd h List.not_mem_nil) hd

/-- A DCS contains all theorems. -/
theorem dcs_contains_theorems (I : ChronicleInterface F) {Omega : Set F}
    (h : SetDeductivelyClosed I Omega)
    {phi : F} (hd : I.Deriv [] phi) : phi ∈ Omega :=
  cud_contains_theorems I h.2 hd

/-- Modus ponens in a CUD set. -/
theorem cud_modus_ponens (I : ChronicleInterface F) {Omega : Set F}
    (h : CIClosedUnderDerivation I Omega)
    {phi psi : F} (h_imp : I.imp phi psi ∈ Omega) (h_phi : phi ∈ Omega) : psi ∈ Omega := by
  apply h [phi, I.imp phi psi] psi
  · intro chi h_mem
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at h_mem
    rcases h_mem with rfl | rfl
    · exact h_phi
    · exact h_imp
  · exact I.modusPonens (φ := phi) (ψ := psi)
      (I.assumption (Γ := [phi, I.imp phi psi]) (φ := I.imp phi psi) (by simp))
      (I.assumption (Γ := [phi, I.imp phi psi]) (φ := phi) (by simp))

/-- Modus ponens in a DCS. -/
theorem dcs_modus_ponens (I : ChronicleInterface F) {Omega : Set F}
    (h : SetDeductivelyClosed I Omega)
    {phi psi : F} (h_imp : I.imp phi psi ∈ Omega) (h_phi : phi ∈ Omega) : psi ∈ Omega :=
  cud_modus_ponens I h.2 h_imp h_phi

/-- A CUD set is closed under conjunction. -/
theorem cud_conj_closed (I : ChronicleInterface F) {Omega : Set F}
    (h : CIClosedUnderDerivation I Omega)
    {phi psi : F} (h_phi : phi ∈ Omega) (h_psi : psi ∈ Omega) : I.and phi psi ∈ Omega := by
  have h_pair := cud_contains_theorems I h (I.pairing phi psi)
  exact cud_modus_ponens I h (cud_modus_ponens I h h_pair h_phi) h_psi

/-- A DCS is closed under conjunction. -/
theorem dcs_conj_closed (I : ChronicleInterface F) {Omega : Set F}
    (h : SetDeductivelyClosed I Omega)
    {phi psi : F} (h_phi : phi ∈ Omega) (h_psi : psi ∈ Omega) : I.and phi psi ∈ Omega :=
  cud_conj_closed I h.2 h_phi h_psi

/-- A CUD set with a non-member is SDC. -/
theorem cud_not_mem_is_sdc (I : ChronicleInterface F) {B : Set F}
    (h_cud : CIClosedUnderDerivation I B)
    {phi : F} (h_not_mem : phi ∉ B) : SetDeductivelyClosed I B := by
  refine ⟨?_, h_cud⟩
  intro L hL ⟨d⟩
  have h_bot : I.bot ∈ B := h_cud L I.bot hL d
  have h_efq : I.Deriv [] (I.imp I.bot phi) := I.efq phi
  exact h_not_mem (cud_modus_ponens I h_cud (cud_contains_theorems I h_cud h_efq) h_bot)

/-! ## The r-Relation (Burgess Lemma 2.3) -/

/-- The r-relation holds between sets `A` and `B` if every until-formula in `A` is
witnessed in `B` (Burgess Lemma 2.3). -/
def rRelation (I : ChronicleInterface F) (A B : Set F) : Prop :=
  ∀ (gamma delta : F), I.untl gamma delta ∈ A →
    delta ∈ B ∨ (gamma ∈ B ∧ I.untl gamma delta ∈ B)

/-- The since-variant of the r-relation, witnessing since-formulas in `A` via `B`. -/
def rRelationSince (I : ChronicleInterface F) (A B : Set F) : Prop :=
  ∀ (gamma delta : F), I.snce gamma delta ∈ A →
    delta ∈ B ∨ (gamma ∈ B ∧ I.snce gamma delta ∈ B)

/-- The combined r3-relation: `A` r-relates to `B` via until and `C` r-since-relates to
`B`. -/
def r3Relation (I : ChronicleInterface F) (A B C : Set F) : Prop :=
  rRelation I A B ∧ rRelationSince I C B

/-- The since-variant of r3: `A` r-since-relates to `B` and `C` r-relates to `B`. -/
def r3RelationSince (I : ChronicleInterface F) (A B C : Set F) : Prop :=
  rRelationSince I A B ∧ rRelation I C B

/-! ## R-Maximality -/

/-- A set `B` is r-maximal for `A` if it is deductively closed, r-relates to `A`, and no
proper extension also r-relates to `A`. -/
def rMaximal (I : ChronicleInterface F) (A B : Set F) : Prop :=
  SetDeductivelyClosed I B ∧
  rRelation I A B ∧
  ∀ (C : Set F), SetDeductivelyClosed I C → B ⊂ C → ¬rRelation I A C

/-- The since-variant of r-maximality: `B` is deductively closed, r-since-relates to `A`,
and no proper extension does. -/
def rMaximalSince (I : ChronicleInterface F) (A B : Set F) : Prop :=
  SetDeductivelyClosed I B ∧
  rRelationSince I A B ∧
  ∀ (C : Set F), SetDeductivelyClosed I C → B ⊂ C → ¬rRelationSince I A C

/-- A set `B` is R3-maximal for `(A, C)` if it is deductively closed, r3-relates to
`(A, C)`, and no proper extension does. -/
def R3Maximal (I : ChronicleInterface F) (A B C : Set F) : Prop :=
  SetDeductivelyClosed I B ∧
  r3Relation I A B C ∧
  ∀ (D : Set F), SetDeductivelyClosed I D → B ⊂ D → ¬r3Relation I A D C

/-- The since-variant of R3-maximality: `B` r3-since-relates to `(A, C)` and no proper
extension does. -/
def R3MaximalSince (I : ChronicleInterface F) (A B C : Set F) : Prop :=
  SetDeductivelyClosed I B ∧
  r3RelationSince I A B C ∧
  ∀ (D : Set F), SetDeductivelyClosed I D → B ⊂ D → ¬r3RelationSince I A D C

/-! ## Chronicle Structure -/

/-- A chronicle: a finite rational domain with point-sets `f` and interval-sets `g`
(Burgess 1982, Section 2). -/
@[nolint dupNamespace]
structure Chronicle (F : Type*) where
  /-- Point-set function assigning a formula set to each rational point. -/
  f : Rat → Set F
  /-- Interval-set function assigning a formula set to each rational interval. -/
  g : Rat → Rat → Set F
  /-- Finite set of rational time-points forming the chronicle domain. -/
  dom : Finset Rat

-- Suppress dupNamespace for auto-generated Chronicle declarations
attribute [nolint dupNamespace] Chronicle.mk Chronicle.rec
  Chronicle.f Chronicle.g Chronicle.dom

/-! ## Chronicle Conditions -/

/-- Condition c0: every point in the domain carries a maximal consistent set. -/
@[nolint dupNamespace]
def Chronicle.c0 (I : ChronicleInterface F) (chi : Chronicle F) : Prop :=
  ∀ x ∈ chi.dom, CISetMaximalConsistent I (chi.f x)

/-- Condition c1: every interval-set `g x y` is closed under derivation. -/
@[nolint dupNamespace]
def Chronicle.c1 (I : ChronicleInterface F) (chi : Chronicle F) : Prop :=
  ∀ x y : Rat, x ∈ chi.dom → y ∈ chi.dom → x < y → CIClosedUnderDerivation I (chi.g x y)

/-- Condition c2: the interval-set `g x y` r3-relates the point-sets at each pair of
domain points. -/
@[nolint dupNamespace]
def Chronicle.c2 (I : ChronicleInterface F) (chi : Chronicle F) : Prop :=
  ∀ x y : Rat, x ∈ chi.dom → y ∈ chi.dom → x < y → r3Relation I (chi.f x) (chi.g x y) (chi.f y)

/-- Condition c2': the interval-set is Burgess-R3-maximal at each adjacent pair of domain
points. -/
@[nolint dupNamespace]
def Chronicle.c2' (I : ChronicleInterface F) (chi : Chronicle F) : Prop :=
  ∀ x y : Rat, Adjacent chi.dom x y →
    CIBurgessR3Maximal I (chi.f x) (chi.g x y) (chi.f y)

/-- Condition c3: the interval-set over `[x,z]` decomposes as `g x y ∩ f y ∩ g y z` for
intermediate `y`. -/
@[nolint dupNamespace]
def Chronicle.c3 (chi : Chronicle F) : Prop :=
  ∀ x y z : Rat, x ∈ chi.dom → y ∈ chi.dom → z ∈ chi.dom →
    x < y → y < z → chi.g x z = chi.g x y ∩ chi.f y ∩ chi.g y z

/-- Condition c4: if `¬(delta U gamma) ∈ f x` and `delta ∈ f y` then some intermediate
point witnesses `¬gamma`. -/
@[nolint dupNamespace]
def Chronicle.c4 (I : ChronicleInterface F) (chi : Chronicle F) : Prop :=
  ∀ x y : Rat, x ∈ chi.dom → y ∈ chi.dom → x < y →
    ∀ (gamma delta : F),
      I.imp (I.untl gamma delta) I.bot ∈ chi.f x →
      delta ∈ chi.f y →
      ∃ z ∈ chi.dom, x < z ∧ z < y ∧ I.imp gamma I.bot ∈ chi.f z

/-- Condition c4': the since-variant of c4, witnessing `¬gamma` between `y` and `x` in the
past direction. -/
@[nolint dupNamespace]
def Chronicle.c4' (I : ChronicleInterface F) (chi : Chronicle F) : Prop :=
  ∀ x y : Rat, x ∈ chi.dom → y ∈ chi.dom → y < x →
    ∀ (gamma delta : F),
      I.imp (I.snce gamma delta) I.bot ∈ chi.f x →
      delta ∈ chi.f y →
      ∃ z ∈ chi.dom, y < z ∧ z < x ∧ I.imp gamma I.bot ∈ chi.f z

/-- Condition c5: if `delta U gamma ∈ f x` then some future `y` witnesses `delta` with
`gamma` holding at all intermediate points. -/
@[nolint dupNamespace]
def Chronicle.c5 (I : ChronicleInterface F) (chi : Chronicle F) : Prop :=
  ∀ x ∈ chi.dom,
    ∀ (gamma delta : F),
      I.untl gamma delta ∈ chi.f x →
      ∃ y ∈ chi.dom, x < y ∧ delta ∈ chi.f y ∧
        ∀ z ∈ chi.dom, x < z → z < y →
          gamma ∈ chi.f z ∧ I.untl gamma delta ∈ chi.f z

/-- Condition c5': the since-variant of c5, witnessing `delta` in the past with `gamma` at
all intermediate points. -/
@[nolint dupNamespace]
def Chronicle.c5' (I : ChronicleInterface F) (chi : Chronicle F) : Prop :=
  ∀ x ∈ chi.dom,
    ∀ (gamma delta : F),
      I.snce gamma delta ∈ chi.f x →
      ∃ y ∈ chi.dom, y < x ∧ delta ∈ chi.f y ∧
        ∀ z ∈ chi.dom, y < z → z < x →
          gamma ∈ chi.f z ∧ I.snce gamma delta ∈ chi.f z

/-! ## Valid Chronicle -/

/-- A valid chronicle: a `Chronicle` satisfying all conditions c0–c5'. -/
structure ValidChronicle (F : Type*) (I : ChronicleInterface F) extends Chronicle F where
  hc0 : toChronicle.c0 I
  hc1 : toChronicle.c1 I
  hc2 : toChronicle.c2 I
  hc2' : toChronicle.c2' I
  hc3 : toChronicle.c3
  hc4 : toChronicle.c4 I
  hc4' : toChronicle.c4' I
  hc5 : toChronicle.c5 I
  hc5' : toChronicle.c5' I

/-! ## C3 Consequences -/

theorem c3_interval_subset_point (chi : Chronicle F) (h_c3 : chi.c3)
    {x y z : Rat} (hx : x ∈ chi.dom) (hy : y ∈ chi.dom) (hz : z ∈ chi.dom)
    (hxy : x < y) (hyz : y < z) :
    chi.g x z ⊆ chi.f y := by
  intro phi hphi; rw [h_c3 x y z hx hy hz hxy hyz] at hphi; exact hphi.1.2

theorem c3_interval_subset_left (chi : Chronicle F) (h_c3 : chi.c3)
    {x y z : Rat} (hx : x ∈ chi.dom) (hy : y ∈ chi.dom) (hz : z ∈ chi.dom)
    (hxy : x < y) (hyz : y < z) :
    chi.g x z ⊆ chi.g x y := by
  intro phi hphi; rw [h_c3 x y z hx hy hz hxy hyz] at hphi; exact hphi.1.1

theorem c3_interval_subset_right (chi : Chronicle F) (h_c3 : chi.c3)
    {x y z : Rat} (hx : x ∈ chi.dom) (hy : y ∈ chi.dom) (hz : z ∈ chi.dom)
    (hxy : x < y) (hyz : y < z) :
    chi.g x z ⊆ chi.g y z := by
  intro phi hphi; rw [h_c3 x y z hx hy hz hxy hyz] at hphi; exact hphi.2

/-! ## ChronicleInvariant Bundle -/

/-- Bundle of the core chronicle invariants (c0, c1, c2', c3) used throughout the
canonicity argument. -/
structure ChronicleInvariant (I : ChronicleInterface F) (chi : Chronicle F) : Prop where
  hc0 : chi.c0 I
  hc1 : chi.c1 I
  hc2' : chi.c2' I
  hc3 : chi.c3

/-! ## Basic Properties -/

theorem rRelation_subset (I : ChronicleInterface F) {A B C : Set F}
    (h_r : rRelation I A B) (h_sub : B ⊆ C) : rRelation I A C := by
  intro gamma delta h_until
  rcases h_r gamma delta h_until with h_delta | ⟨h_gamma, h_u⟩
  · exact Or.inl (h_sub h_delta)
  · exact Or.inr ⟨h_sub h_gamma, h_sub h_u⟩

theorem rRelationSince_subset (I : ChronicleInterface F) {A B C : Set F}
    (h_r : rRelationSince I A B) (h_sub : B ⊆ C) : rRelationSince I A C := by
  intro gamma delta h_since
  rcases h_r gamma delta h_since with h_delta | ⟨h_gamma, h_s⟩
  · exact Or.inl (h_sub h_delta)
  · exact Or.inr ⟨h_sub h_gamma, h_sub h_s⟩

theorem r3Relation_implies_rRelation (I : ChronicleInterface F) {A B C : Set F}
    (h : r3Relation I A B C) : rRelation I A B := h.1

theorem r3Relation_implies_rRelationSince (I : ChronicleInterface F) {A B C : Set F}
    (h : r3Relation I A B C) : rRelationSince I C B := h.2

theorem r3Relation_subset (I : ChronicleInterface F) {A B B' C : Set F}
    (h : r3Relation I A B C) (h_sub : B ⊆ B') : r3Relation I A B' C :=
  ⟨rRelation_subset I h.1 h_sub, rRelationSince_subset I h.2 h_sub⟩

theorem R3Maximal_dcs (I : ChronicleInterface F) {A B C : Set F}
    (h : R3Maximal I A B C) : SetDeductivelyClosed I B := h.1

theorem R3Maximal_r3 (I : ChronicleInterface F) {A B C : Set F}
    (h : R3Maximal I A B C) : r3Relation I A B C := h.2.1

theorem R3Maximal_rRelation (I : ChronicleInterface F) {A B C : Set F}
    (h : R3Maximal I A B C) : rRelation I A B := h.2.1.1

/-! ## DCS Intersection Properties -/

theorem dcs_inter_dcs (I : ChronicleInterface F) {S1 S2 : Set F}
    (h1 : SetDeductivelyClosed I S1) (h2 : SetDeductivelyClosed I S2)
    (h_cons : CISetConsistent I (S1 ∩ S2)) :
    SetDeductivelyClosed I (S1 ∩ S2) := by
  exact ⟨h_cons, fun L phi hL hd => ⟨h1.2 L phi (fun psi hpsi => (hL psi hpsi).1) hd,
    h2.2 L phi (fun psi hpsi => (hL psi hpsi).2) hd⟩⟩

theorem dcs_inter_mcs (I : ChronicleInterface F) {S1 S2 : Set F}
    (h1 : SetDeductivelyClosed I S1) (h2 : CISetMaximalConsistent I S2)
    (h_cons : CISetConsistent I (S1 ∩ S2)) :
    SetDeductivelyClosed I (S1 ∩ S2) :=
  dcs_inter_dcs I h1 (mcs_is_dcs I h2) h_cons

theorem SetConsistent_of_subset (I : ChronicleInterface F) {Omega T : Set F}
    (h_sub : Omega ⊆ T) (h_cons : CISetConsistent I T) : CISetConsistent I Omega := by
  intro L hL hd
  exact h_cons L (fun psi hpsi => h_sub (hL psi hpsi)) hd

theorem three_way_inter_consistent (I : ChronicleInterface F) {S1 S2 S3 : Set F}
    (h3_cons : CISetConsistent I S3) :
    CISetConsistent I (S1 ∩ S2 ∩ S3) :=
  SetConsistent_of_subset I (fun _ h => h.2) h3_cons

theorem dcs_inter_mcs_inter_dcs (I : ChronicleInterface F) {S1 S2 S3 : Set F}
    (h1 : SetDeductivelyClosed I S1) (h2 : CISetMaximalConsistent I S2)
    (h3 : SetDeductivelyClosed I S3)
    (h_cons : CISetConsistent I (S1 ∩ S2 ∩ S3)) :
    SetDeductivelyClosed I (S1 ∩ S2 ∩ S3) := by
  exact ⟨h_cons, fun L phi hL hd =>
    ⟨⟨h1.2 L phi (fun psi hpsi => (hL psi hpsi).1.1) hd,
      (mcs_is_dcs I h2).2 L phi (fun psi hpsi => (hL psi hpsi).1.2) hd⟩,
      h3.2 L phi (fun psi hpsi => (hL psi hpsi).2) hd⟩⟩

end Cslib.Logic.Metalogic.Chronicle
