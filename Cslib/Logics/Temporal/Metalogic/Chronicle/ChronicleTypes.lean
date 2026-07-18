/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Temporal.Metalogic.PropositionalHelpers
public import Cslib.Logics.Temporal.Metalogic.MCS
public import Cslib.Logics.Temporal.Metalogic.GeneralizedNecessitation
public import Cslib.Foundations.Logic.Metalogic.Chronicle.Types

/-!
# Chronicle Types for Temporal Logic

DCS infrastructure, r-relation definitions, r-maximality, and Burgess relation
definitions for the temporal chronicle construction.

## Status (task 530, Phase 1)

The DCS infrastructure (`ClosedUnderDerivation`, `SetDeductivelyClosed`, `mcs_is_dcs`,
`cud_*`/`dcs_*`), r-relations, r-maximality, and Burgess content relations are now thin
instance + re-export wrappers over the generic
`Cslib.Foundations.Logic.Metalogic.Chronicle.Types` module, instantiated by
`temporalChronicleInterface : ChronicleInterface (Formula Atom)` (a single value, since
Temporal is fixed to `FrameClass.Base` -- no `fc`-indexed family needed, mirroring
`temporalSinceInterface` in `PointInsertion/Since.lean`).

The `Chronicle` structure and its conditions (c0-c5', `ValidChronicle`,
`ChronicleInvariant`, C3 consequences) stay logic-local (unchanged), matching the Bimodal
tree's same deviation: routing them through a generic-structure bridge (`toGeneric`) broke
downstream `rcases`/`simp` proofs that pattern-match on Finset-membership subterms nested
inside condition statements. See `Bimodal/.../ChronicleTypes.lean`'s "Chronicle Structure"
section for the full rationale.

## References

* Ported from Cslib/Logics/Bimodal/Metalogic/BXCanonical/Chronicle/ChronicleTypes.lean
* [J. Burgess, *Axioms for Tense Logic II: Time Periods*][Burgess1982II]
-/

set_option linter.style.emptyLine false
set_option linter.dupNamespace false

@[expose] public section

namespace Cslib.Logic.Temporal.Metalogic.Chronicle

open Cslib.Logic.Temporal
open Cslib.Logic.Temporal.Metalogic
open Cslib.Logic.Metalogic.Chronicle (ChronicleInterface)

attribute [local instance] Classical.propDecidable

variable {Atom : Type*}

/-! ## `ChronicleInterface` Instance (task 530, Phase 1)

Populates every field of the shared Foundations interface with Temporal's own apparatus
at `FrameClass.Base`. Not marked `private`: the public re-export `abbrev`s below unfold to
expressions mentioning it directly, and Lean's module-privacy system disallows a `public
section` declaration from referencing a `private` one. -/

/-- The `ChronicleInterface` instance for Temporal (task 530). -/
noncomputable def temporalChronicleInterface : ChronicleInterface (Formula Atom) where
  bot := Formula.bot
  imp := Formula.imp
  and := Formula.and
  or := Formula.or
  untl := Formula.untl
  snce := Formula.snce
  somePast := Formula.somePast
  allPast := Formula.allPast
  allFuture := Formula.allFuture
  someFuture := Formula.someFuture
  Deriv := DerivationTree FrameClass.Base
  assumption := fun h => DerivationTree.assumption _ _ h
  modusPonens := fun h1 h2 => DerivationTree.modus_ponens _ _ _ h1 h2
  weakening := fun Γ Δ φ d hsub => DerivationTree.weakening Γ Δ φ d hsub
  deductionTheorem := fun Γ φ ψ d => deductionTheorem Γ φ ψ d
  identity' := fun φ => identity φ
  impTrans := fun h1 h2 => impTrans h1 h2
  lceImp := fun φ ψ => lceImp φ ψ
  rceImp := fun φ ψ => rceImp φ ψ
  pairing := fun φ ψ => pairing φ ψ
  efq := fun φ => efqAxiom φ
  pastNecessitation := fun φ d => pastNecessitation φ d
  mcsClosedUnderDerivation := by
    intro Ω hmcs L φ hL hd
    exact temporal_closed_under_derivation hmcs hL ⟨hd⟩
  theoremInMcs := by
    intro Ω hmcs φ hd
    exact temporal_closed_under_derivation hmcs (fun _ h => absurd h List.not_mem_nil) ⟨hd⟩
  negationComplete := fun hmcs φ => temporal_negation_complete hmcs φ
  negExcludes := by
    intro Ω hmcs φ hneg hmem
    exact mcs_not_mem_of_neg hmcs hneg hmem
  cudContainsTheorems := by
    intro Ω h φ hd
    exact h [] φ (fun _ hc => absurd hc List.not_mem_nil) hd

/-! ## Deductively Closed Sets (DCS) -/

/-- A set is closed under derivation. -/
abbrev ClosedUnderDerivation (Omega : Set (Formula Atom)) : Prop :=
  Cslib.Logic.Metalogic.Chronicle.CIClosedUnderDerivation temporalChronicleInterface Omega

/-- A set is deductively closed (consistent + closed under derivation). -/
abbrev SetDeductivelyClosed (Omega : Set (Formula Atom)) : Prop :=
  Cslib.Logic.Metalogic.Chronicle.SetDeductivelyClosed temporalChronicleInterface Omega

/-- Every MCS is deductively closed. -/
theorem mcs_is_dcs {Omega : Set (Formula Atom)}
    (h : Temporal.SetMaximalConsistent Omega) :
    SetDeductivelyClosed Omega :=
  Cslib.Logic.Metalogic.Chronicle.mcs_is_dcs temporalChronicleInterface (Omega := Omega) h

/-- A CUD set contains all theorems. -/
theorem cud_contains_theorems {Omega : Set (Formula Atom)}
    (h : ClosedUnderDerivation Omega)
    {phi : Formula Atom} (hd : DerivationTree FrameClass.Base [] phi) : phi ∈ Omega :=
  Cslib.Logic.Metalogic.Chronicle.cud_contains_theorems
    temporalChronicleInterface (Omega := Omega) h (phi := phi) hd

/-- A DCS contains all theorems. -/
theorem dcs_contains_theorems {Omega : Set (Formula Atom)}
    (h : SetDeductivelyClosed Omega)
    {phi : Formula Atom} (hd : DerivationTree FrameClass.Base [] phi) : phi ∈ Omega :=
  cud_contains_theorems h.2 hd

/-- Modus ponens in a CUD set. -/
theorem cud_modus_ponens {Omega : Set (Formula Atom)}
    (h : ClosedUnderDerivation Omega)
    {phi psi : Formula Atom} (h_imp : (phi → psi) ∈ Omega) (h_phi : phi ∈ Omega) : psi ∈ Omega :=
  Cslib.Logic.Metalogic.Chronicle.cud_modus_ponens
    temporalChronicleInterface (Omega := Omega) h (phi := phi) (psi := psi) h_imp h_phi

/-- Modus ponens in a DCS. -/
theorem dcs_modus_ponens {Omega : Set (Formula Atom)}
    (h : SetDeductivelyClosed Omega)
    {phi psi : Formula Atom} (h_imp : (phi → psi) ∈ Omega) (h_phi : phi ∈ Omega) : psi ∈ Omega :=
  cud_modus_ponens h.2 h_imp h_phi

/-- A CUD set is closed under conjunction. -/
theorem cud_conj_closed {Omega : Set (Formula Atom)}
    (h : ClosedUnderDerivation Omega)
    {phi psi : Formula Atom} (h_phi : phi ∈ Omega) (h_psi : psi ∈ Omega) :
    (phi ∧ psi) ∈ Omega :=
  Cslib.Logic.Metalogic.Chronicle.cud_conj_closed
    temporalChronicleInterface (Omega := Omega) h (phi := phi) (psi := psi) h_phi h_psi

/-- A DCS is closed under conjunction. -/
theorem dcs_conj_closed {Omega : Set (Formula Atom)}
    (h : SetDeductivelyClosed Omega)
    {phi psi : Formula Atom} (h_phi : phi ∈ Omega) (h_psi : psi ∈ Omega) :
    (phi ∧ psi) ∈ Omega :=
  cud_conj_closed h.2 h_phi h_psi

/-- A CUD set with a non-member is SDC. -/
theorem cud_not_mem_is_sdc {B : Set (Formula Atom)}
    (h_cud : ClosedUnderDerivation B)
    {phi : Formula Atom} (h_not_mem : phi ∉ B) : SetDeductivelyClosed B :=
  Cslib.Logic.Metalogic.Chronicle.cud_not_mem_is_sdc
    temporalChronicleInterface (B := B) h_cud (phi := phi) h_not_mem

/-! ## The r-Relation (Burgess Lemma 2.3)

`rRelation`/`rRelationSince`/`r3Relation`/`r3RelationSince`/`burgessR`/`burgessRSet`/
`burgessRSince`/`burgessRSetSince`/`burgessR3` depend only on `untl`/`snce`, which never
vary across Temporal's single interface value, so `temporalChronicleInterface` is used
directly (no `fc`-family to pick from, unlike Bimodal). -/

/-- The r-relation: B is a right-successor of A for the Until operator (Burgess Lemma 2.3). -/
abbrev rRelation (A B : Set (Formula Atom)) : Prop :=
  Cslib.Logic.Metalogic.Chronicle.rRelation temporalChronicleInterface A B

/-- The r-relation for the Since operator: B is a left-successor of A. -/
abbrev rRelationSince (A B : Set (Formula Atom)) : Prop :=
  Cslib.Logic.Metalogic.Chronicle.rRelationSince temporalChronicleInterface A B

/-- The combined r3-relation: B is a successor of A (Until) and C (Since). -/
abbrev r3Relation (A B C : Set (Formula Atom)) : Prop :=
  Cslib.Logic.Metalogic.Chronicle.r3Relation temporalChronicleInterface A B C

/-- The combined r3-relation for Since: B is a Since-successor of A and an Until-successor of C. -/
abbrev r3RelationSince (A B C : Set (Formula Atom)) : Prop :=
  Cslib.Logic.Metalogic.Chronicle.r3RelationSince temporalChronicleInterface A B C

/-! ## R-Maximality -/

/-- A set B is r-maximal over A if it is deductively closed,
satisfies rRelation, and no proper superset does. -/
abbrev rMaximal (A B : Set (Formula Atom)) : Prop :=
  Cslib.Logic.Metalogic.Chronicle.rMaximal temporalChronicleInterface A B

/-- A set B is r-maximal over A for Since if it is deductively closed,
satisfies rRelationSince, and no proper superset does. -/
abbrev rMaximalSince (A B : Set (Formula Atom)) : Prop :=
  Cslib.Logic.Metalogic.Chronicle.rMaximalSince temporalChronicleInterface A B

/-- A set B is R3-maximal over A and C if it satisfies r3Relation and no proper superset does. -/
abbrev R3Maximal (A B C : Set (Formula Atom)) : Prop :=
  Cslib.Logic.Metalogic.Chronicle.R3Maximal temporalChronicleInterface A B C

/-- A set B is R3-maximal (Since variant) over A and C if it satisfies
r3RelationSince and no proper superset does. -/
abbrev R3MaximalSince (A B C : Set (Formula Atom)) : Prop :=
  Cslib.Logic.Metalogic.Chronicle.R3MaximalSince temporalChronicleInterface A B C

/-! ## Burgess r-Relation (Content-Based) -/

/-- The Burgess r-relation: every formula in C appears as the left
argument of `gamma U beta` in A. -/
abbrev burgessR (A : Set (Formula Atom)) (beta : Formula Atom) (C : Set (Formula Atom)) : Prop :=
  Cslib.Logic.Metalogic.Chronicle.ciBurgessR temporalChronicleInterface A beta C

/-- Lifts `burgessR` to all beta in B: every pair `(beta, gamma)` with
beta ∈ B, gamma ∈ C satisfies burgessR. -/
abbrev burgessRSet (A B C : Set (Formula Atom)) : Prop :=
  Cslib.Logic.Metalogic.Chronicle.ciBurgessRSet temporalChronicleInterface A B C

/-- The Burgess r-relation for Since: every formula in C appears as
the left argument of `gamma S beta` in A. -/
abbrev burgessRSince
    (A : Set (Formula Atom)) (beta : Formula Atom) (C : Set (Formula Atom)) : Prop :=
  Cslib.Logic.Metalogic.Chronicle.ciBurgessRSince temporalChronicleInterface A beta C

/-- Lifts `burgessRSince` to all beta in B. -/
abbrev burgessRSetSince (A B C : Set (Formula Atom)) : Prop :=
  Cslib.Logic.Metalogic.Chronicle.ciBurgessRSetSince temporalChronicleInterface A B C

/-- The combined Burgess r3-relation: combines burgessRSet for Until
and burgessRSetSince for Since. -/
abbrev burgessR3 (A B C : Set (Formula Atom)) : Prop :=
  Cslib.Logic.Metalogic.Chronicle.ciBurgessR3 temporalChronicleInterface A B C

/-- B is a Burgess R3-maximal set over A and C: deductively closed,
satisfies burgessR3, and no proper superset does. -/
abbrev BurgessR3Maximal (A B C : Set (Formula Atom)) : Prop :=
  Cslib.Logic.Metalogic.Chronicle.CIBurgessR3Maximal temporalChronicleInterface A B C

/-! ## Adjacency Predicate -/

/-- Two rational points x < y in dom are adjacent if no dom-element lies strictly between them. -/
abbrev Adjacent (dom : Finset Rat) (x y : Rat) : Prop :=
  Cslib.Logic.Metalogic.Chronicle.Adjacent dom x y

/-! ## Chronicle Structure

Kept logic-local (unchanged); see the module docstring "Status" section. -/

/-- A chronicle: a finite sequence of MCS-labelled rational points with interval sets. -/
@[nolint dupNamespace]
structure Chronicle (Atom : Type*) where
  /-- Point labelling: assigns an MCS to each rational time point. -/
  f : Rat → Set (Formula Atom)
  /-- Interval labelling: assigns a set of formulas to each pair of rational time points. -/
  g : Rat → Rat → Set (Formula Atom)
  /-- The finite domain of rational time points. -/
  dom : Finset Rat

-- Suppress dupNamespace for auto-generated Chronicle declarations
attribute [nolint dupNamespace] Chronicle.mk Chronicle.rec
  Chronicle.f Chronicle.g Chronicle.dom

/-! ## Chronicle Conditions -/

/-- Condition c0: every point in the domain is labelled by an MCS. -/
@[nolint dupNamespace]
def Chronicle.c0 (chi : Chronicle Atom) : Prop :=
  ∀ x ∈ chi.dom, Temporal.SetMaximalConsistent (chi.f x)

/-- Condition c1: every interval label is closed under derivation. -/
@[nolint dupNamespace]
def Chronicle.c1 (chi : Chronicle Atom) : Prop :=
  ∀ x y : Rat, x ∈ chi.dom → y ∈ chi.dom → x < y → ClosedUnderDerivation (chi.g x y)

/-- Condition c2: every adjacent interval satisfies the r3-relation. -/
@[nolint dupNamespace]
def Chronicle.c2 (chi : Chronicle Atom) : Prop :=
  ∀ x y : Rat, x ∈ chi.dom → y ∈ chi.dom → x < y → r3Relation (chi.f x) (chi.g x y) (chi.f y)

/-- Condition c2': adjacent intervals satisfy Burgess R3-maximality. -/
@[nolint dupNamespace]
def Chronicle.c2' (chi : Chronicle Atom) : Prop :=
  ∀ x y : Rat, Adjacent chi.dom x y →
    BurgessR3Maximal (chi.f x) (chi.g x y) (chi.f y)

/-- Condition c3: the interval label for [x,z] decomposes as g(x,y) ∩ f(y) ∩ g(y,z). -/
@[nolint dupNamespace]
def Chronicle.c3 (chi : Chronicle Atom) : Prop :=
  ∀ x y z : Rat, x ∈ chi.dom → y ∈ chi.dom → z ∈ chi.dom →
    x < y → y < z → chi.g x z = chi.g x y ∩ chi.f y ∩ chi.g y z

/-- Condition c4: for ¬(δ U γ) at x and δ at y, there is a witness z between x and y with ¬γ. -/
@[nolint dupNamespace]
def Chronicle.c4 (chi : Chronicle Atom) : Prop :=
  ∀ x y : Rat, x ∈ chi.dom → y ∈ chi.dom → x < y →
    ∀ (gamma delta : Formula Atom),
      (gamma U delta).neg ∈ chi.f x →
      delta ∈ chi.f y →
      ∃ z ∈ chi.dom, x < z ∧ z < y ∧ gamma.neg ∈ chi.f z

/-- Condition c4': the Since-dual of c4: witness for ¬(δ S γ) at x going backwards. -/
@[nolint dupNamespace]
def Chronicle.c4' (chi : Chronicle Atom) : Prop :=
  ∀ x y : Rat, x ∈ chi.dom → y ∈ chi.dom → y < x →
    ∀ (gamma delta : Formula Atom),
      (gamma S delta).neg ∈ chi.f x →
      delta ∈ chi.f y →
      ∃ z ∈ chi.dom, y < z ∧ z < x ∧ gamma.neg ∈ chi.f z

/-- Condition c5: if δ U γ holds at x, there is a future witness y
where δ holds and γ U δ holds between. -/
@[nolint dupNamespace]
def Chronicle.c5 (chi : Chronicle Atom) : Prop :=
  ∀ x ∈ chi.dom,
    ∀ (gamma delta : Formula Atom),
      (gamma U delta) ∈ chi.f x →
      ∃ y ∈ chi.dom, x < y ∧ delta ∈ chi.f y ∧
        ∀ z ∈ chi.dom, x < z → z < y →
          gamma ∈ chi.f z ∧ (gamma U delta) ∈ chi.f z

/-- Condition c5': the Since-dual of c5: past witness for δ S γ at x. -/
@[nolint dupNamespace]
def Chronicle.c5' (chi : Chronicle Atom) : Prop :=
  ∀ x ∈ chi.dom,
    ∀ (gamma delta : Formula Atom),
      (gamma S delta) ∈ chi.f x →
      ∃ y ∈ chi.dom, y < x ∧ delta ∈ chi.f y ∧
        ∀ z ∈ chi.dom, y < z → z < x →
          gamma ∈ chi.f z ∧ (gamma S delta) ∈ chi.f z

/-! ## Valid Chronicle -/

/-- A valid chronicle: a chronicle satisfying all conditions c0–c5'. -/
structure ValidChronicle (Atom : Type*) extends Chronicle Atom where
  hc0 : toChronicle.c0
  hc1 : toChronicle.c1
  hc2 : toChronicle.c2
  hc2' : toChronicle.c2'
  hc3 : toChronicle.c3
  hc4 : toChronicle.c4
  hc4' : toChronicle.c4'
  hc5 : toChronicle.c5
  hc5' : toChronicle.c5'

/-! ## C3 Consequences -/

theorem c3_interval_subset_point (chi : Chronicle Atom) (h_c3 : chi.c3)
    {x y z : Rat} (hx : x ∈ chi.dom) (hy : y ∈ chi.dom) (hz : z ∈ chi.dom)
    (hxy : x < y) (hyz : y < z) :
    chi.g x z ⊆ chi.f y := by
  intro phi hphi; rw [h_c3 x y z hx hy hz hxy hyz] at hphi; exact hphi.1.2

theorem c3_interval_subset_left (chi : Chronicle Atom) (h_c3 : chi.c3)
    {x y z : Rat} (hx : x ∈ chi.dom) (hy : y ∈ chi.dom) (hz : z ∈ chi.dom)
    (hxy : x < y) (hyz : y < z) :
    chi.g x z ⊆ chi.g x y := by
  intro phi hphi; rw [h_c3 x y z hx hy hz hxy hyz] at hphi; exact hphi.1.1

theorem c3_interval_subset_right (chi : Chronicle Atom) (h_c3 : chi.c3)
    {x y z : Rat} (hx : x ∈ chi.dom) (hy : y ∈ chi.dom) (hz : z ∈ chi.dom)
    (hxy : x < y) (hyz : y < z) :
    chi.g x z ⊆ chi.g y z := by
  intro phi hphi; rw [h_c3 x y z hx hy hz hxy hyz] at hphi; exact hphi.2

/-! ## ChronicleInvariant Bundle -/

/-- Bundles the chronicle invariants c0, c1, c2', and c3 needed for
the canonical model construction. -/
structure ChronicleInvariant (chi : Chronicle Atom) : Prop where
  hc0 : chi.c0
  hc1 : chi.c1
  hc2' : chi.c2'
  hc3 : chi.c3

/-! ## Basic Properties -/

theorem rRelation_subset {A B C : Set (Formula Atom)}
    (h_r : rRelation A B) (h_sub : B ⊆ C) : rRelation A C :=
  Cslib.Logic.Metalogic.Chronicle.rRelation_subset temporalChronicleInterface
    (A := A) (B := B) (C := C) h_r h_sub

theorem rRelationSince_subset {A B C : Set (Formula Atom)}
    (h_r : rRelationSince A B) (h_sub : B ⊆ C) : rRelationSince A C :=
  Cslib.Logic.Metalogic.Chronicle.rRelationSince_subset temporalChronicleInterface
    (A := A) (B := B) (C := C) h_r h_sub

theorem r3Relation_subset {A B B' C : Set (Formula Atom)}
    (h : r3Relation A B C) (h_sub : B ⊆ B') : r3Relation A B' C :=
  ⟨rRelation_subset h.1 h_sub, rRelationSince_subset h.2 h_sub⟩

theorem R3Maximal_dcs {A B C : Set (Formula Atom)}
    (h : R3Maximal A B C) : SetDeductivelyClosed B := h.1

theorem R3Maximal_r3 {A B C : Set (Formula Atom)}
    (h : R3Maximal A B C) : r3Relation A B C := h.2.1

/-! ## DCS Intersection Properties -/

theorem SetConsistent_of_subset {Omega T : Set (Formula Atom)}
    (h_sub : Omega ⊆ T) (h_cons : Temporal.SetConsistent T) : Temporal.SetConsistent Omega :=
  Cslib.Logic.Metalogic.Chronicle.SetConsistent_of_subset temporalChronicleInterface
    (Omega := Omega) (T := T) h_sub h_cons

end Cslib.Logic.Temporal.Metalogic.Chronicle
