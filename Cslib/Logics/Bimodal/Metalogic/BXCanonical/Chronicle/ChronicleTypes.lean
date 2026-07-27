/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Bimodal.Metalogic.Core.MaximalConsistent
public import Cslib.Logics.Bimodal.Metalogic.Core.MCSProperties
public import Cslib.Logics.Bimodal.Theorems.Propositional.Core
public import Cslib.Logics.Bimodal.Metalogic.Bundle.TemporalContent -- shake: keep
public import Cslib.Logics.Bimodal.Metalogic.BXCanonical.Frame -- shake: keep
public import Cslib.Logics.Bimodal.Theorems.GeneralizedNecessitation -- shake: keep
public import Cslib.Logics.Bimodal.Metalogic.Bundle.ModalSaturation -- shake: keep
public import Mathlib.Data.Rat.Defs -- shake: keep
public import Cslib.Foundations.Logic.Metalogic.Chronicle.Types

/-!
# Chronicle Types for Burgess 1982 Construction

Defines the chronicle data structure from Burgess 1982, Section 2.

## Status (task 530, Phase 1)

The DCS infrastructure (`ClosedUnderDerivation`, `SetDeductivelyClosed`, `mcs_is_dcs`,
`cud_*`/`dcs_*`), r-relations (`rRelation`/`rRelationSince`/`r3Relation`/
`r3RelationSince`), r-maximality (`rMaximal`/`rMaximalSince`/`R3Maximal`/
`R3MaximalSince`), Burgess content relations (`burgessR`/`burgessRSet`/`burgessRSince`/
`burgessRSetSince`/`burgessR3`/`BurgessR3Maximal`), and basic subset/intersection
theorems are now thin instance + re-export wrappers over the generic
`Cslib.Foundations.Logic.Metalogic.Chronicle.Types` module, instantiated by
`bimodalChronicleInterface : FrameClass → ChronicleInterface (Formula Atom)`.

The `Chronicle` structure and its conditions (c0-c5', `ValidChronicle`,
`ChronicleInvariant`, C3 consequences) stay logic-local (unchanged) -- see the "Chronicle
Structure" section below for why: routing them through a generic-structure bridge broke
`rcases`/`simp` proofs in downstream `CounterexampleElimination/*.lean` files that
pattern-match on Finset-membership subterms nested inside condition statements.

`liftBase`/`mcs_to_base` stay logic-local (fc-lifting utilities specific to Bimodal, no
temporal analogue).

## References

* Ported from BimodalLogic/Theories/Bimodal/Metalogic/BXCanonical/Chronicle/ChronicleTypes.lean
* Burgess 1982: "Axioms for tense logic II: Time periods"
-/

set_option linter.style.emptyLine false
set_option linter.style.longLine false
set_option linter.dupNamespace false

@[expose] public section

namespace Cslib.Logic.Bimodal.Metalogic.BXCanonical.Chronicle

open Cslib.Logic.Bimodal
open Cslib.Logic.Bimodal.Metalogic.Core
open Cslib.Logic.Bimodal.Metalogic.Bundle
open Cslib.Logic.Bimodal.Theorems
open Cslib.Logic.Bimodal.Theorems.Propositional
open Cslib.Logic.Bimodal.Theorems.Combinators
open Cslib.Logic.Metalogic.Chronicle (ChronicleInterface)

attribute [local instance] Classical.propDecidable

variable {Atom : Type*}

/-! ## FC-Parametric Utilities -/

/-- Lift a Base-level derivation to any frame class. -/
noncomputable def liftBase (fc : FrameClass) {Gamma : Context Atom} {phi : Formula Atom}
    (d : DerivationTree FrameClass.Base Gamma phi) : DerivationTree fc Gamma phi :=
  d.lift (FrameClass.base_le fc)

/-- An MCS at any frame class is also an MCS at Base. -/
theorem mcs_to_base {fc : FrameClass} {A : Set (Formula Atom)}
    (h_mcs : SetMaximalConsistent fc A) :
    SetMaximalConsistent FrameClass.Base A := by
  constructor
  · intro L hL ⟨d⟩
    exact h_mcs.1 L hL ⟨liftBase fc d⟩
  · intro phi hphi
    have h_neg : phi.neg ∈ A := by
      rcases SetMaximalConsistent.negation_complete h_mcs phi with h | h
      · exact absurd h hphi
      · exact h
    intro h_cons
    exact set_consistent_not_both h_cons phi (Set.mem_insert phi A) (Set.mem_insert_of_mem phi h_neg)

/-! ## `ChronicleInterface` Instance Family (task 530, Phase 1)

Populates every field of the shared Foundations interface with Bimodal's own
`fc`-threaded apparatus, indexed by `fc` (Bimodal needs one interface value per live
`fc`, as with `bimodalSinceInterface` in `PointInsertion/Since.lean`). -/

/-- The `ChronicleInterface` instance family for Bimodal (task 530), indexed by `fc`. Not
marked `private`: the public re-export `abbrev`s below (`ClosedUnderDerivation`,
`SetDeductivelyClosed`, `rRelation`, ...) unfold to expressions mentioning it directly, and
Lean's module-privacy system disallows a `public section` declaration from referencing a
`private` one. -/
noncomputable def bimodalChronicleInterface (fc : FrameClass) :
    ChronicleInterface (Formula Atom) where
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
  Deriv := DerivationTree fc
  assumption := fun h => DerivationTree.assumption _ _ h
  modusPonens := fun h1 h2 => DerivationTree.modus_ponens _ _ _ h1 h2
  weakening := fun Γ Δ φ d hsub => DerivationTree.weakening Γ Δ φ d hsub
  deductionTheorem := fun Γ φ ψ d => deductionTheorem Γ φ ψ d
  identity' := fun φ => identity φ
  impTrans := fun h1 h2 => impTrans h1 h2
  lceImp := fun φ ψ => lceImp φ ψ
  rceImp := fun φ ψ => rceImp φ ψ
  pairing := fun φ ψ => Combinators.pairing φ ψ
  efq := fun φ => Propositional.efqAxiom φ
  pastNecessitation := fun φ d => Cslib.Logic.Bimodal.Theorems.pastNecessitation φ d
  mcsClosedUnderDerivation := by
    intro Ω hmcs L φ hL hd
    exact SetMaximalConsistent.closed_under_derivation hmcs L hL hd
  theoremInMcs := by
    intro Ω hmcs φ hd
    exact SetMaximalConsistent.closed_under_derivation hmcs [] (fun _ h => absurd h List.not_mem_nil) hd
  negationComplete := fun hmcs φ => SetMaximalConsistent.negation_complete hmcs φ
  negExcludes := by
    intro Ω hmcs φ hneg hmem
    exact SetMaximalConsistent.neg_excludes hmcs _ hneg hmem
  cudContainsTheorems := by
    intro Ω h φ hd
    exact h [] φ (fun _ hc => absurd hc List.not_mem_nil) hd
  untilF := fun γ δ => DerivationTree.axiom [] _ (Axiom.until_F γ δ) trivial
  selfAccumUntil := fun γ δ => DerivationTree.axiom [] _ (Axiom.self_accum_until γ δ) trivial
  sinceP := fun γ δ => DerivationTree.axiom [] _ (Axiom.since_P γ δ) trivial
  absorbUntil := fun β γ => DerivationTree.axiom [] _ (Axiom.absorb_until β γ) trivial
  absorbSince := fun β γ => DerivationTree.axiom [] _ (Axiom.absorb_since β γ) trivial
  leftMonoUntilG := fun β₁ β₂ γ => DerivationTree.axiom [] _ (Axiom.left_mono_until_G β₁ β₂ γ) trivial
  leftMonoSinceH := fun β₁ β₂ γ => DerivationTree.axiom [] _ (Axiom.left_mono_since_H β₁ β₂ γ) trivial
  rightMonoUntil := fun a b pivot => DerivationTree.axiom (fc := fc) [] _ (Axiom.right_mono_until a b pivot) trivial
  rightMonoSince := fun a b pivot => DerivationTree.axiom (fc := fc) [] _ (Axiom.right_mono_since a b pivot) trivial
  enrichmentUntil := fun β ψ α => DerivationTree.axiom (fc := fc) [] _ (Axiom.enrichment_until β ψ α) trivial
  enrichmentSince := fun β ψ γ => DerivationTree.axiom (fc := fc) [] _ (Axiom.enrichment_since β ψ γ) trivial
  connectFuture := fun α => DerivationTree.axiom (fc := fc) [] _ (Axiom.connect_future α) trivial
  connectPast := fun γ => DerivationTree.axiom (fc := fc) [] _ (Axiom.connect_past γ) trivial
  futureNecessitation := fun _ d => DerivationTree.temporal_necessitation _ d
  doubleNegation := fun φ => Propositional.doubleNegation φ
  futureKDist := fun φ ψ =>
    liftBase fc (Cslib.Logic.Bimodal.Theorems.TemporalDerived.tempKDistDerived (Atom := Atom) φ ψ)
  pastKDist := fun φ ψ => Cslib.Logic.Bimodal.Theorems.pastKDist φ ψ
  someFutureAllFutureNegAbsurd := fun hmcs φ hF hGneg =>
    someFuture_allFuture_neg_absurd hmcs φ hF hGneg
  somePastAllPastNegAbsurd := fun hmcs φ hP hHneg =>
    somePast_allPast_neg_absurd hmcs φ hP hHneg
  negAllPastNegToSomePast := by
    intro Ω hmcs α h
    have h_dne_P : Formula.somePast (α.neg.neg) ∈ Ω := by
      have h_dne : DerivationTree fc [] ((Formula.somePast α.neg.neg).neg.neg.imp (Formula.somePast α.neg.neg)) :=
        Propositional.doubleNegation (Formula.somePast α.neg.neg)
      exact SetMaximalConsistent.implication_property hmcs (theoremInMcsFc hmcs h_dne) h
    have h_dne_ax : DerivationTree fc [] (α.neg.neg.imp α) := Propositional.doubleNegation α
    have h_H_dne : DerivationTree fc [] ((α.neg.neg.imp α).allPast) :=
      Cslib.Logic.Bimodal.Theorems.pastNecessitation _ h_dne_ax
    have h_bx3' : DerivationTree fc [] ((α.neg.neg.imp α).allPast.imp
        ((Formula.snce Formula.top α.neg.neg).imp (Formula.snce Formula.top α))) :=
      DerivationTree.axiom [] _ (Axiom.right_mono_since α.neg.neg α Formula.top) trivial
    have h_P_mono : DerivationTree fc [] ((Formula.somePast α.neg.neg).imp (Formula.somePast α)) :=
      DerivationTree.modus_ponens [] _ _ h_bx3' h_H_dne
    exact SetMaximalConsistent.implication_property hmcs (theoremInMcsFc hmcs h_P_mono) h_dne_P
  negAllFutureNegToSomeFuture := by
    intro Ω hmcs γ h
    have h_dne_F : Formula.someFuture (γ.neg.neg) ∈ Ω := by
      have h_dne : DerivationTree fc [] ((Formula.someFuture γ.neg.neg).neg.neg.imp (Formula.someFuture γ.neg.neg)) :=
        Propositional.doubleNegation (Formula.someFuture γ.neg.neg)
      exact SetMaximalConsistent.implication_property hmcs (theoremInMcsFc hmcs h_dne) h
    have h_dne_ax : DerivationTree fc [] (γ.neg.neg.imp γ) := Propositional.doubleNegation γ
    have h_G_dne : DerivationTree fc [] ((γ.neg.neg.imp γ).allFuture) :=
      DerivationTree.temporal_necessitation _ h_dne_ax
    have h_bx3 : DerivationTree fc [] ((γ.neg.neg.imp γ).allFuture.imp
        ((Formula.untl Formula.top γ.neg.neg).imp (Formula.untl Formula.top γ))) :=
      DerivationTree.axiom [] _ (Axiom.right_mono_until γ.neg.neg γ Formula.top) trivial
    have h_F_mono : DerivationTree fc [] ((Formula.someFuture γ.neg.neg).imp (Formula.someFuture γ)) :=
      DerivationTree.modus_ponens [] _ _ h_bx3 h_G_dne
    exact SetMaximalConsistent.implication_property hmcs (theoremInMcsFc hmcs h_F_mono) h_dne_F
  someFutureHNegGPAbsurd := by
    intro Ω hmcs α h_F h_GP
    have h_dni_ax : DerivationTree fc [] (α.imp α.neg.neg) := dni α
    have h_H_dni : DerivationTree fc [] ((α.imp α.neg.neg).allPast) :=
      Cslib.Logic.Bimodal.Theorems.pastNecessitation _ h_dni_ax
    have h_bx3' : DerivationTree fc [] ((α.imp α.neg.neg).allPast.imp
        ((Formula.snce Formula.top α).imp (Formula.snce Formula.top α.neg.neg))) :=
      DerivationTree.axiom [] _ (Axiom.right_mono_since α α.neg.neg Formula.top) trivial
    have h_P_to_Pnn : DerivationTree fc [] ((Formula.somePast α).imp (Formula.somePast α.neg.neg)) :=
      DerivationTree.modus_ponens [] _ _ h_bx3' h_H_dni
    have h_dni_P : DerivationTree fc [] ((Formula.somePast α.neg.neg).imp (Formula.somePast α.neg.neg).neg.neg) :=
      dni (Formula.somePast α.neg.neg)
    have h_P_to_neg_H : DerivationTree fc [] ((Formula.somePast α).imp (Formula.neg (Formula.allPast (Formula.neg α)))) :=
      impTrans h_P_to_Pnn h_dni_P
    have h_G_imp : DerivationTree fc [] (Formula.allFuture ((Formula.somePast α).imp (Formula.neg (Formula.allPast (Formula.neg α))))) :=
      DerivationTree.temporal_necessitation _ h_P_to_neg_H
    have h_kd : DerivationTree fc [] (((Formula.somePast α).imp (Formula.neg (Formula.allPast (Formula.neg α)))).allFuture.imp
        ((Formula.somePast α).allFuture.imp (Formula.neg (Formula.allPast (Formula.neg α))).allFuture)) :=
      liftBase fc (Cslib.Logic.Bimodal.Theorems.TemporalDerived.tempKDistDerived (Atom := Atom)
        (Formula.somePast α) (Formula.neg (Formula.allPast (Formula.neg α))))
    have h_G_P_imp_G_neg_H : DerivationTree fc [] ((Formula.somePast α).allFuture.imp
        (Formula.neg (Formula.allPast (Formula.neg α))).allFuture) :=
      DerivationTree.modus_ponens [] _ _ h_kd h_G_imp
    have h_G_neg_H : (Formula.neg (Formula.allPast (Formula.neg α))).allFuture ∈ Ω :=
      SetMaximalConsistent.implication_property hmcs (theoremInMcsFc hmcs h_G_P_imp_G_neg_H) h_GP
    exact someFuture_allFuture_neg_absurd hmcs (Formula.allPast (Formula.neg α)) h_F h_G_neg_H
  somePastGNegHFAbsurd := by
    intro Ω hmcs γ h_P h_HF
    have h_dni_ax : DerivationTree fc [] (γ.imp γ.neg.neg) := dni γ
    have h_G_dni : DerivationTree fc [] ((γ.imp γ.neg.neg).allFuture) :=
      DerivationTree.temporal_necessitation _ h_dni_ax
    have h_bx3 : DerivationTree fc [] ((γ.imp γ.neg.neg).allFuture.imp
        ((Formula.untl Formula.top γ).imp (Formula.untl Formula.top γ.neg.neg))) :=
      DerivationTree.axiom [] _ (Axiom.right_mono_until γ γ.neg.neg Formula.top) trivial
    have h_F_to_Fnn : DerivationTree fc [] ((Formula.someFuture γ).imp (Formula.someFuture γ.neg.neg)) :=
      DerivationTree.modus_ponens [] _ _ h_bx3 h_G_dni
    have h_dni_F : DerivationTree fc [] ((Formula.someFuture γ.neg.neg).imp (Formula.someFuture γ.neg.neg).neg.neg) :=
      dni (Formula.someFuture γ.neg.neg)
    have h_F_to_neg_G : DerivationTree fc [] ((Formula.someFuture γ).imp (Formula.neg (Formula.allFuture (Formula.neg γ)))) :=
      impTrans h_F_to_Fnn h_dni_F
    have h_H_imp : DerivationTree fc [] (Formula.allPast ((Formula.someFuture γ).imp (Formula.neg (Formula.allFuture (Formula.neg γ))))) :=
      Cslib.Logic.Bimodal.Theorems.pastNecessitation _ h_F_to_neg_G
    have h_kd : DerivationTree fc [] (((Formula.someFuture γ).imp (Formula.neg (Formula.allFuture (Formula.neg γ)))).allPast.imp
        ((Formula.someFuture γ).allPast.imp (Formula.neg (Formula.allFuture (Formula.neg γ))).allPast)) :=
      Cslib.Logic.Bimodal.Theorems.pastKDist (Formula.someFuture γ) (Formula.neg (Formula.allFuture (Formula.neg γ)))
    have h_H_F_imp_H_neg_G : DerivationTree fc [] ((Formula.someFuture γ).allPast.imp
        (Formula.neg (Formula.allFuture (Formula.neg γ))).allPast) :=
      DerivationTree.modus_ponens [] _ _ h_kd h_H_imp
    have h_H_neg_G : (Formula.neg (Formula.allFuture (Formula.neg γ))).allPast ∈ Ω :=
      SetMaximalConsistent.implication_property hmcs (theoremInMcsFc hmcs h_H_F_imp_H_neg_G) h_HF
    exact somePast_allPast_neg_absurd hmcs (Formula.allFuture (Formula.neg γ)) h_P h_H_neg_G

/-! ## Deductively Closed Sets (DCS) -/

/-- A set is closed under derivation. -/
abbrev ClosedUnderDerivation (fc : FrameClass) (Omega : Set (Formula Atom)) : Prop :=
  Cslib.Logic.Metalogic.Chronicle.CIClosedUnderDerivation (bimodalChronicleInterface fc) Omega

/-- A set is deductively closed (consistent + closed under derivation). -/
abbrev SetDeductivelyClosed (fc : FrameClass) (Omega : Set (Formula Atom)) : Prop :=
  Cslib.Logic.Metalogic.Chronicle.SetDeductivelyClosed (bimodalChronicleInterface fc) Omega

/-- Every MCS is deductively closed. -/
theorem mcs_is_dcs {fc : FrameClass} {Omega : Set (Formula Atom)}
    (h : SetMaximalConsistent fc Omega) :
    SetDeductivelyClosed fc Omega :=
  Cslib.Logic.Metalogic.Chronicle.mcs_is_dcs (bimodalChronicleInterface fc) (Omega := Omega) h

/-- A CUD set contains all theorems. -/
theorem cud_contains_theorems {fc : FrameClass} {Omega : Set (Formula Atom)}
    (h : ClosedUnderDerivation fc Omega)
    {phi : Formula Atom} (hd : DerivationTree fc [] phi) : phi ∈ Omega :=
  Cslib.Logic.Metalogic.Chronicle.cud_contains_theorems
    (bimodalChronicleInterface fc) (Omega := Omega) h (phi := phi) hd

/-- A DCS contains all theorems. -/
theorem dcs_contains_theorems {fc : FrameClass} {Omega : Set (Formula Atom)}
    (h : SetDeductivelyClosed fc Omega)
    {phi : Formula Atom} (hd : DerivationTree fc [] phi) : phi ∈ Omega :=
  cud_contains_theorems h.2 hd

/-- Modus ponens in a CUD set. -/
theorem cud_modus_ponens {fc : FrameClass} {Omega : Set (Formula Atom)}
    (h : ClosedUnderDerivation fc Omega)
    {phi psi : Formula Atom} (h_imp : phi.imp psi ∈ Omega) (h_phi : phi ∈ Omega) : psi ∈ Omega :=
  Cslib.Logic.Metalogic.Chronicle.cud_modus_ponens
    (bimodalChronicleInterface fc) (Omega := Omega) h (phi := phi) (psi := psi) h_imp h_phi

/-- Modus ponens in a DCS. -/
theorem dcs_modus_ponens {fc : FrameClass} {Omega : Set (Formula Atom)}
    (h : SetDeductivelyClosed fc Omega)
    {phi psi : Formula Atom} (h_imp : phi.imp psi ∈ Omega) (h_phi : phi ∈ Omega) : psi ∈ Omega :=
  cud_modus_ponens h.2 h_imp h_phi

/-- A CUD set is closed under conjunction. -/
theorem cud_conj_closed {fc : FrameClass} {Omega : Set (Formula Atom)}
    (h : ClosedUnderDerivation fc Omega)
    {phi psi : Formula Atom} (h_phi : phi ∈ Omega) (h_psi : psi ∈ Omega) : Formula.and phi psi ∈ Omega :=
  Cslib.Logic.Metalogic.Chronicle.cud_conj_closed
    (bimodalChronicleInterface fc) (Omega := Omega) h (phi := phi) (psi := psi) h_phi h_psi

/-- A DCS is closed under conjunction. -/
theorem dcs_conj_closed {fc : FrameClass} {Omega : Set (Formula Atom)}
    (h : SetDeductivelyClosed fc Omega)
    {phi psi : Formula Atom} (h_phi : phi ∈ Omega) (h_psi : psi ∈ Omega) : Formula.and phi psi ∈ Omega :=
  cud_conj_closed h.2 h_phi h_psi

/-- A CUD set with a non-member is SDC. -/
theorem cud_not_mem_is_sdc {fc : FrameClass} {B : Set (Formula Atom)}
    (h_cud : ClosedUnderDerivation fc B)
    {phi : Formula Atom} (h_not_mem : phi ∉ B) : SetDeductivelyClosed fc B :=
  Cslib.Logic.Metalogic.Chronicle.cud_not_mem_is_sdc
    (bimodalChronicleInterface fc) (B := B) h_cud (phi := phi) h_not_mem

/-! ## Adjacency predicate -/

/-- Two rationals are adjacent in `dom` if they are consecutive elements with no point between them. -/
abbrev Adjacent (dom : Finset Rat) (x y : Rat) : Prop :=
  Cslib.Logic.Metalogic.Chronicle.Adjacent dom x y

/-! ## The r-Relation (Burgess Lemma 2.3)

`rRelation`/`rRelationSince`/`r3Relation`/`r3RelationSince` depend only on `untl`/`snce`,
which are `fc`-independent formula constructors, so any interface family member (here
`FrameClass.Base`) may be used to witness them -- exactly as `bimodalSinceInterface
FrameClass.Base` is used for the `fc`-independent `l27s*` helpers in `Since.lean`. -/

/-- The r-relation holds between sets `A` and `B` if every until-formula in `A` is witnessed in `B` (Burgess Lemma 2.3). -/
abbrev rRelation (A B : Set (Formula Atom)) : Prop :=
  Cslib.Logic.Metalogic.Chronicle.rRelation (bimodalChronicleInterface FrameClass.Base) A B

/-- The since-variant of the r-relation, witnessing since-formulas in `A` via `B`. -/
abbrev rRelationSince (A B : Set (Formula Atom)) : Prop :=
  Cslib.Logic.Metalogic.Chronicle.rRelationSince (bimodalChronicleInterface FrameClass.Base) A B

/-- The combined r3-relation: `A` r-relates to `B` via until and `C` r-since-relates to `B`. -/
abbrev r3Relation (A B C : Set (Formula Atom)) : Prop :=
  Cslib.Logic.Metalogic.Chronicle.r3Relation (bimodalChronicleInterface FrameClass.Base) A B C

/-- The since-variant of r3: `A` r-since-relates to `B` and `C` r-relates to `B`. -/
abbrev r3RelationSince (A B C : Set (Formula Atom)) : Prop :=
  Cslib.Logic.Metalogic.Chronicle.r3RelationSince (bimodalChronicleInterface FrameClass.Base) A B C

/-! ## R-Maximality -/

/-- A set `B` is r-maximal for `A` if it is deductively closed, r-relates to `A`, and no proper extension also r-relates to `A`. -/
abbrev rMaximal (fc : FrameClass) (A B : Set (Formula Atom)) : Prop :=
  Cslib.Logic.Metalogic.Chronicle.rMaximal (bimodalChronicleInterface fc) A B

/-- The since-variant of r-maximality: `B` is deductively closed, r-since-relates to `A`, and no proper extension does. -/
abbrev rMaximalSince (fc : FrameClass) (A B : Set (Formula Atom)) : Prop :=
  Cslib.Logic.Metalogic.Chronicle.rMaximalSince (bimodalChronicleInterface fc) A B

/-- A set `B` is R3-maximal for `(A, C)` if it is deductively closed, r3-relates to `(A, C)`, and no proper extension does. -/
abbrev R3Maximal (fc : FrameClass) (A B C : Set (Formula Atom)) : Prop :=
  Cslib.Logic.Metalogic.Chronicle.R3Maximal (bimodalChronicleInterface fc) A B C

/-- The since-variant of R3-maximality: `B` r3-since-relates to `(A, C)` and no proper extension does. -/
abbrev R3MaximalSince (fc : FrameClass) (A B C : Set (Formula Atom)) : Prop :=
  Cslib.Logic.Metalogic.Chronicle.R3MaximalSince (bimodalChronicleInterface fc) A B C

/-! ## Burgess r-Relation (Content-Based)

`burgessR`/`burgessRSet`/`burgessRSince`/`burgessRSetSince`/`burgessR3` are also
`fc`-independent (formula-only), so `FrameClass.Base` is used arbitrarily. -/

/-- Content-based Burgess r-relation: every `gamma` in `C` satisfies `untl beta gamma ∈ A`. -/
abbrev burgessR (A : Set (Formula Atom)) (beta : Formula Atom) (C : Set (Formula Atom)) : Prop :=
  Cslib.Logic.Metalogic.Chronicle.ciBurgessR (bimodalChronicleInterface FrameClass.Base) A beta C

/-- Burgess r-relation lifted to a set of pivot formulas `B`. -/
abbrev burgessRSet (A B C : Set (Formula Atom)) : Prop :=
  Cslib.Logic.Metalogic.Chronicle.ciBurgessRSet (bimodalChronicleInterface FrameClass.Base) A B C

/-- Since-variant of the content-based Burgess r-relation: every `gamma` in `C` satisfies `snce gamma beta ∈ A`. -/
abbrev burgessRSince (A : Set (Formula Atom)) (beta : Formula Atom) (C : Set (Formula Atom)) : Prop :=
  Cslib.Logic.Metalogic.Chronicle.ciBurgessRSince (bimodalChronicleInterface FrameClass.Base) A beta C

/-- Since-variant of `burgessRSet`: every pivot in `B` since-relates `A` to `C`. -/
abbrev burgessRSetSince (A B C : Set (Formula Atom)) : Prop :=
  Cslib.Logic.Metalogic.Chronicle.ciBurgessRSetSince (bimodalChronicleInterface FrameClass.Base) A B C

/-- Combined Burgess r3-relation: `burgessRSet A B C` and `burgessRSetSince C B A`. -/
abbrev burgessR3 (A B C : Set (Formula Atom)) : Prop :=
  Cslib.Logic.Metalogic.Chronicle.ciBurgessR3 (bimodalChronicleInterface FrameClass.Base) A B C

/-- A set `B` is Burgess-R3-maximal for `(A, C)` if it is CUD, burgessR3-relates to `(A, C)`, and no proper extension does. -/
abbrev BurgessR3Maximal (fc : FrameClass) (A B C : Set (Formula Atom)) : Prop :=
  Cslib.Logic.Metalogic.Chronicle.CIBurgessR3Maximal (bimodalChronicleInterface fc) A B C

/-! ## Chronicle Structure

**Deviation from full genericity (task 530, Phase 1)**: `Chronicle` and its conditions
c0-c5', `ValidChronicle`, `ChronicleInvariant`, and the C3 consequences are kept
logic-local (verbatim, unchanged), NOT routed through the generic
`Cslib.Foundations.Logic.Metalogic.Chronicle.Types.Chronicle`/`.c0`-`.c5'` machinery.

An earlier draft of this phase bridged the local `Chronicle` to the generic one via a
`toGeneric` conversion (`⟨chi.f, chi.g, chi.dom⟩`), routing `Chronicle.c0`..`c5'` through
it. This compiled standalone, but broke downstream `CounterexampleElimination/*.lean`
files: several `rcases`/pattern-matching proofs there destructure Finset-membership
subterms nested inside condition statements (e.g. `a ∈ { f := ..., dom := insert y
χ.dom }.dom`), and once those statements are stated in terms of `chi.toGeneric.dom`
rather than `chi.dom` directly, the extra (defeq but not eagerly-reduced) `.toGeneric`
projection layer caused `rcases`/`simp` to no longer recognize the term as a Finset,
producing hard failures ("is not an inductive datatype"). Per the plan's explicit
contingency (keep a lemma logic-local rather than deferring it with a placeholder when a
proof body resists generic abstraction), the `Chronicle`-structure layer stays logic-local; the
DCS/r-relation/r-maximality/Burgess layers above (which do NOT touch the `Chronicle`
structure) remain fully generic. -/

/-- A chronicle: a finite rational domain with point-sets `f` and interval-sets `g` (Burgess 1982, Section 2). -/
structure Chronicle (Atom : Type*) where
  /-- Point-set function assigning a formula set to each rational point. -/
  f : Rat → Set (Formula Atom)
  /-- Interval-set function assigning a formula set to each rational interval. -/
  g : Rat → Rat → Set (Formula Atom)
  /-- Finite set of rational time-points forming the chronicle domain. -/
  dom : Finset Rat


/-! ## Chronicle Conditions -/

/-- Condition c0: every point in the domain carries a maximal consistent set. -/
def Chronicle.c0 (fc : FrameClass) (chi : Chronicle Atom) : Prop :=
  ∀ x ∈ chi.dom, SetMaximalConsistent fc (chi.f x)

/-- Condition c1: every interval-set `g x y` is closed under derivation. -/
def Chronicle.c1 (fc : FrameClass) (chi : Chronicle Atom) : Prop :=
  ∀ x y : Rat, x ∈ chi.dom → y ∈ chi.dom → x < y → ClosedUnderDerivation fc (chi.g x y)

/-- Condition c2: the interval-set `g x y` r3-relates the point-sets at each pair of domain points. -/
def Chronicle.c2 (chi : Chronicle Atom) : Prop :=
  ∀ x y : Rat, x ∈ chi.dom → y ∈ chi.dom → x < y → r3Relation (chi.f x) (chi.g x y) (chi.f y)

/-- Condition c2': the interval-set is Burgess-R3-maximal at each adjacent pair of domain points. -/
def Chronicle.c2' (fc : FrameClass) (chi : Chronicle Atom) : Prop :=
  ∀ x y : Rat, Adjacent chi.dom x y →
    BurgessR3Maximal fc (chi.f x) (chi.g x y) (chi.f y)

/-- Condition c3: the interval-set over `[x,z]` decomposes as `g x y ∩ f y ∩ g y z` for intermediate `y`. -/
def Chronicle.c3 (chi : Chronicle Atom) : Prop :=
  ∀ x y z : Rat, x ∈ chi.dom → y ∈ chi.dom → z ∈ chi.dom →
    x < y → y < z → chi.g x z = chi.g x y ∩ chi.f y ∩ chi.g y z

/-- Condition c4: if `¬(delta U gamma) ∈ f x` and `delta ∈ f y` then some intermediate point witnesses `¬gamma`. -/
def Chronicle.c4 (chi : Chronicle Atom) : Prop :=
  ∀ x y : Rat, x ∈ chi.dom → y ∈ chi.dom → x < y →
    ∀ (gamma delta : Formula Atom),
      (Formula.untl gamma delta).neg ∈ chi.f x →
      delta ∈ chi.f y →
      ∃ z ∈ chi.dom, x < z ∧ z < y ∧ gamma.neg ∈ chi.f z

/-- Condition c4': the since-variant of c4, witnessing `¬gamma` between `y` and `x` in the past direction. -/
def Chronicle.c4' (chi : Chronicle Atom) : Prop :=
  ∀ x y : Rat, x ∈ chi.dom → y ∈ chi.dom → y < x →
    ∀ (gamma delta : Formula Atom),
      (Formula.snce gamma delta).neg ∈ chi.f x →
      delta ∈ chi.f y →
      ∃ z ∈ chi.dom, y < z ∧ z < x ∧ gamma.neg ∈ chi.f z

/-- Condition c5: if `delta U gamma ∈ f x` then some future `y` witnesses `delta` with `gamma` holding at all intermediate points. -/
def Chronicle.c5 (chi : Chronicle Atom) : Prop :=
  ∀ x ∈ chi.dom,
    ∀ (gamma delta : Formula Atom),
      Formula.untl gamma delta ∈ chi.f x →
      ∃ y ∈ chi.dom, x < y ∧ delta ∈ chi.f y ∧
        ∀ z ∈ chi.dom, x < z → z < y →
          gamma ∈ chi.f z ∧ Formula.untl gamma delta ∈ chi.f z

/-- Condition c5': the since-variant of c5, witnessing `delta` in the past with `gamma` at all intermediate points. -/
def Chronicle.c5' (chi : Chronicle Atom) : Prop :=
  ∀ x ∈ chi.dom,
    ∀ (gamma delta : Formula Atom),
      Formula.snce gamma delta ∈ chi.f x →
      ∃ y ∈ chi.dom, y < x ∧ delta ∈ chi.f y ∧
        ∀ z ∈ chi.dom, y < z → z < x →
          gamma ∈ chi.f z ∧ Formula.snce gamma delta ∈ chi.f z

/-! ## Valid Chronicle -/

/-- A valid chronicle: a `Chronicle` satisfying all conditions c0–c5'. -/
structure ValidChronicle (Atom : Type*) (fc : FrameClass) extends Chronicle Atom where
  hc0 : toChronicle.c0 fc
  hc1 : toChronicle.c1 fc
  hc2 : toChronicle.c2
  hc2' : toChronicle.c2' fc
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

/-- Bundle of the core chronicle invariants (c0, c1, c2', c3) used throughout the canonicity argument. -/
structure ChronicleInvariant (fc : FrameClass) (chi : Chronicle Atom) : Prop where
  hc0 : chi.c0 fc
  hc1 : chi.c1 fc
  hc2' : chi.c2' fc
  hc3 : chi.c3

/-! ## Basic Properties -/

theorem rRelation_subset {A B C : Set (Formula Atom)}
    (h_r : rRelation A B) (h_sub : B ⊆ C) : rRelation A C :=
  Cslib.Logic.Metalogic.Chronicle.rRelation_subset (bimodalChronicleInterface FrameClass.Base)
    (A := A) (B := B) (C := C) h_r h_sub

theorem rRelationSince_subset {A B C : Set (Formula Atom)}
    (h_r : rRelationSince A B) (h_sub : B ⊆ C) : rRelationSince A C :=
  Cslib.Logic.Metalogic.Chronicle.rRelationSince_subset (bimodalChronicleInterface FrameClass.Base)
    (A := A) (B := B) (C := C) h_r h_sub

theorem r3Relation_implies_rRelation {A B C : Set (Formula Atom)}
    (h : r3Relation A B C) : rRelation A B := h.1

theorem r3Relation_implies_rRelationSince {A B C : Set (Formula Atom)}
    (h : r3Relation A B C) : rRelationSince C B := h.2

theorem r3Relation_subset {A B B' C : Set (Formula Atom)}
    (h : r3Relation A B C) (h_sub : B ⊆ B') : r3Relation A B' C :=
  ⟨rRelation_subset h.1 h_sub, rRelationSince_subset h.2 h_sub⟩

theorem R3Maximal_dcs {fc : FrameClass} {A B C : Set (Formula Atom)}
    (h : R3Maximal fc A B C) : SetDeductivelyClosed fc B := h.1

theorem R3Maximal_r3 {fc : FrameClass} {A B C : Set (Formula Atom)}
    (h : R3Maximal fc A B C) : r3Relation A B C := h.2.1

theorem R3Maximal_rRelation {fc : FrameClass} {A B C : Set (Formula Atom)}
    (h : R3Maximal fc A B C) : rRelation A B := h.2.1.1

/-! ## DCS Intersection Properties -/

theorem dcs_inter_dcs {fc : FrameClass} {S1 S2 : Set (Formula Atom)}
    (h1 : SetDeductivelyClosed fc S1) (h2 : SetDeductivelyClosed fc S2)
    (h_cons : SetConsistent fc (S1 ∩ S2)) :
    SetDeductivelyClosed fc (S1 ∩ S2) :=
  Cslib.Logic.Metalogic.Chronicle.dcs_inter_dcs (bimodalChronicleInterface fc)
    (S1 := S1) (S2 := S2) h1 h2 h_cons

theorem dcs_inter_mcs {fc : FrameClass} {S1 S2 : Set (Formula Atom)}
    (h1 : SetDeductivelyClosed fc S1) (h2 : SetMaximalConsistent fc S2)
    (h_cons : SetConsistent fc (S1 ∩ S2)) :
    SetDeductivelyClosed fc (S1 ∩ S2) :=
  dcs_inter_dcs h1 (mcs_is_dcs h2) h_cons

theorem SetConsistent_of_subset {fc : FrameClass} {Omega T : Set (Formula Atom)}
    (h_sub : Omega ⊆ T) (h_cons : SetConsistent fc T) : SetConsistent fc Omega :=
  Cslib.Logic.Metalogic.Chronicle.SetConsistent_of_subset (bimodalChronicleInterface fc)
    (Omega := Omega) (T := T) h_sub h_cons

theorem three_way_inter_consistent {fc : FrameClass} {S1 S2 S3 : Set (Formula Atom)}
    (h3_cons : SetConsistent fc S3) :
    SetConsistent fc (S1 ∩ S2 ∩ S3) :=
  SetConsistent_of_subset (fun _ h => h.2) h3_cons

theorem dcs_inter_mcs_inter_dcs {fc : FrameClass} {S1 S2 S3 : Set (Formula Atom)}
    (h1 : SetDeductivelyClosed fc S1) (h2 : SetMaximalConsistent fc S2)
    (h3 : SetDeductivelyClosed fc S3)
    (h_cons : SetConsistent fc (S1 ∩ S2 ∩ S3)) :
    SetDeductivelyClosed fc (S1 ∩ S2 ∩ S3) :=
  Cslib.Logic.Metalogic.Chronicle.dcs_inter_mcs_inter_dcs (bimodalChronicleInterface fc)
    (S1 := S1) (S2 := S2) (S3 := S3) h1 h2 h3 h_cons

end Cslib.Logic.Bimodal.Metalogic.BXCanonical.Chronicle
