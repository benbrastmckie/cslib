/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Bimodal.ProofSystem.Derivation
public import Cslib.Logics.Bimodal.Syntax.Formula
public import Cslib.Logics.Bimodal.Theorems.Combinators
public import Cslib.Logics.Bimodal.Theorems.GeneralizedNecessitation
public import Cslib.Logics.Bimodal.Theorems.Propositional.Connectives
public import Cslib.Foundations.Logic.Theorems.Temporal.TemporalDerived

/-!
# Temporal Derived Theorems from BX Axioms

Temporal theorems derived from the Burgess-Xu (BX) axiom system.

Ported from BimodalLogic/Theories/Bimodal/Theorems/TemporalDerived.lean
-/

set_option linter.unusedSimpArgs false
set_option linter.style.emptyLine false
set_option linter.style.longLine false

@[expose] public section

namespace Cslib.Logic.Bimodal.Theorems.TemporalDerived

open Cslib.Logic.Bimodal
open Cslib.Logic.Bimodal.Theorems.Combinators
open Cslib.Logic.Bimodal.Theorems.Propositional
open Cslib.Logic.Bimodal.Theorems
open Cslib.Logic.Bimodal.Theorems.Perpetuity (unwrap)

variable {Atom : Type*}

noncomputable section

section DerivedAxioms

/-- `⊢ ¬(¬ψ → ¬φ) → ¬(φ → ψ)`: negation of contrapositive implies negation of implication. -/
noncomputable def negContrapositiveImpNeg (φ ψ : Formula Atom) :
    DerivationTree FrameClass.Base [] ((ψ.neg.imp φ.neg).neg.imp (φ.imp ψ).neg) :=
  mp (contraposeImp φ ψ) (contraposeImp (φ.imp ψ) (ψ.neg.imp φ.neg))

/-- `⊢ X → (⊤ ∧ X)`: introduce top conjunction. -/
def topAndIntro (X : Formula Atom) :
    DerivationTree FrameClass.Base [] (X.imp (Formula.top.and X)) :=
  mp (identity Formula.bot) (pairing Formula.top X)

/-- `⊢ F(¬(¬ψ → ¬φ)) → F(¬(φ → ψ))`: lift negated contrapositive implication to someFuture. -/
noncomputable def fNegContraImpFNeg (φ ψ : Formula Atom) :
    DerivationTree FrameClass.Base []
      ((Formula.someFuture (ψ.neg.imp φ.neg).neg).imp
       (Formula.someFuture (φ.imp ψ).neg)) :=
  mp (DerivationTree.temporal_necessitation _ (negContrapositiveImpNeg φ ψ))
     (DerivationTree.axiom [] _
       (Axiom.right_mono_until (ψ.neg.imp φ.neg).neg (φ.imp ψ).neg Formula.top) trivial)

/-- `⊢ G(φ → ψ) → G(¬ψ → ¬φ)`: lift contrapositive to G. -/
noncomputable def gImpToGContra (φ ψ : Formula Atom) :
    DerivationTree FrameClass.Base []
      ((φ.imp ψ).allFuture.imp (ψ.neg.imp φ.neg).allFuture) :=
  contraposition (fNegContraImpFNeg φ ψ)

/-- `⊢ G(¬ψ → ¬φ) → (Gφ → Gψ)`: G-contrapositive implies G-K-distribution. -/
noncomputable def gContraToGK (φ ψ : Formula Atom) :
    DerivationTree FrameClass.Base []
      ((ψ.neg.imp φ.neg).allFuture.imp (φ.allFuture.imp ψ.allFuture)) :=
  impTrans
    (DerivationTree.axiom [] _ (Axiom.right_mono_until ψ.neg φ.neg Formula.top) trivial)
    (contraposeImp (Formula.someFuture ψ.neg) (Formula.someFuture φ.neg))

/-- Temporal K-distribution derived from BX axioms: `⊢ G(φ → ψ) → (Gφ → Gψ)`. -/
noncomputable def tempKDistDerived (φ ψ : Formula Atom) :
    DerivationTree FrameClass.Base []
      ((φ.imp ψ).allFuture.imp (φ.allFuture.imp ψ.allFuture)) :=
  impTrans (gImpToGContra φ ψ) (gContraToGK φ ψ)

/-- `⊢ F(¬¬F(¬φ)) → F(F(¬φ))`: lift double-negation elimination into someFuture. -/
noncomputable def dneLiftF (φ : Formula Atom) :
    DerivationTree FrameClass.Base []
      ((Formula.someFuture (Formula.someFuture φ.neg).neg.neg).imp
       (Formula.someFuture (Formula.someFuture φ.neg))) :=
  mp (DerivationTree.temporal_necessitation _ (doubleNegation (Formula.someFuture φ.neg)))
     (DerivationTree.axiom [] _
       (Axiom.right_mono_until
         (Formula.someFuture φ.neg).neg.neg (Formula.someFuture φ.neg) Formula.top) trivial)

/-- `⊢ F(F(¬φ)) → F(⊤ ∧ F(¬φ))`: introduce top conjunction inside someFuture. -/
noncomputable def ffToFTopAnd (φ : Formula Atom) :
    DerivationTree FrameClass.Base []
      ((Formula.someFuture (Formula.someFuture φ.neg)).imp
       (Formula.someFuture (Formula.top.and (Formula.someFuture φ.neg)))) :=
  mp (DerivationTree.temporal_necessitation _ (topAndIntro (Formula.someFuture φ.neg)))
     (DerivationTree.axiom [] _
       (Axiom.right_mono_until
         (Formula.someFuture φ.neg)
         (Formula.top.and (Formula.someFuture φ.neg)) Formula.top) trivial)

/-- `⊢ F(⊤ ∧ F(¬φ)) → F(¬φ)`: absorb top from the until eventuality (BX absorb axiom). -/
def fTopAndAbsorb (φ : Formula Atom) :
    DerivationTree FrameClass.Base []
      ((Formula.someFuture (Formula.top.and (Formula.someFuture φ.neg))).imp
       (Formula.someFuture φ.neg)) :=
  DerivationTree.axiom [] _ (Axiom.absorb_until Formula.top φ.neg) trivial

/-- Temporal 4-axiom derived from BX axioms: `⊢ Gφ → GGφ`. -/
noncomputable def temp4Derived (φ : Formula Atom) :
    DerivationTree FrameClass.Base []
      (φ.allFuture.imp φ.allFuture.allFuture) :=
  contraposition (impTrans (impTrans (dneLiftF φ) (ffToFTopAnd φ)) (fTopAndAbsorb φ))

end DerivedAxioms

/-- G-distribution: `⊢ G(φ → ψ) → (Gφ → Gψ)` (unwrapped from Foundations). -/
noncomputable def gDistribution (φ ψ : Formula Atom) :
    DerivationTree FrameClass.Base []
      ((φ.imp ψ).allFuture.imp (φ.allFuture.imp ψ.allFuture)) :=
  unwrap (@Cslib.Logic.Theorems.Temporal.TemporalDerived.gDistribution
    _ _ _ _ _ Bimodal.HilbertTM _ _ (φ := φ) (ψ := ψ))

/-- H-distribution: `⊢ H(φ → ψ) → (Hφ → Hψ)` (unwrapped from Foundations). -/
noncomputable def hDistribution (φ ψ : Formula Atom) :
    DerivationTree FrameClass.Base []
      ((φ.imp ψ).allPast.imp (φ.allPast.imp ψ.allPast)) :=
  unwrap (@Cslib.Logic.Theorems.Temporal.TemporalDerived.hDistribution
    _ _ _ _ _ Bimodal.HilbertTM _ _ (φ := φ) (ψ := ψ))

/-- G-transitivity (temporal 4-axiom): `⊢ Gφ → GGφ`. -/
noncomputable def gTransitivity (φ : Formula Atom) :
    DerivationTree FrameClass.Base []
      (φ.allFuture.imp φ.allFuture.allFuture) :=
  temp4Derived φ

/-- H-transitivity (temporal 4-axiom for past): `⊢ Hφ → HHφ` (via temporal duality). -/
noncomputable def hTransitivity (φ : Formula Atom) :
    DerivationTree FrameClass.Base []
      (φ.allPast.imp φ.allPast.allPast) := by
  let ψ := φ.swapTemporal
  have h1 := temp4Derived ψ
  have h2 := DerivationTree.temporal_duality _ h1
  simp only [Formula.swapTemporal_allFuture, Formula.swapTemporal] at h2
  have h_inv : ψ.swapTemporal = φ := Formula.swapTemporal_involution φ
  rw [h_inv] at h2
  exact h2

/-- Future connection axiom: `⊢ φ → G(Pφ)`. -/
def connectFutureThm (φ : Formula Atom) :
    DerivationTree FrameClass.Base [] (φ.imp (φ.somePast.allFuture)) :=
  DerivationTree.axiom [] _ (Axiom.connect_future φ) trivial

/-- Past connection axiom: `⊢ φ → H(Fφ)`. -/
def connectPastThm (φ : Formula Atom) :
    DerivationTree FrameClass.Base [] (φ.imp (φ.someFuture.allPast)) :=
  DerivationTree.axiom [] _ (Axiom.connect_past φ) trivial

/-- `⊢ Ga → G(a → a)`: lift the identity for `a` under G. -/
def gImpliesGId (a : Formula Atom) :
    DerivationTree FrameClass.Base []
      (a.allFuture.imp (a.imp a).allFuture) :=
  mp (DerivationTree.temporal_necessitation _ (identity a))
     (DerivationTree.axiom [] _ (Axiom.imp_s (a.imp a).allFuture a.allFuture) trivial)

/-- `⊢ (ψ U φ) → Fψ`: Until implies someFuture of the event (BX until_F axiom). -/
def untilImpliesSomeFuture (φ ψ : Formula Atom) :
    DerivationTree FrameClass.Base []
      ((Formula.untl φ ψ).imp (Formula.someFuture ψ)) :=
  DerivationTree.axiom [] _ (Axiom.until_F φ ψ) trivial

/-- `⊢ (ψ S φ) → Pψ`: Since implies somePast of the event (BX since_P axiom). -/
def sinceImpliesSomePast (φ ψ : Formula Atom) :
    DerivationTree FrameClass.Base []
      ((Formula.snce φ ψ).imp (Formula.somePast ψ)) :=
  DerivationTree.axiom [] _ (Axiom.since_P φ ψ) trivial

/-- `⊢ (ψ U φ) → Fψ`: alias for `untilImpliesSomeFuture`. -/
def untilImpF (φ ψ : Formula Atom) :
    DerivationTree FrameClass.Base []
      ((Formula.untl φ ψ).imp (Formula.someFuture ψ)) :=
  DerivationTree.axiom [] _ (Axiom.until_F φ ψ) trivial

/-- `⊢ (ψ S φ) → Pψ`: alias for `sinceImpliesSomePast`. -/
def sinceImpP (φ ψ : Formula Atom) :
    DerivationTree FrameClass.Base []
      ((Formula.snce φ ψ).imp (Formula.somePast ψ)) :=
  DerivationTree.axiom [] _ (Axiom.since_P φ ψ) trivial

/-- `⊢ (A → B) → (¬B → ¬A)`: contrapositive as a derivation. -/
noncomputable def contrapositiveThm (A B : Formula Atom) :
    DerivationTree FrameClass.Base [] ((A.imp B).imp (B.neg.imp A.neg)) :=
  mp bCombinator (flip (A := (B.imp Formula.bot)) (B := (A.imp B)) (C := (A.imp Formula.bot)))

/-- Modus ponens in context: derive B from a derivation of (A → B) and a derivation of A. -/
noncomputable def ctxMp {Γ : Context Atom} {A B : Formula Atom}
    (h1 : DerivationTree FrameClass.Base Γ (A.imp B))
    (h2 : DerivationTree FrameClass.Base Γ A) :
    DerivationTree FrameClass.Base Γ B :=
  DerivationTree.modus_ponens Γ A B h1 h2

/-- Lift a closed theorem into any context by weakening. -/
noncomputable def ctxThm {Γ : Context Atom} {A : Formula Atom}
    (h : DerivationTree FrameClass.Base [] A) :
    DerivationTree FrameClass.Base Γ A :=
  DerivationTree.weakening [] Γ A h (List.nil_subset Γ)

/-- `⊢ (A ∨ B) → (B ∨ A)`: commutativity of disjunction. -/
noncomputable def formulaOrComm (A B : Formula Atom) :
    DerivationTree FrameClass.Base [] ((A.or B).imp (B.or A)) := by
  apply Cslib.Logic.Bimodal.Metalogic.Core.deductionTheorem [] (A.neg.imp B) (B.neg.imp A)
  apply Cslib.Logic.Bimodal.Metalogic.Core.deductionTheorem [A.neg.imp B] B.neg A
  have h1 : DerivationTree FrameClass.Base [B.neg, A.neg.imp B] (A.neg.imp B) :=
    DerivationTree.assumption _ _ (by simp)
  have h2 : DerivationTree FrameClass.Base [B.neg, A.neg.imp B] B.neg :=
    DerivationTree.assumption _ _ (by simp)
  have h3 := ctxMp (ctxMp (ctxThm bCombinator) h2) h1
  exact ctxMp (ctxThm (doubleNegation A)) h3

section TemporalMonotonicity

/-- `⊢ G(φ → ψ) → (Fφ → Fψ)`: monotonicity of someFuture under G-implication. -/
def fMono (φ ψ : Formula Atom) :
    DerivationTree FrameClass.Base []
      ((φ.imp ψ).allFuture.imp (φ.someFuture.imp ψ.someFuture)) :=
  DerivationTree.axiom [] _ (Axiom.right_mono_until φ ψ Formula.top) trivial

/-- `⊢ H(φ → ψ) → (Pφ → Pψ)`: monotonicity of somePast under H-implication. -/
def pMono (φ ψ : Formula Atom) :
    DerivationTree FrameClass.Base []
      ((φ.imp ψ).allPast.imp (φ.somePast.imp ψ.somePast)) :=
  DerivationTree.axiom [] _ (Axiom.right_mono_since φ ψ Formula.top) trivial

/-- `⊢ G(φ → ψ) → (Gφ → Gψ)`: allFuture monotonicity (alias for `gDistribution`). -/
noncomputable abbrev gMono (φ ψ : Formula Atom) :
    DerivationTree FrameClass.Base []
      ((φ.imp ψ).allFuture.imp (φ.allFuture.imp ψ.allFuture)) :=
  gDistribution φ ψ

/-- `⊢ H(φ → ψ) → (Hφ → Hψ)`: allPast monotonicity (alias for `hDistribution`). -/
noncomputable abbrev hMono (φ ψ : Formula Atom) :
    DerivationTree FrameClass.Base []
      ((φ.imp ψ).allPast.imp (φ.allPast.imp ψ.allPast)) :=
  hDistribution φ ψ

end TemporalMonotonicity

section UntilSinceStructural

/-- `⊢ G(φ → χ) → ((ψ U φ) → (ψ U χ))`: monotonicity in the guard of Until. -/
def untilMonoGuard (φ χ ψ : Formula Atom) :
    DerivationTree FrameClass.Base []
      ((φ.imp χ).allFuture.imp ((Formula.untl φ ψ).imp (Formula.untl χ ψ))) :=
  DerivationTree.axiom [] _ (Axiom.left_mono_until_G φ χ ψ) trivial

/-- `⊢ H(φ → χ) → ((ψ S φ) → (ψ S χ))`: monotonicity in the guard of Since. -/
def sinceMonoGuard (φ χ ψ : Formula Atom) :
    DerivationTree FrameClass.Base []
      ((φ.imp χ).allPast.imp ((Formula.snce φ ψ).imp (Formula.snce χ ψ))) :=
  DerivationTree.axiom [] _ (Axiom.left_mono_since_H φ χ ψ) trivial

/-- `⊢ G(φ → ψ) → ((φ U χ) → (ψ U χ))`: monotonicity in the event of Until. -/
def untilMonoEvent (φ ψ χ : Formula Atom) :
    DerivationTree FrameClass.Base []
      ((φ.imp ψ).allFuture.imp ((Formula.untl χ φ).imp (Formula.untl χ ψ))) :=
  DerivationTree.axiom [] _ (Axiom.right_mono_until φ ψ χ) trivial

/-- `⊢ H(φ → ψ) → ((φ S χ) → (ψ S χ))`: monotonicity in the event of Since. -/
def sinceMonoEvent (φ ψ χ : Formula Atom) :
    DerivationTree FrameClass.Base []
      ((φ.imp ψ).allPast.imp ((Formula.snce χ φ).imp (Formula.snce χ ψ))) :=
  DerivationTree.axiom [] _ (Axiom.right_mono_since φ ψ χ) trivial

end UntilSinceStructural

section TemporalDuality

/-- `⊢ F(¬φ) → ¬Gφ`: someFuture of negation implies negation of allFuture. -/
def fNegG (φ : Formula Atom) :
    DerivationTree FrameClass.Base []
      ((φ.neg.someFuture).imp φ.allFuture.neg) :=
  dni (φ.neg.someFuture)

/-- `⊢ P(¬φ) → ¬Hφ`: somePast of negation implies negation of allPast. -/
def pNegH (φ : Formula Atom) :
    DerivationTree FrameClass.Base []
      ((φ.neg.somePast).imp φ.allPast.neg) :=
  dni (φ.neg.somePast)

end TemporalDuality

section DistributionVariants

/-- `⊢ Gφ → (Gψ → G(φ ∧ ψ))`: conjunction introduction inside G. -/
noncomputable def gAndIntro (φ ψ : Formula Atom) :
    DerivationTree FrameClass.Base []
      (φ.allFuture.imp (ψ.allFuture.imp (φ.and ψ).allFuture)) :=
  unwrap (@Cslib.Logic.Theorems.Temporal.TemporalDerived.gAndIntro
    _ _ _ _ _ Bimodal.HilbertTM _ _ (φ := φ) (ψ := ψ))

/-- `⊢ Hφ → (Hψ → H(φ ∧ ψ))`: conjunction introduction inside H. -/
noncomputable def hAndIntro (φ ψ : Formula Atom) :
    DerivationTree FrameClass.Base []
      (φ.allPast.imp (ψ.allPast.imp (φ.and ψ).allPast)) :=
  unwrap (@Cslib.Logic.Theorems.Temporal.TemporalDerived.hAndIntro
    _ _ _ _ _ Bimodal.HilbertTM _ _ (φ := φ) (ψ := ψ))

/-- `⊢ G(φ → ψ) → (G(ψ → χ) → G(φ → χ))`: G-implication transitivity. -/
noncomputable def gImpTrans (φ ψ χ : Formula Atom) :
    DerivationTree FrameClass.Base []
      ((φ.imp ψ).allFuture.imp ((ψ.imp χ).allFuture.imp (φ.imp χ).allFuture)) :=
  unwrap (@Cslib.Logic.Theorems.Temporal.TemporalDerived.gImpTrans
    _ _ _ _ _ Bimodal.HilbertTM _ _ (φ := φ) (ψ := ψ) (χ := χ))

/-- `⊢ H(φ → ψ) → (H(ψ → χ) → H(φ → χ))`: H-implication transitivity. -/
noncomputable def hImpTrans (φ ψ χ : Formula Atom) :
    DerivationTree FrameClass.Base []
      ((φ.imp ψ).allPast.imp ((ψ.imp χ).allPast.imp (φ.imp χ).allPast)) :=
  unwrap (@Cslib.Logic.Theorems.Temporal.TemporalDerived.hImpTrans
    _ _ _ _ _ Bimodal.HilbertTM _ _ (φ := φ) (ψ := ψ) (χ := χ))

end DistributionVariants

section TemporalContraposition

/-- `⊢ G(φ → ψ) → G(¬ψ → ¬φ)`: contrapositive distribution over G. -/
noncomputable def gContrapose (φ ψ : Formula Atom) :
    DerivationTree FrameClass.Base []
      ((φ.imp ψ).allFuture.imp (ψ.neg.imp φ.neg).allFuture) :=
  unwrap (@Cslib.Logic.Theorems.Temporal.TemporalDerived.gContrapose
    _ _ _ _ _ Bimodal.HilbertTM _ _ (φ := φ) (ψ := ψ))

/-- `⊢ H(φ → ψ) → H(¬ψ → ¬φ)`: contrapositive distribution over H. -/
noncomputable def hContrapose (φ ψ : Formula Atom) :
    DerivationTree FrameClass.Base []
      ((φ.imp ψ).allPast.imp (ψ.neg.imp φ.neg).allPast) :=
  unwrap (@Cslib.Logic.Theorems.Temporal.TemporalDerived.hContrapose
    _ _ _ _ _ Bimodal.HilbertTM _ _ (φ := φ) (ψ := ψ))

end TemporalContraposition

section FuturePastChains

/-- `⊢ Gφ → G(P(φ) is always reachable)`: G implies G(Pφ allFuture). -/
noncomputable def connectFutureG (φ : Formula Atom) :
    DerivationTree FrameClass.Base []
      (φ.allFuture.imp (φ.somePast.allFuture).allFuture) :=
  unwrap (@Cslib.Logic.Theorems.Temporal.TemporalDerived.connect_future_G
    _ _ _ _ _ Bimodal.HilbertTM _ _ (φ := φ))

/-- `⊢ Hφ → H(F(φ) is always past)`: H implies H(Fφ allPast). -/
noncomputable def connectPastH (φ : Formula Atom) :
    DerivationTree FrameClass.Base []
      (φ.allPast.imp (φ.someFuture.allPast).allPast) :=
  unwrap (@Cslib.Logic.Theorems.Temporal.TemporalDerived.connect_past_H
    _ _ _ _ _ Bimodal.HilbertTM _ _ (φ := φ))

/-- `⊢ φ → G(H(F(P(φ))))`: forward connectivity chain for temporal modal interaction. -/
noncomputable def connectFutureChain (φ : Formula Atom) :
    DerivationTree FrameClass.Base []
      (φ.imp ((φ.somePast.someFuture.allPast).allFuture)) :=
  let step1 := DerivationTree.temporal_necessitation _ (connectPastThm φ.somePast)
  let step2 := mp step1 (gDistribution φ.somePast (φ.somePast.someFuture.allPast))
  impTrans (connectFutureThm φ) step2

/-- `⊢ φ → H(G(F(P(φ))))`: backward connectivity chain for temporal modal interaction. -/
noncomputable def connectPastChain (φ : Formula Atom) :
    DerivationTree FrameClass.Base []
      (φ.imp ((φ.someFuture.somePast.allFuture).allPast)) :=
  let step1 := pastNecessitation _ (connectFutureThm φ.someFuture)
  let step2 := mp step1 (hDistribution φ.someFuture (φ.someFuture.somePast.allFuture))
  impTrans (connectPastThm φ) step2

end FuturePastChains

section ConjunctionElimination

/-- Always implies present: `⊢ Aφ → φ` where `A = H ∧ (id ∧ G)`. -/
noncomputable def alwaysToPresent (φ : Formula Atom) :
    DerivationTree FrameClass.Base [] (φ.always.imp φ) :=
  impTrans (rceImp φ.allPast (φ.and φ.allFuture)) (lceImp φ φ.allFuture)

/-- Present implies sometimes: `⊢ φ → Sφ` where `S = ¬A¬`. -/
noncomputable def presentToSometimes (φ : Formula Atom) :
    DerivationTree FrameClass.Base [] (φ.imp φ.sometimes) := by
  exact impTrans (dni φ) (contraposition (alwaysToPresent φ.neg))

/-- `⊢ (φ ∧ Gφ) → φ`: project left from the weak future conjunction. -/
noncomputable def weakFutureLeft (φ : Formula Atom) :
    DerivationTree FrameClass.Base [] ((φ.and φ.allFuture).imp φ) :=
  lceImp φ φ.allFuture

/-- `⊢ (φ ∧ Gφ) → Gφ`: project right from the weak future conjunction. -/
noncomputable def weakFutureRight (φ : Formula Atom) :
    DerivationTree FrameClass.Base [] ((φ.and φ.allFuture).imp φ.allFuture) :=
  rceImp φ φ.allFuture

/-- `⊢ (φ ∧ Hφ) → φ`: project left from the weak past conjunction. -/
noncomputable def weakPastLeft (φ : Formula Atom) :
    DerivationTree FrameClass.Base [] ((φ.and φ.allPast).imp φ) :=
  lceImp φ φ.allPast

/-- `⊢ (φ ∧ Hφ) → Hφ`: project right from the weak past conjunction. -/
noncomputable def weakPastRight (φ : Formula Atom) :
    DerivationTree FrameClass.Base [] ((φ.and φ.allPast).imp φ.allPast) :=
  rceImp φ φ.allPast

/-- `⊢ Aφ → Gφ`: always (H ∧ (id ∧ G)) implies allFuture. -/
noncomputable def alwaysImpAllFuture (φ : Formula Atom) :
    DerivationTree FrameClass.Base [] (φ.always.imp φ.allFuture) :=
  impTrans (rceImp φ.allPast (φ.and φ.allFuture)) (rceImp φ φ.allFuture)

/-- `⊢ Aφ → Hφ`: always (H ∧ (id ∧ G)) implies allPast. -/
noncomputable def alwaysImpAllPast (φ : Formula Atom) :
    DerivationTree FrameClass.Base [] (φ.always.imp φ.allPast) :=
  lceImp φ.allPast (φ.and φ.allFuture)

end ConjunctionElimination

end -- noncomputable section

end Cslib.Logic.Bimodal.Theorems.TemporalDerived
