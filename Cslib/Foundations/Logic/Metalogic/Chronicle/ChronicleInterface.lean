/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

import Cslib.Init
public import Cslib.Foundations.Logic.Metalogic.Chronicle.SinceSeedConsistency

/-! # Chronicle Interface — Shared Bimodal/Temporal Chronicle Construction Interface

This module factors the duplicated, `fc`-diverged Burgess-1982 chronicle /
counterexample-elimination machinery shared by
`Logics/Bimodal/.../BXCanonical/Chronicle/` and `Logics/Temporal/.../Chronicle/` into a
common, interface-parameterized module tree, extending the landed `SinceSeedInterface F`
precedent (`Cslib.Foundations.Logic.Metalogic.Chronicle.SinceSeedConsistency`) with a
broader `ChronicleInterface F`.

## Architecture

`ChronicleInterface F` bundles:
- the abstract formula operators (`bot`, `imp`, `and`, `or`, `untl`, `snce`, `somePast`,
  `allPast`, `allFuture`, `someFuture`) needed across the `ChronicleTypes` /
  `RRelation` / `CounterexampleElimination` / `ChronicleConstruction` layers;
- an abstract `Type*`-valued contextual derivation family `Deriv : List F → F → Type*`
  (mirroring `DerivationTree fc` / `DerivationTree FrameClass.Base`, parallel to
  `GenericMCS.HilbertTree` and `SinceSeedInterface.Deriv`);
- the low-level derivation combinators each logic already proves for its own
  `DerivationTree` (`assumption`, `modusPonens`, `weakening`, `deductionTheorem`,
  `identity'`, `impTrans`, `lceImp`, `rceImp`, `pairing`, `efq`, `pastNecessitation`);
  `untlLeftMonoDeriv` and `combineImpConj` are deliberately **not** included here — their
  only proofs live downstream of `ChronicleTypes.lean` (in each tree's
  `PointInsertion/Burgess.lean`), confirmed for `untlLeftMonoDeriv` in both trees and for
  `combineImpConj` in Temporal specifically (Bimodal's own `combineImpConj` is available
  via `Theorems/Combinators.lean` with no cycle, but the field must serve both trees
  uniformly). Both are deferred to `RRelation.lean`, which sits at the correct
  layer to supply them;
- the MCS/Burgess apparatus lemmas the `ChronicleTypes` layer invokes
  (`mcsClosedUnderDerivation`, `theoremInMcs`, `negationComplete`, `negExcludes`,
  `cudContainsTheorems`) as *statement-only* fields — each logic supplies its own proof
  when building its instance.

Purely definitional notions (`SetConsistent`, `SetMaximalConsistent`,
`ClosedUnderDerivation`, deductive closure, the Burgess r-relations, `BurgessR3Maximal`,
`gContent`, `hContent`) are **not** re-declared here: both logics define them identically
(modulo `fc`) in terms of the primitives above, and `SinceSeedConsistency.lean` already
provides them as generic `def`s (`isSetConsistent`, `isSetMaximalConsistent`,
`isClosedUnderDerivation`, `dClosureOf`, `rBurgessOf`, `rSetBurgessOf`, `rSinceBurgessOf`,
`rSetSinceBurgessOf`, `r3BurgessOf`, `r3MaximalBurgessOf`, `gContentOf`, `hContentOf`)
parameterized directly by the primitive pieces they need. `ChronicleInterface` reuses
those verbatim (they only need `Deriv`/`bot`/`untl`/`snce`/`allFuture`/`allPast` in scope,
which this structure also provides), so no duplication is introduced.

A `structure` (not a `class`) is used, for the same reason `SinceSeedInterface` is a
`structure`: Bimodal needs an *instance family* indexed by `fc : FrameClass`, while
Temporal needs exactly one instance — explicit passing is clearer than instance
resolution across several live `fc`.

## Relationship to `SinceSeedInterface`

`ChronicleInterface` is a deliberately **separate** structure from `SinceSeedInterface`,
not an `extends` of it, so that this consolidation's phased rollout does not disturb the
already green `SinceSeedConsistency.lean` / `PointInsertion/Since.lean` path. The two
interfaces' field sets overlap substantially (both bundle the same formula operators and a
similar derivation-combinator/MCS-apparatus core) — this overlap is intentional and is noted
here for the optional future reconciliation (`SinceSeedInterface` reusing the broader
`ChronicleInterface`), which is treated as low-priority and not required.

## Status

This module implements the signature/defeq skeleton stage of the Bimodal/Temporal
chronicle-construction consolidation. The field set here covers exactly what the
`ChronicleTypes` lift needs (DCS infrastructure: `mcs_is_dcs`, `cud_contains_theorems`,
`cud_modus_ponens`, `cud_conj_closed`, `cud_not_mem_is_sdc`). The larger Burgess/Zorn/Xu
apparatus needed by the `RRelation` shared core and the enrichment/walk machinery needed by
`CounterexampleElimination`/`ChronicleConstruction` are deliberately **not** included yet —
per this consolidation's risk mitigation, fields are expanded conservatively as each later
stage needs them, mirroring how `SinceSeedInterface` itself was built up incrementally.

## References

* Cslib/Logics/Bimodal/Metalogic/BXCanonical/Chronicle/ChronicleTypes.lean
* Cslib/Logics/Temporal/Metalogic/Chronicle/ChronicleTypes.lean
* Cslib/Foundations/Logic/Metalogic/Chronicle/SinceSeedConsistency.lean — the
  `SinceSeedInterface` precedent this module extends the pattern of.
* Cslib/Foundations/Logic/Metalogic/GenericMCS.lean — `HilbertTree`, the precedent for a
  `Type*`-valued abstract derivation family.
-/

@[expose] public section

namespace Cslib.Logic.Metalogic.Chronicle

variable {F : Type*}

/-! ## `ChronicleInterface`: the shared chronicle-construction apparatus

One instance per logic (Temporal: a single value; Bimodal: an `fc`-indexed family, since
`FrameClass` threading means Bimodal needs one interface value per `fc`), exactly as with
`SinceSeedInterface`. -/

/-- Everything the shared Burgess-1982 chronicle-construction layers
(`ChronicleTypes`/`RRelation`/`CounterexampleElimination`/`ChronicleConstruction`) consume
from the formula/derivation/Burgess layer of a tense logic, statement-only where the
underlying proof is logic-specific. One instance per `(logic, frame index)`. -/
structure ChronicleInterface (F : Type*) where
  /-- Falsum. -/
  bot : F
  /-- Implication. -/
  imp : F → F → F
  /-- Conjunction. -/
  and : F → F → F
  /-- Disjunction. -/
  or : F → F → F
  /-- Until. -/
  untl : F → F → F
  /-- Since. -/
  snce : F → F → F
  /-- Some-past (`𝐏`). -/
  somePast : F → F
  /-- All-past (`𝐇`). -/
  allPast : F → F
  /-- All-future (`𝐆`). -/
  allFuture : F → F
  /-- Some-future (`𝐅`). -/
  someFuture : F → F
  /-- Abstract `Type`-valued contextual derivation family (mirrors `DerivationTree fc` /
  `DerivationTree FrameClass.Base`). -/
  Deriv : List F → F → Type*
  /-- Assumption. -/
  assumption : ∀ {Γ : List F} {φ : F}, φ ∈ Γ → Deriv Γ φ
  /-- Modus ponens. -/
  modusPonens : ∀ {Γ : List F} {φ ψ : F}, Deriv Γ (imp φ ψ) → Deriv Γ φ → Deriv Γ ψ
  /-- Weakening. -/
  weakening : ∀ (Γ Δ : List F) (φ : F), Deriv Γ φ → (∀ x ∈ Γ, x ∈ Δ) → Deriv Δ φ
  /-- Deduction theorem. -/
  deductionTheorem : ∀ (Γ : List F) (φ ψ : F), Deriv (φ :: Γ) ψ → Deriv Γ (imp φ ψ)
  /-- `⊢ φ → φ`. -/
  identity' : ∀ (φ : F), Deriv [] (imp φ φ)
  /-- Transitivity of empty-context implication. -/
  impTrans : ∀ {φ ψ χ : F}, Deriv [] (imp φ ψ) → Deriv [] (imp ψ χ) → Deriv [] (imp φ χ)
  /-- Left conjunction elimination: `⊢ (φ ∧ ψ) → φ`. -/
  lceImp : ∀ (φ ψ : F), Deriv [] (imp (and φ ψ) φ)
  /-- Right conjunction elimination: `⊢ (φ ∧ ψ) → ψ`. -/
  rceImp : ∀ (φ ψ : F), Deriv [] (imp (and φ ψ) ψ)
  /-- Pairing combinator: `⊢ φ → ψ → (φ ∧ ψ)` (used by `cud_conj_closed`). -/
  pairing : ∀ (φ ψ : F), Deriv [] (imp φ (imp ψ (and φ ψ)))
  /-- Ex falso quodlibet: `⊢ ⊥ → φ` (used by `cud_not_mem_is_sdc`). -/
  efq : ∀ (φ : F), Deriv [] (imp bot φ)
  /-- Past necessitation: `⊢ φ` implies `⊢ allPast φ`. -/
  pastNecessitation : ∀ (φ : F), Deriv [] φ → Deriv [] (allPast φ)
  /-- Derivable formulas from an MCS-subset context are already in the MCS (the general,
  non-empty-context version of `theoremInMcs`; used by `mcs_is_dcs`). -/
  mcsClosedUnderDerivation : ∀ {Ω : Set F}, isSetMaximalConsistent Deriv bot Ω →
    ∀ {L : List F} {φ : F}, (∀ ψ ∈ L, ψ ∈ Ω) → Deriv L φ → φ ∈ Ω
  /-- Theorems (empty-context derivations) belong to every MCS. -/
  theoremInMcs : ∀ {Ω : Set F}, isSetMaximalConsistent Deriv bot Ω →
    ∀ {φ : F}, Deriv [] φ → φ ∈ Ω
  /-- Negation completeness for MCS. -/
  negationComplete : ∀ {Ω : Set F}, isSetMaximalConsistent Deriv bot Ω →
    ∀ (φ : F), φ ∈ Ω ∨ imp φ bot ∈ Ω
  /-- `neg φ ∈ Ω` (MCS) excludes `φ ∈ Ω`. -/
  negExcludes : ∀ {Ω : Set F}, isSetMaximalConsistent Deriv bot Ω →
    ∀ {φ : F}, imp φ bot ∈ Ω → φ ∈ Ω → False
  /-- CUD sets contain all theorems. -/
  cudContainsTheorems : ∀ {Ω : Set F}, isClosedUnderDerivation Deriv Ω →
    ∀ {φ : F}, Deriv [] φ → φ ∈ Ω
  /-- BX10: `⊢ (γ U δ) → F(δ)`. -/
  untilF : ∀ (γ δ : F), Deriv [] (imp (untl γ δ) (someFuture δ))
  /-- BX5: `⊢ (γ U δ) → ((γ ∧ (γ U δ)) U δ)`. -/
  selfAccumUntil : ∀ (γ δ : F), Deriv [] (imp (untl γ δ) (untl (and γ (untl γ δ)) δ))
  /-- BX10': `⊢ (γ S δ) → P(δ)`. -/
  sinceP : ∀ (γ δ : F), Deriv [] (imp (snce γ δ) (somePast δ))
  /-- BX6: `⊢ (β U (β ∧ (β U γ))) → (β U γ)`. -/
  absorbUntil : ∀ (β γ : F), Deriv [] (imp (untl β (and β (untl β γ))) (untl β γ))
  /-- BX6': `⊢ (β S (β ∧ (β S γ))) → (β S γ)`. -/
  absorbSince : ∀ (β γ : F), Deriv [] (imp (snce β (and β (snce β γ))) (snce β γ))
  /-- BX2G: `⊢ G(β₁ → β₂) → ((β₁ U γ) → (β₂ U γ))`. -/
  leftMonoUntilG : ∀ (β₁ β₂ γ : F),
    Deriv [] (imp (allFuture (imp β₁ β₂)) (imp (untl β₁ γ) (untl β₂ γ)))
  /-- BX2H: `⊢ H(β₁ → β₂) → ((β₁ S γ) → (β₂ S γ))`. -/
  leftMonoSinceH : ∀ (β₁ β₂ γ : F),
    Deriv [] (imp (allPast (imp β₁ β₂)) (imp (snce β₁ γ) (snce β₂ γ)))
  /-- BX3: `⊢ G(a → b) → ((pivot U a) → (pivot U b))`. -/
  rightMonoUntil : ∀ (a b pivot : F),
    Deriv [] (imp (allFuture (imp a b)) (imp (untl pivot a) (untl pivot b)))
  /-- BX3': `⊢ H(a → b) → ((pivot S a) → (pivot S b))`. -/
  rightMonoSince : ∀ (a b pivot : F),
    Deriv [] (imp (allPast (imp a b)) (imp (snce pivot a) (snce pivot b)))
  /-- A3a (enrichment_until): `⊢ (α ∧ (β U ψ)) → (β U (ψ ∧ (β S α)))`. -/
  enrichmentUntil : ∀ (β ψ α : F),
    Deriv [] (imp (and α (untl β ψ)) (untl β (and ψ (snce β α))))
  /-- A3b (enrichment_since): `⊢ (γ ∧ (β S ψ)) → (β S (ψ ∧ (β U γ)))`. -/
  enrichmentSince : ∀ (β ψ γ : F),
    Deriv [] (imp (and γ (snce β ψ)) (snce β (and ψ (untl β γ))))
  /-- BX4: `⊢ α → G(P(α))`. -/
  connectFuture : ∀ (α : F), Deriv [] (imp α (allFuture (somePast α)))
  /-- BX4': `⊢ γ → H(F(γ))`. -/
  connectPast : ∀ (γ : F), Deriv [] (imp γ (allPast (someFuture γ)))
  /-- Future necessitation: `⊢ φ` implies `⊢ G(φ)`. -/
  futureNecessitation : ∀ (φ : F), Deriv [] φ → Deriv [] (allFuture φ)
  /-- Double negation elimination: `⊢ ¬¬φ → φ`. -/
  doubleNegation : ∀ (φ : F), Deriv [] (imp (imp (imp φ bot) bot) φ)
  /-- K-distribution for `allFuture`: `⊢ G(φ → ψ) → (G φ → G ψ)`. -/
  futureKDist : ∀ (φ ψ : F), Deriv [] (imp (allFuture (imp φ ψ)) (imp (allFuture φ) (allFuture ψ)))
  /-- K-distribution for `allPast`: `⊢ H(φ → ψ) → (H φ → H ψ)`. -/
  pastKDist : ∀ (φ ψ : F), Deriv [] (imp (allPast (imp φ ψ)) (imp (allPast φ) (allPast ψ)))
  /-- `F(φ) ∈ Ω` and `G(¬φ) ∈ Ω` are contradictory in an MCS (duality bridge). -/
  someFutureAllFutureNegAbsurd : ∀ {Ω : Set F}, isSetMaximalConsistent Deriv bot Ω →
    ∀ (φ : F), someFuture φ ∈ Ω → allFuture (imp φ bot) ∈ Ω → False
  /-- `P(φ) ∈ Ω` and `H(¬φ) ∈ Ω` are contradictory in an MCS (duality bridge). -/
  somePastAllPastNegAbsurd : ∀ {Ω : Set F}, isSetMaximalConsistent Deriv bot Ω →
    ∀ (φ : F), somePast φ ∈ Ω → allPast (imp φ bot) ∈ Ω → False
  /-- In an MCS, `¬H(¬α) ∈ Ω` implies `P(α) ∈ Ω` (duality bridge for Burgess Lemma 2.3). -/
  negAllPastNegToSomePast : ∀ {Ω : Set F}, isSetMaximalConsistent Deriv bot Ω →
    ∀ (α : F), imp (allPast (imp α bot)) bot ∈ Ω → somePast α ∈ Ω
  /-- In an MCS, `¬G(¬γ) ∈ Ω` implies `F(γ) ∈ Ω` (duality bridge for Burgess Lemma 2.3). -/
  negAllFutureNegToSomeFuture : ∀ {Ω : Set F}, isSetMaximalConsistent Deriv bot Ω →
    ∀ (γ : F), imp (allFuture (imp γ bot)) bot ∈ Ω → someFuture γ ∈ Ω
  /-- `F(H(¬α)) ∈ Ω` and `G(P(α)) ∈ Ω` are contradictory in an MCS. -/
  someFutureHNegGPAbsurd : ∀ {Ω : Set F}, isSetMaximalConsistent Deriv bot Ω →
    ∀ (α : F), someFuture (allPast (imp α bot)) ∈ Ω → allFuture (somePast α) ∈ Ω → False
  /-- `P(G(¬γ)) ∈ Ω` and `H(F(γ)) ∈ Ω` are contradictory in an MCS. -/
  somePastGNegHFAbsurd : ∀ {Ω : Set F}, isSetMaximalConsistent Deriv bot Ω →
    ∀ (γ : F), somePast (allFuture (imp γ bot)) ∈ Ω → allPast (someFuture γ) ∈ Ω → False

/-! ## Convenience wrappers over an interface value

Mirror the `SinceSeedInterface` convenience wrappers: purely definitional notions reuse
the generic `SinceSeedConsistency.lean` defs directly (`isSetConsistent`,
`isSetMaximalConsistent`, `isClosedUnderDerivation`, `dClosureOf`, `rBurgessOf`,
`rSetBurgessOf`, `rSinceBurgessOf`, `rSetSinceBurgessOf`, `r3BurgessOf`,
`r3MaximalBurgessOf`, `gContentOf`, `hContentOf`), so only the `I.*`-qualified thin
wrappers are declared here. -/

/-- Negation w.r.t. `I`: `neg φ := imp φ bot` (the Lukasiewicz default both `Formula.neg`
instances delegate to; see `Cslib.Foundations.Logic.Connectives`). -/
def ciNeg (I : ChronicleInterface F) (φ : F) : F := I.imp φ I.bot

/-- Verum w.r.t. `I`: `top := imp bot bot`. -/
def ciTop (I : ChronicleInterface F) : F := I.imp I.bot I.bot

/-- `SetConsistent` w.r.t. `I`'s derivation family. -/
def CISetConsistent (I : ChronicleInterface F) (S : Set F) : Prop :=
  isSetConsistent I.Deriv I.bot S

/-- `SetMaximalConsistent` w.r.t. `I`'s derivation family. -/
def CISetMaximalConsistent (I : ChronicleInterface F) (S : Set F) : Prop :=
  isSetMaximalConsistent I.Deriv I.bot S

/-- `ClosedUnderDerivation` w.r.t. `I`'s derivation family. -/
def CIClosedUnderDerivation (I : ChronicleInterface F) (S : Set F) : Prop :=
  isClosedUnderDerivation I.Deriv S

/-- Deductive closure w.r.t. `I`'s derivation family. -/
noncomputable def ciDeductiveClosure (I : ChronicleInterface F) (S : Set F) : Set F :=
  dClosureOf I.Deriv S

/-- Burgess r-relation w.r.t. `I`'s `untl`. -/
def ciBurgessR (I : ChronicleInterface F) (A : Set F) (beta : F) (C : Set F) : Prop :=
  rBurgessOf I.untl A beta C

/-- `ciBurgessR` lifted to a set of pivots. -/
def ciBurgessRSet (I : ChronicleInterface F) (A B C : Set F) : Prop :=
  rSetBurgessOf I.untl A B C

/-- Since-variant Burgess r-relation w.r.t. `I`'s `snce`. -/
def ciBurgessRSince (I : ChronicleInterface F) (A : Set F) (beta : F) (C : Set F) : Prop :=
  rSinceBurgessOf I.snce A beta C

/-- `ciBurgessRSince` lifted to a set of pivots. -/
def ciBurgessRSetSince (I : ChronicleInterface F) (A B C : Set F) : Prop :=
  rSetSinceBurgessOf I.snce A B C

/-- Combined Burgess r3-relation w.r.t. `I`. -/
def ciBurgessR3 (I : ChronicleInterface F) (A B C : Set F) : Prop :=
  r3BurgessOf I.untl I.snce A B C

/-- `B` is Burgess-R3-maximal for `(A, C)` w.r.t. `I`. -/
def CIBurgessR3Maximal (I : ChronicleInterface F) (A B C : Set F) : Prop :=
  r3MaximalBurgessOf I.Deriv I.untl I.snce A B C

/-- `gContent` w.r.t. `I`'s `allFuture`. -/
def ciGContent (I : ChronicleInterface F) (M : Set F) : Set F := gContentOf I.allFuture M

/-- `hContent` w.r.t. `I`'s `allPast`. -/
def ciHContent (I : ChronicleInterface F) (M : Set F) : Set F := hContentOf I.allPast M

end Cslib.Logic.Metalogic.Chronicle
