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
  uniformly). Both are deferred to Phase 2 (`RRelation.lean`), which sits at the correct
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
not an `extends` of it, so that this task's phased rollout does not disturb the already
green `SinceSeedConsistency.lean` / `PointInsertion/Since.lean` path. The two interfaces'
field sets overlap substantially (both bundle the same formula operators and a similar
derivation-combinator/MCS-apparatus core) — this overlap is intentional and is noted here
for the optional Phase 5 reconciliation (`SinceSeedInterface` reusing the broader
`ChronicleInterface`), which this task treats as low-priority and does not require.

## Status

Phase 0 (signature/defeq skeleton) of the task-530 plan
(`specs/530_consolidate_chronicle_construction_bimodal_temporal/plans/`). The field set
here covers exactly what the Phase 1 `ChronicleTypes` lift needs (DCS infrastructure:
`mcs_is_dcs`, `cud_contains_theorems`, `cud_modus_ponens`, `cud_conj_closed`,
`cud_not_mem_is_sdc`). The larger Burgess/Zorn/Xu apparatus needed by the `RRelation`
shared core (Phase 2) and the enrichment/walk machinery needed by
`CounterexampleElimination`/`ChronicleConstruction` (Phases 3–4) are deliberately **not**
included yet — per the task-530 plan's risk mitigation, fields are expanded conservatively
as each later phase needs them, mirroring how `SinceSeedInterface` itself was built up
incrementally across the task-454 phases.

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

set_option linter.style.setOption false
set_option linter.flexible false

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

/-! ## Convenience wrappers over an interface value

Mirror the `SinceSeedInterface` convenience wrappers: purely definitional notions reuse
the generic `SinceSeedConsistency.lean` defs directly (`isSetConsistent`,
`isSetMaximalConsistent`, `isClosedUnderDerivation`, `dClosureOf`, `rBurgessOf`,
`rSetBurgessOf`, `rSinceBurgessOf`, `rSetSinceBurgessOf`, `r3BurgessOf`,
`r3MaximalBurgessOf`, `gContentOf`, `hContentOf`), so only the `I.*`-qualified thin
wrappers are declared here. -/

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
