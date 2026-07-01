/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

import Cslib.Init
public import Mathlib.Tactic.SetLike
public import Mathlib.Data.Set.Basic
public import Aesop

/-! # Since Seed Consistency — Shared Chronicle Point-Insertion Interface

This module factors the duplicated, `fc`-diverged Chronicle point-insertion *Since*
seed-consistency helpers shared by `Logics/Bimodal/.../PointInsertion/Since.lean` and
`Logics/Temporal/.../PointInsertion/Since.lean` into a common, interface-parameterized
module. The two logics' `lemma_2_7_since`/`lemma_2_8_since` proof skeletons are
line-for-line the same modulo an explicit `fc : FrameClass` parameter, notation aliases,
and a small number of genuinely divergent auxiliary-lemma shapes (all bridged here via
interface fields rather than assumed identical).

## Architecture

`SinceSeedInterface F` bundles:
- the abstract formula operators (`and`, `untl`, `snce`, `somePast`, `allPast`) and an
  abstract `Type`-valued contextual derivation family `Deriv : List F → F → Type*`
  (mirroring each logic's `DerivationTree fc`/`DerivationTree FrameClass.Base`);
- the low-level derivation combinators (`assumption`, `modusPonens`, `weakening`,
  `deductionTheorem`, `identity'`, `impTrans`, `lceImp`, `rceImp`, `combineImpConj`,
  `untlLeftMonoDeriv`, `pastNecessitation`) each logic already proves for its own
  `DerivationTree`;
- the Burgess/MCS apparatus lemmas the Since seed-consistency proofs invoke
  (`dcDeltaBControlled`, `selfAccumSinceMcs`, `linearSinceMcs`, `rightMonoSinceMcs`,
  `sinceImpliesP`, `consistentOfPMem`, `inconsistentSingletonFalse`,
  `derivationFromImplied`, `iteratedEnrichmentSince`, `xuLemma321Until`,
  `xuLemma321Since`, `burgessRImpliesBurgessRSince`, `burgessRSinceImpliesBurgessR`,
  `burgessRConj`, `burgessRSinceConj`, `dcDeltaBBurgessR3`,
  `burgessR3MaximalExtensionFails`, `burgessR3MaximalExtensionExists`,
  `listConjMemDcs`, `listConjMemMcs`, `listConjImpliesElem`, `theoremInMcs`,
  `negationComplete`, `negExcludes`, `cudContainsTheorems`) as *statements only* —
  each logic supplies its own proof when building its instance.

Purely definitional notions (`SetConsistent`, `SetMaximalConsistent`,
`ClosedUnderDerivation`, `deductiveClosure`, `burgessR`, `burgessRSet`, `burgessRSince`,
`burgessRSetSince`, `burgessR3`, `BurgessR3Maximal`, `gContent`, `hContent`, `listConj`)
are **not** interface fields: both logics define them identically (modulo `fc`) in terms
of the primitives above, so they are generic `def`s parameterized by an interface value.

A `structure` (not a `class`) is used because Bimodal needs an *instance family* indexed
by `fc : FrameClass`, while Temporal needs exactly one instance — explicit passing (as in
task 452's `HilbertTree`) is clearer than instance resolution across several live `fc`.

## Status

Phase 0 (signature/defeq skeleton) + Phase 1 (small `l27s*` formula-operator helpers).
The generic `lemma_2_7_since_seed_consistent` / `lemma_2_8_since_seed_consistent` bodies
are ported in later phases (2/3/4/5 of the task-454 plan); see
`specs/454_consolidate_chronicle_pointinsertion_bimodal_temporal/plans/`.

## References

* Cslib/Logics/Bimodal/Metalogic/BXCanonical/Chronicle/PointInsertion/Since.lean
* Cslib/Logics/Temporal/Metalogic/Chronicle/PointInsertion/Since.lean
* Cslib/Foundations/Logic/Metalogic/GenericMCS.lean — `HilbertTree`, the precedent for a
  `Type*`-valued abstract derivation family.
-/

@[expose] public section

namespace Cslib.Logic.Metalogic.Chronicle

set_option linter.style.setOption false
set_option linter.flexible false
set_option linter.unusedSimpArgs false

variable {F : Type*}

/-! ## Purely Definitional Notions (parameterized directly by primitives)

These helpers take the primitive pieces they need as explicit arguments so they can be
used both (a) inside `SinceSeedInterface` field types, where the primitive fields are
already in scope by name, and (b) after the structure is closed, via the `I.*`-qualified
wrappers in the next section. -/

/-- A finite context is consistent iff it does not derive `⊥`. -/
def isConsistentCtx (Deriv : List F → F → Type*) (bot : F) (Γ : List F) : Prop :=
  ¬ Nonempty (Deriv Γ bot)

/-- A set is consistent iff every finite subset (as a list) is consistent. -/
def isSetConsistent (Deriv : List F → F → Type*) (bot : F) (S : Set F) : Prop :=
  ∀ L : List F, (∀ φ ∈ L, φ ∈ S) → isConsistentCtx Deriv bot L

/-- A set is maximally consistent iff it is consistent and no proper extension is. -/
def isSetMaximalConsistent (Deriv : List F → F → Type*) (bot : F) (S : Set F) : Prop :=
  isSetConsistent Deriv bot S ∧ ∀ φ : F, φ ∉ S → ¬ isSetConsistent Deriv bot (insert φ S)

/-- A set is closed under derivation iff every derivable consequence of a finite subset
already belongs to the set. -/
def isClosedUnderDerivation (Deriv : List F → F → Type*) (S : Set F) : Prop :=
  ∀ (L : List F) (φ : F), (∀ ψ ∈ L, ψ ∈ S) → Deriv L φ → φ ∈ S

/-- Deductive closure: all formulas derivable from some finite subset of `S`. -/
noncomputable def dClosureOf (Deriv : List F → F → Type*) (S : Set F) : Set F :=
  {φ | ∃ L : List F, (∀ ψ ∈ L, ψ ∈ S) ∧ Nonempty (Deriv L φ)}

/-- Content-based Burgess r-relation: every `gamma` in `C` satisfies `untl beta gamma ∈ A`. -/
def rBurgessOf (untl : F → F → F) (A : Set F) (beta : F) (C : Set F) : Prop :=
  ∀ gamma ∈ C, untl beta gamma ∈ A

/-- `rBurgessOf` lifted to a set of pivot formulas `B`. -/
def rSetBurgessOf (untl : F → F → F) (A B C : Set F) : Prop :=
  ∀ beta ∈ B, rBurgessOf untl A beta C

/-- Since-variant of the content-based Burgess r-relation. -/
def rSinceBurgessOf (snce : F → F → F) (A : Set F) (beta : F) (C : Set F) : Prop :=
  ∀ gamma ∈ C, snce beta gamma ∈ A

/-- `rSinceBurgessOf` lifted to a set of pivot formulas `B`. -/
def rSetSinceBurgessOf (snce : F → F → F) (A B C : Set F) : Prop :=
  ∀ beta ∈ B, rSinceBurgessOf snce A beta C

/-- Combined Burgess r3-relation: `rSetBurgessOf A B C` and `rSetSinceBurgessOf C B A`. -/
def r3BurgessOf (untl snce : F → F → F) (A B C : Set F) : Prop :=
  rSetBurgessOf untl A B C ∧ rSetSinceBurgessOf snce C B A

/-- `B` is Burgess-R3-maximal for `(A, C)`: CUD, `r3BurgessOf`-related, no proper
extension is. -/
def r3MaximalBurgessOf (Deriv : List F → F → Type*) (untl snce : F → F → F)
    (A B C : Set F) : Prop :=
  isClosedUnderDerivation Deriv B ∧
  r3BurgessOf untl snce A B C ∧
  ∀ D, isClosedUnderDerivation Deriv D → B ⊂ D → ¬ r3BurgessOf untl snce A D C

/-- `gContent M`: formulas `φ` such that `allFuture φ ∈ M`. -/
def gContentOf (allFuture : F → F) (M : Set F) : Set F := {φ | allFuture φ ∈ M}

/-- `hContent M`: formulas `φ` such that `allPast φ ∈ M`. -/
def hContentOf (allPast : F → F) (M : Set F) : Set F := {φ | allPast φ ∈ M}

/-! ## `SinceSeedInterface`: the shared apparatus

One instance per logic (Temporal: a single value; Bimodal: an `fc`-indexed family, since
`FrameClass` threading means Bimodal needs one interface value per `fc`). -/

/-- Everything the Since point-insertion seed-consistency proofs consume from the
formula/derivation/Burgess layer of a tense logic, statement-only where the underlying
proof is logic-specific. One instance per `(logic, frame index)`. -/
structure SinceSeedInterface (F : Type*) where
  /-- Falsum. -/
  bot : F
  /-- Implication. -/
  imp : F → F → F
  /-- Conjunction. -/
  and : F → F → F
  /-- Until. -/
  untl : F → F → F
  /-- Since. -/
  snce : F → F → F
  /-- Injectivity of `untl` (a genuine primitive `Formula` constructor in both logics). -/
  untlInjective : ∀ {a b c d : F}, untl a b = untl c d → a = c ∧ b = d
  /-- Injectivity of `and` (derived from the Lukasiewicz encoding `and φ ψ := imp (imp φ
  (imp ψ bot)) bot` in both logics, hence injective via `imp`'s injectivity; kept as a
  field rather than re-derived so `and` itself can stay an opaque primitive here). -/
  andInjective : ∀ {a b c d : F}, and a b = and c d → a = c ∧ b = d
  /-- Some-past (`𝐏`). -/
  somePast : F → F
  /-- All-past (`𝐇`). -/
  allPast : F → F
  /-- All-future (`𝐆`), needed only for `gContent`'s definitional shape. -/
  allFuture : F → F
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
  /-- Combine two empty-context implications into a conjunction. -/
  combineImpConj : ∀ {φ ψ χ : F},
    Deriv [] (imp φ ψ) → Deriv [] (imp φ χ) → Deriv [] (imp φ (and ψ χ))
  /-- Left monotonicity of `untl` at the derivation level. -/
  untlLeftMonoDeriv : ∀ (guard1 event guard2 : F),
    Deriv [] (imp guard1 guard2) → Deriv [] (imp (untl guard1 event) (untl guard2 event))
  /-- Past necessitation: `⊢ φ` implies `⊢ allPast φ`. -/
  pastNecessitation : ∀ (φ : F), Deriv [] φ → Deriv [] (allPast φ)
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
  /-- BX5' at MCS level: `snce γ β ∈ A` implies `snce (γ ∧ snce γ β) β ∈ A`. -/
  selfAccumSinceMcs : ∀ {A : Set F}, isSetMaximalConsistent Deriv bot A →
    ∀ (γ β : F), snce γ β ∈ A → snce (and γ (snce γ β)) β ∈ A
  /-- BX7' (linear_since) at MCS level. -/
  linearSinceMcs : ∀ {A : Set F}, isSetMaximalConsistent Deriv bot A →
    ∀ (φ ψ χ θ : F), snce φ ψ ∈ A → snce χ θ ∈ A →
      snce (and φ χ) (and ψ θ) ∈ A ∨ snce (and φ χ) (and ψ χ) ∈ A ∨
      snce (and φ χ) (and φ θ) ∈ A
  /-- Right monotonicity for Since at MCS level. -/
  rightMonoSinceMcs : ∀ {C : Set F}, isSetMaximalConsistent Deriv bot C →
    ∀ {φ ψ χ : F}, Deriv [] (imp ψ χ) → snce φ ψ ∈ C → snce φ χ ∈ C
  /-- `snce γ δ ∈ A` (MCS) implies `somePast δ ∈ A`. -/
  sinceImpliesP : ∀ {A : Set F}, isSetMaximalConsistent Deriv bot A →
    ∀ {γ δ : F}, snce γ δ ∈ A → somePast δ ∈ A
  /-- `somePast φ ∈ C` (MCS) implies `{φ}` is consistent. -/
  consistentOfPMem : ∀ {C : Set F}, isSetMaximalConsistent Deriv bot C →
    ∀ (φ : F), somePast φ ∈ C → isSetConsistent Deriv bot ({φ} : Set F)
  /-- A consistent singleton `{φ}` cannot derive `⊥` in context `[φ]`. -/
  inconsistentSingletonFalse : ∀ {φ : F},
    isSetConsistent Deriv bot ({φ} : Set F) → Deriv [φ] bot → False
  /-- Chain empty-context implications of every list element through to `Γ`. -/
  derivationFromImplied : ∀ (Γ L : List F) (ψ : F),
    (∀ φ ∈ L, Deriv Γ φ) → Deriv L ψ → Deriv Γ ψ
  /-- `dcDeltaBControlled`: an element derivable from `{delta} ∪ B` (B a CUD) is either
  already in `B`, or `⊢ (beta ∧ delta) → phi` for some guard `beta ∈ B`. -/
  dcDeltaBControlled : ∀ {B : Set F}, isClosedUnderDerivation Deriv B →
    ∀ {delta phi : F} {L : List F}, (∀ psi ∈ L, psi ∈ ({delta} : Set F) ∪ B) →
      Deriv L phi → (phi ∈ B) ∨ (∃ beta ∈ B, Nonempty (Deriv [] (imp (and beta delta) phi)))
  /-- Iterated BX13' enrichment (Since direction): given a Since-obligation on `guard`,
  produce a refined `event'` implying `event` and each `γ ∈ gammas` via `untl guard γ`. -/
  iteratedEnrichmentSince : ∀ {C : Set F}, isSetMaximalConsistent Deriv bot C →
    ∀ (guard : F) (gammas : List F), (∀ γ ∈ gammas, γ ∈ C) → ∀ (event : F),
      snce guard event ∈ C →
      Σ' (event' : F), (snce guard event' ∈ C) ×' (Deriv [] (imp event' event)) ×'
        (∀ γ ∈ gammas, Deriv [] (imp event' (untl guard γ)))
  /-- Xu Lemma 3.2.1 (i): if `R3Maximal(A, B, C)` then `untl beta gamma ∈ B` for
  `beta ∈ B`, `gamma ∈ C`. -/
  xuLemma321Until : ∀ {A B C : Set F}, isSetMaximalConsistent Deriv bot A →
    isSetMaximalConsistent Deriv bot C → r3MaximalBurgessOf Deriv untl snce A B C →
    ∀ {beta : F}, beta ∈ B → ∀ {gamma : F}, gamma ∈ C → untl beta gamma ∈ B
  /-- Xu Lemma 3.2.1 (ii): mirror for Since. -/
  xuLemma321Since : ∀ {A B C : Set F}, isSetMaximalConsistent Deriv bot A →
    isSetMaximalConsistent Deriv bot C → r3MaximalBurgessOf Deriv untl snce A B C →
    ∀ {beta : F}, beta ∈ B → ∀ {alpha : F}, alpha ∈ A → snce beta alpha ∈ B
  /-- Burgess Lemma 2.3 (forward): `rBurgessOf A β C` implies `rSinceBurgessOf C β A`. -/
  burgessRImpliesBurgessRSince : ∀ {A C : Set F}, isSetMaximalConsistent Deriv bot A →
    isSetMaximalConsistent Deriv bot C → ∀ {β : F}, rBurgessOf untl A β C →
      rSinceBurgessOf snce C β A
  /-- Burgess Lemma 2.3 (backward): `rSinceBurgessOf C β A` implies `rBurgessOf A β C`. -/
  burgessRSinceImpliesBurgessR : ∀ {A C : Set F}, isSetMaximalConsistent Deriv bot A →
    isSetMaximalConsistent Deriv bot C → ∀ {β : F}, rSinceBurgessOf snce C β A →
      rBurgessOf untl A β C
  /-- Set-level guard conjunction for `rBurgessOf`. -/
  burgessRConj : ∀ {A C : Set F}, isSetMaximalConsistent Deriv bot A →
    ∀ {α β : F}, rBurgessOf untl A α C → rBurgessOf untl A β C →
      rBurgessOf untl A (and α β) C
  /-- Set-level guard conjunction for `rSinceBurgessOf`. -/
  burgessRSinceConj : ∀ {A C : Set F}, isSetMaximalConsistent Deriv bot C →
    ∀ {α β : F}, rSinceBurgessOf snce C α A → rSinceBurgessOf snce C β A →
      rSinceBurgessOf snce C (and α β) A
  /-- `r3BurgessOf` extension fails: if `delta ∉ B`, the deductive closure of
  `{delta} ∪ B` does not satisfy `r3BurgessOf`. -/
  burgessR3MaximalExtensionFails : ∀ {A B C : Set F},
    r3MaximalBurgessOf Deriv untl snce A B C →
    ∀ {delta : F}, delta ∉ B → ¬ r3BurgessOf untl snce A (dClosureOf Deriv ({delta} ∪ B)) C
  /-- Extending `B` by `delta` preserves `r3BurgessOf`, given the Until/Since guard
  conditions relating `delta` to `A`/`C`. -/
  dcDeltaBBurgessR3 : ∀ {A B C : Set F}, isSetMaximalConsistent Deriv bot A →
    isSetMaximalConsistent Deriv bot C → isClosedUnderDerivation Deriv B →
    r3BurgessOf untl snce A B C → ∀ {delta : F},
      (∀ beta ∈ B, ∀ gamma ∈ C, untl (and beta delta) gamma ∈ A) →
      (∀ beta ∈ B, ∀ alpha ∈ A, snce (and beta delta) alpha ∈ C) →
      r3BurgessOf untl snce A (dClosureOf Deriv ({delta} ∪ B)) C
  /-- Zorn's-lemma extension: any CUD `Sig` satisfying `r3BurgessOf A Sig C` extends to
  some `B ⊇ Sig` with `BurgessR3Maximal A B C` (the extra `ClosedUnderDerivation B`
  conjunct some logics additionally return is discarded at the instantiation site). -/
  burgessR3MaximalExtensionExists : ∀ {A C Sig : Set F},
    isSetMaximalConsistent Deriv bot A → isSetMaximalConsistent Deriv bot C →
    isClosedUnderDerivation Deriv Sig → r3BurgessOf untl snce A Sig C →
    ∃ B : Set F, Sig ⊆ B ∧ r3MaximalBurgessOf Deriv untl snce A B C
  /-- Conjunction of a list of formulas (each logic supplies its own recursive
  definition; the empty list conventionally gives `⊤ := ⊥ → ⊥`). Kept as a field
  (rather than a generic `def`) so each logic's *own* `listConj` — and the lemmas
  about it below — can be reused verbatim, with no defeq-bridging obligation. -/
  listConj : List F → F
  /-- If `B` is CUD and every element of `L` is in `B`, so is `listConj L`. -/
  listConjMemDcs : ∀ {B : Set F}, isClosedUnderDerivation Deriv B →
    ∀ (L : List F), (∀ φ ∈ L, φ ∈ B) → listConj L ∈ B
  /-- If `A` is MCS and every element of `L` is in `A`, so is `listConj L`. -/
  listConjMemMcs : ∀ {A : Set F}, isSetMaximalConsistent Deriv bot A →
    ∀ (L : List F), (∀ φ ∈ L, φ ∈ A) → listConj L ∈ A
  /-- `⊢ listConj L → φ` for each `φ ∈ L`. -/
  listConjImpliesElem : ∀ (L : List F) (φ : F), φ ∈ L →
    Deriv [] (imp (listConj L) φ)

/-! ## Convenience wrappers over an interface value

These mirror the "P"/"Of" helpers above but take a bundled `I : SinceSeedInterface F`,
for use once an instance is in hand (e.g. in the generic seed-consistency theorems). -/

/-- `SetConsistent` w.r.t. `I`'s derivation family. -/
def SetConsistent (I : SinceSeedInterface F) (S : Set F) : Prop :=
  isSetConsistent I.Deriv I.bot S

/-- `SetMaximalConsistent` w.r.t. `I`'s derivation family. -/
def SetMaximalConsistent (I : SinceSeedInterface F) (S : Set F) : Prop :=
  isSetMaximalConsistent I.Deriv I.bot S

/-- `ClosedUnderDerivation` w.r.t. `I`'s derivation family. -/
def ClosedUnderDerivation (I : SinceSeedInterface F) (S : Set F) : Prop :=
  isClosedUnderDerivation I.Deriv S

/-- Deductive closure w.r.t. `I`'s derivation family. -/
noncomputable def deductiveClosure (I : SinceSeedInterface F) (S : Set F) : Set F :=
  dClosureOf I.Deriv S

/-- Burgess r-relation w.r.t. `I`'s `untl`. -/
def burgessR (I : SinceSeedInterface F) (A : Set F) (beta : F) (C : Set F) : Prop :=
  rBurgessOf I.untl A beta C

/-- `burgessR` lifted to a set of pivots. -/
def burgessRSet (I : SinceSeedInterface F) (A B C : Set F) : Prop :=
  rSetBurgessOf I.untl A B C

/-- Since-variant Burgess r-relation w.r.t. `I`'s `snce`. -/
def burgessRSince (I : SinceSeedInterface F) (A : Set F) (beta : F) (C : Set F) : Prop :=
  rSinceBurgessOf I.snce A beta C

/-- `burgessRSince` lifted to a set of pivots. -/
def burgessRSetSince (I : SinceSeedInterface F) (A B C : Set F) : Prop :=
  rSetSinceBurgessOf I.snce A B C

/-- Combined Burgess r3-relation w.r.t. `I`. -/
def burgessR3 (I : SinceSeedInterface F) (A B C : Set F) : Prop :=
  r3BurgessOf I.untl I.snce A B C

/-- `B` is Burgess-R3-maximal for `(A, C)` w.r.t. `I`. -/
def BurgessR3Maximal (I : SinceSeedInterface F) (A B C : Set F) : Prop :=
  r3MaximalBurgessOf I.Deriv I.untl I.snce A B C

/-- `gContent` w.r.t. `I`'s `allFuture`. -/
def gContent (I : SinceSeedInterface F) (M : Set F) : Set F := gContentOf I.allFuture M

/-- `hContent` w.r.t. `I`'s `allPast`. -/
def hContent (I : SinceSeedInterface F) (M : Set F) : Set F := hContentOf I.allPast M

/-! ## Since-Direction Seed and Small `l27s*` Helpers (task-454 Phase 1)

Ported verbatim (modulo `I.*`-qualification) from the near-byte-identical
`lemma27SinceSeed`/`l27s*` family shared by both logics' `Since.lean` files. These
depend only on the formula operators (`and`, `untl`) and pure list plumbing — no
Burgess/MCS apparatus — so they factor over `SinceSeedInterface` with no additional
fields. The one non-mechanical proof-line divergence noted in the task-454 research
(`simp only [Formula.and, Formula.neg]` in Bimodal vs. `simp only [Formula.and]` in
Temporal, inside `l27s_b5_β_mem`) is resolved here by using `andInjective` directly
instead of unfolding `and`/`neg` via `simp`, which sidesteps the divergence entirely. -/

variable (I : SinceSeedInterface F)

/-- Since-direction seed: `B ∪ {eta} ∪ {untl(β∧xi, γ) | β∈B, γ∈C}`. -/
@[nolint unusedArguments]
def lemma27SinceSeed (_A B C : Set F) (xi eta : F) : Set F :=
  B ∪ {eta} ∪ {φ | ∃ β ∈ B, ∃ γ ∈ C, φ = I.untl (I.and β xi) γ}

/-- Extract `γ'` events from component-3 elements (`untl(β∧xi, γ')`) of a list. -/
noncomputable def l27sC5EventList (B C : Set F) (xi : F) (L : List F) : List F :=
  L.filterMap (fun φ => by
    classical
    exact if h : ∃ β' ∈ B, ∃ γ ∈ C, φ = I.untl (I.and β' xi) γ then
      some (Classical.choose (Classical.choose_spec h).2)
    else none)

/-- Elements of `l27sC5EventList` are in `C`. -/
theorem l27s_c5_event_list_mem {B C : Set F} {xi : F}
    {L : List F} {γ : F} (hγ : γ ∈ l27sC5EventList I B C xi L) : γ ∈ C := by
  unfold l27sC5EventList at hγ
  simp [List.mem_filterMap] at hγ
  obtain ⟨φ, _, hγ_eq⟩ := hγ
  by_cases h : ∃ β' ∈ B, ∃ γ' ∈ C, φ = I.untl (I.and β' xi) γ'
  · simp [h] at hγ_eq; subst hγ_eq
    exact (Classical.choose_spec (Classical.choose_spec h).2).1
  · simp [h] at hγ_eq

/-- Extract `β'` guards from component-3 elements of a list. -/
noncomputable def l27sB5GuardList (B C : Set F) (xi : F) (L : List F) : List F :=
  L.filterMap (fun φ => by
    classical
    exact if h : ∃ β' ∈ B, ∃ γ ∈ C, φ = I.untl (I.and β' xi) γ then
      some (Classical.choose h)
    else none)

/-- Elements of `l27sB5GuardList` are in `B`. -/
theorem l27s_b5_guard_list_mem {B C : Set F} {xi : F}
    {L : List F} {β : F} (hβ : β ∈ l27sB5GuardList I B C xi L) : β ∈ B := by
  unfold l27sB5GuardList at hβ
  simp [List.mem_filterMap] at hβ
  obtain ⟨φ, _, hβ_eq⟩ := hβ
  by_cases h : ∃ β' ∈ B, ∃ γ' ∈ C, φ = I.untl (I.and β' xi) γ'
  · simp [h] at hβ_eq; subst hβ_eq
    exact (Classical.choose_spec h).1
  · simp [h] at hβ_eq

/-- For a component-3 element `untl(β'∧xi, γ')` in `L`, the extracted `γ'` is in
`l27sC5EventList`. -/
theorem l27s_c5_γ_mem {B C : Set F} {xi : F}
    {L : List F} {β' γ' : F}
    (hφ : I.untl (I.and β' xi) γ' ∈ L)
    (hβ' : β' ∈ B) (hγ' : γ' ∈ C) :
    γ' ∈ l27sC5EventList I B C xi L := by
  unfold l27sC5EventList
  simp only [List.mem_filterMap]
  refine ⟨I.untl (I.and β' xi) γ', hφ, ?_⟩
  have h : ∃ β'' ∈ B, ∃ γ'' ∈ C, I.untl (I.and β' xi) γ' =
      I.untl (I.and β'' xi) γ'' := ⟨β', hβ', γ', hγ', rfl⟩
  simp only [h, ↓reduceDIte]
  have h_spec := (Classical.choose_spec (Classical.choose_spec h).2)
  exact congr_arg some (I.untlInjective h_spec.2).2.symm

/-- For a component-3 element `untl(β'∧xi, γ')` in `L`, the extracted `β'` is in
`l27sB5GuardList`. -/
theorem l27s_b5_β_mem {B C : Set F} {xi : F}
    {L : List F} {β' γ' : F}
    (hφ : I.untl (I.and β' xi) γ' ∈ L)
    (hβ' : β' ∈ B) (hγ' : γ' ∈ C) :
    β' ∈ l27sB5GuardList I B C xi L := by
  unfold l27sB5GuardList
  simp only [List.mem_filterMap]
  refine ⟨I.untl (I.and β' xi) γ', hφ, ?_⟩
  have h : ∃ β'' ∈ B, ∃ γ'' ∈ C, I.untl (I.and β' xi) γ' =
      I.untl (I.and β'' xi) γ'' := ⟨β', hβ', γ', hγ', rfl⟩
  simp only [h, ↓reduceDIte]
  have h_spec := Classical.choose_spec h
  obtain ⟨_, γ'', _, h_formula_eq⟩ := h_spec
  have h_inj := I.untlInjective h_formula_eq
  exact congr_arg some (I.andInjective h_inj.1).1.symm

end Cslib.Logic.Metalogic.Chronicle
