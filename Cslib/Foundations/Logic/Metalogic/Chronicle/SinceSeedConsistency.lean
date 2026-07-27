/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

import Cslib.Init
public import Mathlib.Tactic.SetLike
public import Mathlib.Data.Set.Basic
public import Mathlib.Data.Set.Insert
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
`GenericMCS.lean`'s `HilbertTree`) is clearer than instance resolution across several live `fc`.

## Status

Complete: the signature/defeq skeleton, the small `l27s*` formula-operator helpers, and the
generic `lemma_2_7_since_seed_consistent`/`lemma_2_7_since`/`lemma_2_8_since_seed_consistent`/
`lemma_2_8_since` bodies are all landed sorry-free below.

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
  /-- Disjunction (needed by `lemma_2_8_since`'s `α'` construction).
  Negation is NOT a separate field -- both logics' `Formula.neg` is the transparent
  Lukasiewicz encoding `imp _ bot`, so it is always written inline as `imp _ bot` rather
  than through an opaque projection (an opaque `neg` field would block `modusPonens`/
  `deductionTheorem` steps that need to see through it as an implication). -/
  or : F → F → F
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
  /-- Left monotonicity of `untl` at MCS-membership level (not
  derivable from `untlLeftMonoDeriv` alone since it additionally needs
  `theoremInMcs`/`temporal_necessitation` bridging specific to each logic's `𝐆`
  encoding; kept as a field). -/
  untlLeftMonoThm : ∀ {A : Set F}, isSetMaximalConsistent Deriv bot A →
    ∀ {β₁ β₂ γ : F}, Deriv [] (imp β₁ β₂) → untl β₁ γ ∈ A → untl β₂ γ ∈ A
  /-- Left monotonicity of `snce` at MCS-membership level (mirror of
  `untlLeftMonoThm` for Since). -/
  snceLeftMonoThm : ∀ {A : Set F}, isSetMaximalConsistent Deriv bot A →
    ∀ {β₁ β₂ γ : F}, Deriv [] (imp β₁ β₂) → snce β₁ γ ∈ A → snce β₂ γ ∈ A
  /-- Lindenbaum's lemma: every consistent set extends to a maximally consistent
  superset. -/
  lindenbaum : ∀ {S : Set F}, isSetConsistent Deriv bot S →
    ∃ M, S ⊆ M ∧ isSetMaximalConsistent Deriv bot M
  /-- De Morgan for disjunction negation, written with `imp _ bot`
  standing for negation throughout (see the `or` field docstring):
  `⊢ ¬(A ∨ B) → ¬A ∧ ¬B`. -/
  demorganDisjNegForward : ∀ (A B : F),
    Deriv [] (imp (imp (or A B) bot) (and (imp A bot) (imp B bot)))
  /-- Right monotonicity of `somePast`-membership under empty-context implication
  (mirrors `rightMonoSinceMcs` but for the derived `somePast`
  operator, which is not assumed reducible to `snce` generically). -/
  pMonoMcs : ∀ {C : Set F}, isSetMaximalConsistent Deriv bot C →
    ∀ {phi psi : F}, Deriv [] (imp phi psi) → somePast phi ∈ C → somePast psi ∈ C
  /-- `somePast psi ∈ M` and `allPast ¬psi ∈ M` (with `¬psi := imp psi bot`) cannot both
  hold in an MCS. -/
  somePastAllPastNegAbsurd : ∀ {M : Set F}, isSetMaximalConsistent Deriv bot M →
    ∀ (psi : F), somePast psi ∈ M → allPast (imp psi bot) ∈ M → False

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

/-! ## Since-Direction Seed and Small `l27s*` Helpers

Ported verbatim (modulo `I.*`-qualification) from the near-byte-identical
`lemma27SinceSeed`/`l27s*` family shared by both logics' `Since.lean` files. These
depend only on the formula operators (`and`, `untl`) and pure list plumbing — no
Burgess/MCS apparatus — so they factor over `SinceSeedInterface` with no additional
fields. The one non-mechanical proof-line divergence between the two logics
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

/-! ## Deductive Closure is a Closure Operator

Both logics prove `Sig ⊆ deductiveClosure Sig` and
`ClosedUnderDerivation (deductiveClosure Sig)` by the same argument purely in terms of the
abstract `Deriv` family, so these factor generically with no new interface fields. -/

/-- Every element of `Sig` is in its own deductive closure (singleton witness list). -/
theorem subsetDeductiveClosure (Sig : Set F) : Sig ⊆ deductiveClosure I Sig := by
  intro φ hφ
  exact ⟨[φ], fun ψ hψ => by simp at hψ; exact hψ ▸ hφ, ⟨I.assumption (by simp)⟩⟩

/-- `deductiveClosure Sig` is closed under derivation (the deductive-closure closure lemma,
proved by induction on the witness context). -/
theorem deductiveClosureClosed (Sig : Set F) :
    ∀ (L : List F) (φ : F),
      (∀ ψ ∈ L, ψ ∈ deductiveClosure I Sig) → I.Deriv L φ → φ ∈ deductiveClosure I Sig := by
  intro L
  induction L with
  | nil =>
    intro φ _ d
    exact ⟨[], fun _ h => absurd h List.not_mem_nil, ⟨d⟩⟩
  | cons ψ L' ih =>
    intro φ hL d
    have d_imp := I.deductionTheorem L' ψ φ d
    have hψ := hL ψ (List.mem_cons_self ..)
    have hL' : ∀ χ ∈ L', χ ∈ deductiveClosure I Sig :=
      fun χ hχ => hL χ (List.mem_cons_of_mem ψ hχ)
    have h_imp := ih (I.imp ψ φ) hL' d_imp
    obtain ⟨M1, hM1_sub, ⟨d1⟩⟩ := h_imp
    obtain ⟨M2, hM2_sub, ⟨d2⟩⟩ := hψ
    refine ⟨M1 ++ M2, fun χ hχ => ?_, ?_⟩
    · rcases List.mem_append.mp hχ with h | h
      · exact hM1_sub χ h
      · exact hM2_sub χ h
    · exact ⟨I.modusPonens
        (I.weakening M1 (M1 ++ M2) (I.imp ψ φ) d1 (List.subset_append_left ..))
        (I.weakening M2 (M1 ++ M2) ψ d2 (List.subset_append_right ..))⟩

/-- `deductiveClosure Sig` is closed under derivation. -/
theorem deductiveClosureClosedUnderDerivation (Sig : Set F) :
    ClosedUnderDerivation I (deductiveClosure I Sig) :=
  deductiveClosureClosed I Sig

/-! ## Generic `lemma_2_7_since_seed_consistent` / `lemma_2_7_since`

Ported from Temporal's `fc := .Base` reading (the two logics' bodies diverge 100%
mechanically modulo `fc`-threading and notation). -/

/-- Since-direction seed consistency. Uses the BX5'+BX7'+BX13' chain (via `I`'s
apparatus fields) to show the `lemma27SinceSeed` is consistent whenever `xi ∉ B`. -/
theorem lemma_2_7_since_seed_consistent {A B C : Set F}
    (h_mcs_A : SetMaximalConsistent I A)
    (h_mcs_C : SetMaximalConsistent I C)
    (h_r3m : BurgessR3Maximal I A B C)
    (h_B_dcs : ClosedUnderDerivation I B)
    (_h_gc : gContent I A ⊆ C)
    (xi eta : F)
    (h_since : I.snce xi eta ∈ C)
    (h_xi_not_B : xi ∉ B) :
    SetConsistent I (lemma27SinceSeed I A B C xi eta) := by
  have h_r3 : burgessR3 I A B C := h_r3m.2.1
  have h_not_r3_xi := I.burgessR3MaximalExtensionFails h_r3m h_xi_not_B
  have h_neg_since_exists : ∃ beta0 ∈ B, ∃ alpha0 ∈ A,
      I.snce (I.and beta0 xi) alpha0 ∉ C := by
    by_contra h_all_since
    push Not at h_all_since
    have h_rset : burgessRSet I A (deductiveClosure I ({xi} ∪ B)) C := by
      intro phi hphi gamma hgamma
      obtain ⟨Ldc, hL_sub, ⟨ddc⟩⟩ := hphi
      rcases I.dcDeltaBControlled h_B_dcs hL_sub ddc with h_B_case | ⟨beta_w, hbeta_w, ⟨hImpl⟩⟩
      · exact h_r3.1 phi h_B_case gamma hgamma
      · have h_burgessRSince_ext : burgessRSince I C (I.and beta_w xi) A :=
          fun alpha halpha => h_all_since beta_w hbeta_w alpha halpha
        have h_burgessR_ext := I.burgessRSinceImpliesBurgessR h_mcs_A h_mcs_C h_burgessRSince_ext
        exact I.untlLeftMonoThm h_mcs_A hImpl (h_burgessR_ext gamma hgamma)
    have h_rsince : burgessRSetSince I C (deductiveClosure I ({xi} ∪ B)) A := by
      intro phi hphi alpha halpha
      obtain ⟨Ldc, hL_sub, ⟨ddc⟩⟩ := hphi
      rcases I.dcDeltaBControlled h_B_dcs hL_sub ddc with h_B_case | ⟨beta_w, hbeta_w, ⟨hImpl⟩⟩
      · exact h_r3.2 phi h_B_case alpha halpha
      · exact I.snceLeftMonoThm h_mcs_C hImpl (h_all_since beta_w hbeta_w alpha halpha)
    exact h_not_r3_xi ⟨h_rset, h_rsince⟩
  obtain ⟨beta0, h_beta0, alpha0, h_alpha0, h_not_in_C⟩ := h_neg_since_exists
  have h_neg_since_in_C : I.imp (I.snce (I.and beta0 xi) alpha0) I.bot ∈ C := by
    rcases I.negationComplete h_mcs_C (I.snce (I.and beta0 xi) alpha0) with h | h
    · exfalso; exact h_not_in_C h
    · exact h
  intro L hL ⟨d⟩
  have h_bx5_xe := I.selfAccumSinceMcs h_mcs_C xi eta h_since
  suffices h_key : ∀ (b : F) (hb : b ∈ B) (h_b_beta0 : I.Deriv [] (I.imp b beta0))
      (α_hat : F) (hα : α_hat ∈ A) (h_α_alpha0 : I.Deriv [] (I.imp α_hat alpha0))
      (gamma_list : List F) (h_gammas : ∀ γ ∈ gamma_list, γ ∈ C),
      Σ' (event : F),
        I.somePast event ∈ C ×'
        I.Deriv [] (I.imp event b) ×'
        I.Deriv [] (I.imp event eta) ×'
        I.Deriv [] (I.imp event (I.snce b α_hat)) ×'
        (∀ γ ∈ gamma_list,
          I.Deriv [] (I.imp event (I.untl (I.and b (I.and xi (I.snce xi eta))) γ))) by
    let b_list_5 := l27sB5GuardList I B C xi L
    have hb_list_5 : ∀ g ∈ b_list_5, g ∈ B := fun g hg => l27s_b5_guard_list_mem I hg
    let c_list := l27sC5EventList I B C xi L
    have hc_list : ∀ γ ∈ c_list, γ ∈ C := fun γ hγ => l27s_c5_event_list_mem I hγ
    haveI : DecidablePred (· ∈ B) := fun _ => Classical.dec _
    let b_list_B := L.filter (· ∈ B)
    have hb_list_B : ∀ g ∈ b_list_B, g ∈ B := by
      intro g hg; exact decide_eq_true_eq.mp (List.mem_filter.mp hg).2
    let b_list := beta0 :: (b_list_B ++ b_list_5)
    have hb_list' : ∀ g ∈ b_list, g ∈ B := by
      intro g hg; rcases List.mem_cons.mp hg with rfl | h
      · exact h_beta0
      · rcases List.mem_append.mp h with h1 | h2
        · exact hb_list_B g h1
        · exact hb_list_5 g h2
    let a_list : List F := [alpha0]
    have ha_list : ∀ α ∈ a_list, α ∈ A := by
      intro α hα; simp [a_list] at hα; subst hα; exact h_alpha0
    let b := I.listConj b_list
    let α_hat := I.listConj a_list
    have hb_B : b ∈ B := I.listConjMemDcs h_B_dcs b_list hb_list'
    have hα_A : α_hat ∈ A := I.listConjMemMcs h_mcs_A a_list ha_list
    have h_b_to_beta0 : I.Deriv [] (I.imp b beta0) :=
      I.listConjImpliesElem b_list beta0 (List.mem_cons.mpr (Or.inl rfl))
    have h_α_to_alpha0 : I.Deriv [] (I.imp α_hat alpha0) :=
      I.listConjImpliesElem a_list alpha0 (by simp [a_list])
    obtain ⟨event, h_P_event, h_ev_b, h_ev_eta, _h_ev_snce, h_ev_untl⟩ :=
      h_key b hb_B h_b_to_beta0 α_hat hα_A h_α_to_alpha0 c_list hc_list
    let χ_gen := I.and xi (I.snce xi eta)
    have h_event_implies_L : ∀ φ ∈ L, I.Deriv [event] φ := by
      intro φ hφ
      have h_φ_seed := hL φ hφ
      by_cases h_B_case : φ ∈ B
      · have h_φ_in_B_list : φ ∈ b_list_B :=
          List.mem_filter.mpr ⟨hφ, decide_eq_true_eq.mpr h_B_case⟩
        have h_φ_in_b : φ ∈ b_list :=
          List.mem_cons.mpr (Or.inr (List.mem_append.mpr (Or.inl h_φ_in_B_list)))
        have h_b_to_φ := I.listConjImpliesElem b_list φ h_φ_in_b
        have h_ev_to_φ := I.impTrans h_ev_b h_b_to_φ
        exact I.modusPonens
          (I.weakening [] _ _ h_ev_to_φ (List.nil_subset _))
          (I.assumption (by exact List.mem_singleton.mpr rfl))
      · by_cases h_eta : φ = eta
        · subst h_eta
          exact I.modusPonens
            (I.weakening [] _ _ h_ev_eta (List.nil_subset _))
            (I.assumption (by exact List.mem_singleton.mpr rfl))
        · by_cases h_comp5 : ∃ β' ∈ B, ∃ γ' ∈ C, φ = I.untl (I.and β' xi) γ'
          · let β' := Classical.choose h_comp5
            have hβ' : β' ∈ B := (Classical.choose_spec h_comp5).1
            let γ' := Classical.choose (Classical.choose_spec h_comp5).2
            have hγ' : γ' ∈ C :=
              (Classical.choose_spec (Classical.choose_spec h_comp5).2).1
            have h_eq : φ = I.untl (I.and β' xi) γ' :=
              (Classical.choose_spec (Classical.choose_spec h_comp5).2).2
            rw [h_eq]
            have h_φ_eq : I.untl (I.and β' xi) γ' ∈ L := by
              rw [← h_eq]; exact hφ
            have h_β'_in_5 := l27s_b5_β_mem I h_φ_eq hβ' hγ'
            have h_β'_in_b : β' ∈ b_list :=
              List.mem_cons.mpr (Or.inr (List.mem_append.mpr (Or.inr h_β'_in_5)))
            have h_b_to_β' := I.listConjImpliesElem b_list β' h_β'_in_b
            have h_γ'_in_c := l27s_c5_γ_mem I h_φ_eq hβ' hγ'
            have h_ev_untl_γ' := h_ev_untl γ' h_γ'_in_c
            have h_bχ_to_β'xi : I.Deriv [] (I.imp (I.and b χ_gen) (I.and β' xi)) := by
              have h1 := I.impTrans (I.lceImp b χ_gen) h_b_to_β'
              have h2 : I.Deriv [] (I.imp (I.and b χ_gen) xi) :=
                I.impTrans (I.rceImp b χ_gen) (I.lceImp xi (I.snce xi eta))
              exact I.combineImpConj h1 h2
            have h_left := I.untlLeftMonoDeriv (I.and b χ_gen) γ'
              (I.and β' xi) h_bχ_to_β'xi
            have h_chain := I.impTrans h_ev_untl_γ' h_left
            exact I.modusPonens
              (I.weakening [] _ _ h_chain (List.nil_subset _))
              (I.assumption (by exact List.mem_singleton.mpr rfl))
          · exfalso
            simp only [lemma27SinceSeed, Set.mem_union, Set.mem_ofPred_eq,
              Set.mem_singleton_iff] at h_φ_seed
            rcases h_φ_seed with ((h1 | h2) | h5)
            · exact h_B_case h1
            · exact h_eta h2
            · exact h_comp5 h5
    have d_event : I.Deriv [event] I.bot :=
      I.derivationFromImplied [event] L I.bot h_event_implies_L d
    have h_event_cons := I.consistentOfPMem h_mcs_C event h_P_event
    exact I.inconsistentSingletonFalse h_event_cons d_event
  -- Prove h_key: BX5'+BX7'+BX13' chain.
  intro b hb h_b_beta0 α_hat hα h_α_alpha0 gamma_list h_gammas
  have h_snce_ba : I.snce b α_hat ∈ C := h_r3.2 b hb α_hat hα
  have h_bx5_ba := I.selfAccumSinceMcs h_mcs_C b α_hat h_snce_ba
  let φ_gen := I.and b (I.snce b α_hat)
  let χ_gen := I.and xi (I.snce xi eta)
  have h_bx7_gen := I.linearSinceMcs h_mcs_C φ_gen α_hat χ_gen eta h_bx5_ba h_bx5_xe
  have h_guard_to_b0xi : I.Deriv [] (I.imp (I.and φ_gen χ_gen) (I.and beta0 xi)) := by
    have h1 : I.Deriv [] _ :=
      I.impTrans (I.impTrans (I.lceImp φ_gen χ_gen) (I.lceImp b (I.snce b α_hat))) h_b_beta0
    have h2 : I.Deriv [] _ := I.impTrans (I.rceImp φ_gen χ_gen) (I.lceImp xi (I.snce xi eta))
    exact I.combineImpConj h1 h2
  have h_guard_to_alpha0 : I.Deriv [] (I.imp (I.and α_hat eta) alpha0) :=
    I.impTrans (I.lceImp α_hat eta) h_α_alpha0
  have h_D3_gen : I.snce (I.and φ_gen χ_gen) (I.and φ_gen eta) ∈ C := by
    rcases h_bx7_gen with h_D1 | h_D2 | h_D3
    · exfalso
      have h_rm : I.Deriv [] (I.imp (I.and α_hat eta) alpha0) := h_guard_to_alpha0
      have h_contra := I.rightMonoSinceMcs h_mcs_C h_rm
        (I.snceLeftMonoThm h_mcs_C h_guard_to_b0xi h_D1)
      exact I.negExcludes h_mcs_C h_neg_since_in_C h_contra
    · exfalso
      have h_rm : I.Deriv [] (I.imp (I.and α_hat χ_gen) alpha0) :=
        I.impTrans (I.lceImp α_hat χ_gen) h_α_alpha0
      have h_contra := I.rightMonoSinceMcs h_mcs_C h_rm
        (I.snceLeftMonoThm h_mcs_C h_guard_to_b0xi h_D2)
      exact I.negExcludes h_mcs_C h_neg_since_in_C h_contra
    · exact h_D3
  let guard := I.and φ_gen χ_gen
  let base_event := I.and φ_gen eta
  let evt := I.iteratedEnrichmentSince h_mcs_C guard gamma_list h_gammas base_event h_D3_gen
  let event := evt.1
  have h_P_event : I.somePast event ∈ C := I.sinceImpliesP h_mcs_C evt.2.1
  have h_ev_base := evt.2.2.1
  have h_ev_b : I.Deriv [] (I.imp event b) :=
    I.impTrans h_ev_base (I.impTrans (I.lceImp φ_gen eta) (I.lceImp b (I.snce b α_hat)))
  have h_ev_eta : I.Deriv [] (I.imp event eta) :=
    I.impTrans h_ev_base (I.rceImp φ_gen eta)
  have h_ev_snce_ba : I.Deriv [] (I.imp event (I.snce b α_hat)) :=
    I.impTrans h_ev_base (I.impTrans (I.lceImp φ_gen eta) (I.rceImp b (I.snce b α_hat)))
  have h_ev_untl : ∀ γ ∈ gamma_list,
      I.Deriv [] (I.imp event (I.untl (I.and b χ_gen) γ)) := by
    intro γ hγ
    have h_untl_guard := evt.2.2.2 γ hγ
    have h_guard_to_bχ : I.Deriv [] (I.imp guard (I.and b χ_gen)) := by
      have h1 : I.Deriv [] _ := I.impTrans (I.lceImp φ_gen χ_gen) (I.lceImp b (I.snce b α_hat))
      have h2 : I.Deriv [] _ := I.rceImp φ_gen χ_gen
      exact I.combineImpConj h1 h2
    exact I.impTrans h_untl_guard (I.untlLeftMonoDeriv guard γ (I.and b χ_gen) h_guard_to_bχ)
  exact ⟨event, h_P_event, h_ev_b, h_ev_eta, h_ev_snce_ba, h_ev_untl⟩

/-- **Lemma 2.7 (Since direction)**, generic over `I`: given `BurgessR3Maximal(A, B, C)`
with `snce(xi, eta) ∈ C` and `xi ∉ B`, construct MCS `D` with `eta ∈ D` splitting the R3
pair, returning `xi ∈ B''` via the `DC(B ∪ {xi})` Zorn seed. -/
theorem lemma_2_7_since {A B C : Set F}
    (h_mcs_A : SetMaximalConsistent I A)
    (h_mcs_C : SetMaximalConsistent I C)
    (h_r3m : BurgessR3Maximal I A B C)
    (h_B_dcs : ClosedUnderDerivation I B)
    (h_gc : gContent I A ⊆ C)
    (xi eta : F)
    (h_since : I.snce xi eta ∈ C)
    (h_xi_not_B : xi ∉ B) :
    ∃ B' D B'' : Set F,
      BurgessR3Maximal I A B' D ∧
      BurgessR3Maximal I D B'' C ∧
      SetMaximalConsistent I D ∧
      eta ∈ D ∧
      B ⊆ B' ∧
      B ⊆ D ∧
      B ⊆ B'' ∧
      xi ∈ B'' := by
  have h_seed_cons := lemma_2_7_since_seed_consistent I h_mcs_A h_mcs_C h_r3m h_B_dcs h_gc
    xi eta h_since h_xi_not_B
  obtain ⟨D, h_sup, h_D_mcs⟩ := I.lindenbaum h_seed_cons
  have h_eta_D : eta ∈ D := by
    apply h_sup; show eta ∈ lemma27SinceSeed I A B C xi eta
    simp [lemma27SinceSeed]
  have h_B_sub_D : B ⊆ D := by
    intro φ hφ; apply h_sup
    show φ ∈ lemma27SinceSeed I A B C xi eta; simp [lemma27SinceSeed, hφ]
  have h_untl_D : ∀ β ∈ B, ∀ γ ∈ C, I.untl β γ ∈ D := by
    intro β hβ γ hγ
    exact h_B_sub_D (I.xuLemma321Until h_mcs_A h_mcs_C h_r3m hβ hγ)
  have h_snce_D : ∀ β ∈ B, ∀ α ∈ A, I.snce β α ∈ D := by
    intro β hβ α hα
    exact h_B_sub_D (I.xuLemma321Since h_mcs_A h_mcs_C h_r3m hβ hα)
  have h_rSet_D : burgessRSet I D B C := fun β hβ γ hγ => h_untl_D β hβ γ hγ
  have h_rSetSince_D : burgessRSetSince I C B D := by
    intro β hβ
    exact I.burgessRImpliesBurgessRSince h_D_mcs h_mcs_C (h_rSet_D β hβ)
  have h_r3_DBC : burgessR3 I D B C := ⟨h_rSet_D, h_rSetSince_D⟩
  have h_rSetSince_A : burgessRSetSince I D B A := fun β hβ α hα => h_snce_D β hβ α hα
  have h_rSet_A : burgessRSet I A B D := by
    intro β hβ
    exact I.burgessRSinceImpliesBurgessR h_mcs_A h_D_mcs (h_rSetSince_A β hβ)
  have h_r3_ABD : burgessR3 I A B D := ⟨h_rSet_A, h_rSetSince_A⟩
  have h_untl_conj_xi_D : ∀ β ∈ B, ∀ γ ∈ C, I.untl (I.and β xi) γ ∈ D := by
    intro β hβ γ hγ; apply h_sup
    show I.untl (I.and β xi) γ ∈ lemma27SinceSeed I A B C xi eta
    simp only [lemma27SinceSeed, Set.mem_union, Set.mem_ofPred_eq]
    right; exact ⟨β, hβ, γ, hγ, rfl⟩
  have h_B_nonempty : ∃ β₀ : F, β₀ ∈ B := by
    exact ⟨I.imp I.bot I.bot, I.cudContainsTheorems h_r3m.1 (I.identity' I.bot)⟩
  obtain ⟨β₀, hβ₀⟩ := h_B_nonempty
  have h_untl_xi_D : ∀ γ ∈ C, I.untl xi γ ∈ D := by
    intro γ hγ
    exact I.untlLeftMonoThm h_D_mcs (I.rceImp β₀ xi) (h_untl_conj_xi_D β₀ hβ₀ γ hγ)
  have h_burgessR_xi : burgessR I D xi C := h_untl_xi_D
  have h_burgessRSince_xi : burgessRSince I C xi D :=
    I.burgessRImpliesBurgessRSince h_D_mcs h_mcs_C h_burgessR_xi
  have h_burgessR_conj' : ∀ β ∈ B, burgessR I D (I.and β xi) C := by
    intro β hβ
    exact I.burgessRConj h_D_mcs (h_rSet_D β hβ) h_burgessR_xi
  have h_snce_conj_xi_C : ∀ β ∈ B, ∀ δ ∈ D, I.snce (I.and β xi) δ ∈ C := by
    intro β hβ δ hδ
    have h_rSince := I.burgessRSinceConj h_mcs_C (h_rSetSince_D β hβ) h_burgessRSince_xi
    exact h_rSince δ hδ
  have h_r3_DC_DBC : burgessR3 I D (deductiveClosure I ({xi} ∪ B)) C :=
    I.dcDeltaBBurgessR3 h_D_mcs h_mcs_C h_B_dcs h_r3_DBC h_untl_conj_xi_D h_snce_conj_xi_C
  have h_DC_cud : ClosedUnderDerivation I (deductiveClosure I ({xi} ∪ B)) :=
    deductiveClosureClosedUnderDerivation I _
  obtain ⟨B', h_B_sub_B', h_B'_max⟩ := I.burgessR3MaximalExtensionExists h_mcs_A h_D_mcs
    h_B_dcs h_r3_ABD
  obtain ⟨B'', h_DC_sub_B'', h_B''_max⟩ := I.burgessR3MaximalExtensionExists h_D_mcs h_mcs_C
    h_DC_cud h_r3_DC_DBC
  have h_B_sub_DC : B ⊆ deductiveClosure I ({xi} ∪ B) :=
    fun φ hφ => subsetDeductiveClosure I _ (Set.mem_union_right _ hφ)
  have h_B_sub_B'' : B ⊆ B'' := Set.Subset.trans h_B_sub_DC h_DC_sub_B''
  have h_xi_in_DC : xi ∈ deductiveClosure I ({xi} ∪ B) :=
    subsetDeductiveClosure I _ (Set.mem_union_left _ (Set.mem_singleton xi))
  have h_xi_in_B'' : xi ∈ B'' := h_DC_sub_B'' h_xi_in_DC
  exact ⟨B', D, B'', h_B'_max, h_B''_max, h_D_mcs, h_eta_D, h_B_sub_B', h_B_sub_D,
    h_B_sub_B'', h_xi_in_B''⟩

/-! ## Generic `lemma_2_8_since_seed_consistent` / `lemma_2_8_since`

Ported from Temporal's `fc := .Base` reading, mirroring the `lemma_2_7_since` port above.
Uses the same BX5'+BX7'+BX13' chain but eliminates the D1/D2 cases via `α'` (the negated
disjunction `¬(eta ∨ (xi ∧ snce(xi, eta)))`) instead of `xi ∉ B`. -/

/-- Since-direction seed consistency for Lemma 2.8: same seed as `lemma_2_7_since_seed_consistent`
but proved via `¬(eta ∨ (xi ∧ snce(xi, eta))) ∈ A` instead of `xi ∉ B`. -/
theorem lemma_2_8_since_seed_consistent {A B C : Set F}
    (h_mcs_A : SetMaximalConsistent I A)
    (h_mcs_C : SetMaximalConsistent I C)
    (h_r3m : BurgessR3Maximal I A B C)
    (h_B_dcs : ClosedUnderDerivation I B)
    (_h_gc : gContent I A ⊆ C)
    (xi eta : F)
    (h_since : I.snce xi eta ∈ C)
    (h_neg_disj : I.imp (I.or eta (I.and xi (I.snce xi eta))) I.bot ∈ A) :
    SetConsistent I (lemma27SinceSeed I A B C xi eta) := by
  have h_r3 : burgessR3 I A B C := h_r3m.2.1
  set α' := I.imp (I.or eta (I.and xi (I.snce xi eta))) I.bot with α'_def
  have h_α'_to_neg_eta : I.Deriv [] (I.imp α' (I.imp eta I.bot)) :=
    I.impTrans (I.demorganDisjNegForward eta (I.and xi (I.snce xi eta)))
      (I.lceImp (I.imp eta I.bot) (I.imp (I.and xi (I.snce xi eta)) I.bot))
  have h_α'_to_neg_chi : I.Deriv [] (I.imp α' (I.imp (I.and xi (I.snce xi eta)) I.bot)) :=
    I.impTrans (I.demorganDisjNegForward eta (I.and xi (I.snce xi eta)))
      (I.rceImp (I.imp eta I.bot) (I.imp (I.and xi (I.snce xi eta)) I.bot))
  have h_bx5_xe := I.selfAccumSinceMcs h_mcs_C xi eta h_since
  suffices h_key : ∀ (b : F) (hb : b ∈ B)
      (α_hat : F) (hα : α_hat ∈ A) (h_α_to_α' : I.Deriv [] (I.imp α_hat α'))
      (gamma_list : List F) (h_gammas : ∀ γ ∈ gamma_list, γ ∈ C),
      Σ' (event : F),
        I.somePast event ∈ C ×'
        I.Deriv [] (I.imp event b) ×'
        I.Deriv [] (I.imp event eta) ×'
        I.Deriv [] (I.imp event (I.snce b α_hat)) ×'
        (∀ γ ∈ gamma_list,
          I.Deriv [] (I.imp event (I.untl (I.and b (I.and xi (I.snce xi eta))) γ))) by
    intro L hL ⟨d⟩
    haveI : DecidablePred (· ∈ B) := fun _ => Classical.dec _
    let b_list_5 := l27sB5GuardList I B C xi L
    have hb_list_5 : ∀ g ∈ b_list_5, g ∈ B := fun g hg => l27s_b5_guard_list_mem I hg
    let c_list := l27sC5EventList I B C xi L
    have hc_list : ∀ γ ∈ c_list, γ ∈ C := fun γ hγ => l27s_c5_event_list_mem I hγ
    let b_list_B := L.filter (· ∈ B)
    have hb_list_B : ∀ g ∈ b_list_B, g ∈ B := by
      intro g hg; exact decide_eq_true_eq.mp (List.mem_filter.mp hg).2
    let b_list := (I.imp I.bot I.bot) :: (b_list_B ++ b_list_5)
    have hb_list' : ∀ g ∈ b_list, g ∈ B := by
      intro g hg; rcases List.mem_cons.mp hg with rfl | h
      · exact I.cudContainsTheorems h_B_dcs (I.identity' I.bot)
      · rcases List.mem_append.mp h with h1 | h2
        · exact hb_list_B g h1
        · exact hb_list_5 g h2
    let a_list : List F := [α']
    have ha_list : ∀ α_elem ∈ a_list, α_elem ∈ A := by
      intro α_elem hα_elem; simp [a_list] at hα_elem; subst hα_elem; exact h_neg_disj
    let b := I.listConj b_list
    let α_hat := I.listConj a_list
    have hb_B : b ∈ B := I.listConjMemDcs h_B_dcs b_list hb_list'
    have hα_A : α_hat ∈ A := I.listConjMemMcs h_mcs_A a_list ha_list
    have h_αhat_to_α' : I.Deriv [] (I.imp α_hat α') :=
      I.listConjImpliesElem a_list α' (by simp [a_list])
    obtain ⟨event, h_P_event, h_ev_b, h_ev_eta, _h_ev_snce, h_ev_untl⟩ :=
      h_key b hb_B α_hat hα_A h_αhat_to_α' c_list hc_list
    let χ_gen := I.and xi (I.snce xi eta)
    have h_event_implies_L : ∀ φ ∈ L, I.Deriv [event] φ := by
      intro φ hφ
      have h_φ_seed := hL φ hφ
      by_cases h_B_case : φ ∈ B
      · have h_φ_in_B_list : φ ∈ b_list_B :=
          List.mem_filter.mpr ⟨hφ, decide_eq_true_eq.mpr h_B_case⟩
        have h_φ_in_b : φ ∈ b_list :=
          List.mem_cons.mpr (Or.inr (List.mem_append.mpr (Or.inl h_φ_in_B_list)))
        have h_b_to_φ := I.listConjImpliesElem b_list φ h_φ_in_b
        have h_ev_to_φ := I.impTrans h_ev_b h_b_to_φ
        exact I.modusPonens
          (I.weakening [] _ _ h_ev_to_φ (List.nil_subset _))
          (I.assumption (by exact List.mem_singleton.mpr rfl))
      · by_cases h_eta_case : φ = eta
        · subst h_eta_case
          exact I.modusPonens
            (I.weakening [] _ _ h_ev_eta (List.nil_subset _))
            (I.assumption (by exact List.mem_singleton.mpr rfl))
        · by_cases h_comp5 : ∃ β' ∈ B, ∃ γ' ∈ C, φ = I.untl (I.and β' xi) γ'
          · let β' := Classical.choose h_comp5
            have hβ' : β' ∈ B := (Classical.choose_spec h_comp5).1
            let γ' := Classical.choose (Classical.choose_spec h_comp5).2
            have hγ' : γ' ∈ C :=
              (Classical.choose_spec (Classical.choose_spec h_comp5).2).1
            have h_eq : φ = I.untl (I.and β' xi) γ' :=
              (Classical.choose_spec (Classical.choose_spec h_comp5).2).2
            rw [h_eq]
            have h_φ_eq : I.untl (I.and β' xi) γ' ∈ L := by
              rw [← h_eq]; exact hφ
            have h_β'_in_5 := l27s_b5_β_mem I h_φ_eq hβ' hγ'
            have h_β'_in_b : β' ∈ b_list :=
              List.mem_cons.mpr (Or.inr (List.mem_append.mpr (Or.inr h_β'_in_5)))
            have h_b_to_β' := I.listConjImpliesElem b_list β' h_β'_in_b
            have h_γ'_in_c := l27s_c5_γ_mem I h_φ_eq hβ' hγ'
            have h_ev_untl_γ' := h_ev_untl γ' h_γ'_in_c
            have h_bχ_to_β'xi : I.Deriv [] (I.imp (I.and b χ_gen) (I.and β' xi)) := by
              have h1 := I.impTrans (I.lceImp b χ_gen) h_b_to_β'
              have h2 : I.Deriv [] (I.imp (I.and b χ_gen) xi) :=
                I.impTrans (I.rceImp b χ_gen) (I.lceImp xi (I.snce xi eta))
              exact I.combineImpConj h1 h2
            have h_left := I.untlLeftMonoDeriv (I.and b χ_gen) γ'
              (I.and β' xi) h_bχ_to_β'xi
            have h_chain := I.impTrans h_ev_untl_γ' h_left
            exact I.modusPonens
              (I.weakening [] _ _ h_chain (List.nil_subset _))
              (I.assumption (by exact List.mem_singleton.mpr rfl))
          · exfalso
            simp only [lemma27SinceSeed, Set.mem_union, Set.mem_ofPred_eq,
              Set.mem_singleton_iff] at h_φ_seed
            rcases h_φ_seed with ((h1 | h2) | h5)
            · exact h_B_case h1
            · exact h_eta_case h2
            · exact h_comp5 h5
    have d_event : I.Deriv [event] I.bot :=
      I.derivationFromImplied [event] L I.bot h_event_implies_L d
    have h_event_cons := I.consistentOfPMem h_mcs_C event h_P_event
    exact I.inconsistentSingletonFalse h_event_cons d_event
  -- Prove h_key: BX5'+BX7'+BX13' chain with D1/D2 eliminated via α'
  intro b hb α_hat hα h_α_to_α' gamma_list h_gammas
  have h_snce_ba : I.snce b α_hat ∈ C := h_r3.2 b hb α_hat hα
  have h_bx5_ba := I.selfAccumSinceMcs h_mcs_C b α_hat h_snce_ba
  let φ_gen := I.and b (I.snce b α_hat)
  let χ_gen := I.and xi (I.snce xi eta)
  have h_bx7_gen := I.linearSinceMcs h_mcs_C φ_gen α_hat χ_gen eta h_bx5_ba h_bx5_xe
  have h_D3_gen : I.snce (I.and φ_gen χ_gen) (I.and φ_gen eta) ∈ C := by
    rcases h_bx7_gen with h_D1 | h_D2 | h_D3
    · exfalso
      have h_event_to_bot : I.Deriv [] (I.imp (I.and α_hat eta) I.bot) := by
        have h1 : I.Deriv [] (I.imp (I.and α_hat eta) (I.imp eta I.bot)) :=
          I.impTrans (I.lceImp α_hat eta) (I.impTrans h_α_to_α' h_α'_to_neg_eta)
        have h2 : I.Deriv [] _ := I.rceImp α_hat eta
        let PConj := I.and α_hat eta
        have d1 : I.Deriv [PConj] (I.imp eta I.bot) := I.modusPonens
          (I.weakening [] _ _ h1 (List.nil_subset _))
          (I.assumption (φ := PConj) (by simp))
        have d2 : I.Deriv [PConj] eta := I.modusPonens
          (I.weakening [] _ _ h2 (List.nil_subset _))
          (I.assumption (φ := PConj) (by simp))
        exact I.deductionTheorem [] PConj I.bot (I.modusPonens d1 d2)
      have h_P_bot := I.pMonoMcs h_mcs_C h_event_to_bot (I.sinceImpliesP h_mcs_C h_D1)
      have h_H_top : I.allPast (I.imp I.bot I.bot) ∈ C :=
        I.theoremInMcs h_mcs_C (I.pastNecessitation _ (I.identity' I.bot))
      exact I.somePastAllPastNegAbsurd h_mcs_C I.bot h_P_bot h_H_top
    · exfalso
      have h_event_to_bot : I.Deriv [] (I.imp (I.and α_hat χ_gen) I.bot) := by
        have h1 : I.Deriv [] (I.imp (I.and α_hat χ_gen) (I.imp χ_gen I.bot)) :=
          I.impTrans (I.lceImp α_hat χ_gen) (I.impTrans h_α_to_α' h_α'_to_neg_chi)
        have h2 : I.Deriv [] _ := I.rceImp α_hat χ_gen
        let PConj := I.and α_hat χ_gen
        have d1 : I.Deriv [PConj] (I.imp χ_gen I.bot) := I.modusPonens
          (I.weakening [] _ _ h1 (List.nil_subset _))
          (I.assumption (φ := PConj) (by simp))
        have d2 : I.Deriv [PConj] χ_gen := I.modusPonens
          (I.weakening [] _ _ h2 (List.nil_subset _))
          (I.assumption (φ := PConj) (by simp))
        exact I.deductionTheorem [] PConj I.bot (I.modusPonens d1 d2)
      have h_P_bot := I.pMonoMcs h_mcs_C h_event_to_bot (I.sinceImpliesP h_mcs_C h_D2)
      have h_H_top : I.allPast (I.imp I.bot I.bot) ∈ C :=
        I.theoremInMcs h_mcs_C (I.pastNecessitation _ (I.identity' I.bot))
      exact I.somePastAllPastNegAbsurd h_mcs_C I.bot h_P_bot h_H_top
    · exact h_D3
  let guard := I.and φ_gen χ_gen
  let base_event := I.and φ_gen eta
  let evt := I.iteratedEnrichmentSince h_mcs_C guard gamma_list h_gammas base_event h_D3_gen
  let event := evt.1
  have h_P_event : I.somePast event ∈ C := I.sinceImpliesP h_mcs_C evt.2.1
  have h_ev_base := evt.2.2.1
  have h_ev_b : I.Deriv [] (I.imp event b) :=
    I.impTrans h_ev_base (I.impTrans (I.lceImp φ_gen eta) (I.lceImp b (I.snce b α_hat)))
  have h_ev_eta : I.Deriv [] (I.imp event eta) :=
    I.impTrans h_ev_base (I.rceImp φ_gen eta)
  have h_ev_snce_ba : I.Deriv [] (I.imp event (I.snce b α_hat)) :=
    I.impTrans h_ev_base (I.impTrans (I.lceImp φ_gen eta) (I.rceImp b (I.snce b α_hat)))
  have h_ev_untl : ∀ γ ∈ gamma_list,
      I.Deriv [] (I.imp event (I.untl (I.and b χ_gen) γ)) := by
    intro γ hγ
    have h_untl_guard := evt.2.2.2 γ hγ
    have h_guard_to_bχ : I.Deriv [] (I.imp guard (I.and b χ_gen)) := by
      have h1 : I.Deriv [] _ := I.impTrans (I.lceImp φ_gen χ_gen) (I.lceImp b (I.snce b α_hat))
      have h2 : I.Deriv [] _ := I.rceImp φ_gen χ_gen
      exact I.combineImpConj h1 h2
    exact I.impTrans h_untl_guard (I.untlLeftMonoDeriv guard γ (I.and b χ_gen) h_guard_to_bχ)
  exact ⟨event, h_P_event, h_ev_b, h_ev_eta, h_ev_snce_ba, h_ev_untl⟩

/-- **Lemma 2.8 (Since direction)**, generic over `I`: given `BurgessR3Maximal(A, B, C)`
with `snce(xi, eta) ∈ C` and `¬(eta ∨ (xi ∧ snce(xi, eta))) ∈ A`, construct MCS `D` with
`eta ∈ D` splitting the R3 pair. -/
theorem lemma_2_8_since {A B C : Set F}
    (h_mcs_A : SetMaximalConsistent I A)
    (h_mcs_C : SetMaximalConsistent I C)
    (h_r3m : BurgessR3Maximal I A B C)
    (h_B_dcs : ClosedUnderDerivation I B)
    (h_gc : gContent I A ⊆ C)
    (xi eta : F)
    (h_since : I.snce xi eta ∈ C)
    (h_neg_disj : I.imp (I.or eta (I.and xi (I.snce xi eta))) I.bot ∈ A) :
    ∃ B' D B'' : Set F,
      BurgessR3Maximal I A B' D ∧
      BurgessR3Maximal I D B'' C ∧
      SetMaximalConsistent I D ∧
      eta ∈ D ∧
      B ⊆ D ∧
      B ⊆ B' ∧
      B ⊆ B'' ∧
      xi ∈ B'' := by
  have h_seed_cons := lemma_2_8_since_seed_consistent I h_mcs_A h_mcs_C h_r3m h_B_dcs h_gc
    xi eta h_since h_neg_disj
  obtain ⟨D, h_sup, h_D_mcs⟩ := I.lindenbaum h_seed_cons
  have h_eta_D : eta ∈ D := by
    apply h_sup; show eta ∈ lemma27SinceSeed I A B C xi eta
    simp [lemma27SinceSeed]
  have h_B_sub_D : B ⊆ D := by
    intro φ hφ; apply h_sup
    show φ ∈ lemma27SinceSeed I A B C xi eta; simp [lemma27SinceSeed, hφ]
  have h_untl_D : ∀ β ∈ B, ∀ γ ∈ C, I.untl β γ ∈ D := by
    intro β hβ γ hγ
    exact h_B_sub_D (I.xuLemma321Until h_mcs_A h_mcs_C h_r3m hβ hγ)
  have h_snce_D : ∀ β ∈ B, ∀ α ∈ A, I.snce β α ∈ D := by
    intro β hβ α hα
    exact h_B_sub_D (I.xuLemma321Since h_mcs_A h_mcs_C h_r3m hβ hα)
  have h_rSet_D : burgessRSet I D B C := fun β hβ γ hγ => h_untl_D β hβ γ hγ
  have h_rSetSince_D : burgessRSetSince I C B D := by
    intro β hβ
    exact I.burgessRImpliesBurgessRSince h_D_mcs h_mcs_C (h_rSet_D β hβ)
  have h_r3_DBC : burgessR3 I D B C := ⟨h_rSet_D, h_rSetSince_D⟩
  have h_rSetSince_A : burgessRSetSince I D B A := fun β hβ α hα => h_snce_D β hβ α hα
  have h_rSet_A : burgessRSet I A B D := by
    intro β hβ
    exact I.burgessRSinceImpliesBurgessR h_mcs_A h_D_mcs (h_rSetSince_A β hβ)
  have h_r3_ABD : burgessR3 I A B D := ⟨h_rSet_A, h_rSetSince_A⟩
  have h_untl_conj_xi_D : ∀ β ∈ B, ∀ γ ∈ C, I.untl (I.and β xi) γ ∈ D := by
    intro β hβ γ hγ; apply h_sup
    show I.untl (I.and β xi) γ ∈ lemma27SinceSeed I A B C xi eta
    simp only [lemma27SinceSeed, Set.mem_union, Set.mem_ofPred_eq]
    right; exact ⟨β, hβ, γ, hγ, rfl⟩
  have h_B_nonempty : ∃ β₀ : F, β₀ ∈ B := by
    exact ⟨I.imp I.bot I.bot, I.cudContainsTheorems h_r3m.1 (I.identity' I.bot)⟩
  obtain ⟨β₀, hβ₀⟩ := h_B_nonempty
  have h_untl_xi_D : ∀ γ ∈ C, I.untl xi γ ∈ D := by
    intro γ hγ
    exact I.untlLeftMonoThm h_D_mcs (I.rceImp β₀ xi) (h_untl_conj_xi_D β₀ hβ₀ γ hγ)
  have h_burgessR_xi : burgessR I D xi C := h_untl_xi_D
  have h_burgessRSince_xi : burgessRSince I C xi D :=
    I.burgessRImpliesBurgessRSince h_D_mcs h_mcs_C h_burgessR_xi
  have h_snce_conj_xi_C : ∀ β ∈ B, ∀ δ ∈ D, I.snce (I.and β xi) δ ∈ C := by
    intro β hβ δ hδ
    exact (I.burgessRSinceConj h_mcs_C (h_rSetSince_D β hβ) h_burgessRSince_xi) δ hδ
  have h_r3_DC_DBC : burgessR3 I D (deductiveClosure I ({xi} ∪ B)) C :=
    I.dcDeltaBBurgessR3 h_D_mcs h_mcs_C h_B_dcs h_r3_DBC h_untl_conj_xi_D h_snce_conj_xi_C
  have h_DC_cud : ClosedUnderDerivation I (deductiveClosure I ({xi} ∪ B)) :=
    deductiveClosureClosedUnderDerivation I _
  obtain ⟨B', h_B_sub_B', h_B'_max⟩ := I.burgessR3MaximalExtensionExists h_mcs_A h_D_mcs
    h_B_dcs h_r3_ABD
  obtain ⟨B'', h_DC_sub_B'', h_B''_max⟩ := I.burgessR3MaximalExtensionExists h_D_mcs h_mcs_C
    h_DC_cud h_r3_DC_DBC
  have h_B_sub_DC : B ⊆ deductiveClosure I ({xi} ∪ B) :=
    fun φ hφ => subsetDeductiveClosure I _ (Set.mem_union_right _ hφ)
  have h_B_sub_B'' : B ⊆ B'' := Set.Subset.trans h_B_sub_DC h_DC_sub_B''
  have h_xi_in_DC : xi ∈ deductiveClosure I ({xi} ∪ B) :=
    subsetDeductiveClosure I _ (Set.mem_union_left _ (Set.mem_singleton xi))
  have h_xi_in_B'' : xi ∈ B'' := h_DC_sub_B'' h_xi_in_DC
  exact ⟨B', D, B'', h_B'_max, h_B''_max, h_D_mcs, h_eta_D, h_B_sub_D, h_B_sub_B',
    h_B_sub_B'', h_xi_in_B''⟩

end Cslib.Logic.Metalogic.Chronicle
