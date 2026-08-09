/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Modal.Tableau.FmpMeasure

/-! # Structural-Hypothesis Interface for the Generic Tableau Driver

This module defines `RuleApplicationSpec`, the explicit bundle of structural hypotheses a
rule-application function `apply : RuleApply Atom` (see `Saturation.lean`) must satisfy to reuse
the K-style FMP termination measure (`modalUniverse`/`modalWork`/`modalExpMeasure`/`modalFuel`,
`FmpMeasure.lean`) with the generic driver `modalStepBranchGen`/`modalExpandBranchesGen`/
`modalTableauGen` (`Saturation.lean`).

## Main Definitions

- `RuleApplicationSpec apply`: the structural-hypothesis bundle (eleven fields, see below --
  seven from the termination-lemma generalization, four more, F9-F12, from the
  Hintikka/saturation generalization).
- `RuleApplicationSpecAt φ0 apply`/`RuleApplicationSpecCoreAt φ0 apply`: additive siblings of
  `RuleApplicationSpec`/`RuleApplicationSpecCore` that narrow `outputsSubsetUniverse` from
  `∀ φ0, …` to a single structure-parametric `φ0`, for rules (e.g. D, `DDriver.lean`) whose
  outputs are only universe-closed at one dual-closed seed, not at an arbitrary universe.
  `RuleApplicationSpec.toAt`/`RuleApplicationSpecCore.toAt` project any existing witness down to
  this narrower interface at an arbitrary `φ0`, for free.
- `modalApplyOne_spec`: `modalApplyOne` (K) trivially satisfies the bundle.
- `modalStepBranchGen_preserves_outDegEq`/`_exists_rank'`/`_preserves_accTargetsKnown`/
  `_knownWorlds`/`_eClosure`/`_potential_step`/`_worldBound`/`_expMeasure_step_lt`: the
  `(apply, spec)`-bundled wrappers around `FmpMeasure.lean`'s `_gen` lemmas, available for
  downstream (T/S5/B) reuse.

## Sufficiency (the Hintikka/Saturation Chain Generalized)

This extends the bundle from seven to eleven fields to generalize the Hintikka-set/
saturation-characterisation chain (`Completeness.lean`/`CompletenessLoop.lean`) over `apply`:

8. **`localShapeInvariance`** (F8): branch-independence on non-box/non-diamond shapes. Forces the
   Hintikka-clause lift lemma. Mirrors `modalApplyOne_fst_eq_of_not_box` (`Completeness.lean`).
9. **`boxPosNotExpanding`** (F9): a box-positive shaped input's result is always `.notApplicable`
   or `.persistent` (**existentially-quantified payload** -- see the field's own docstring for why
   this is load-bearing for T/B/S5). Mirrors `modalApplyOne_boxPos_eq` (`Rules.lean`).
10. **`diaNegNotExpanding`** (F10): dual of F9 for diamond-negative shapes. Mirrors
    `modalApplyOne_diamondNeg_eq` (`Rules.lean`).
11. **`boxNegWitness`**/**`diaPosWitness`** (F11/F12): the two fresh-world-minting rules always
    apply and produce a specific witness/edge shape. Mirrors `modalApplyOne_boxNeg_witness`/
    `_diamondPos_witness` (`Rules.lean`).

`modalHintikkaSetGen` (`Saturation.lean`) is the corresponding generic saturation predicate --
itself **spec-free** (no field dependency), so S4 (excluded below from discharging this spec) can
still consume its statement shape.

## Sufficiency (All Three K Termination Lemmas Generalized)

The generic driver and this file's three original fields
(`freshLocal`/`outputsSubsetUniverse`/`persistentFresh`) were delivered first, sufficient to
*state* the three K
termination lemmas (`modalStepBranch_potential_step`/`_worldBound`, `modalExpMeasure_step_lt`)
generically but not to *replay their proofs* -- roughly fifteen private helper lemmas in
`FmpMeasure.lean` additionally `rcases` directly on `modalApplyOne`'s five internal rule shapes
(propositional/boxPos/diamondNeg/diamondPos/boxNeg), not merely on the four top-level
`RuleResult` constructor shapes (which *are* rule-agnostic and need no interface support). Four
further fields close this gap, and **all three termination lemmas are now
proven generically** (`FmpMeasure.lean`'s `_gen` lemmas), confirmed sorry-free/axiom-free and
CI-clean at every step:

1. **`freshLocal`** (world-creation confinement): `apply sf b acc` either leaves `acc`
   unchanged, or adds exactly one edge from `sf`'s own world to a single fresh witness world,
   with a `.linear` result headed by that witness. Mirrors `modalApplyOne_fresh_local`.
2. **`outputsSubsetUniverse`** (catalog membership): every formula `apply` can emit (across all
   four `RuleResult` shapes) stays inside the finite universe `modalUniverse φ0`, given the
   branch/source/freshness/world-bound hypotheses `modalApplyOne_outputs_subset` needs. Mirrors
   `modalApplyOne_outputs_subset`.
3. **`persistentFresh`** (persistence hook): whenever `apply` produces a `.persistent` result,
   the emitted formulas are nonempty and fresh (not already on the branch). Mirrors
   `modalApplyOne_persistent_props`.
4. **`rankStep`**: given a `rank` map satisfying the depth-bound/edge
   invariants pre-call, `apply` produces a `rank'` (agreeing with `rank` off `modalNextWorld b`)
   satisfying both invariants on `(apply sf b acc).snd`/`.fst`. Needed by
   `modalStepBranch_exists_rank'_gen`. Discharged by `modalApplyOne_rank_step`, whose body matches
   the corresponding proof in `modalStepBranch_exists_rank'`.
5. **`outDegStep`**: given the outDeg/expanded-set counting correspondence
   pre-call, `apply` preserves it on `(apply sf b acc).snd`/`.fst`. Needed by
   `modalStepBranch_preserves_outDegEq_gen`. Discharged by `modalApplyOne_outDeg_step`.
6. **`knownWorldsStep`**: the known-worlds dichotomy for a single call --
   either `apply` leaves `acc` unchanged with all output labels already known, or it mints
   exactly one edge `sf.label → modalNextWorld b` with a nonempty `.linear` result entirely
   labeled at the fresh point. Needed by `modalStepBranch_knownWorlds_gen`. Discharged by
   `modalApplyOne_knownWorlds_step`.
7. **`branchingLength`**: every `.branching` result `apply` can produce has
   exactly two sub-branches. A fixed-arity catalog fact (not an aggregate-behaviour fact like
   the other six), needed by `modalExpMeasure_step_lt_gen`'s `.branching` case. Discharged by
   `modalApplyOne_branching_length`.

Fields 1-3 restate *conclusions* about `apply`'s aggregate behaviour; fields 4-6 are
**per-single-call** structural facts (needed because ~15 helper lemmas case-split on
`modalApplyOne`'s five internal rule shapes, not just the four `RuleResult` constructors); field
7 is a fixed-arity shape constraint. Each field's *statement* is rule-agnostic (parametrized over
`apply`); each field's *discharge* for `modalApplyOne` reuses the pre-existing K-specific proof
verbatim (as a standalone lemma in `FmpMeasure.lean`). The crux `modalStepBranch_potential_step`
itself needs no field beyond `freshLocal` once its three callees (rank/outDeg/knownWorlds) are
generalized -- its arithmetic core (`geomCap_zero`/`geomCap_succ`/`Nat`/`ring`) is entirely
independent of `apply`.

**Architectural note**: `FmpMeasure.lean`'s `_gen` lemmas take these seven facts as *raw,
unbundled hypothesis parameters* rather than a `spec : RuleApplicationSpec apply` argument,
because `RuleApplicationSpec` is defined in *this* file, which imports `FmpMeasure.lean` --
bundling would create an import cycle. This file supplies the `(apply, spec)`-bundled wrapper
theorems (listed under Main Definitions) that unpack `spec.field` into each `_gen` lemma's raw
parameters, giving downstream instances (T/S5/B) the ergonomic `(apply, spec)` calling
convention this design specifies.

## Downstream Reuse

- **T** (`TDriver.lean`): `modalApplyOneT` agrees with `modalApplyOne` outside the
  box-positive/diamond-negative self-propagation shapes
  (`modalApplyOneT_eq_of_not_boxPos_diaNeg`, `FrameRules.lean`), and those two shapes only add
  formulas at **existing** worlds drawn from the (possibly closure-enlarged) universe -- so
  `freshLocal` is discharged by agreement with `modalApplyOne` on every mint-shaped input, and
  the remaining six fields are discharged by the same agreement plus T's own catalog-membership
  facts (its own propositional/box-propagation-to-existing-successors reasoning).
- **S5 / KB5** (universal rule): the universal rule only adds formulas at existing
  worlds (drawn from the finite catalog, since it propagates along `EqvGen`-closed pairs of
  labels already on the branch); it never mints a world itself, so `freshLocal` is discharged
  trivially (agreement with `modalApplyOne` on every mint-shaped input) and the remaining fields
  follow the same shape as T's discharge.
- **B** (backward/symmetric rule): the backward rule only adds formulas at existing
  worlds reachable via the symmetric closure `SymmGen` of already-recorded edges; likewise never
  mints a world, so the same discharge pattern as S5 applies.
- **S4 is explicitly NOT an instance**: transitive box propagation requires
  loop-checking (`#worlds ≤ 2^|Sf|`) rather than the depth-based `modalWorldBound` this bundle
  presupposes via `outputsSubsetUniverse`'s reliance on `modalApplyOne_outputs_subset`-style
  world-bound hypotheses; S4 needs a structurally different termination argument.

## Completeness and Soundness Are Both Generic Over `(apply, spec)`

The completeness-side Hintikka/saturation chain is fully generic over `(apply, spec)`:
`modalExpandBranchesGen_hintikka` (`CompletenessLoop.lean`) is typed at the `φ0`-indexed
`RuleApplicationSpecAt φ0 apply` interface, so it turns any `RuleApplicationSpec apply` witness --
e.g. T's `modalApplyOneT_spec` (`TDriver.lean`) -- into a Hintikka-set-producing top-loop lemma
for free, one `.toAt φ0` step away (`RuleApplicationSpec.toAt`, below). The T-specific
completeness work (`hintikkaT_box_pos`/`hintikkaT_diamond_neg`, `modalTruthLemmaT`,
`modalTableauT_complete`, all in `FrameCompleteness.lean`) needed new content only at the two
shapes where T's rule differs from K's; the other two modal shapes reuse the free projection
bridges
`hintikka_box_neg_gen`/`hintikka_diamond_pos_gen` (`Completeness.lean`).

The soundness side is likewise generic, via the frame-relativized chain in `FrameSoundness.lean`:
`branchSatisfiableIn FC` and `frameValid FC` generalize `branchSatisfiable`/`kValid` with an
explicit frame-condition predicate `FC`, and `modalStepBranchGen_preserves_satIn` /
`modalExpandBranchesGen_closed_unsatIn` are the `(apply, spec)`-parametric fuel-induction
soundness arguments (the ambient Kripke model is never replaced; only the world-assignment `f`
is pointwise redefined at the minting rules, so an `FC m.r` witness threads through unchanged).
`modalTableau_sound_frame` re-derives K soundness through this vocabulary to confirm the K arms
port unchanged. Each per-system tableau supplies its own `hAgree`/`hBoxPos`/`hDiaNeg` triple and
instantiates the generic chain -- see `modalTableauT_sound`, `modalTableauB_sound`,
`modalTableauS5_sound`, `modalTableauFive_sound` in `FrameCompleteness.lean`/`FrameSoundness.lean`.

Consequently the decision procedures are all delivered: `instDecidableTValid`,
`instDecidableBValid`, `instDecidableS5Valid`, `instDecidableFiveValid`, and
`instDecidableKb5Valid` (all in `FrameCompleteness.lean`), alongside K's `instDecidableKValid`
(`CompletenessLoop.lean`).
-/

@[expose] public section

namespace Cslib.Logic.Modal.Tableau

open Cslib.Logic.Tableau

variable {Atom : Type*} [DecidableEq Atom] [Hashable Atom]

/-! ## The Structural-Hypothesis Bundle -/

/-- **Core bundle** (the Hintikka/saturation-forcing fields, F1-F3 + F7-F12): the subset of
`RuleApplicationSpec`'s fields that `CompletenessLoop.lean`'s generic Hintikka-set machinery
actually consumes -- no `rankStep`, no `outDegStep`, no `knownWorldsStep`. Split out so a rule
that cannot discharge the termination-measure fields (S5's witness-reuse rule
`modalApplyOneS5w`, `S5Simplification.lean`) can still supply everything the *completeness* side
needs. The two witness fields (`boxNegWitness'`/`diaPosWitness'`) are existentially quantified on
the witness world -- weaker than `RuleApplicationSpec`'s eventual concrete-`modalNextWorld b`
form -- exactly what lets a witness-reuse rule (which may redirect the edge to an arbitrary
already-known world, not the fresh mint point) discharge them. -/
structure RuleApplicationSpecCore (apply : RuleApply Atom) : Prop where
  /-- World-creation confinement: `apply sf b acc` either leaves `acc` unchanged, or adds
  exactly one edge from `sf`'s own world to a fresh witness world, with a `.linear` result
  headed by that witness. No other accessibility change or result shape may accompany a new
  edge. Mirrors `modalApplyOne_fresh_local`. -/
  freshLocal : ∀ (sf : SignedFormula (Proposition Atom) WorldIndex)
      (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility),
      (apply sf b acc).snd = acc ∨
      (∃ wsf rest, (apply sf b acc).fst = RuleResult.linear (wsf :: rest) ∧
        (apply sf b acc).snd = acc.addEdge sf.label wsf.label)
  /-- Catalog membership: every formula `apply sf b acc` can emit (across all four `RuleResult`
  shapes) stays inside the finite universe `modalUniverse φ0`, given that `sf` is a branch
  formula drawn from `b ⊆ modalUniverse φ0`, the freshness invariant `accFreshInv b acc`, and
  the world-bound hypothesis `modalMaxWorld b < modalWorldBound φ0`. Mirrors
  `modalApplyOne_outputs_subset`. -/
  outputsSubsetUniverse : ∀ (φ0 : Proposition Atom)
      (sf : SignedFormula (Proposition Atom) WorldIndex)
      (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility),
      (∀ x ∈ b, x ∈ modalUniverse φ0) → sf ∈ b → accFreshInv b acc →
      modalMaxWorld b < modalWorldBound φ0 →
      (match (apply sf b acc).fst with
        | .linear formulas => ∀ x ∈ formulas, x ∈ modalUniverse φ0
        | .branching branches => ∀ x ∈ branches.flatten, x ∈ modalUniverse φ0
        | .persistent formulas => ∀ x ∈ formulas, x ∈ modalUniverse φ0
        | .notApplicable => True)
  /-- Persistence hook: whenever `apply sf b acc` produces a `.persistent` result, the emitted
  formulas are nonempty and fresh (none already on `b`). Drives the counting-measure
  strict-decrease argument (`modalWork_drop_persistent`). Mirrors
  `modalApplyOne_persistent_props`. -/
  persistentFresh : ∀ (sf : SignedFormula (Proposition Atom) WorldIndex)
      (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
      (nf : List (SignedFormula (Proposition Atom) WorldIndex)),
      (apply sf b acc).fst = .persistent nf → nf ≠ [] ∧ ∀ x ∈ nf, x ∉ b
  /-- Branching arity: every `.branching` result `apply sf b acc` can
  produce has exactly two sub-branches. Needed by the counting-measure engine
  `modalExpMeasure_step_lt`'s `.branching` case. Mirrors `modalApplyOne_branching_length`. -/
  branchingLength : ∀ (sf : SignedFormula (Proposition Atom) WorldIndex)
      (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
      (brs : List (List (SignedFormula (Proposition Atom) WorldIndex))),
      (apply sf b acc).fst = .branching brs → brs.length = 2
  /-- **F8** Branch-independence on structural shapes: for a signed formula whose
  formula-component is neither `box`- nor `diamond`-shaped, `apply`'s rule result does not
  depend on the branch or the accessibility relation. Forces `modalHintikkaClauseGen_lift`
  (and, through it, `modalStepBranchGen_hintikka_inv`), which lifts the expanded-set Hintikka
  invariant from the old branch to each strictly larger child branch. Mirrors
  `modalApplyOne_fst_eq_of_not_box` (`Completeness.lean`). -/
  localShapeInvariance : ∀ (s : Sign) (φ : Proposition Atom) (w : WorldIndex),
      (∀ ψ, φ ≠ .box ψ) → (∀ ψ, φ ≠ .diamond ψ) →
      ∀ (b b' : List (SignedFormula (Proposition Atom) WorldIndex))
        (acc acc' : Accessibility),
      (apply ⟨s, φ, w⟩ b acc).1 = (apply ⟨s, φ, w⟩ b' acc').1
  /-- **F9** Box-positive is never expanding: `apply`'s result on a `T(□ψ)@w`-shaped
  input is always `.notApplicable` or `.persistent` -- never `.linear`/`.branching`. Since
  `.persistent` leaves the expanded set unchanged (`modalStepBranchGen`, `Saturation.lean`),
  this is what makes `modalLoopGen_eBoxOnlyNeg` go through: a `boxPos`-shaped formula can never
  be the `sf_exp` appended to `e`. **The payload is existentially quantified on purpose**: every
  use site discards it (it serves only to contradict the `.linear`/`.branching` case split), and
  quantifying it is exactly what lets T's self-conjunct, B's symmetric propagation, and S5's
  universal propagation discharge this field. Mirrors `modalApplyOne_boxPos_eq` (`Rules.lean`),
  weakened from its concrete `boxPropagation` payload. -/
  boxPosNotExpanding : ∀ (sf : SignedFormula (Proposition Atom) WorldIndex),
      sf.sign = .pos → ∀ (ψ : Proposition Atom), sf.formula = .box ψ →
      ∀ (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility),
      (apply sf b acc).1 = .notApplicable ∨
        ∃ out, (apply sf b acc).1 = .persistent out
  /-- **F10** Diamond-negative is never expanding: dual of `boxPosNotExpanding`,
  forcing `modalLoopGen_eDiamondOnlyPos`. Mirrors `modalApplyOne_diamondNeg_eq` (`Rules.lean`),
  likewise payload-weakened. -/
  diaNegNotExpanding : ∀ (sf : SignedFormula (Proposition Atom) WorldIndex),
      sf.sign = .neg → ∀ (ψ : Proposition Atom), sf.formula = .diamond ψ →
      ∀ (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility),
      (apply sf b acc).1 = .notApplicable ∨
        ∃ out, (apply sf b acc).1 = .persistent out
  /-- **F11'** Box-negative witness minting/reuse, existentially quantified
  on the witness world: `apply` on `F(□ψ)@w` is *always* applicable, adds the edge
  `w → w'` for **some** world `w'`, and heads its `.linear` output with the witness
  `F(ψ)@w'`. Weaker than the eventual `RuleApplicationSpec.boxNegWitness` (which fixes
  `w' := modalNextWorld b`, the fresh mint point) -- this existential form is exactly what a
  witness-*reuse* rule (which may redirect the edge to an already-known world) can discharge.
  Mirrors `modalApplyOne_boxNeg_witness` (`Rules.lean`), further weakened from `boxNegWitness`. -/
  boxNegWitness' : ∀ (b : List (SignedFormula (Proposition Atom) WorldIndex))
      (acc : Accessibility) (ψ : Proposition Atom) (w : WorldIndex),
      ∃ w', (apply (⟨.neg, .box ψ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) b acc).snd
          = acc.addEdge w w' ∧
      ∃ rest,
        (apply (⟨.neg, .box ψ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) b acc).fst
          = RuleResult.linear
              ((⟨.neg, ψ, w'⟩ : SignedFormula (Proposition Atom) WorldIndex) :: rest)
  /-- **F12'** Diamond-positive witness minting/reuse: dual of
  `boxNegWitness'`. Mirrors `modalApplyOne_diamondPos_witness` (`Rules.lean`), further weakened
  from `diaPosWitness`. -/
  diaPosWitness' : ∀ (b : List (SignedFormula (Proposition Atom) WorldIndex))
      (acc : Accessibility) (ψ : Proposition Atom) (w : WorldIndex),
      ∃ w', (apply (⟨.pos, .diamond ψ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) b acc).snd
          = acc.addEdge w w' ∧
      ∃ rest,
        (apply (⟨.pos, .diamond ψ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) b acc).fst
          = RuleResult.linear
              ((⟨.pos, ψ, w'⟩ : SignedFormula (Proposition Atom) WorldIndex) :: rest)

/-- The structural-hypothesis bundle a rule-application function `apply` (matching
`modalApplyOne`'s signature, see `RuleApply`) must satisfy to reuse the K-style FMP termination
measure with the generic tableau driver. See the module docstring for the provenance of each
field and the downstream-reuse contract for S5/KB5, B, and S4 (explicitly
excluded). Extends `RuleApplicationSpecCore` with the three fields (`rankStep`/`outDegStep`/
`knownWorldsStep`) the K-style FMP *termination-measure* argument needs but the *completeness*
side (`CompletenessLoop.lean`) does not -- see `RuleApplicationSpecCore`'s docstring. -/
structure RuleApplicationSpec (apply : RuleApply Atom) : Prop extends
    RuleApplicationSpecCore apply where
  /-- Per-call rank-step: given `rank` satisfying the depth-bound/edge invariants
  pre-call, `apply sf b acc` yields a `rank'` (agreeing with `rank` off `modalNextWorld b`)
  satisfying the edge invariant on `(apply sf b acc).snd` and the depth bound on
  `(apply sf b acc).fst`'s output. Mirrors `modalApplyOne_rank_step`. -/
  rankStep : ∀ (sf : SignedFormula (Proposition Atom) WorldIndex)
      (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility),
      sf ∈ b → accFreshInv b acc →
      ∀ (rank : WorldIndex → Nat),
      (∀ x ∈ b, modalDepth x.formula ≤ rank x.label) →
      (∀ w w', acc.hasEdge w w' → rank w' + 1 = rank w) →
      ∃ rank' : WorldIndex → Nat,
        (∀ w, w ≠ modalNextWorld b → rank' w = rank w) ∧
        (∀ w w', (apply sf b acc).snd.hasEdge w w' → rank' w' + 1 = rank' w) ∧
        (match (apply sf b acc).fst with
          | .linear formulas => ∀ x ∈ formulas, modalDepth x.formula ≤ rank' x.label
          | .branching branches => ∀ x ∈ branches.flatten, modalDepth x.formula ≤ rank' x.label
          | .persistent formulas => ∀ x ∈ formulas, modalDepth x.formula ≤ rank' x.label
          | .notApplicable => True)
  /-- Per-call outDeg-step: given the outDeg/expanded-set minting-count
  correspondence pre-call, `apply sf b acc` preserves it on `(apply sf b acc).snd`, counted
  against the post-call expanded set implied by `(apply sf b acc).fst`'s shape. Mirrors
  `modalApplyOne_outDeg_step`. -/
  outDegStep : ∀ (sf : SignedFormula (Proposition Atom) WorldIndex)
      (b e : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility),
      (∀ w, outDeg acc w = (e.filter (fun x => x.label == w && isMintingShaped x)).length) →
      ∀ w, outDeg (apply sf b acc).snd w =
        (List.filter (fun x => x.label == w && isMintingShaped x)
          (match (apply sf b acc).fst with
            | .linear _ => e ++ [sf]
            | .branching _ => e ++ [sf]
            | .persistent _ => e
            | .notApplicable => (e : List (SignedFormula (Proposition Atom) WorldIndex)))).length
  /-- Per-call knownWorlds-step: either `apply sf b acc` leaves `acc` unchanged with
  every output label already known on `b`, or it mints exactly one edge
  `sf.label → modalNextWorld b` with a nonempty `.linear` result entirely labeled at the fresh
  point. Mirrors `modalApplyOne_knownWorlds_step`. -/
  knownWorldsStep : ∀ (sf : SignedFormula (Proposition Atom) WorldIndex)
      (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility),
      sf ∈ b → accTargetsKnown b acc →
      ((apply sf b acc).snd = acc ∧
        (match (apply sf b acc).fst with
          | .linear formulas => ∀ x ∈ formulas, x.label ∈ modalKnownWorlds b
          | .branching branches => ∀ x ∈ branches.flatten, x.label ∈ modalKnownWorlds b
          | .persistent formulas => ∀ x ∈ formulas, x.label ∈ modalKnownWorlds b
          | .notApplicable => True)) ∨
      ((apply sf b acc).snd = acc.addEdge sf.label (modalNextWorld b) ∧
        (match (apply sf b acc).fst with
          | .linear formulas => formulas ≠ [] ∧ ∀ x ∈ formulas, x.label = modalNextWorld b
          | .branching _ => False
          | .persistent _ => False
          | .notApplicable => False))

/-- The Core-projection theorem: every `RuleApplicationSpec` witness is, in particular, a
`RuleApplicationSpecCore` witness (immediate from `extends`; named for readability at call
sites and to give downstream consumers a stable API independent of the `extends`-generated
projection name). -/
theorem RuleApplicationSpec.toCore {apply : RuleApply Atom} (spec : RuleApplicationSpec apply) :
    RuleApplicationSpecCore apply :=
  spec.toRuleApplicationSpecCore

/-! ## The Additive `…At` Sibling: Universe Fixed at a Single `φ0`

`RuleApplicationSpecCoreAt`/`RuleApplicationSpecAt` narrow `outputsSubsetUniverse` from
`∀ φ0, …` to a single, structure-parametric `φ0`. This is the interface D's rule
(`modalApplyOneD`, `FrameRules.lean`) actually satisfies: its dual arms escape `modalUniverse
φ0` for a *plain* `φ0` (`modalApplyOneD_outputsSubsetUniverse_fails`, `DDriver.lean`), but do
stay inside the dual-closed universe `modalUniverse (modalDualAugment φ0)` at that one fixed
`φ0` (`DDriver.lean`). Every other field is identical to `RuleApplicationSpecCore`/
`RuleApplicationSpec` -- only `outputsSubsetUniverse`'s universal quantifier over `φ0` is
narrowed to the structure's own parameter.

`RuleApplicationSpecCore.toAt`/`RuleApplicationSpec.toAt` project any (universally-quantified)
existing witness down to this narrower interface at an arbitrary `φ0`, so every existing
instance (K/T/B/TB/Five/Kb5''/S5w) can supply a `…At` witness for free without re-proving
anything. This narrowing is purely additive: `RuleApplicationSpec`/`RuleApplicationSpecCore`
themselves, and all seven of `RuleApplicationSpec`'s existing discharge sites, are untouched.
`CompletenessLoop.lean`'s top-loop Hintikka chain, however, has since been narrowed to consume
this `…At` interface directly (its nine declarations are now typed at `RuleApplicationSpecCoreAt
φ0`/`RuleApplicationSpecAt φ0`, not the universal originals), so its T/B/TB/S5/Five/Kb5''
call sites now go through `.toAt φ0` rather than the universal spec directly -- unblocking D's
otherwise-only-`…At`-satisfiable `modalApplyOneD` from reusing the same chain. -/

/-- Core-projection of `RuleApplicationSpecCore`, universe fixed at a single `φ0`: identical to
`RuleApplicationSpecCore` except `outputsSubsetUniverse` is stated only at the structure's own
`φ0` rather than universally quantified over it. See the section docstring above for the
motivating example (D's rule). -/
structure RuleApplicationSpecCoreAt (φ0 : Proposition Atom) (apply : RuleApply Atom) : Prop where
  /-- World-creation confinement, identical to `RuleApplicationSpecCore.freshLocal`. -/
  freshLocal : ∀ (sf : SignedFormula (Proposition Atom) WorldIndex)
      (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility),
      (apply sf b acc).snd = acc ∨
      (∃ wsf rest, (apply sf b acc).fst = RuleResult.linear (wsf :: rest) ∧
        (apply sf b acc).snd = acc.addEdge sf.label wsf.label)
  /-- Catalog membership, narrowed to the structure's own fixed `φ0` rather than universally
  quantified -- the one field this sibling exists to weaken. -/
  outputsSubsetUniverse : ∀ (sf : SignedFormula (Proposition Atom) WorldIndex)
      (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility),
      (∀ x ∈ b, x ∈ modalUniverse φ0) → sf ∈ b → accFreshInv b acc →
      modalMaxWorld b < modalWorldBound φ0 →
      (match (apply sf b acc).fst with
        | .linear formulas => ∀ x ∈ formulas, x ∈ modalUniverse φ0
        | .branching branches => ∀ x ∈ branches.flatten, x ∈ modalUniverse φ0
        | .persistent formulas => ∀ x ∈ formulas, x ∈ modalUniverse φ0
        | .notApplicable => True)
  /-- Persistence hook, identical to `RuleApplicationSpecCore.persistentFresh`. -/
  persistentFresh : ∀ (sf : SignedFormula (Proposition Atom) WorldIndex)
      (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
      (nf : List (SignedFormula (Proposition Atom) WorldIndex)),
      (apply sf b acc).fst = .persistent nf → nf ≠ [] ∧ ∀ x ∈ nf, x ∉ b
  /-- Branching arity, identical to `RuleApplicationSpecCore.branchingLength`. -/
  branchingLength : ∀ (sf : SignedFormula (Proposition Atom) WorldIndex)
      (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
      (brs : List (List (SignedFormula (Proposition Atom) WorldIndex))),
      (apply sf b acc).fst = .branching brs → brs.length = 2
  /-- **F8**, identical to `RuleApplicationSpecCore.localShapeInvariance`. -/
  localShapeInvariance : ∀ (s : Sign) (φ : Proposition Atom) (w : WorldIndex),
      (∀ ψ, φ ≠ .box ψ) → (∀ ψ, φ ≠ .diamond ψ) →
      ∀ (b b' : List (SignedFormula (Proposition Atom) WorldIndex))
        (acc acc' : Accessibility),
      (apply ⟨s, φ, w⟩ b acc).1 = (apply ⟨s, φ, w⟩ b' acc').1
  /-- **F9**, identical to `RuleApplicationSpecCore.boxPosNotExpanding`. -/
  boxPosNotExpanding : ∀ (sf : SignedFormula (Proposition Atom) WorldIndex),
      sf.sign = .pos → ∀ (ψ : Proposition Atom), sf.formula = .box ψ →
      ∀ (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility),
      (apply sf b acc).1 = .notApplicable ∨
        ∃ out, (apply sf b acc).1 = .persistent out
  /-- **F10**, identical to `RuleApplicationSpecCore.diaNegNotExpanding`. -/
  diaNegNotExpanding : ∀ (sf : SignedFormula (Proposition Atom) WorldIndex),
      sf.sign = .neg → ∀ (ψ : Proposition Atom), sf.formula = .diamond ψ →
      ∀ (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility),
      (apply sf b acc).1 = .notApplicable ∨
        ∃ out, (apply sf b acc).1 = .persistent out
  /-- **F11'**, identical to `RuleApplicationSpecCore.boxNegWitness'`. -/
  boxNegWitness' : ∀ (b : List (SignedFormula (Proposition Atom) WorldIndex))
      (acc : Accessibility) (ψ : Proposition Atom) (w : WorldIndex),
      ∃ w', (apply (⟨.neg, .box ψ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) b acc).snd
          = acc.addEdge w w' ∧
      ∃ rest,
        (apply (⟨.neg, .box ψ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) b acc).fst
          = RuleResult.linear
              ((⟨.neg, ψ, w'⟩ : SignedFormula (Proposition Atom) WorldIndex) :: rest)
  /-- **F12'**, identical to `RuleApplicationSpecCore.diaPosWitness'`. -/
  diaPosWitness' : ∀ (b : List (SignedFormula (Proposition Atom) WorldIndex))
      (acc : Accessibility) (ψ : Proposition Atom) (w : WorldIndex),
      ∃ w', (apply (⟨.pos, .diamond ψ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) b acc).snd
          = acc.addEdge w w' ∧
      ∃ rest,
        (apply (⟨.pos, .diamond ψ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) b acc).fst
          = RuleResult.linear
              ((⟨.pos, ψ, w'⟩ : SignedFormula (Proposition Atom) WorldIndex) :: rest)

/-- Universe-fixed sibling of `RuleApplicationSpec`: identical except `outputsSubsetUniverse` is
stated only at the structure's own `φ0`. See the section docstring above for the motivating
example (D's rule) and `RuleApplicationSpecCoreAt` for the narrowed field. -/
structure RuleApplicationSpecAt (φ0 : Proposition Atom) (apply : RuleApply Atom) : Prop extends
    RuleApplicationSpecCoreAt φ0 apply where
  /-- Per-call rank-step, identical to `RuleApplicationSpec.rankStep`. -/
  rankStep : ∀ (sf : SignedFormula (Proposition Atom) WorldIndex)
      (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility),
      sf ∈ b → accFreshInv b acc →
      ∀ (rank : WorldIndex → Nat),
      (∀ x ∈ b, modalDepth x.formula ≤ rank x.label) →
      (∀ w w', acc.hasEdge w w' → rank w' + 1 = rank w) →
      ∃ rank' : WorldIndex → Nat,
        (∀ w, w ≠ modalNextWorld b → rank' w = rank w) ∧
        (∀ w w', (apply sf b acc).snd.hasEdge w w' → rank' w' + 1 = rank' w) ∧
        (match (apply sf b acc).fst with
          | .linear formulas => ∀ x ∈ formulas, modalDepth x.formula ≤ rank' x.label
          | .branching branches => ∀ x ∈ branches.flatten, modalDepth x.formula ≤ rank' x.label
          | .persistent formulas => ∀ x ∈ formulas, modalDepth x.formula ≤ rank' x.label
          | .notApplicable => True)
  /-- Per-call outDeg-step, identical to `RuleApplicationSpec.outDegStep`. -/
  outDegStep : ∀ (sf : SignedFormula (Proposition Atom) WorldIndex)
      (b e : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility),
      (∀ w, outDeg acc w = (e.filter (fun x => x.label == w && isMintingShaped x)).length) →
      ∀ w, outDeg (apply sf b acc).snd w =
        (List.filter (fun x => x.label == w && isMintingShaped x)
          (match (apply sf b acc).fst with
            | .linear _ => e ++ [sf]
            | .branching _ => e ++ [sf]
            | .persistent _ => e
            | .notApplicable => (e : List (SignedFormula (Proposition Atom) WorldIndex)))).length
  /-- Per-call knownWorlds-step, identical to `RuleApplicationSpec.knownWorldsStep`. -/
  knownWorldsStep : ∀ (sf : SignedFormula (Proposition Atom) WorldIndex)
      (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility),
      sf ∈ b → accTargetsKnown b acc →
      ((apply sf b acc).snd = acc ∧
        (match (apply sf b acc).fst with
          | .linear formulas => ∀ x ∈ formulas, x.label ∈ modalKnownWorlds b
          | .branching branches => ∀ x ∈ branches.flatten, x.label ∈ modalKnownWorlds b
          | .persistent formulas => ∀ x ∈ formulas, x.label ∈ modalKnownWorlds b
          | .notApplicable => True)) ∨
      ((apply sf b acc).snd = acc.addEdge sf.label (modalNextWorld b) ∧
        (match (apply sf b acc).fst with
          | .linear formulas => formulas ≠ [] ∧ ∀ x ∈ formulas, x.label = modalNextWorld b
          | .branching _ => False
          | .persistent _ => False
          | .notApplicable => False))

/-- The Core-projection theorem for the `…At` sibling, analogous to `RuleApplicationSpec.toCore`. -/
theorem RuleApplicationSpecAt.toCore {φ0 : Proposition Atom} {apply : RuleApply Atom}
    (spec : RuleApplicationSpecAt φ0 apply) : RuleApplicationSpecCoreAt φ0 apply :=
  spec.toRuleApplicationSpecCoreAt

/-- Every `RuleApplicationSpecCore` witness (universally quantified over `φ0`) projects down to
a `RuleApplicationSpecCoreAt` witness at an arbitrary fixed `φ0`, by specializing
`outputsSubsetUniverse` and reusing every other field unchanged. -/
theorem RuleApplicationSpecCore.toAt {apply : RuleApply Atom}
    (spec : RuleApplicationSpecCore apply)
    (φ0 : Proposition Atom) : RuleApplicationSpecCoreAt φ0 apply where
  freshLocal := spec.freshLocal
  outputsSubsetUniverse := spec.outputsSubsetUniverse φ0
  persistentFresh := spec.persistentFresh
  branchingLength := spec.branchingLength
  localShapeInvariance := spec.localShapeInvariance
  boxPosNotExpanding := spec.boxPosNotExpanding
  diaNegNotExpanding := spec.diaNegNotExpanding
  boxNegWitness' := spec.boxNegWitness'
  diaPosWitness' := spec.diaPosWitness'

/-- Every `RuleApplicationSpec` witness (universally quantified over `φ0`) projects down to a
`RuleApplicationSpecAt` witness at an arbitrary fixed `φ0`, by specializing
`outputsSubsetUniverse` (via `RuleApplicationSpecCore.toAt`) and reusing every other field
unchanged. This is the projection that lets D (`DDriver.lean`) reuse the generic driver without
requiring any existing `RuleApplicationSpec` instance to be re-proved. -/
theorem RuleApplicationSpec.toAt {apply : RuleApply Atom} (spec : RuleApplicationSpec apply)
    (φ0 : Proposition Atom) : RuleApplicationSpecAt φ0 apply where
  toRuleApplicationSpecCoreAt := spec.toCore.toAt φ0
  rankStep := spec.rankStep
  outDegStep := spec.outDegStep
  knownWorldsStep := spec.knownWorldsStep

/-! ## The Trivial K Witness -/

/-- `modalApplyOne` (K) trivially satisfies `RuleApplicationSpec`: each field is exactly an
existing K lemma applied at `apply := modalApplyOne`. This is the K re-derivation's interface
witness -- the base case every downstream instantiation (T, S5, B) is compared against. -/
theorem modalApplyOne_spec : RuleApplicationSpec (Atom := Atom) modalApplyOne where
  freshLocal := modalApplyOne_fresh_local
  outputsSubsetUniverse := fun φ0 sf b acc hb hsf hInv hW =>
    modalApplyOne_outputs_subset φ0 sf b acc hb hsf hInv hW
  persistentFresh := fun sf b acc nf hca => modalApplyOne_persistent_props sf b acc nf hca
  rankStep := fun sf b acc hsfmem hInv rank hbound hedge =>
    modalApplyOne_rank_step sf b acc hsfmem hInv rank hbound hedge
  outDegStep := fun sf b e acc houtdeg => modalApplyOne_outDeg_step sf b e acc houtdeg
  knownWorldsStep := fun sf b acc hsfmem hknown =>
    modalApplyOne_knownWorlds_step sf b acc hsfmem hknown
  branchingLength := fun sf b acc brs hca => modalApplyOne_branching_length sf b acc brs hca
  localShapeInvariance := fun s φ w hnb hnd b b' acc acc' =>
    modalApplyOne_fst_eq_of_not_box s φ w hnb hnd b b' acc acc'
  boxPosNotExpanding := fun sf hsign ψ hform b acc =>
    modalApplyOne_boxPos_eq sf hsign ψ hform b acc
  diaNegNotExpanding := fun sf hsign ψ hform b acc =>
    modalApplyOne_diamondNeg_eq sf hsign ψ hform b acc
  boxNegWitness' := fun b acc ψ w =>
    ⟨modalNextWorld b, (modalApplyOne_boxNeg_witness b acc ψ w).1,
      (modalApplyOne_boxNeg_witness b acc ψ w).2⟩
  diaPosWitness' := fun b acc ψ w =>
    ⟨modalNextWorld b, (modalApplyOne_diamondPos_witness b acc ψ w).1,
      (modalApplyOne_diamondPos_witness b acc ψ w).2⟩

/-! ## Generic outDeg-Preservation (spec-bundled) -/

/-- **Generic form**: `modalStepBranchGen apply` preserves the out-degree/expanded-set
correspondence, bundled via `RuleApplicationSpec` (thin wrapper around
`modalStepBranch_preserves_outDegEq_gen`, `FmpMeasure.lean`, which takes the raw `outDegStep`
hypothesis directly to avoid the import cycle documented in the module docstring's
"Architectural note"). -/
theorem modalStepBranchGen_preserves_outDegEq
    (apply : RuleApply Atom) (spec : RuleApplicationSpec apply)
    (b e : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (newBs newExps : List (List (SignedFormula (Proposition Atom) WorldIndex)))
    (newAcc : Accessibility)
    (hstep : modalStepBranchGen apply b e acc = some (newBs, newExps, newAcc))
    (houtdeg : ∀ w, outDeg acc w =
      (e.filter (fun x => x.label == w && isMintingShaped x)).length) :
    ∀ e' ∈ newExps, ∀ w, outDeg newAcc w =
      (e'.filter (fun x => x.label == w && isMintingShaped x)).length :=
  modalStepBranch_preserves_outDegEq_gen apply spec.outDegStep
    b e acc newBs newExps newAcc hstep houtdeg

/-! ## Generic Rank-Existence (spec-bundled) -/

/-- **Generic form**: given `rank` satisfying the rank-bound/rank-edge invariants pre-step,
`modalStepBranchGen apply` produces a `rank'` satisfying both invariants on every child branch,
bundled via `RuleApplicationSpec` (thin wrapper around `modalStepBranch_exists_rank'_gen`,
`FmpMeasure.lean`, which takes the raw `rankStep` hypothesis directly to avoid the import cycle
documented in the module docstring's "Architectural note"). -/
theorem modalStepBranchGen_exists_rank'
    (apply : RuleApply Atom) (spec : RuleApplicationSpec apply)
    (b e : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (newBs newExps : List (List (SignedFormula (Proposition Atom) WorldIndex)))
    (newAcc : Accessibility)
    (hstep : modalStepBranchGen apply b e acc = some (newBs, newExps, newAcc))
    (hInv : accFreshInv b acc)
    (rank : WorldIndex → Nat)
    (hbound : ∀ x ∈ b, modalDepth x.formula ≤ rank x.label)
    (hedge : ∀ w w', acc.hasEdge w w' → rank w' + 1 = rank w) :
    ∃ rank' : WorldIndex → Nat,
      (∀ w, w ≠ modalNextWorld b → rank' w = rank w) ∧
      (∀ b' ∈ newBs, ∀ x ∈ b', modalDepth x.formula ≤ rank' x.label) ∧
      (∀ w w', newAcc.hasEdge w w' → rank' w' + 1 = rank' w) :=
  modalStepBranch_exists_rank'_gen apply spec.rankStep
    b e acc newBs newExps newAcc hstep hInv rank hbound hedge

/-! ## Generic knownWorlds/accTargetsKnown/eClosure (spec-bundled) -/

/-- **Generic form**: `modalStepBranchGen apply` preserves `accTargetsKnown`, bundled via
`RuleApplicationSpec` (thin wrapper around `modalStepBranch_preserves_accTargetsKnown_gen`,
`FmpMeasure.lean`, which takes the raw `freshLocal` hypothesis directly to avoid the import
cycle documented in the module docstring's "Architectural note"). -/
theorem modalStepBranchGen_preserves_accTargetsKnown
    (apply : RuleApply Atom) (spec : RuleApplicationSpec apply)
    (b e : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (newBs newExps : List (List (SignedFormula (Proposition Atom) WorldIndex)))
    (newAcc : Accessibility)
    (hstep : modalStepBranchGen apply b e acc = some (newBs, newExps, newAcc))
    (hknown : accTargetsKnown b acc) :
    ∀ b' ∈ newBs, accTargetsKnown b' newAcc :=
  modalStepBranch_preserves_accTargetsKnown_gen apply spec.freshLocal
    b e acc newBs newExps newAcc hstep hknown

/-- **Generic form**: the known-worlds/max-world dichotomy for a single
`modalStepBranchGen apply` step, bundled via `RuleApplicationSpec` (thin wrapper around
`modalStepBranch_knownWorlds_gen`, `FmpMeasure.lean`, which takes the raw `knownWorldsStep`
hypothesis directly to avoid the import cycle documented in the module docstring's
"Architectural note"). -/
theorem modalStepBranchGen_knownWorlds
    (apply : RuleApply Atom) (spec : RuleApplicationSpec apply)
    (b e : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (newBs newExps : List (List (SignedFormula (Proposition Atom) WorldIndex)))
    (newAcc : Accessibility)
    (hstep : modalStepBranchGen apply b e acc = some (newBs, newExps, newAcc))
    (hknown : accTargetsKnown b acc) :
    (newAcc = acc ∧
      ∀ b' ∈ newBs, modalMaxWorld b' = modalMaxWorld b ∧
        (modalKnownWorlds b').Perm (modalKnownWorlds b)) ∨
    (∃ l ∈ modalKnownWorlds b, newAcc = acc.addEdge l (modalNextWorld b) ∧
      ∀ b' ∈ newBs, modalMaxWorld b' = modalNextWorld b ∧
        (modalKnownWorlds b').Perm (modalNextWorld b :: modalKnownWorlds b)) :=
  modalStepBranch_knownWorlds_gen apply spec.knownWorldsStep
    b e acc newBs newExps newAcc hstep hknown

/-- **Generic form**: the expanded set's `modalUniverse` closure is preserved across a
`modalStepBranchGen apply` step, bundled via `RuleApplicationSpec` (thin wrapper around
`modalStepBranch_eClosure_gen`, `FmpMeasure.lean`, which needs no `spec` field at all -- see its
docstring). -/
theorem modalStepBranchGen_eClosure
    (apply : RuleApply Atom) (_spec : RuleApplicationSpec apply)
    (φ0 : Proposition Atom)
    (b e : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (newBs newExps : List (List (SignedFormula (Proposition Atom) WorldIndex)))
    (newAcc : Accessibility)
    (hstep : modalStepBranchGen apply b e acc = some (newBs, newExps, newAcc))
    (hb : ∀ x ∈ b, x ∈ modalUniverse φ0)
    (heclosure : ∀ x ∈ e, x ∈ modalUniverse φ0) :
    ∀ e' ∈ newExps, ∀ x ∈ e', x ∈ modalUniverse φ0 :=
  modalStepBranch_eClosure_gen apply φ0 b e acc newBs newExps newAcc hstep hb heclosure

/-! ## Generic Potential-Step Crux (spec-bundled) -/

/-- **The crux (generic form, spec-bundled)**: the exact single-step potential-drop identity
for `modalStepBranchGen apply`, bundled via `RuleApplicationSpec` (thin wrapper around
`modalStepBranch_potential_step_gen`, `FmpMeasure.lean`, which takes the four raw hypotheses
`freshLocal`/`rankStep`/`outDegStep`/`knownWorldsStep` directly to avoid the import cycle
documented in the module docstring's "Architectural note"). This is the crux confirmation:
`RuleApplicationSpec`'s three original fields plus the three per-call step fields
are jointly **sufficient** to replay the EXACT `geomCap`-based potential-drop identity
generically -- no further field is needed. -/
theorem modalStepBranchGen_potential_step
    (apply : RuleApply Atom) (spec : RuleApplicationSpec apply)
    (φ0 : Proposition Atom)
    (b e : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (newBs newExps : List (List (SignedFormula (Proposition Atom) WorldIndex)))
    (newAcc : Accessibility) (rank : WorldIndex → Nat)
    (hstep : modalStepBranchGen apply b e acc = some (newBs, newExps, newAcc))
    (hinv : ModalPotentialInv φ0 b e acc rank) :
    ∃ rank' : WorldIndex → Nat,
      (∀ w, w ≠ modalNextWorld b → rank' w = rank w) ∧
      (∀ b' ∈ newBs, ∀ x ∈ b', modalDepth x.formula ≤ rank' x.label) ∧
      (∀ w w', newAcc.hasEdge w w' → rank' w' + 1 = rank' w) ∧
      (∀ b' ∈ newBs,
        modalMaxWorld b' + modalPotential (modalSubfmls φ0).length b' newAcc rank' =
          modalMaxWorld b + modalPotential (modalSubfmls φ0).length b acc rank) :=
  modalStepBranch_potential_step_gen apply spec.freshLocal spec.rankStep spec.outDegStep
    spec.knownWorldsStep φ0 b e acc newBs newExps newAcc rank hstep hinv

/-! ## Generic World-Bound Preservation (spec-bundled) -/

/-- **Generic form**: the a-priori world bound `modalWorldBound φ0` is preserved as a loop
invariant of `modalStepBranchGen apply`, bundled via `RuleApplicationSpec` (thin wrapper around
`modalStepBranch_worldBound_gen`, `FmpMeasure.lean`, which takes the four raw hypotheses
directly to avoid the import cycle documented in the module docstring's "Architectural note"). -/
theorem modalStepBranchGen_worldBound
    (apply : RuleApply Atom) (spec : RuleApplicationSpec apply)
    (φ0 : Proposition Atom)
    (b e : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (newBs newExps : List (List (SignedFormula (Proposition Atom) WorldIndex)))
    (newAcc : Accessibility) (rank : WorldIndex → Nat)
    (hstep : modalStepBranchGen apply b e acc = some (newBs, newExps, newAcc))
    (hinv : ModalPotentialInv φ0 b e acc rank)
    (hPhiBound : modalMaxWorld b + modalPotential (modalSubfmls φ0).length b acc rank + 1 ≤
      geomCap (modalSubfmls φ0).length (modalDepth φ0)) :
    ∀ b' ∈ newBs, modalMaxWorld b' < modalWorldBound φ0 :=
  modalStepBranch_worldBound_gen apply spec.freshLocal spec.rankStep spec.outDegStep
    spec.knownWorldsStep φ0 b e acc newBs newExps newAcc rank hstep hinv hPhiBound

/-! ## Generic Counting-Measure Engine (spec-bundled) -/

/-- **Generic form**: one `modalStepBranchGen apply` step strictly decreases the base-3
damped worklist measure by at least one, bundled via `RuleApplicationSpec` (thin wrapper around
`modalExpMeasure_step_lt_gen`, `FmpMeasure.lean`, which takes the three raw hypotheses
`branchingLength`/`persistentFresh`/`outputsSubsetUniverse` directly to avoid the import cycle
documented in the module docstring's "Architectural note"). -/
theorem modalStepBranchGen_expMeasure_step_lt
    (apply : RuleApply Atom) (spec : RuleApplicationSpec apply)
    (φ0 : Proposition Atom)
    (done bt newBs : List (List (SignedFormula (Proposition Atom) WorldIndex)))
    (doneExp es : List (List (SignedFormula (Proposition Atom) WorldIndex)))
    (newExp : List (SignedFormula (Proposition Atom) WorldIndex))
    (bh e : List (SignedFormula (Proposition Atom) WorldIndex))
    (acc newAcc : Accessibility)
    (hdlen : done.length = doneExp.length)
    (hb : ∀ x ∈ bh, x ∈ modalUniverse φ0)
    (hInv : accFreshInv bh acc)
    (hW : modalMaxWorld bh < modalWorldBound φ0)
    (hstep : modalStepBranchGen apply bh e acc = some (newBs, newBs.map (fun _ => newExp),
      newAcc)) :
    modalExpMeasure (modalUniverse φ0) (done ++ newBs ++ bt)
        (doneExp ++ newBs.map (fun _ => newExp) ++ es) + 1
      ≤ modalExpMeasure (modalUniverse φ0) (done ++ bh :: bt) (doneExp ++ e :: es) :=
  modalExpMeasure_step_lt_gen apply spec.branchingLength spec.persistentFresh φ0
    (spec.outputsSubsetUniverse φ0) done bt newBs doneExp es newExp bh e acc newAcc hdlen hb hInv
    hW hstep

/-- **`…At` sibling of `modalStepBranchGen_expMeasure_step_lt`**, taking `RuleApplicationSpecAt
φ0 apply` instead of `RuleApplicationSpec apply`: identical proof, except
`spec.outputsSubsetUniverse` is already stated at the fixed `φ0` (no explicit specialization
needed), which is exactly what lets a rule whose universe-closure only holds at one dual-closed
seed (D, `DDriver.lean`) reuse the counting-measure engine. -/
theorem modalStepBranchGenAt_expMeasure_step_lt
    {φ0 : Proposition Atom} (apply : RuleApply Atom) (spec : RuleApplicationSpecAt φ0 apply)
    (done bt newBs : List (List (SignedFormula (Proposition Atom) WorldIndex)))
    (doneExp es : List (List (SignedFormula (Proposition Atom) WorldIndex)))
    (newExp : List (SignedFormula (Proposition Atom) WorldIndex))
    (bh e : List (SignedFormula (Proposition Atom) WorldIndex))
    (acc newAcc : Accessibility)
    (hdlen : done.length = doneExp.length)
    (hb : ∀ x ∈ bh, x ∈ modalUniverse φ0)
    (hInv : accFreshInv bh acc)
    (hW : modalMaxWorld bh < modalWorldBound φ0)
    (hstep : modalStepBranchGen apply bh e acc = some (newBs, newBs.map (fun _ => newExp),
      newAcc)) :
    modalExpMeasure (modalUniverse φ0) (done ++ newBs ++ bt)
        (doneExp ++ newBs.map (fun _ => newExp) ++ es) + 1
      ≤ modalExpMeasure (modalUniverse φ0) (done ++ bh :: bt) (doneExp ++ e :: es) :=
  modalExpMeasure_step_lt_gen apply spec.branchingLength spec.persistentFresh φ0
    spec.outputsSubsetUniverse done bt newBs doneExp es newExp bh e acc newAcc hdlen hb hInv hW
    hstep

end Cslib.Logic.Modal.Tableau

end
