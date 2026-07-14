/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

import Cslib.Init
public import Cslib.Logics.Modal.Tableau.FmpMeasure

/-! # Structural-Hypothesis Interface for the Generic Tableau Driver

This module defines `RuleApplicationSpec`, the explicit bundle of structural hypotheses a
rule-application function `apply : RuleApply Atom` (see `Saturation.lean`) must satisfy to reuse
the K-style FMP termination measure (`modalUniverse`/`modalWork`/`modalExpMeasure`/`modalFuel`,
`FmpMeasure.lean`) with the generic driver `modalStepBranchGen`/`modalExpandBranchesGen`/
`modalTableauGen` (`Saturation.lean`).

## Main Definitions

- `RuleApplicationSpec apply`: the structural-hypothesis bundle.
- `modalApplyOne_spec`: `modalApplyOne` (K) trivially satisfies the bundle.

## Design

The field set is extracted from what `FmpMeasure.lean`'s `modalStepBranch_potential_step`
(the termination-measure crux) and its supporting lemmas actually use about `modalApplyOne`:

1. **`freshLocal`** (world-creation confinement): `apply sf b acc` either leaves `acc`
   unchanged, or adds exactly one edge from `sf`'s own world to a single fresh witness world,
   with a `.linear` result headed by that witness. This is the exact dichotomy
   `modalStepBranch_knownWorlds`/`modalStepBranch_exists_rank'` case-split on, mirroring the
   local restatement `modalApplyOne_fresh_local`.
2. **`outputsSubsetUniverse`** (catalog membership): every formula `apply` can emit (across all
   four `RuleResult` shapes) stays inside the finite universe `modalUniverse φ0`, given the
   branch/source/freshness/world-bound hypotheses `modalApplyOne_outputs_subset` needs. This is
   what the potential-step lemma's closure obligations (`ModalPotentialInv.bClosure`/`eClosure`
   propagation) consume at every step.
3. **`persistentFresh`** (persistence hook): whenever `apply` produces a `.persistent` result,
   the emitted formulas are nonempty and fresh (not already on the branch). This drives the
   counting-measure strict-decrease argument `modalWork_drop_persistent` needs, mirroring
   `modalApplyOne_persistent_props`.

## Downstream Reuse (tasks 504, 505; not 506)

- **T** (this task, `TDriver.lean`): `modalApplyOneT` agrees with `modalApplyOne` outside the
  box-positive/diamond-negative self-propagation shapes
  (`modalApplyOneT_eq_of_not_boxPos_diaNeg`, `FrameRules.lean`), and those two shapes only add
  formulas at **existing** worlds drawn from the (possibly closure-enlarged) universe -- so
  `freshLocal` is discharged by agreement with `modalApplyOne` on every mint-shaped input, and
  `outputsSubsetUniverse`/`persistentFresh` are discharged by the same agreement plus the T
  rules' own catalog-membership facts.
- **S5 / KB5** (task 504, universal rule): the universal rule only adds formulas at existing
  worlds (drawn from the finite catalog, since it propagates along `EqvGen`-closed pairs of
  labels already on the branch); it never mints a world itself, so `freshLocal` is discharged
  trivially (agreement with `modalApplyOne` on every mint-shaped input) and
  `outputsSubsetUniverse`/`persistentFresh` follow the same shape as T's discharge.
- **B** (task 505, backward/symmetric rule): the backward rule only adds formulas at existing
  worlds reachable via the symmetric closure `SymmGen` of already-recorded edges; likewise never
  mints a world, so the same discharge pattern as S5 applies.
- **S4 is explicitly NOT an instance** (task 506): transitive box propagation requires
  loop-checking (`#worlds ≤ 2^|Sf|`) rather than the depth-based `modalWorldBound` this bundle
  presupposes via `outputsSubsetUniverse`'s reliance on `modalApplyOne_outputs_subset`-style
  world-bound hypotheses; S4 needs a structurally different termination argument.

## Task 507: Per-Call Step Fields (`rankStep`/`outDegStep`/`knownWorldsStep`)

The three fields above restate *conclusions* about `apply`'s aggregate behaviour
(freshness/catalog-membership/persistence), but three of `FmpMeasure.lean`'s private helper
lemmas (`modalStepBranch_exists_rank'`, `modalStepBranch_preserves_outDegEq`,
`modalStepBranch_knownWorlds`) additionally need a **per-single-call** structural fact that
genuinely depends on which of `modalApplyOne`'s five internal rule shapes
(propositional/boxPos/diamondNeg/diamondPos/boxNeg) fired -- not merely on the four top-level
`RuleResult` constructor shapes (`.linear`/`.branching`/`.persistent`/`.notApplicable`), which
*are* rule-agnostic and need no interface support. Task 507 adds exactly these three fields:

- **`rankStep`**: given a `rank` map satisfying the depth-bound/edge invariants pre-call, `apply`
  produces a `rank'` (agreeing with `rank` off `modalNextWorld b`) satisfying both invariants on
  `(apply sf b acc).snd`/`.fst`. Discharged for `modalApplyOne` by `modalApplyOne_rank_step`
  (`FmpMeasure.lean`), whose body is the exact proof that was formerly inlined inside
  `modalStepBranch_exists_rank'`.
- **`outDegStep`**: given the outDeg/expanded-set counting correspondence pre-call, `apply`
  preserves it on `(apply sf b acc).snd`/`.fst`. Discharged by `modalApplyOne_outDeg_step`.
- **`knownWorldsStep`**: the known-worlds dichotomy for a single call -- either `apply` leaves
  `acc` unchanged with all output labels already known, or it mints exactly one edge
  `sf.label → modalNextWorld b` with a nonempty `.linear` result entirely labeled at the fresh
  point. Discharged by `modalApplyOne_knownWorlds_step`.

Each field's *statement* is rule-agnostic (parametrized over `apply`); each field's *discharge*
for `modalApplyOne` reuses the pre-existing K-specific proof verbatim (now a standalone lemma).
This is the intended shape of downstream (T/S5/B) discharge too: reuse `modalApplyOne`'s own
per-call facts on every input where the new rule agrees with `modalApplyOne` (per the
`freshLocal` docstring above), and supply fresh reasoning only where the new rule's own catalog
(box propagation to existing successors, etc.) differs.

## Known Limitation (documented for Phase 5 continuation)

This bundle is **necessary but not yet proven sufficient** to re-derive
`modalStepBranch_potential_step` (`FmpMeasure.lean:2146`) for an abstract `apply`: the crux
lemma's own body (once its helper lemmas are generalized via the six fields above) is expected
to need no further field beyond `freshLocal`, but this is confirmed only once
`modalStepBranch_potential_step` itself is re-derived generically (task 507 Phase 5). If a
future continuation finds the six fields above insufficient, extend this bundle (do not weaken
`modalApplyOne_spec`'s proof with `sorry`).
-/

@[expose] public section

namespace Cslib.Logic.Modal.Tableau

open Cslib.Logic.Tableau

variable {Atom : Type*} [DecidableEq Atom] [Hashable Atom]

/-! ## The Structural-Hypothesis Bundle -/

/-- The structural-hypothesis bundle a rule-application function `apply` (matching
`modalApplyOne`'s signature, see `RuleApply`) must satisfy to reuse the K-style FMP termination
measure with the generic tableau driver. See the module docstring for the provenance of each
field and the downstream-reuse contract for tasks 504 (S5/KB5), 505 (B), and 506 (S4, explicitly
excluded). -/
structure RuleApplicationSpec (apply : RuleApply Atom) : Prop where
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
  /-- Per-call rank-step (task 507): given `rank` satisfying the depth-bound/edge invariants
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
  /-- Per-call outDeg-step (task 507): given the outDeg/expanded-set minting-count
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
  /-- Per-call knownWorlds-step (task 507): either `apply sf b acc` leaves `acc` unchanged with
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

/-! ## Task 507 Phase 2: Generic outDeg-Preservation (spec-bundled) -/

/-- **Task 507 Phase 2**: `modalStepBranchGen apply` preserves the out-degree/expanded-set
correspondence, bundled via `RuleApplicationSpec` (thin wrapper around
`modalStepBranch_preserves_outDegEq_gen`, `FmpMeasure.lean`, which takes the raw `outDegStep`
hypothesis directly to avoid the import cycle documented in the plan's "Architectural Note"). -/
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

/-! ## Task 507 Phase 3: Generic Rank-Existence (spec-bundled) -/

/-- **Task 507 Phase 3**: given `rank` satisfying the rank-bound/rank-edge invariants pre-step,
`modalStepBranchGen apply` produces a `rank'` satisfying both invariants on every child branch,
bundled via `RuleApplicationSpec` (thin wrapper around `modalStepBranch_exists_rank'_gen`,
`FmpMeasure.lean`, which takes the raw `rankStep` hypothesis directly to avoid the import cycle
documented in the plan's "Architectural Note"). -/
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

end Cslib.Logic.Modal.Tableau

end
