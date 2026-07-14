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

## Task 507 Phase 5 Confirmation: the Crux Needs No Further Field

`modalStepBranch_potential_step_gen`'s own body (`FmpMeasure.lean`), once its helper lemmas are
generalized via `freshLocal`/`rankStep`/`outDegStep`/`knownWorldsStep`, needs no field beyond
`freshLocal` -- the crux's arithmetic core (`geomCap_zero`/`geomCap_succ`/`Nat`/`ring`) is
entirely independent of `apply`. This confirms the six fields above are **sufficient** for the
termination-measure crux.

## Task 507 Phase 7: `branchingLength` (Counting-Measure Engine)

The strict-decrease engine `modalExpMeasure_step_lt` needs one further per-call fact its
`.branching` case relies on that is not covered by any of the six fields above: every
`.branching` result `apply` can produce has **exactly two** sub-branches (`brs.length = 2`).
This is genuinely catalog-specific (only the 3 branching propositional rules
`andNeg`/`orPos`/`impPos` ever produce `.branching`, and each is hard-coded to a 2-element
list) -- unlike `freshLocal`/`outputsSubsetUniverse`/`persistentFresh`, it is not a fact about
*aggregate* behaviour but a fixed-arity shape constraint. Discharged for `modalApplyOne` by the
pre-existing `modalApplyOne_branching_length`.
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
  /-- Branching arity (task 507 Phase 7): every `.branching` result `apply sf b acc` can
  produce has exactly two sub-branches. Needed by the counting-measure engine
  `modalExpMeasure_step_lt`'s `.branching` case. Mirrors `modalApplyOne_branching_length`. -/
  branchingLength : ∀ (sf : SignedFormula (Proposition Atom) WorldIndex)
      (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
      (brs : List (List (SignedFormula (Proposition Atom) WorldIndex))),
      (apply sf b acc).fst = .branching brs → brs.length = 2

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

/-! ## Task 507 Phase 4: Generic knownWorlds/accTargetsKnown/eClosure (spec-bundled) -/

/-- **Task 507 Phase 4**: `modalStepBranchGen apply` preserves `accTargetsKnown`, bundled via
`RuleApplicationSpec` (thin wrapper around `modalStepBranch_preserves_accTargetsKnown_gen`,
`FmpMeasure.lean`, which takes the raw `freshLocal` hypothesis directly to avoid the import
cycle documented in the plan's "Architectural Note"). -/
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

/-- **Task 507 Phase 4**: the known-worlds/max-world dichotomy for a single
`modalStepBranchGen apply` step, bundled via `RuleApplicationSpec` (thin wrapper around
`modalStepBranch_knownWorlds_gen`, `FmpMeasure.lean`, which takes the raw `knownWorldsStep`
hypothesis directly to avoid the import cycle documented in the plan's "Architectural Note"). -/
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

/-- **Task 507 Phase 4**: the expanded set's `modalUniverse` closure is preserved across a
`modalStepBranchGen apply` step, bundled via `RuleApplicationSpec` (thin wrapper around
`modalStepBranch_eClosure_gen`, `FmpMeasure.lean`, which needs no `spec` field at all -- see its
docstring). -/
theorem modalStepBranchGen_eClosure
    (apply : RuleApply Atom) (spec : RuleApplicationSpec apply)
    (φ0 : Proposition Atom)
    (b e : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (newBs newExps : List (List (SignedFormula (Proposition Atom) WorldIndex)))
    (newAcc : Accessibility)
    (hstep : modalStepBranchGen apply b e acc = some (newBs, newExps, newAcc))
    (hb : ∀ x ∈ b, x ∈ modalUniverse φ0)
    (heclosure : ∀ x ∈ e, x ∈ modalUniverse φ0) :
    ∀ e' ∈ newExps, ∀ x ∈ e', x ∈ modalUniverse φ0 :=
  modalStepBranch_eClosure_gen apply φ0 b e acc newBs newExps newAcc hstep hb heclosure

/-! ## Task 507 Phase 5: Generic Potential-Step Crux (spec-bundled) -/

/-- **Task 507 Phase 5 (the crux, spec-bundled)**: the exact single-step potential-drop identity
for `modalStepBranchGen apply`, bundled via `RuleApplicationSpec` (thin wrapper around
`modalStepBranch_potential_step_gen`, `FmpMeasure.lean`, which takes the four raw hypotheses
`freshLocal`/`rankStep`/`outDegStep`/`knownWorldsStep` directly to avoid the import cycle
documented in the plan's "Architectural Note"). This is the crux confirmation for the whole
task: `RuleApplicationSpec`'s three original fields plus the three Phase-1 per-call step fields
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

/-! ## Task 507 Phase 6: Generic World-Bound Preservation (spec-bundled) -/

/-- **Task 507 Phase 6**: the a-priori world bound `modalWorldBound φ0` is preserved as a loop
invariant of `modalStepBranchGen apply`, bundled via `RuleApplicationSpec` (thin wrapper around
`modalStepBranch_worldBound_gen`, `FmpMeasure.lean`, which takes the four raw hypotheses
directly to avoid the import cycle documented in the plan's "Architectural Note"). -/
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

/-! ## Task 507 Phase 7: Generic Counting-Measure Engine (spec-bundled) -/

/-- **Task 507 Phase 7**: one `modalStepBranchGen apply` step strictly decreases the base-3
damped worklist measure by at least one, bundled via `RuleApplicationSpec` (thin wrapper around
`modalExpMeasure_step_lt_gen`, `FmpMeasure.lean`, which takes the three raw hypotheses
`branchingLength`/`persistentFresh`/`outputsSubsetUniverse` directly to avoid the import cycle
documented in the plan's "Architectural Note"). -/
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
  modalExpMeasure_step_lt_gen apply spec.branchingLength spec.persistentFresh
    spec.outputsSubsetUniverse φ0 done bt newBs doneExp es newExp bh e acc newAcc hdlen hb hInv hW
    hstep

end Cslib.Logic.Modal.Tableau

end
