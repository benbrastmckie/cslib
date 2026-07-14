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

## Known Limitation (documented for Phase 3 continuation)

This bundle is **necessary but not yet proven sufficient** to re-derive
`modalStepBranch_potential_step` (`FmpMeasure.lean:2146`) for an abstract `apply`: that proof
additionally inlines case-specific facts from ~15 private helper lemmas
(`modalStepBranch_exists_rank'`, `modalStepBranch_knownWorlds`,
`modalStepBranch_preserves_outDegEq`, `outDeg_le_of_expandedNodup`, ...) that case-split
directly on `modalApplyOne`'s four concrete rule shapes rather than going through a
`RuleApplicationSpec` hypothesis. Generalizing that ~900-line potential-function argument
(`FmpMeasure.lean` lines ~1058–2415) over this interface is task 503 Phase 3, tracked
separately; if a future continuation finds the three fields above insufficient, extend this
bundle (do not weaken `modalApplyOne_spec`'s proof with `sorry`).
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

/-! ## The Trivial K Witness -/

/-- `modalApplyOne` (K) trivially satisfies `RuleApplicationSpec`: each field is exactly an
existing K lemma applied at `apply := modalApplyOne`. This is the K re-derivation's interface
witness -- the base case every downstream instantiation (T, S5, B) is compared against. -/
theorem modalApplyOne_spec : RuleApplicationSpec (Atom := Atom) modalApplyOne where
  freshLocal := modalApplyOne_fresh_local
  outputsSubsetUniverse := fun φ0 sf b acc hb hsf hInv hW =>
    modalApplyOne_outputs_subset φ0 sf b acc hb hsf hInv hW
  persistentFresh := fun sf b acc nf hca => modalApplyOne_persistent_props sf b acc nf hca

end Cslib.Logic.Modal.Tableau

end
