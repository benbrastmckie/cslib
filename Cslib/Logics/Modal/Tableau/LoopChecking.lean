/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

import Cslib.Init
import Mathlib.Tactic.Ring
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Prod
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Finset.Filter
public import Mathlib.Data.Finset.Dedup
public import Cslib.Logics.Modal.Tableau.FmpMeasure
public import Cslib.Logics.Modal.Tableau.FrameRules
public import Cslib.Logics.Modal.Tableau.S4.BirthKey
public import Cslib.Logics.Modal.Tableau.S4.Driver
public import Cslib.Logics.Modal.Tableau.S4.Guard
public import Cslib.Logics.Modal.Tableau.S4.Hintikka
public import Cslib.Logics.Modal.Tableau.S4.HintikkaInvariant
public import Cslib.Logics.Modal.Tableau.S4.Invariant
public import Cslib.Logics.Modal.Tableau.S4.InvariantAcc
public import Cslib.Logics.Modal.Tableau.S4.InvariantKeys
public import Cslib.Logics.Modal.Tableau.S4.Redirect -- shake: keep
public import Cslib.Logics.Modal.Tableau.S4.Universe
public import Cslib.Logics.Modal.Tableau.Support.Accessibility
public import Cslib.Logics.Modal.Tableau.Support.KnownWorlds

/-! # S4 Loop-Checking: Driver Entry Points, Termination Measure, and Barrel

This module is now a **`public import` barrel plus a 20-declaration residue**: the S4
(reflexive-transitive) modal tableau's driver entry points, its termination argument, and its
two end-to-end capstone theorems. The equality-blocking loop-checking machinery this file used
to hold directly -- universe/fuel bookkeeping, the birth-key guard, the rule-application driver,
the Hintikka-set construction, the blocked-redirect machinery, and the four-way `S4LoopInv`
invariant split -- was extracted into ten `S4/*.lean` modules (below), each along the
research-verified acyclic dependency layering. Every declaration that used to live here directly
is still reachable through this file's `public import`s: **no downstream file needed to change
its own imports** as a result of the split.

## The `S4/` module cluster, bottom-up

```
                       Universe
                          │
                      BirthKey
                          │
                        Guard
                          │
                        Driver
                     ╱    │    ╲
              Hintikka  InvariantKeys  InvariantAcc
                 │              ╲       ╱
              Redirect         Invariant
                 │                  │
                 │             HintikkaInvariant
                 ╲                 ╱
                  LoopChecking (this file: barrel + entry points)
```

- `S4/Universe.lean`: per-world relevant-formula-set extraction, the world-bound/fuel measures,
  and the signed-subformula universe.
- `S4/BirthKey.lean`: birth-content computation and the box-plus enrichment.
- `S4/Guard.lean`: the blocking-guard functions and the mint-shape predicate.
- `S4/Driver.lean`: the S4 rule-application and step-branch definitions -- the structurally
  forced seventh module (a deviation from the six-family split the task description proposed;
  the invariant material makes ~248 references into these definitions, so leaving them here
  would create an import cycle).
- `S4/Hintikka.lean`: the Hintikka-set construction and its saturation step lemmas.
- `S4/Redirect.lean`: the blocked-redirect / `accWithReds` machinery, including
  `modalS4Saturated_addEdge_of_blocked` (sits above `Hintikka` despite its name prefix).
- `S4/InvariantKeys.lean`, `S4/InvariantAcc.lean`, `S4/Invariant.lean`,
  `S4/HintikkaInvariant.lean`: the four-way split of the `S4LoopInv` invariant material (a
  single `Invariant.lean` would have been ~4,445 lines) -- keys-facing fields, accessibility/
  expansion fields, the `S4LoopInv` structure and its assembling capstones, and the top-level
  keyed-Hintikka/ordered-fuel invariants respectively.

S4 is deliberately **not** an instantiation of `RuleApplicationSpec` (`GenericDriver.lean`):
its transitively-propagating 4-rule places `T(□φ)` (unchanged modal depth) at successor
worlds, which falsifies the exact-decrement edge invariant (`rankStep`) that
`RuleApplicationSpec` demands. S4 reuses the generic driver (`modalStepBranchGen` etc.)
**definitionally only**, via a `φ₀`-parameterized `RuleApply` value, and supplies its own
sibling termination argument (`S4LoopInv`, a pigeonhole bound on `2 ^ (2 * |modalSubfmls φ₀|)`
possible signed-relevant-formula sets) instead of the K/T rank-decrease argument.

## What remains in this file

Twenty declarations, ~1,700 lines:

- **Entry points**: `modalTableauS4Keyed`, `modalTableauS4KeyedOrdered`,
  `modalTableauS4Keyed_eq_modalExpandBranchesGenSt`.
- **Termination measure**: the `persistentFresh`/`branchingLength`/`outputsSubsetUniverse`
  per-call obligations, the `modalExpMeasure_*` bridges, the `stepBranch` projection lemmas, and
  the 4-tuple-to-3-tuple `findSome?` projection helpers this measure needs.
- **Capstones**: `modalExpandBranchesS4Keyed_hintikka`,
  `modalExpandBranchesS4Keyed_openBranch_initial_mem`.

This is a coherent residue -- "the S4 driver's entry points, its termination argument, and its
two end-to-end theorems" -- not a leftover bucket.

## Strategy

Blocking is **equality-of-relevant-formula-set**, not subset-blocking: two worlds `w`,
`w'` are considered "the same" for loop-checking purposes exactly when they agree, for
every `ψ ∈ modalSubfmls φ₀` and every sign `s`, on whether `⟨s, ψ, w⟩` (`⟨s, ψ, w'⟩`
respectively) is on the branch. This is simpler than subset blocking and still yields a
`2 ^ (2 * |modalSubfmls φ₀|)` bound on the number of distinct worlds a saturating S4 tableau
can create, since each world's *birth key* is a distinct element of the powerset of
`modalSubfmls φ₀ × Sign` -- the *birth key*, not the live relevant set, is what the
pigeonhole argument now injects (see `S4/Invariant.lean`'s `S4LoopInv`).

Do **not** import `LoopInduction.lean`: despite the name, it is a `Forall2` list lemma
about the *fuel* loop in the generic driver, unrelated to modal loop-checking.

## Measured Baseline

The subsystem-wide census documentation (sorry/axiom counts, size figures, inventory tallies)
that used to live in this section was re-homed to `Cslib/Logics/Modal/Tableau/README.md` --
it was never specifically about loop-checking, and its `LoopChecking.lean` size/declaration
figures were stale by the time the `S4/` split began. See that file for the current numbers,
each with the command that reproduces it.

## References

* [M. Fitting, *Proof Methods for Modal and Intuitionistic Logics*][Fitting1983], Chapter 2
-/

@[expose] public section

namespace Cslib.Logic.Modal.Tableau

open Cslib.Logic.Tableau Cslib.Logic.Modal

variable {Atom : Type*} [DecidableEq Atom] [Hashable Atom]

/-- The keyed S4 modal tableau decision procedure: the entry point for the bespoke keyed driver,
mirroring `modalTableauGen`/`modalTableauS4`'s entry-branch shape (`F(φ)@0`), with
`keys := [(0, ∅)]` at the start: the root world `0` is pre-existing (not minted), so it is seeded
with the trivial (empty) birth key rather than left absent from `keys`. **Correction:**
an earlier version of this entry used `keys := []`; that violates `S4LoopInv.keysTotal` (every
known world has a recorded key) since `0 ∈ modalKnownWorlds [F(φ)@0]` from the very first
formula's label, and no step ever mints world `0` again to backfill a key for it. Seeding `(0, ∅)`
satisfies `keysTotal` trivially (`∅ ⊆ relevantSetFinset φ₀ b 0` and `∅ ⊆ signedSubfmls φ₀` both
hold unconditionally) and is invisible to every lemma established earlier in this file, all of
which are stated for an arbitrary `keys` list. Fuel is `modalFuelS4 φ`, the S4-specific fuel
bound (sufficiency: `modalExpMeasure_entry_le_fuelS4`) -- K's `modalFuel φ` is confirmed NOT
provably sufficient for
the S4 keyed loop's pigeonhole world bound `modalWorldBoundS4`. The live `modalTableauS4` is NOT
redefined. **Correction**: `instDecidableS4Valid` now exists and points at the ordered successor
`modalTableauS4KeyedOrdered` below (`FrameCompleteness.lean`), not at this (unordered) declaration
-- soundness is false for the unordered keyed driver, so the decision procedure could not have
been built on top of it. -/
def modalTableauS4Keyed (φ : Proposition Atom) : ModalTableauResult Atom :=
  let initialBranch : List (SignedFormula (Proposition Atom) WorldIndex) :=
    [⟨.neg, φ, 0⟩]
  modalExpandBranchesS4Keyed φ [initialBranch] [[]] [Accessibility.empty]
    [[(0, (∅ : Finset (Sign × Proposition Atom)))]] (modalFuelS4 φ)

/-- **Entry-point corollary, closing the `RuleApplySt` ladder story end-to-end.**
`modalTableauS4Keyed` -- the keyed S4 decision procedure's entry point -- equals the generic
state-threaded entry-point machinery (`modalExpandBranchesGenSt`) instantiated at the keyed
`RuleApplySt` rule `modalApplyOneS4KeyedSt φ`, at the same initial branch/accessibility/keys and
the same `modalFuelS4 φ` fuel bound. This cannot route through `modalTableauGenSt`
(`Saturation.lean`) instead, because that entry point hardwires K's `modalFuel φ`, whereas the S4
keyed loop needs `modalFuelS4 φ` for its pigeonhole world bound `modalWorldBoundS4` -- K's fuel is
confirmed NOT provably sufficient here (see `modalTableauS4Keyed`'s own docstring above). No fuel
parameter is added to `modalTableauGenSt`, and `modalTableauGen_eq_St` is untouched. -/
theorem modalTableauS4Keyed_eq_modalExpandBranchesGenSt (φ : Proposition Atom) :
    modalTableauS4Keyed φ =
      modalExpandBranchesGenSt (modalApplyOneS4KeyedSt φ)
        [[(⟨.neg, φ, 0⟩ : SignedFormula (Proposition Atom) WorldIndex)]] [[]]
        [Accessibility.empty] [[(0, (∅ : Finset (Sign × Proposition Atom)))]]
        (modalFuelS4 φ) := by
  unfold modalTableauS4Keyed
  rw [modalExpandBranchesGenSt_eq_S4Keyed]

/-! ## Ordered Keyed S4 Driver and Entry Point (Successor to the Bespoke Driver Above)

Structural copies of `modalExpandBranchesS4Keyed`/`modalTableauS4Keyed` above, with the reordered
stepper `modalStepBranchS4KeyedOrdered` (settled-context scheduling: non-minting candidates
first, minting fallback only once the branch has settled) substituted for
`modalStepBranchS4Keyed` at the single per-branch step call. Termination of the copied `fuel'`
recursion is not a new obligation here: the existing measure lemma
(`modalExpMeasure_step_lt_S4KeyedOrdered`) already establishes strict decrease for the ordered
stepper's `some` case, and the `processNext` recursion shape (structural recursion on the outer
`fuel`, exactly as in `modalExpandBranchesS4Keyed`) is unchanged from the original, so Lean's
termination checker accepts the copy identically. `modalStepBranchS4Keyed`,
`modalExpandBranchesS4Keyed`, and `modalTableauS4Keyed` themselves are left untouched pending
Phase 15's destructive retirement, once every consumer below has an ordered replacement. -/

/-- The ordered-stepper analogue of `modalTableauS4Keyed`: the entry point for the settled-context
scheduling driver, mirroring its predecessor's entry-branch shape (`F(φ)@0`) and seeding exactly
`keys := [(0, ∅)]` -- **not** `keys := []`, per the correction at `modalTableauS4Keyed`
above (an empty `keys` list violates `S4LoopInv.keysTotal`, since `0 ∈ modalKnownWorlds [F(φ)@0]`
from the first formula's label and no step re-mints world `0` to backfill a key for it). Fuel is
the same S4-specific bound `modalFuelS4 φ` used by `modalTableauS4Keyed`
(`modalExpMeasure_entry_le_fuelS4` was confirmed to apply verbatim to the ordered
driver, independent of traversal order). Successor to `modalTableauS4Keyed`, which Phase 15
retires once this entry point has a proved soundness/completeness pair of its own. -/
def modalTableauS4KeyedOrdered (φ : Proposition Atom) : ModalTableauResult Atom :=
  let initialBranch : List (SignedFormula (Proposition Atom) WorldIndex) :=
    [⟨.neg, φ, 0⟩]
  modalExpandBranchesS4KeyedOrdered φ [initialBranch] [[]] [Accessibility.empty]
    [[(0, (∅ : Finset (Sign × Proposition Atom)))]] (modalFuelS4 φ)

/-! ## Keyed-Driver Termination Measure: Combinatorial Primitives

Territory-local re-derivations of the four generic `List.countP`-based combinatorial facts
underpinning the per-step measure decrease (`FmpMeasure.lean:2788-2922`). Those originals are
`private` and hence unreachable from this file; since the keyed S4 driver's territory is
additive-only within `LoopChecking.lean` (not an edit to `FmpMeasure.lean`), the four lemmas are
re-derived here verbatim (same proofs, `_S4`-suffixed names) rather than exposed upstream. -/

/-! ## Keyed-Driver Termination Measure: Per-Call Obligations for `modalApplyOneS4Keyed`

The three raw measure-step hypotheses (`hBranchingLength`/`hPersistentFresh`/
`hOutputsSubsetUniverse`, the shape consumed by `modalExpMeasure_step_lt_gen`,
`FmpMeasure.lean:3227-3246`) as S4Keyed analogues, each universally quantified over `keys` so a
single lemma serves every fuel step. Built by the same mint-blocked/mint-unblocked/non-mint case
split as `modalStepBranchS4_preserves_bClosure`. The T-rule/4-rule propagation arms
(`modalTBoxSelf`/`modalTDiaNegSelf`/`modalFourBoxProp`/`modalFourDiaNegProp`, `FrameRules.lean`)
never appear in K's own dispatch, so their persistent-freshness is new content, established here
via their shared filter-guard shape (mirroring `diamondNeg_filterMap_fresh`,
`FmpMeasure.lean:3032`). -/

omit [Hashable Atom] in
/-- **Persistent-rule nonemptiness/freshness for `modalApplyOneT`** (T-augmented K): whenever
`modalApplyOneT sf b acc` produces a `.persistent` result, the emitted formulas are nonempty and
fresh. At the two T-relevant shapes (`T(□φ)@w`/`F(◇φ)@w`), composes K's own
`modalApplyOne_persistent_props` with `modalTBoxSelf_fresh`/`modalTDiaNegSelf_fresh`; at every
other shape `modalApplyOneT` reduces to `modalApplyOne` directly
(`modalApplyOneT_eq_of_not_boxPos_diaNeg`), so K's fact applies unchanged. -/
lemma modalApplyOneT_persistentFresh
    (sf : SignedFormula (Proposition Atom) WorldIndex)
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (nf : List (SignedFormula (Proposition Atom) WorldIndex))
    (hca : (modalApplyOneT sf b acc).fst = .persistent nf) :
    nf ≠ [] ∧ ∀ x ∈ nf, x ∉ b := by
  by_cases hbp : sf.sign = .pos ∧ ∃ φ, sf.formula = .box φ
  · obtain ⟨hs, ψ, hf⟩ := hbp
    have hsfeq : sf = (⟨Sign.pos, .box ψ, sf.label⟩ :
        SignedFormula (Proposition Atom) WorldIndex) := by rw [← hs, ← hf]
    rw [hsfeq] at hca
    unfold modalApplyOneT at hca
    dsimp only at hca
    rcases hk : (modalApplyOne (⟨Sign.pos, .box ψ, sf.label⟩ :
        SignedFormula (Proposition Atom) WorldIndex) b acc).fst with kf | kbrs | kf | -
    · rw [hk] at hca; simp at hca
    · rw [hk] at hca; simp at hca
    · rw [hk] at hca
      simp only [RuleResult.persistent.injEq] at hca
      obtain ⟨hkf, hkfresh⟩ := modalApplyOne_persistent_props _ b acc kf hk
      have hself := modalTBoxSelf_fresh b ψ sf.label
      refine ⟨?_, ?_⟩
      · rw [← hca]; exact List.append_ne_nil_of_left_ne_nil hkf _
      · intro x hx
        rw [← hca] at hx
        rcases List.mem_append.mp hx with hxk | hxs
        · exact hkfresh x hxk
        · exact hself x (List.mem_of_mem_filter hxs)
    · rw [hk] at hca
      dsimp only at hca
      split_ifs at hca with hemp
      · simp only [RuleResult.persistent.injEq] at hca
        refine ⟨?_, ?_⟩
        · rw [← hca]; simp only [Bool.not_eq_true] at hemp
          exact List.isEmpty_eq_false_iff.mp hemp
        · intro x hx; rw [← hca] at hx; exact modalTBoxSelf_fresh b ψ sf.label x hx
  · by_cases hdn : sf.sign = .neg ∧ ∃ φ, sf.formula = .diamond φ
    · obtain ⟨hs, ψ, hf⟩ := hdn
      have hsfeq : sf = (⟨Sign.neg, .diamond ψ, sf.label⟩ :
          SignedFormula (Proposition Atom) WorldIndex) := by rw [← hs, ← hf]
      rw [hsfeq] at hca
      unfold modalApplyOneT at hca
      dsimp only at hca
      rcases hk : (modalApplyOne (⟨Sign.neg, .diamond ψ, sf.label⟩ :
          SignedFormula (Proposition Atom) WorldIndex) b acc).fst with kf | kbrs | kf | -
      · rw [hk] at hca; simp at hca
      · rw [hk] at hca; simp at hca
      · rw [hk] at hca
        simp only [RuleResult.persistent.injEq] at hca
        obtain ⟨hkf, hkfresh⟩ := modalApplyOne_persistent_props _ b acc kf hk
        have hself := modalTDiaNegSelf_fresh b ψ sf.label
        refine ⟨?_, ?_⟩
        · rw [← hca]; exact List.append_ne_nil_of_left_ne_nil hkf _
        · intro x hx
          rw [← hca] at hx
          rcases List.mem_append.mp hx with hxk | hxs
          · exact hkfresh x hxk
          · exact hself x (List.mem_of_mem_filter hxs)
      · rw [hk] at hca
        dsimp only at hca
        split_ifs at hca with hemp
        · simp only [RuleResult.persistent.injEq] at hca
          refine ⟨?_, ?_⟩
          · rw [← hca]; simp only [Bool.not_eq_true] at hemp
            exact List.isEmpty_eq_false_iff.mp hemp
          · intro x hx; rw [← hca] at hx; exact modalTDiaNegSelf_fresh b ψ sf.label x hx
    · have heq : modalApplyOneT sf b acc = modalApplyOne sf b acc :=
        modalApplyOneT_eq_of_not_boxPos_diaNeg sf b acc ⟨hbp, hdn⟩
      rw [heq] at hca
      exact modalApplyOne_persistent_props sf b acc nf hca

omit [Hashable Atom] in
/-- **Branching-length for `modalApplyOneT`**: `modalApplyOneT` never introduces branching at
the two T-relevant shapes (K's own dispatch is `persistent`/`notApplicable` only there, and the
T-merge never turns either into `.branching`), so any `.branching` result must come from the
`_,_` fallthrough, i.e. from `modalApplyOne` directly, where K's own
`modalApplyOne_branching_length` applies. -/
lemma modalApplyOneT_branchingLength
    (sf : SignedFormula (Proposition Atom) WorldIndex)
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (brs : List (List (SignedFormula (Proposition Atom) WorldIndex)))
    (hca : (modalApplyOneT sf b acc).fst = .branching brs) :
    brs.length = 2 := by
  by_cases hbp : sf.sign = .pos ∧ ∃ φ, sf.formula = .box φ
  · obtain ⟨hs, ψ, hf⟩ := hbp
    have hsfeq : sf = (⟨Sign.pos, .box ψ, sf.label⟩ :
        SignedFormula (Proposition Atom) WorldIndex) := by rw [← hs, ← hf]
    rw [hsfeq] at hca
    unfold modalApplyOneT at hca
    dsimp only at hca
    rcases hk : (modalApplyOne (⟨Sign.pos, .box ψ, sf.label⟩ :
        SignedFormula (Proposition Atom) WorldIndex) b acc).fst with kf | kbrs | kf | -
    · rw [hk] at hca; simp at hca
    · rw [hk] at hca
      dsimp only at hca
      simp only [RuleResult.branching.injEq] at hca
      rw [← hca]
      exact modalApplyOne_branching_length _ b acc kbrs hk
    · rw [hk] at hca; simp at hca
    · rw [hk] at hca
      dsimp only at hca
      split_ifs at hca
  · by_cases hdn : sf.sign = .neg ∧ ∃ φ, sf.formula = .diamond φ
    · obtain ⟨hs, ψ, hf⟩ := hdn
      have hsfeq : sf = (⟨Sign.neg, .diamond ψ, sf.label⟩ :
          SignedFormula (Proposition Atom) WorldIndex) := by rw [← hs, ← hf]
      rw [hsfeq] at hca
      unfold modalApplyOneT at hca
      dsimp only at hca
      rcases hk : (modalApplyOne (⟨Sign.neg, .diamond ψ, sf.label⟩ :
          SignedFormula (Proposition Atom) WorldIndex) b acc).fst with kf | kbrs | kf | -
      · rw [hk] at hca; simp at hca
      · rw [hk] at hca
        dsimp only at hca
        simp only [RuleResult.branching.injEq] at hca
        rw [← hca]
        exact modalApplyOne_branching_length _ b acc kbrs hk
      · rw [hk] at hca; simp at hca
      · rw [hk] at hca
        dsimp only at hca
        split_ifs at hca
    · have heq : modalApplyOneT sf b acc = modalApplyOne sf b acc :=
        modalApplyOneT_eq_of_not_boxPos_diaNeg sf b acc ⟨hbp, hdn⟩
      rw [heq] at hca
      exact modalApplyOne_branching_length sf b acc brs hca

omit [Hashable Atom] in
/-- **Persistent-rule nonemptiness/freshness for `modalApplyOneS4Rules`** (T+4-augmented K):
same recipe as `modalApplyOneT_persistentFresh`, one layer up -- composes
`modalApplyOneT_persistentFresh` with `modalFourBoxProp_fresh`/`modalFourDiaNegProp_fresh` at the
two 4-relevant shapes, and reduces to `modalApplyOneT` directly elsewhere
(`modalApplyOneS4Rules_eq_of_not_boxPos_diaNeg`). -/
private lemma modalApplyOneS4Rules_persistentFresh
    (sf : SignedFormula (Proposition Atom) WorldIndex)
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (nf : List (SignedFormula (Proposition Atom) WorldIndex))
    (hca : (modalApplyOneS4Rules sf b acc).fst = .persistent nf) :
    nf ≠ [] ∧ ∀ x ∈ nf, x ∉ b := by
  by_cases hbp : sf.sign = .pos ∧ ∃ φ, sf.formula = .box φ
  · obtain ⟨hs, ψ, hf⟩ := hbp
    have hsfeq : sf = (⟨Sign.pos, .box ψ, sf.label⟩ :
        SignedFormula (Proposition Atom) WorldIndex) := by rw [← hs, ← hf]
    rw [hsfeq] at hca
    unfold modalApplyOneS4Rules at hca
    dsimp only at hca
    rcases ht : (modalApplyOneT (⟨Sign.pos, .box ψ, sf.label⟩ :
        SignedFormula (Proposition Atom) WorldIndex) b acc).fst with tf | tbrs | tf | -
    · rw [ht] at hca; simp at hca
    · rw [ht] at hca; simp at hca
    · rw [ht] at hca
      simp only [RuleResult.persistent.injEq] at hca
      obtain ⟨htf, htfresh⟩ := modalApplyOneT_persistentFresh _ b acc tf ht
      have hfour := modalFourBoxProp_fresh b acc ψ sf.label
      refine ⟨?_, ?_⟩
      · rw [← hca]; exact List.append_ne_nil_of_left_ne_nil htf _
      · intro x hx
        rw [← hca] at hx
        rcases List.mem_append.mp hx with hxt | hxs
        · exact htfresh x hxt
        · exact hfour x (List.mem_of_mem_filter hxs)
    · rw [ht] at hca
      dsimp only at hca
      split_ifs at hca with hemp
      · simp only [RuleResult.persistent.injEq] at hca
        refine ⟨?_, ?_⟩
        · rw [← hca]; simp only [Bool.not_eq_true] at hemp
          exact List.isEmpty_eq_false_iff.mp hemp
        · intro x hx; rw [← hca] at hx; exact modalFourBoxProp_fresh b acc ψ sf.label x hx
  · by_cases hdn : sf.sign = .neg ∧ ∃ φ, sf.formula = .diamond φ
    · obtain ⟨hs, ψ, hf⟩ := hdn
      have hsfeq : sf = (⟨Sign.neg, .diamond ψ, sf.label⟩ :
          SignedFormula (Proposition Atom) WorldIndex) := by rw [← hs, ← hf]
      rw [hsfeq] at hca
      unfold modalApplyOneS4Rules at hca
      dsimp only at hca
      rcases ht : (modalApplyOneT (⟨Sign.neg, .diamond ψ, sf.label⟩ :
          SignedFormula (Proposition Atom) WorldIndex) b acc).fst with tf | tbrs | tf | -
      · rw [ht] at hca; simp at hca
      · rw [ht] at hca; simp at hca
      · rw [ht] at hca
        simp only [RuleResult.persistent.injEq] at hca
        obtain ⟨htf, htfresh⟩ := modalApplyOneT_persistentFresh _ b acc tf ht
        have hfour := modalFourDiaNegProp_fresh b acc ψ sf.label
        refine ⟨?_, ?_⟩
        · rw [← hca]; exact List.append_ne_nil_of_left_ne_nil htf _
        · intro x hx
          rw [← hca] at hx
          rcases List.mem_append.mp hx with hxt | hxs
          · exact htfresh x hxt
          · exact hfour x (List.mem_of_mem_filter hxs)
      · rw [ht] at hca
        dsimp only at hca
        split_ifs at hca with hemp
        · simp only [RuleResult.persistent.injEq] at hca
          refine ⟨?_, ?_⟩
          · rw [← hca]; simp only [Bool.not_eq_true] at hemp
            exact List.isEmpty_eq_false_iff.mp hemp
          · intro x hx; rw [← hca] at hx
            exact modalFourDiaNegProp_fresh b acc ψ sf.label x hx
    · have heq : modalApplyOneS4Rules sf b acc = modalApplyOneT sf b acc :=
        modalApplyOneS4Rules_eq_of_not_boxPos_diaNeg sf b acc ⟨hbp, hdn⟩
      rw [heq] at hca
      exact modalApplyOneT_persistentFresh sf b acc nf hca

omit [Hashable Atom] in
/-- **Branching-length for `modalApplyOneS4Rules`**: same argument as
`modalApplyOneT_branchingLength`, one layer up. -/
private lemma modalApplyOneS4Rules_branchingLength
    (sf : SignedFormula (Proposition Atom) WorldIndex)
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (brs : List (List (SignedFormula (Proposition Atom) WorldIndex)))
    (hca : (modalApplyOneS4Rules sf b acc).fst = .branching brs) :
    brs.length = 2 := by
  by_cases hbp : sf.sign = .pos ∧ ∃ φ, sf.formula = .box φ
  · obtain ⟨hs, ψ, hf⟩ := hbp
    have hsfeq : sf = (⟨Sign.pos, .box ψ, sf.label⟩ :
        SignedFormula (Proposition Atom) WorldIndex) := by rw [← hs, ← hf]
    rw [hsfeq] at hca
    unfold modalApplyOneS4Rules at hca
    dsimp only at hca
    rcases ht : (modalApplyOneT (⟨Sign.pos, .box ψ, sf.label⟩ :
        SignedFormula (Proposition Atom) WorldIndex) b acc).fst with tf | tbrs | tf | -
    · rw [ht] at hca; simp at hca
    · rw [ht] at hca
      dsimp only at hca
      simp only [RuleResult.branching.injEq] at hca
      rw [← hca]
      exact modalApplyOneT_branchingLength _ b acc tbrs ht
    · rw [ht] at hca; simp at hca
    · rw [ht] at hca
      dsimp only at hca
      split_ifs at hca
  · by_cases hdn : sf.sign = .neg ∧ ∃ φ, sf.formula = .diamond φ
    · obtain ⟨hs, ψ, hf⟩ := hdn
      have hsfeq : sf = (⟨Sign.neg, .diamond ψ, sf.label⟩ :
          SignedFormula (Proposition Atom) WorldIndex) := by rw [← hs, ← hf]
      rw [hsfeq] at hca
      unfold modalApplyOneS4Rules at hca
      dsimp only at hca
      rcases ht : (modalApplyOneT (⟨Sign.neg, .diamond ψ, sf.label⟩ :
          SignedFormula (Proposition Atom) WorldIndex) b acc).fst with tf | tbrs | tf | -
      · rw [ht] at hca; simp at hca
      · rw [ht] at hca
        dsimp only at hca
        simp only [RuleResult.branching.injEq] at hca
        rw [← hca]
        exact modalApplyOneT_branchingLength _ b acc tbrs ht
      · rw [ht] at hca; simp at hca
      · rw [ht] at hca
        dsimp only at hca
        split_ifs at hca
    · have heq : modalApplyOneS4Rules sf b acc = modalApplyOneT sf b acc :=
        modalApplyOneS4Rules_eq_of_not_boxPos_diaNeg sf b acc ⟨hbp, hdn⟩
      rw [heq] at hca
      exact modalApplyOneT_branchingLength sf b acc brs hca

/-- **`hPersistentFresh` obligation for `modalApplyOneS4Keyed`**, for any `keys`: mint-blocked
gives `.linear []` (vacuous, never `.persistent`); mint-unblocked reduces to raw `modalApplyOne`
(K's own `modalApplyOne_persistent_props` applies directly); non-mint reduces to
`modalApplyOneS4Rules` (`modalApplyOneS4Rules_persistentFresh` applies). -/
private lemma modalApplyOneS4Keyed_persistentFresh_S4
    (φ₀ : Proposition Atom) (keys : List (WorldIndex × Finset (Sign × Proposition Atom)))
    (sf : SignedFormula (Proposition Atom) WorldIndex)
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (nf : List (SignedFormula (Proposition Atom) WorldIndex))
    (hca : (modalApplyOneS4Keyed φ₀ keys sf b acc).fst = .persistent nf) :
    nf ≠ [] ∧ ∀ x ∈ nf, x ∉ b := by
  by_cases hmint : (sf.sign = .neg ∧ ∃ φ, sf.formula = .box φ) ∨
      (sf.sign = .pos ∧ ∃ φ, sf.formula = .diamond φ)
  · rcases hmint with ⟨hs, ψ, hf⟩ | ⟨hs, ψ, hf⟩
    · have hsfeq : sf = (⟨Sign.neg, .box ψ, sf.label⟩ :
          SignedFormula (Proposition Atom) WorldIndex) := by rw [← hs, ← hf]
      rw [hsfeq] at hca
      rcases hblock : blockingWorldS4Keyed φ₀ b keys .neg ψ sf.label with _ | wBlock
      · have heq2 := modalApplyOneS4Keyed_boxNeg_unblocked_eq φ₀ b acc keys ψ sf.label hblock
        rw [heq2, congrArg Prod.fst (modalApplyOneS4KeyedMint_boxNeg_eq_S4 b acc ψ sf.label)]
          at hca
        simp at hca
      · have heq2 := modalApplyOneS4Keyed_boxNeg_blocked_eq φ₀ b acc keys ψ sf.label wBlock hblock
        rw [heq2] at hca; simp at hca
    · have hsfeq : sf = (⟨Sign.pos, .diamond ψ, sf.label⟩ :
          SignedFormula (Proposition Atom) WorldIndex) := by rw [← hs, ← hf]
      rw [hsfeq] at hca
      rcases hblock : blockingWorldS4Keyed φ₀ b keys .pos ψ sf.label with _ | wBlock
      · have heq2 := modalApplyOneS4Keyed_diaPos_unblocked_eq φ₀ b acc keys ψ sf.label hblock
        rw [heq2, congrArg Prod.fst (modalApplyOneS4KeyedMint_diaPos_eq_S4 b acc ψ sf.label)]
          at hca
        simp at hca
      · have heq2 := modalApplyOneS4Keyed_diaPos_blocked_eq φ₀ b acc keys ψ sf.label wBlock hblock
        rw [heq2] at hca; simp at hca
  · have hnbd : ¬ (sf.sign = .neg ∧ ∃ φ, sf.formula = .box φ) ∧
        ¬ (sf.sign = .pos ∧ ∃ φ, sf.formula = .diamond φ) :=
      ⟨fun hc => hmint (Or.inl hc), fun hc => hmint (Or.inr hc)⟩
    have heq1 : modalApplyOneS4Keyed φ₀ keys sf b acc = modalApplyOneS4 φ₀ sf b acc := by
      unfold modalApplyOneS4Keyed
      rcases hs : sf.sign with _ | _ <;> rcases hf : sf.formula with _ | _ | _ | _ | _ | φ | φ <;>
        simp_all
    rw [heq1, modalApplyOneS4_eq_of_not_boxNeg_diaPos φ₀ sf b acc hnbd] at hca
    by_cases h2' : (sf.sign = .pos ∧ ∃ φ, sf.formula = .box φ) ∨
        (sf.sign = .neg ∧ ∃ φ, sf.formula = .diamond φ)
    · exact modalApplyOneS4Rules_persistentFresh sf b acc nf hca
    · have hnbd2 : ¬ (sf.sign = .pos ∧ ∃ φ, sf.formula = .box φ) ∧
          ¬ (sf.sign = .neg ∧ ∃ φ, sf.formula = .diamond φ) :=
        ⟨fun hc => h2' (Or.inl hc), fun hc => h2' (Or.inr hc)⟩
      rw [modalApplyOneS4Rules_eq_of_not_boxPos_diaNeg sf b acc hnbd2,
          modalApplyOneT_eq_of_not_boxPos_diaNeg sf b acc hnbd2] at hca
      exact modalApplyOne_persistent_props sf b acc nf hca

/-- **`hBranchingLength` obligation for `modalApplyOneS4Keyed`**, for any `keys`: same
mint-blocked/mint-unblocked/non-mint split as `modalApplyOneS4Keyed_persistentFresh_S4`. -/
private lemma modalApplyOneS4Keyed_branchingLength_S4
    (φ₀ : Proposition Atom) (keys : List (WorldIndex × Finset (Sign × Proposition Atom)))
    (sf : SignedFormula (Proposition Atom) WorldIndex)
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (brs : List (List (SignedFormula (Proposition Atom) WorldIndex)))
    (hca : (modalApplyOneS4Keyed φ₀ keys sf b acc).fst = .branching brs) :
    brs.length = 2 := by
  by_cases hmint : (sf.sign = .neg ∧ ∃ φ, sf.formula = .box φ) ∨
      (sf.sign = .pos ∧ ∃ φ, sf.formula = .diamond φ)
  · rcases hmint with ⟨hs, ψ, hf⟩ | ⟨hs, ψ, hf⟩
    · have hsfeq : sf = (⟨Sign.neg, .box ψ, sf.label⟩ :
          SignedFormula (Proposition Atom) WorldIndex) := by rw [← hs, ← hf]
      rw [hsfeq] at hca
      rcases hblock : blockingWorldS4Keyed φ₀ b keys .neg ψ sf.label with _ | wBlock
      · have heq2 := modalApplyOneS4Keyed_boxNeg_unblocked_eq φ₀ b acc keys ψ sf.label hblock
        rw [heq2, congrArg Prod.fst (modalApplyOneS4KeyedMint_boxNeg_eq_S4 b acc ψ sf.label)]
          at hca
        simp at hca
      · have heq2 := modalApplyOneS4Keyed_boxNeg_blocked_eq φ₀ b acc keys ψ sf.label wBlock hblock
        rw [heq2] at hca; simp at hca
    · have hsfeq : sf = (⟨Sign.pos, .diamond ψ, sf.label⟩ :
          SignedFormula (Proposition Atom) WorldIndex) := by rw [← hs, ← hf]
      rw [hsfeq] at hca
      rcases hblock : blockingWorldS4Keyed φ₀ b keys .pos ψ sf.label with _ | wBlock
      · have heq2 := modalApplyOneS4Keyed_diaPos_unblocked_eq φ₀ b acc keys ψ sf.label hblock
        rw [heq2, congrArg Prod.fst (modalApplyOneS4KeyedMint_diaPos_eq_S4 b acc ψ sf.label)]
          at hca
        simp at hca
      · have heq2 := modalApplyOneS4Keyed_diaPos_blocked_eq φ₀ b acc keys ψ sf.label wBlock hblock
        rw [heq2] at hca; simp at hca
  · have hnbd : ¬ (sf.sign = .neg ∧ ∃ φ, sf.formula = .box φ) ∧
        ¬ (sf.sign = .pos ∧ ∃ φ, sf.formula = .diamond φ) :=
      ⟨fun hc => hmint (Or.inl hc), fun hc => hmint (Or.inr hc)⟩
    have heq1 : modalApplyOneS4Keyed φ₀ keys sf b acc = modalApplyOneS4 φ₀ sf b acc := by
      unfold modalApplyOneS4Keyed
      rcases hs : sf.sign with _ | _ <;> rcases hf : sf.formula with _ | _ | _ | _ | _ | φ | φ <;>
        simp_all
    rw [heq1, modalApplyOneS4_eq_of_not_boxNeg_diaPos φ₀ sf b acc hnbd] at hca
    by_cases h2' : (sf.sign = .pos ∧ ∃ φ, sf.formula = .box φ) ∨
        (sf.sign = .neg ∧ ∃ φ, sf.formula = .diamond φ)
    · exact modalApplyOneS4Rules_branchingLength sf b acc brs hca
    · have hnbd2 : ¬ (sf.sign = .pos ∧ ∃ φ, sf.formula = .box φ) ∧
          ¬ (sf.sign = .neg ∧ ∃ φ, sf.formula = .diamond φ) :=
        ⟨fun hc => h2' (Or.inl hc), fun hc => h2' (Or.inr hc)⟩
      rw [modalApplyOneS4Rules_eq_of_not_boxPos_diaNeg sf b acc hnbd2,
          modalApplyOneT_eq_of_not_boxPos_diaNeg sf b acc hnbd2] at hca
      exact modalApplyOne_branching_length sf b acc brs hca

/-- **`hOutputsSubsetUniverse` obligation for `modalApplyOneS4Keyed`**, assembled from the
mint-unblocked outputs-subset facts (`modalApplyOne_boxNeg_outputs_subset_S4`/
`modalApplyOne_diamondPos_outputs_subset_S4`, needing the STRICT world bound `hW`, supplied by
`modalStepBranchS4_worldBound`), the vacuous mint-blocked case, and the already-landed
`modalApplyOneS4Keyed_nonMint_universe_S4` for the 12 non-minting shapes. Mirrors
`modalStepBranchS4_preserves_bClosure`'s case split exactly, concluding the raw universe-subset
match fact instead of branch-closure. -/
private lemma modalApplyOneS4Keyed_outputsSubsetUniverse_S4
    (φ₀ : Proposition Atom) (keys : List (WorldIndex × Finset (Sign × Proposition Atom)))
    (sf : SignedFormula (Proposition Atom) WorldIndex)
    (b : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (hb : ∀ x ∈ b, x ∈ modalUniverseS4 φ₀) (hsfmem : sf ∈ b)
    (hknown : accTargetsKnown b acc)
    (hWC : worldsContiguousS4 b)
    (hKT : ∀ w ∈ modalKnownWorlds b, ∃ k, (w, k) ∈ keys)
    (hKD : ∀ w1 w2 k1 k2, (w1, k1) ∈ keys → (w2, k2) ∈ keys → w1 ≠ w2 → k1 ≠ k2)
    (hKI : ∀ w k, (w, k) ∈ keys → k ⊆ signedSubfmls φ₀) :
    (match (modalApplyOneS4Keyed φ₀ keys sf b acc).fst with
      | .linear fs => ∀ x ∈ fs, x ∈ modalUniverseS4 φ₀
      | .branching brs => ∀ x ∈ brs.flatten, x ∈ modalUniverseS4 φ₀
      | .persistent fs => ∀ x ∈ fs, x ∈ modalUniverseS4 φ₀
      | .notApplicable => True) := by
  by_cases hmint : (sf.sign = .neg ∧ ∃ φ, sf.formula = .box φ) ∨
      (sf.sign = .pos ∧ ∃ φ, sf.formula = .diamond φ)
  · have hW := modalStepBranchS4_worldBound φ₀ b keys hWC hKT hKD hKI
    rcases hmint with ⟨hs, ψ, hf⟩ | ⟨hs, ψ, hf⟩
    · have hsfeq : sf = (⟨Sign.neg, .box ψ, sf.label⟩ :
          SignedFormula (Proposition Atom) WorldIndex) := by rw [← hs, ← hf]
      have hsfmem' : (⟨Sign.neg, .box ψ, sf.label⟩ :
          SignedFormula (Proposition Atom) WorldIndex) ∈ b := hsfeq ▸ hsfmem
      rw [hsfeq]
      rcases hblock : blockingWorldS4Keyed φ₀ b keys .neg ψ sf.label with _ | wBlock
      · have heq2 := modalApplyOneS4Keyed_boxNeg_unblocked_eq φ₀ b acc keys ψ sf.label hblock
        rw [heq2, congrArg Prod.fst (modalApplyOneS4KeyedMint_boxNeg_eq_S4 b acc ψ sf.label)]
        exact modalApplyOne_boxNeg_outputs_subset_S4 φ₀ b ψ sf.label hb hsfmem' hW
      · have heq2 := modalApplyOneS4Keyed_boxNeg_blocked_eq φ₀ b acc keys ψ sf.label wBlock hblock
        rw [heq2]; simp
    · have hsfeq : sf = (⟨Sign.pos, .diamond ψ, sf.label⟩ :
          SignedFormula (Proposition Atom) WorldIndex) := by rw [← hs, ← hf]
      have hsfmem' : (⟨Sign.pos, .diamond ψ, sf.label⟩ :
          SignedFormula (Proposition Atom) WorldIndex) ∈ b := hsfeq ▸ hsfmem
      rw [hsfeq]
      rcases hblock : blockingWorldS4Keyed φ₀ b keys .pos ψ sf.label with _ | wBlock
      · have heq2 := modalApplyOneS4Keyed_diaPos_unblocked_eq φ₀ b acc keys ψ sf.label hblock
        rw [heq2, congrArg Prod.fst (modalApplyOneS4KeyedMint_diaPos_eq_S4 b acc ψ sf.label)]
        exact modalApplyOne_diamondPos_outputs_subset_S4 φ₀ b ψ sf.label hb hsfmem' hW
      · have heq2 := modalApplyOneS4Keyed_diaPos_blocked_eq φ₀ b acc keys ψ sf.label wBlock hblock
        rw [heq2]; simp
  · have hnbd : ¬ (sf.sign = .neg ∧ ∃ φ, sf.formula = .box φ) ∧
        ¬ (sf.sign = .pos ∧ ∃ φ, sf.formula = .diamond φ) :=
      ⟨fun hc => hmint (Or.inl hc), fun hc => hmint (Or.inr hc)⟩
    exact modalApplyOneS4Keyed_nonMint_universe_S4 φ₀ keys sf b acc hb hsfmem hknown hnbd

/-! ## Keyed-Driver Termination Measure: Entry-Measure Sufficiency for `modalFuelS4`

`modalFuel φ₀` (K's fuel) is confirmed NOT provably sufficient for the S4 keyed loop: at
`modalComplexity φ₀ = 0`, `modalWorldBoundS4 φ₀ = 2 ^ (2 * 1) = 4` exceeds K's
`modalWorldBound φ₀ = 1`. The dedicated `modalFuelS4` (defined earlier, alongside
`modalWorldBoundS4`/`modalUniverseS4`, so it is in scope for `modalTableauS4Keyed`'s fuel
argument) is shown sufficient here, mirroring `modalExpMeasure_entry_le_fuel`
(`FmpMeasure.lean:208-251`). -/

omit [Hashable Atom] in
/-- **Entry-measure sufficiency for `modalFuelS4`**: at the S4 keyed tableau's entry point, the
worklist measure over `modalUniverseS4 φ₀` is bounded by `modalFuelS4 φ₀`. Direct transcription
of `modalExpMeasure_entry_le_fuel` (`FmpMeasure.lean:208-251`), substituting `modalUniverseS4`/
`modalWorldBoundS4`/`modalUniverseS4_length_le` for their K counterparts -- the
`modalWork ≤ 2 * U.length` step is universe-agnostic (`List.countP_le_length` + `simp` on the
empty expanded-set case), so it transfers verbatim. -/
lemma modalExpMeasure_entry_le_fuelS4 (φ₀ : Proposition Atom) :
    modalExpMeasure (modalUniverseS4 φ₀) [[(⟨.neg, φ₀, 0⟩ :
      SignedFormula (Proposition Atom) WorldIndex)]] [[]] ≤ modalFuelS4 φ₀ := by
  have hmeas : modalExpMeasure (modalUniverseS4 φ₀)
      [[(⟨.neg, φ₀, 0⟩ : SignedFormula (Proposition Atom) WorldIndex)]] [[]]
      = 3 ^ modalWork (modalUniverseS4 φ₀)
          [(⟨.neg, φ₀, 0⟩ : SignedFormula (Proposition Atom) WorldIndex)] [] := by
    simp [modalExpMeasure]
  rw [hmeas]
  have hwork : modalWork (modalUniverseS4 φ₀)
      [(⟨.neg, φ₀, 0⟩ : SignedFormula (Proposition Atom) WorldIndex)] []
      ≤ 2 * (modalUniverseS4 φ₀).length := by
    unfold modalWork
    have h1 : (modalUniverseS4 φ₀).countP
        (fun sf => !(([(⟨.neg, φ₀, 0⟩ : SignedFormula (Proposition Atom) WorldIndex)]).any
          (· == sf))) ≤ (modalUniverseS4 φ₀).length :=
      List.countP_le_length
    have h2 : (modalUniverseS4 φ₀).countP
        (fun sf => !((([] : List (SignedFormula (Proposition Atom) WorldIndex))).any
          (· == sf))) = (modalUniverseS4 φ₀).length := by
      simp
    omega
  have hUlen := modalUniverseS4_length_le φ₀
  have hfinal : modalWork (modalUniverseS4 φ₀)
      [(⟨.neg, φ₀, 0⟩ : SignedFormula (Proposition Atom) WorldIndex)] [] ≤
      4 * (2 * modalComplexity φ₀ + 1) * (modalWorldBoundS4 φ₀ + 1) := by
    have h2U : 2 * (modalUniverseS4 φ₀).length ≤
        2 * (2 * (2 * modalComplexity φ₀ + 1) * (modalWorldBoundS4 φ₀ + 1)) :=
      Nat.mul_le_mul_left 2 hUlen
    have heq : 2 * (2 * (2 * modalComplexity φ₀ + 1) * (modalWorldBoundS4 φ₀ + 1)) =
        4 * (2 * modalComplexity φ₀ + 1) * (modalWorldBoundS4 φ₀ + 1) := by ring
    rw [heq] at h2U
    omega
  calc 3 ^ modalWork (modalUniverseS4 φ₀)
        [(⟨.neg, φ₀, 0⟩ : SignedFormula (Proposition Atom) WorldIndex)] []
      ≤ 3 ^ (4 * (2 * modalComplexity φ₀ + 1) * (modalWorldBoundS4 φ₀ + 1)) :=
        Nat.pow_le_pow_right (by norm_num) hfinal
    _ = modalFuelS4 φ₀ := rfl

/-! ## 4-Tuple Stepper Projection Bridge + Local Measure-Split Helpers

The measure-decrease engine (`modalExpMeasure_step_lt_gen`, `FmpMeasure.lean:3227`) is phrased
against the generic 3-tuple driver `modalStepBranchGen` (`Saturation.lean:122`), whereas the
keyed S4 driver `modalStepBranchS4Keyed` returns a 4-tuple with `keys'` bolted on. This section
bridges the two: `modalStepBranchS4Keyed_proj_stepBranchGen` shows a keyed step implies the
corresponding generic step at `apply := modalApplyOneS4Keyed φ₀ keys`, dropping the `keys'`
component. Both drivers scan the same branch `b` via `List.findSome?` with the same
"already expanded" guard and the same four `RuleResult` arms, so this is a structural
`findSome?`-congruence argument, not a semantic one. -/

/-- **Generic `findSome?` projection helper**: if a list-scan via `g1` (into a 4-tuple type
`A × B × Accessibility × K`) succeeds pointwise-projecting to a scan via `g2` (into the
3-tuple `A × B × Accessibility`, dropping the last component whenever `g1` is `some`, and
agreeing with `g1` on which elements are skipped/`none`), then `g1`'s scan result projects to
`g2`'s scan result the same way. Purely structural: no reference to any tableau-specific type. -/
private lemma stepBranch_findSome?_proj4to3
    {α A B K : Type*}
    {g1 : α → Option (A × B × Accessibility × K)}
    {g2 : α → Option (A × B × Accessibility)}
    (hpt : ∀ (x : α) (a : A) (bb : B) (c : Accessibility) (k : K),
      g1 x = some (a, bb, c, k) → g2 x = some (a, bb, c))
    (hnone : ∀ x : α, g1 x = none → g2 x = none) :
    ∀ (l : List α) (a : A) (bb : B) (c : Accessibility) (k : K),
      l.findSome? g1 = some (a, bb, c, k) → l.findSome? g2 = some (a, bb, c) := by
  intro l
  induction l with
  | nil => intro a bb c k h; simp at h
  | cons x rest ih =>
    intro a bb c k h
    rw [List.findSome?_cons] at h
    rw [List.findSome?_cons]
    cases hg1 : g1 x with
    | none =>
      rw [hg1] at h
      rw [hnone x hg1]
      exact ih a bb c k h
    | some v =>
      rw [hg1] at h
      simp only [Option.some.injEq] at h
      have hg1' : g1 x = some (a, bb, c, k) := by rw [hg1, h]
      rw [hpt x a bb c k hg1']

/-- **The projection lemma**: a keyed step at `modalStepBranchS4Keyed φ₀ b e acc keys`
implies the corresponding step of the generic driver at `apply := modalApplyOneS4Keyed φ₀ keys`,
dropping the `keys'` component. Both sides select the SAME formula `sf` from `b` (same
"already expanded" guard `e.any (· == sf)`) and dispatch on the SAME `RuleResult` value
`(modalApplyOneS4Keyed φ₀ keys sf b acc).1`, since `modalStepBranchGen`'s `apply sf b acc` at
`apply := modalApplyOneS4Keyed φ₀ keys` computes literally the same pair the keyed stepper
computes internally. -/
lemma modalStepBranchS4Keyed_proj_stepBranchGen (φ₀ : Proposition Atom)
    (b e : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (keys : List (WorldIndex × Finset (Sign × Proposition Atom)))
    (newBs newExps : List (List (SignedFormula (Proposition Atom) WorldIndex)))
    (newAcc : Accessibility) (keys' : List (WorldIndex × Finset (Sign × Proposition Atom)))
    (hstep : modalStepBranchS4Keyed φ₀ b e acc keys = some (newBs, newExps, newAcc, keys')) :
    modalStepBranchGen (modalApplyOneS4Keyed φ₀ keys) b e acc = some (newBs, newExps, newAcc) := by
  unfold modalStepBranchS4Keyed at hstep
  unfold modalStepBranchGen
  refine stepBranch_findSome?_proj4to3 ?_ ?_ b newBs newExps newAcc keys' hstep
  · -- hpt: pointwise, the keyed inner computation projects to the generic one.
    intro sf a bb c k h
    split_ifs at h ⊢ with hexp
    rcases hpair : modalApplyOneS4Keyed φ₀ keys sf b acc with ⟨result, newAcc0⟩
    rw [hpair] at h
    rcases hres : result with nf | brs | nf | -
    · rw [hres] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h ⊢
      obtain ⟨h1, h2, h3, -⟩ := h
      exact ⟨h1, h2, h3⟩
    · rw [hres] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h ⊢
      obtain ⟨h1, h2, h3, -⟩ := h
      exact ⟨h1, h2, h3⟩
    · rw [hres] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h ⊢
      obtain ⟨h1, h2, h3, -⟩ := h
      exact ⟨h1, h2, h3⟩
    · rw [hres] at h; simp at h
  · -- hnone: pointwise, both drivers skip the same elements.
    intro sf h
    split_ifs at h ⊢ with hexp
    · rfl
    · rcases hpair : modalApplyOneS4Keyed φ₀ keys sf b acc with ⟨result, newAcc0⟩
      rw [hpair] at h
      rcases hres : result with nf | brs | nf | -
      · rw [hres] at h; simp at h
      · rw [hres] at h; simp at h
      · rw [hres] at h; simp at h
      · rfl

/-! ## Keyed Per-Step Measure Decrease over `modalUniverseS4`

Transcription of `modalExpMeasure_step_lt_gen` (`FmpMeasure.lean:3227`, public but hardwired to
K's `modalUniverse φ0`/`modalWorldBound φ0`) over `modalUniverseS4 φ₀`/`modalWorldBoundS4 φ₀`.
Direct instantiation does not typecheck (see the plan's "Measure-Decrease Lead"), so the proof
below is a line-by-line transcription consuming: four universe-generic combinatorial
primitives (`_S4`-suffixed above), three landed per-call obligations
(`modalApplyOneS4Keyed_branchingLength_S4`/`_persistentFresh_S4`/`_outputsSubsetUniverse_S4`),
and the projection bridge (`modalStepBranchS4Keyed_proj_stepBranchGen`) plus its local
`modalExpMeasure_split`/`_append_S4` helpers (and the `_const_exp_S4` helper just above).
`hstep` is phrased directly against the keyed 4-tuple stepper `modalStepBranchS4Keyed` (dropping
`keys'` via the projection bridge inside the proof), matching what the top-loop induction below
will have in hand at each call site. The `hOutputsSubsetUniverse` obligation's extra hypotheses
(`hknown`/`hWC`/`hKT`/`hKD`/`hKI`, in place of the generic template's `accFreshInv`/strict-world-
bound pair) are threaded as raw hypotheses here rather than derived; the top-loop induction
below supplies them from
the ambient `S4LoopInv`. -/

/-- **The keyed engine**: one `modalStepBranchS4Keyed` step strictly decreases the base-3 damped
worklist measure over `modalUniverseS4 φ₀` by at least one. -/
lemma modalExpMeasure_step_lt_S4Keyed
    (φ₀ : Proposition Atom) (keys keys' : List (WorldIndex × Finset (Sign × Proposition Atom)))
    (done bt newBs : List (List (SignedFormula (Proposition Atom) WorldIndex)))
    (doneExp es : List (List (SignedFormula (Proposition Atom) WorldIndex)))
    (newExp : List (SignedFormula (Proposition Atom) WorldIndex))
    (bh e : List (SignedFormula (Proposition Atom) WorldIndex))
    (acc newAcc : Accessibility)
    (hdlen : done.length = doneExp.length)
    (hb : ∀ x ∈ bh, x ∈ modalUniverseS4 φ₀)
    (hknown : accTargetsKnown bh acc)
    (hWC : worldsContiguousS4 bh)
    (hKT : ∀ w ∈ modalKnownWorlds bh, ∃ k, (w, k) ∈ keys)
    (hKD : ∀ w1 w2 k1 k2, (w1, k1) ∈ keys → (w2, k2) ∈ keys → w1 ≠ w2 → k1 ≠ k2)
    (hKI : ∀ w k, (w, k) ∈ keys → k ⊆ signedSubfmls φ₀)
    (hstep : modalStepBranchS4Keyed φ₀ bh e acc keys =
      some (newBs, newBs.map (fun _ => newExp), newAcc, keys')) :
    modalExpMeasure (modalUniverseS4 φ₀) (done ++ newBs ++ bt)
        (doneExp ++ newBs.map (fun _ => newExp) ++ es) + 1
      ≤ modalExpMeasure (modalUniverseS4 φ₀) (done ++ bh :: bt) (doneExp ++ e :: es) := by
  have hstepGen := modalStepBranchS4Keyed_proj_stepBranchGen φ₀ bh e acc keys
    newBs (newBs.map (fun _ => newExp)) newAcc keys' hstep
  set U := modalUniverseS4 φ₀ with hUdef
  have hrhs : modalExpMeasure U (done ++ bh :: bt) (doneExp ++ e :: es) =
      modalExpMeasure U done doneExp + 3 ^ modalWork U bh e + modalExpMeasure U bt es :=
    modalExpMeasure_split U done doneExp bh e bt es hdlen
  have hlhs : modalExpMeasure U (done ++ newBs ++ bt)
        (doneExp ++ newBs.map (fun _ => newExp) ++ es) =
      modalExpMeasure U done doneExp +
        (newBs.map (fun child => 3 ^ modalWork U child newExp)).sum +
        modalExpMeasure U bt es := by
    have hlen1 : (done ++ newBs).length = (doneExp ++ newBs.map (fun _ => newExp)).length := by
      simp [List.length_append, hdlen]
    rw [modalExpMeasure_append U (done ++ newBs) bt
          (doneExp ++ newBs.map (fun _ => newExp)) es hlen1,
        modalExpMeasure_append U done newBs doneExp (newBs.map (fun _ => newExp)) hdlen,
        modalExpMeasure_const_exp U newBs newExp]
  rw [hrhs, hlhs]
  suffices h : (newBs.map (fun child => 3 ^ modalWork U child newExp)).sum + 1 ≤
      3 ^ modalWork U bh e by omega
  simp only [modalStepBranchGen] at hstepGen
  obtain ⟨sf, hsfmem, hfound⟩ := List.exists_of_findSome?_eq_some hstepGen
  split_ifs at hfound with hany
  simp only [Bool.not_eq_true] at hany
  have hsfU : sf ∈ U := hb sf hsfmem
  rcases hca : (modalApplyOneS4Keyed φ₀ keys sf bh acc).1 with nf | brs | nf | -
  · -- linear
    rw [hca] at hfound
    obtain ⟨rfl, hne, -⟩ := Option.some.inj hfound
    have hdrop : modalWork U (nf ++ bh) (e ++ [sf]) + 1 ≤ modalWork U bh e :=
      modalWork_drop_linear U bh (nf ++ bh) e sf hsfU hany
        (fun z hz => List.mem_append_right nf hz)
    have hC : 1 ≤ modalWork U bh e := by omega
    have h0 : modalWork U (nf ++ bh) (e ++ [sf]) ≤ modalWork U bh e - 1 := by omega
    simp only [List.map_singleton, List.sum_singleton]
    exact pow3_add_one_le hC h0
  · -- branching
    have hlen2 : brs.length = 2 :=
      modalApplyOneS4Keyed_branchingLength_S4 φ₀ keys sf bh acc brs hca
    obtain ⟨b0, b1, hbrs⟩ : ∃ b0 b1, brs = [b0, b1] := by
      match brs, hlen2 with
      | [b0, b1], _ => exact ⟨b0, b1, rfl⟩
    subst hbrs
    rw [hca] at hfound
    obtain ⟨rfl, hne, -⟩ := Option.some.inj hfound
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
    have hdrop0 : modalWork U (b0 ++ bh) (e ++ [sf]) + 1 ≤ modalWork U bh e :=
      modalWork_drop_linear U bh (b0 ++ bh) e sf hsfU hany
        (fun z hz => List.mem_append_right b0 hz)
    have hdrop1 : modalWork U (b1 ++ bh) (e ++ [sf]) + 1 ≤ modalWork U bh e :=
      modalWork_drop_linear U bh (b1 ++ bh) e sf hsfU hany
        (fun z hz => List.mem_append_right b1 hz)
    have hC : 1 ≤ modalWork U bh e := by omega
    have h0 : modalWork U (b0 ++ bh) (e ++ [sf]) ≤ modalWork U bh e - 1 := by omega
    have h1 : modalWork U (b1 ++ bh) (e ++ [sf]) ≤ modalWork U bh e - 1 := by omega
    exact pow3_two_add_one_le hC h0 h1
  · -- persistent
    rw [hca] at hfound
    obtain ⟨rfl, hne, -⟩ := Option.some.inj hfound
    obtain ⟨hnfne, hnffresh⟩ :=
      modalApplyOneS4Keyed_persistentFresh_S4 φ₀ keys sf bh acc nf hca
    obtain ⟨x0, hx0mem⟩ := List.exists_mem_of_ne_nil nf hnfne
    have hclosure := modalApplyOneS4Keyed_outputsSubsetUniverse_S4 φ₀ keys sf bh acc hb hsfmem
      hknown hWC hKT hKD hKI
    rw [hca] at hclosure
    have hx0U : x0 ∈ U := hclosure x0 hx0mem
    have hx0b : x0 ∉ bh := hnffresh x0 hx0mem
    have hx0b' : x0 ∈ nf ++ bh := List.mem_append_left bh hx0mem
    have hdrop : modalWork U (nf ++ bh) newExp + 1 ≤ modalWork U bh newExp :=
      modalWork_drop_persistent U bh (nf ++ bh) newExp x0 hx0U hx0b hx0b'
        (fun z hz => List.mem_append_right nf hz)
    have hC : 1 ≤ modalWork U bh newExp := by omega
    have h0 : modalWork U (nf ++ bh) newExp ≤ modalWork U bh newExp - 1 := by omega
    simp only [List.map_singleton, List.sum_singleton]
    exact pow3_add_one_le hC h0
  · rw [hca] at hfound; simp at hfound

/-! ## Ordered Stepper: Termination Measure Re-Verification

Re-establishes the strict per-step measure decrease just proved against
`modalStepBranchS4Keyed` above, this time for the ordered stepper. The projection bridge
`modalStepBranchS4Keyed_proj_stepBranchGen` is replaced by a selection-agnostic form,
`modalStepBranchS4KeyedOrdered_proj`: rather than asserting the ordered stepper's result equals
the UNordered generic driver's own whole-branch `b.findSome?` traversal (false in general -- a
different formula may genuinely be selected first, that being the entire point of reordering),
it extracts the weaker existential fact `modalExpMeasure_step_lt_S4Keyed`'s proof actually
consumes: SOME formula `sf ∈ b`, `sf ∉ e`, whose rule application produces exactly the result
the ordered stepper returned. That proof never uses more than this existential (it never needs
`sf` to be the FIRST such formula in `b`), so the measure argument below transcribes unchanged
once fed this replacement bridge -- every other ingredient (the four combinatorial measure
primitives, the three per-call rule-application obligations) is selection-independent and reused
exactly as is. -/

/-- **The projection lemma, ordered form.** Selection-agnostic replacement for
`modalStepBranchS4Keyed_proj_stepBranchGen`, built directly from
`modalStepBranchS4KeyedOrdered_selected_mem` rather than from `modalStepBranchGen`'s own
`findSome?`. The conclusion drops the `keys'` component of `modalStepBranchS4KeyedBody`'s output
via `Option.map`, matching the 3-tuple shape `modalStepBranchGen` itself would have produced. -/
lemma modalStepBranchS4KeyedOrdered_proj (φ₀ : Proposition Atom)
    (b e : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (keys : List (WorldIndex × Finset (Sign × Proposition Atom)))
    (newBs newExps : List (List (SignedFormula (Proposition Atom) WorldIndex)))
    (newAcc : Accessibility) (keys' : List (WorldIndex × Finset (Sign × Proposition Atom)))
    (hstep : modalStepBranchS4KeyedOrdered φ₀ b e acc keys =
      some (newBs, newExps, newAcc, keys')) :
    ∃ sf ∈ b, sf ∉ e ∧
      (modalStepBranchS4KeyedBody φ₀ b e acc keys sf).map (fun p => (p.1, p.2.1, p.2.2.1)) =
        some (newBs, newExps, newAcc) := by
  obtain ⟨sf, hsf_mem, hsf_ne, hsf_body⟩ :=
    modalStepBranchS4KeyedOrdered_selected_mem φ₀ b e acc keys newBs newExps newAcc keys' hstep
  exact ⟨sf, hsf_mem, hsf_ne, by rw [hsf_body]; rfl⟩

/-- **The keyed engine, ordered form.** One `modalStepBranchS4KeyedOrdered` step strictly
decreases the base-3 damped worklist measure over `modalUniverseS4 φ₀` by at least one.
Line-by-line transcription of `modalExpMeasure_step_lt_S4Keyed` above, substituting
`modalStepBranchS4KeyedOrdered_proj` for `modalStepBranchS4Keyed_proj_stepBranchGen`. -/
lemma modalExpMeasure_step_lt_S4KeyedOrdered
    (φ₀ : Proposition Atom) (keys keys' : List (WorldIndex × Finset (Sign × Proposition Atom)))
    (done bt newBs : List (List (SignedFormula (Proposition Atom) WorldIndex)))
    (doneExp es : List (List (SignedFormula (Proposition Atom) WorldIndex)))
    (newExp : List (SignedFormula (Proposition Atom) WorldIndex))
    (bh e : List (SignedFormula (Proposition Atom) WorldIndex))
    (acc newAcc : Accessibility)
    (hdlen : done.length = doneExp.length)
    (hb : ∀ x ∈ bh, x ∈ modalUniverseS4 φ₀)
    (hknown : accTargetsKnown bh acc)
    (hWC : worldsContiguousS4 bh)
    (hKT : ∀ w ∈ modalKnownWorlds bh, ∃ k, (w, k) ∈ keys)
    (hKD : ∀ w1 w2 k1 k2, (w1, k1) ∈ keys → (w2, k2) ∈ keys → w1 ≠ w2 → k1 ≠ k2)
    (hKI : ∀ w k, (w, k) ∈ keys → k ⊆ signedSubfmls φ₀)
    (hstep : modalStepBranchS4KeyedOrdered φ₀ bh e acc keys =
      some (newBs, newBs.map (fun _ => newExp), newAcc, keys')) :
    modalExpMeasure (modalUniverseS4 φ₀) (done ++ newBs ++ bt)
        (doneExp ++ newBs.map (fun _ => newExp) ++ es) + 1
      ≤ modalExpMeasure (modalUniverseS4 φ₀) (done ++ bh :: bt) (doneExp ++ e :: es) := by
  obtain ⟨sf, hsfmem, hsf_ne, hfound⟩ :=
    modalStepBranchS4KeyedOrdered_proj φ₀ bh e acc keys newBs (newBs.map (fun _ => newExp))
      newAcc keys' hstep
  set U := modalUniverseS4 φ₀ with hUdef
  have hrhs : modalExpMeasure U (done ++ bh :: bt) (doneExp ++ e :: es) =
      modalExpMeasure U done doneExp + 3 ^ modalWork U bh e + modalExpMeasure U bt es :=
    modalExpMeasure_split U done doneExp bh e bt es hdlen
  have hlhs : modalExpMeasure U (done ++ newBs ++ bt)
        (doneExp ++ newBs.map (fun _ => newExp) ++ es) =
      modalExpMeasure U done doneExp +
        (newBs.map (fun child => 3 ^ modalWork U child newExp)).sum +
        modalExpMeasure U bt es := by
    have hlen1 : (done ++ newBs).length = (doneExp ++ newBs.map (fun _ => newExp)).length := by
      simp [List.length_append, hdlen]
    rw [modalExpMeasure_append U (done ++ newBs) bt
          (doneExp ++ newBs.map (fun _ => newExp)) es hlen1,
        modalExpMeasure_append U done newBs doneExp (newBs.map (fun _ => newExp)) hdlen,
        modalExpMeasure_const_exp U newBs newExp]
  rw [hrhs, hlhs]
  suffices h : (newBs.map (fun child => 3 ^ modalWork U child newExp)).sum + 1 ≤
      3 ^ modalWork U bh e by omega
  have hany : e.any (· == sf) = false := by
    rw [List.any_eq_false]
    intro x hx heq
    rw [beq_iff_eq] at heq
    subst heq
    exact hsf_ne hx
  have hsfU : sf ∈ U := hb sf hsfmem
  unfold modalStepBranchS4KeyedBody at hfound
  rw [if_neg (by simp [hany])] at hfound
  rcases hpair : modalApplyOneS4Keyed φ₀ keys sf bh acc with ⟨result, newAcc0⟩
  rw [hpair] at hfound
  rcases hres : result with nf | brs | nf | -
  · -- linear
    rw [hres] at hfound
    simp only [Option.map_some] at hfound
    obtain ⟨rfl, hne, -⟩ := Option.some.inj hfound
    have hdrop : modalWork U (nf ++ bh) (e ++ [sf]) + 1 ≤ modalWork U bh e :=
      modalWork_drop_linear U bh (nf ++ bh) e sf hsfU hany
        (fun z hz => List.mem_append_right nf hz)
    have hC : 1 ≤ modalWork U bh e := by omega
    have h0 : modalWork U (nf ++ bh) (e ++ [sf]) ≤ modalWork U bh e - 1 := by omega
    simp only [List.map_singleton, List.sum_singleton]
    exact pow3_add_one_le hC h0
  · -- branching
    have hca : (modalApplyOneS4Keyed φ₀ keys sf bh acc).1 = RuleResult.branching brs := by
      rw [hpair, hres]
    have hlen2 : brs.length = 2 :=
      modalApplyOneS4Keyed_branchingLength_S4 φ₀ keys sf bh acc brs hca
    obtain ⟨b0, b1, hbrs⟩ : ∃ b0 b1, brs = [b0, b1] := by
      match brs, hlen2 with
      | [b0, b1], _ => exact ⟨b0, b1, rfl⟩
    subst hbrs
    rw [hres] at hfound
    simp only [Option.map_some] at hfound
    obtain ⟨rfl, hne, -⟩ := Option.some.inj hfound
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
    have hdrop0 : modalWork U (b0 ++ bh) (e ++ [sf]) + 1 ≤ modalWork U bh e :=
      modalWork_drop_linear U bh (b0 ++ bh) e sf hsfU hany
        (fun z hz => List.mem_append_right b0 hz)
    have hdrop1 : modalWork U (b1 ++ bh) (e ++ [sf]) + 1 ≤ modalWork U bh e :=
      modalWork_drop_linear U bh (b1 ++ bh) e sf hsfU hany
        (fun z hz => List.mem_append_right b1 hz)
    have hC : 1 ≤ modalWork U bh e := by omega
    have h0 : modalWork U (b0 ++ bh) (e ++ [sf]) ≤ modalWork U bh e - 1 := by omega
    have h1 : modalWork U (b1 ++ bh) (e ++ [sf]) ≤ modalWork U bh e - 1 := by omega
    exact pow3_two_add_one_le hC h0 h1
  · -- persistent
    have hca : (modalApplyOneS4Keyed φ₀ keys sf bh acc).1 = RuleResult.persistent nf := by
      rw [hpair, hres]
    rw [hres] at hfound
    simp only [Option.map_some] at hfound
    obtain ⟨rfl, hne, -⟩ := Option.some.inj hfound
    obtain ⟨hnfne, hnffresh⟩ :=
      modalApplyOneS4Keyed_persistentFresh_S4 φ₀ keys sf bh acc nf hca
    obtain ⟨x0, hx0mem⟩ := List.exists_mem_of_ne_nil nf hnfne
    have hclosure := modalApplyOneS4Keyed_outputsSubsetUniverse_S4 φ₀ keys sf bh acc hb hsfmem
      hknown hWC hKT hKD hKI
    rw [hca] at hclosure
    have hx0U : x0 ∈ U := hclosure x0 hx0mem
    have hx0b : x0 ∉ bh := hnffresh x0 hx0mem
    have hx0b' : x0 ∈ nf ++ bh := List.mem_append_left bh hx0mem
    have hdrop : modalWork U (nf ++ bh) newExp + 1 ≤ modalWork U bh newExp :=
      modalWork_drop_persistent U bh (nf ++ bh) newExp x0 hx0U hx0b hx0b'
        (fun z hz => List.mem_append_right nf hz)
    have hC : 1 ≤ modalWork U bh newExp := by omega
    have h0 : modalWork U (nf ++ bh) newExp ≤ modalWork U bh newExp - 1 := by omega
    simp only [List.map_singleton, List.sum_singleton]
    exact pow3_add_one_le hC h0
  · rw [hres] at hfound; simp at hfound

/-! ## Top-Loop Induction — `modalExpandBranchesS4Keyed_hintikka`

Assembles the termination top-loop: an open branch produced by the keyed driver is a Hintikka
set for the live S4 rule. Structural port of `modalExpandBranchesHintikka`
(`CompletenessLoop.lean:1430-1740`) with the per-index invariant taken as the CONJUNCTION
`S4LoopInv ∧ S4KeyedHintikkaInv ∧ keysWorldsKnown ∧ worldsContiguousS4` (there is no single
bundled structure playing `ModalLoopInvHintikka`'s role for the keyed driver, per this file's
deliberate non-bundling), and threading the extra `keys` worklist column throughout. -/

/-- **Local re-derivation** of `CompletenessLoop.lean`'s `private modalStepBranchGen_newExps_const`
(`:515`), specialized to the keyed 4-tuple stepper (dropping the `keys'` component from the
conclusion, which plays no role in the constant-expanded-set fact). Identical case-split proof. -/
private lemma modalStepBranchS4Keyed_newExps_const (φ₀ : Proposition Atom)
    (b e : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (keys : List (WorldIndex × Finset (Sign × Proposition Atom)))
    (newBs newExps : List (List (SignedFormula (Proposition Atom) WorldIndex)))
    (newAcc : Accessibility) (keys' : List (WorldIndex × Finset (Sign × Proposition Atom)))
    (hstep : modalStepBranchS4Keyed φ₀ b e acc keys = some (newBs, newExps, newAcc, keys')) :
    ∃ newExp, newExps = newBs.map (fun _ => newExp) := by
  unfold modalStepBranchS4Keyed at hstep
  obtain ⟨sf, hsfmem, hsf⟩ := List.exists_of_findSome?_eq_some hstep
  split_ifs at hsf with hexp
  rcases hpair : modalApplyOneS4Keyed φ₀ keys sf b acc with ⟨result, newAcc0⟩
  rw [hpair] at hsf
  rcases hres : result with nf | brs | nf | -
  · rw [hres] at hsf
    simp only [Option.some.injEq, Prod.mk.injEq] at hsf
    obtain ⟨rfl, rfl, -, -⟩ := hsf
    exact ⟨e ++ [sf], rfl⟩
  · rw [hres] at hsf
    simp only [Option.some.injEq, Prod.mk.injEq] at hsf
    obtain ⟨rfl, rfl, -, -⟩ := hsf
    exact ⟨e ++ [sf], by simp [List.map_map, Function.comp_def]⟩
  · rw [hres] at hsf
    simp only [Option.some.injEq, Prod.mk.injEq] at hsf
    obtain ⟨rfl, rfl, -, -⟩ := hsf
    exact ⟨e, rfl⟩
  · rw [hres] at hsf; simp at hsf

/-- **Local re-derivation** of the saturated-leaf characterisation
(`modalStepBranchGen_none_saturated`, `Completeness.lean:809`, public but phrased against the
generic 3-tuple driver, hence not directly applicable to the keyed 4-tuple stepper), mirroring
this file's own `findSome?_eq_none_iff` + case-split idiom rather than routing through a
generic-driver projection for the `none` direction. -/
private lemma modalStepBranchS4Keyed_none_saturated (φ₀ : Proposition Atom)
    (b e : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (keys : List (WorldIndex × Finset (Sign × Proposition Atom)))
    (hstep : modalStepBranchS4Keyed φ₀ b e acc keys = none)
    (sf : SignedFormula (Proposition Atom) WorldIndex) (hsfb : sf ∈ b) :
    sf ∈ e ∨ (modalApplyOneS4Keyed φ₀ keys sf b acc).1 = .notApplicable := by
  unfold modalStepBranchS4Keyed at hstep
  rw [List.findSome?_eq_none_iff] at hstep
  have hbody := hstep sf hsfb
  by_cases hany : e.any (· == sf) = true
  · left
    simp only [List.any_eq_true] at hany
    obtain ⟨sf', hme, heq⟩ := hany
    simp only [beq_iff_eq] at heq
    exact heq ▸ hme
  · right
    simp only [Bool.not_eq_true] at hany
    simp only [hany] at hbody
    rcases hca : modalApplyOneS4Keyed φ₀ keys sf b acc with ⟨res, newAcc0⟩
    simp only [hca] at hbody
    rcases res with out | brs | out | _
    · exact absurd hbody (by simp)
    · exact absurd hbody (by simp)
    · exact absurd hbody (by simp)
    · rfl

/-- **Ordered twin** of `modalStepBranchS4Keyed_none_saturated`. Transfers the saturated-leaf
characterisation from the unordered keyed stepper to the ordered one via
`modalStepBranchS4KeyedOrdered_eq_none_iff` (`S4/Driver.lean:678`), whose own docstring records
that this transfer is exactly what it was written to enable: "lets later phases — the saturation
step in particular — transfer facts about the old stepper's termination condition to the new one
without re-deriving anything". -/
private lemma modalStepBranchS4KeyedOrdered_none_saturated (φ₀ : Proposition Atom)
    (b e : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (keys : List (WorldIndex × Finset (Sign × Proposition Atom)))
    (hstep : modalStepBranchS4KeyedOrdered φ₀ b e acc keys = none)
    (sf : SignedFormula (Proposition Atom) WorldIndex) (hsfb : sf ∈ b) :
    sf ∈ e ∨ (modalApplyOneS4Keyed φ₀ keys sf b acc).1 = .notApplicable :=
  modalStepBranchS4Keyed_none_saturated φ₀ b e acc keys
    ((modalStepBranchS4KeyedOrdered_eq_none_iff φ₀ b e acc keys).mp hstep) sf hsfb

/-- **Structural fact**: whenever `modalStepBranchS4KeyedOrdered` steps, the returned `newExps`
column is CONSTANT across `newBs` -- every one of the four `RuleResult` arms produces `newExps`
as either a genuine singleton (matching `newBs`'s own singleton) or a `branches.map (fun _ => ...)`
constant map post-composed with `newBs = branches.map (· ++ b)`, and `List.map_map` collapses the
composition back to the same constant map over `branches`. This is what licenses transporting an
existential `b' ∈ newBs` witness to a matching `newExps` entry without ever pinning down an
index.

**Relocated** from `FrameCompleteness.lean` so that the ordered top-loop Hintikka lemma (which
lives here, below `FrameCompleteness` in the import order) can consume it. Pure move, no proof
edit; the original call site at `FrameCompleteness.lean:8164`-adjacent continues to resolve via
`FrameCompleteness.lean`'s public import of this module. -/
lemma modalStepBranchS4KeyedOrdered_newExps_eq_map (φ₀ : Proposition Atom)
    (b e : List (SignedFormula (Proposition Atom) WorldIndex)) (acc : Accessibility)
    (keys : List (WorldIndex × Finset (Sign × Proposition Atom)))
    (newBs newExps : List (List (SignedFormula (Proposition Atom) WorldIndex)))
    (newAcc : Accessibility) (keys' : List (WorldIndex × Finset (Sign × Proposition Atom)))
    (hstep : modalStepBranchS4KeyedOrdered φ₀ b e acc keys =
      some (newBs, newExps, newAcc, keys')) :
    ∃ e'0, newExps = newBs.map (fun _ => e'0) := by
  rcases modalStepBranchS4KeyedOrdered_cases φ₀ b e acc keys newBs newExps newAcc keys' hstep with
    ⟨sf, hcand, hbody⟩ | ⟨-, hfallback⟩
  · have hsfnote := modalNonMintCandidates_not_mem_expanded φ₀ keys b e acc sf hcand
    have hany : e.any (· == sf) = false := by
      rw [List.any_eq_false]
      intro x hx heq
      rw [beq_iff_eq] at heq
      subst heq
      exact hsfnote hx
    unfold modalStepBranchS4KeyedBody at hbody
    rw [if_neg (by simp [hany])] at hbody
    rcases hpair : modalApplyOneS4Keyed φ₀ keys sf b acc with ⟨result, newAcc0⟩
    rw [hpair] at hbody
    dsimp only at hbody
    rcases result with nf | brs | nf | -
    · simp only [Option.some.injEq, Prod.mk.injEq] at hbody
      obtain ⟨rfl, rfl, -, -⟩ := hbody
      exact ⟨e ++ [sf], rfl⟩
    · simp only [Option.some.injEq, Prod.mk.injEq] at hbody
      obtain ⟨rfl, rfl, -, -⟩ := hbody
      exact ⟨e ++ [sf], by rw [List.map_map]; rfl⟩
    · simp only [Option.some.injEq, Prod.mk.injEq] at hbody
      obtain ⟨rfl, rfl, -, -⟩ := hbody
      exact ⟨e, rfl⟩
    · simp at hbody
  · unfold modalStepBranchS4Keyed at hfallback
    obtain ⟨sf, -, hsf⟩ := List.exists_of_findSome?_eq_some hfallback
    by_cases hany : e.any (· == sf) = true
    · rw [if_pos hany] at hsf
      simp at hsf
    · rw [if_neg hany] at hsf
      rcases hpair : modalApplyOneS4Keyed φ₀ keys sf b acc with ⟨result, newAcc0⟩
      rw [hpair] at hsf
      dsimp only at hsf
      rcases result with nf | brs | nf | -
      · simp only [Option.some.injEq, Prod.mk.injEq] at hsf
        obtain ⟨rfl, rfl, -, -⟩ := hsf
        exact ⟨e ++ [sf], rfl⟩
      · simp only [Option.some.injEq, Prod.mk.injEq] at hsf
        obtain ⟨rfl, rfl, -, -⟩ := hsf
        exact ⟨e ++ [sf], by rw [List.map_map]; rfl⟩
      · simp only [Option.some.injEq, Prod.mk.injEq] at hsf
        obtain ⟨rfl, rfl, -, -⟩ := hsf
        exact ⟨e, rfl⟩
      · simp at hsf

set_option maxHeartbeats 1000000 in
-- `maxHeartbeats` raised: Phase 8's move to upstream `HasBox`/`HasImp`/`HasDiamond` notation
-- (`Cslib.Foundations.Logic.Operators`) adds a typeclass-projection layer that `isDefEq` must
-- unfold at every occurrence of `□`/`→`/`◇` inside this large nested-induction motive, which
-- pushed elaboration past the default 200000-heartbeat budget. The proof itself is unchanged.
/-- **The keyed top-loop Hintikka lemma**: an open branch produced by
`modalExpandBranchesS4Keyed` is a Hintikka set for the LIVE S4 rule `modalApplyOneS4 φ₀`
(bridged from the keyed rule via `hintikka_congr_S4`/`modalHintikkaSetS4_eq` at the very end).
Per-index hypothesis is the conjunction `S4LoopInv ∧ S4KeyedHintikkaInv ∧ keysWorldsKnown ∧
worldsContiguousS4` (no single bundled structure plays `ModalLoopInvHintikka`'s role here, per
the same deliberate non-bundling); an extra `keyss` worklist column is threaded alongside
`branches`/`expandedSets`/`accs` throughout, mirroring `modalExpandBranchesS4Keyed`'s own
`keyss`/`pendingKeys`/`doneKeys` bookkeeping. Structural port of `modalExpandBranchesHintikka`
(`CompletenessLoop.lean:1430-1740`). -/
theorem modalExpandBranchesS4Keyed_hintikka (φ₀ : Proposition Atom) (fuel : Nat) :
    ∀ (branches expandedSets : List (List (SignedFormula (Proposition Atom) WorldIndex)))
      (accs : List Accessibility)
      (keyss : List (List (WorldIndex × Finset (Sign × Proposition Atom)))),
      expandedSets.length = branches.length →
      accs.length = branches.length →
      keyss.length = branches.length →
      modalExpMeasure (modalUniverseS4 φ₀) branches expandedSets ≤ fuel →
      (∀ (i : Nat) (bi ei : List (SignedFormula (Proposition Atom) WorldIndex))
          (ai : Accessibility) (keysi : List (WorldIndex × Finset (Sign × Proposition Atom))),
        branches[i]? = some bi → expandedSets[i]? = some ei → accs[i]? = some ai →
        keyss[i]? = some keysi →
        S4LoopInv φ₀ bi ei ai keysi ∧ S4KeyedHintikkaInv φ₀ bi ei ai keysi ∧
          (∀ w k, (w, k) ∈ keysi → w ∈ modalKnownWorlds bi) ∧ worldsContiguousS4 bi) →
      ∀ (bR : List (SignedFormula (Proposition Atom) WorldIndex)) (aR : Accessibility),
        modalExpandBranchesS4Keyed φ₀ branches expandedSets accs keyss fuel = .openBranch bR aR →
        modalHintikkaSetS4 φ₀ bR aR := by
  induction fuel with
  | zero =>
    intro branches expandedSets accs keyss hlen hlenA hlenK hfuel _hInv bR aR h
    have hm : modalExpMeasure (modalUniverseS4 φ₀) branches expandedSets = 0 :=
      Nat.le_zero.mp hfuel
    have hbranches : branches = [] := by
      rcases branches with _ | ⟨bh, bt⟩
      · rfl
      · exfalso
        rcases expandedSets with _ | ⟨e, es⟩
        · simp only [List.length_nil, List.length_cons] at hlen; omega
        · simp only [modalExpMeasure, List.zip_cons_cons, List.map_cons, List.sum_cons] at hm
          have h3 := Nat.one_le_pow (modalWork (modalUniverseS4 φ₀) bh e) 3 (by omega)
          omega
    subst hbranches
    simp [modalExpandBranchesS4Keyed] at h
  | succ fuel' ih =>
    intro branches expandedSets accs keyss hlen hlenA hlenK hfuel hInv bR aR h
    simp only [modalExpandBranchesS4Keyed] at h
    suffices key : ∀ (pending pendingExp :
          List (List (SignedFormula (Proposition Atom) WorldIndex)))
        (pendingAccs : List Accessibility)
        (pendingKeys : List (List (WorldIndex × Finset (Sign × Proposition Atom))))
        (done doneExp : List (List (SignedFormula (Proposition Atom) WorldIndex)))
        (doneAccs : List Accessibility)
        (doneKeys : List (List (WorldIndex × Finset (Sign × Proposition Atom)))),
        pendingExp.length = pending.length →
        pendingAccs.length = pending.length →
        pendingKeys.length = pending.length →
        doneExp.length = done.length →
        doneAccs.length = done.length →
        doneKeys.length = done.length →
        (∀ (i : Nat) (bi ei : List (SignedFormula (Proposition Atom) WorldIndex))
            (ai : Accessibility) (keysi : List (WorldIndex × Finset (Sign × Proposition Atom))),
          (done ++ pending)[i]? = some bi → (doneExp ++ pendingExp)[i]? = some ei →
          (doneAccs ++ pendingAccs)[i]? = some ai → (doneKeys ++ pendingKeys)[i]? = some keysi →
          S4LoopInv φ₀ bi ei ai keysi ∧ S4KeyedHintikkaInv φ₀ bi ei ai keysi ∧
            (∀ w k, (w, k) ∈ keysi → w ∈ modalKnownWorlds bi) ∧ worldsContiguousS4 bi) →
        modalExpMeasure (modalUniverseS4 φ₀) (done ++ pending) (doneExp ++ pendingExp) ≤
          fuel' + 1 →
        modalExpandBranchesS4Keyed.processNext φ₀ fuel' pending pendingExp pendingAccs pendingKeys
            done doneExp doneAccs doneKeys = .openBranch bR aR →
        modalHintikkaSetS4 φ₀ bR aR from
      key branches expandedSets accs keyss [] [] [] [] hlen hlenA hlenK rfl rfl rfl hInv hfuel
        (by simpa [modalExpandBranchesS4Keyed] using h)
    intro pending
    induction pending with
    | nil =>
      intro pendingExp pendingAccs pendingKeys done doneExp doneAccs doneKeys
        _ _ _ _ _ _ _ _ hinner
      simp [modalExpandBranchesS4Keyed.processNext] at hinner
    | cons bh bt ih_inner =>
      intro pendingExp pendingAccs pendingKeys done doneExp doneAccs doneKeys
        hlength_p hlenP_accs hlenP_keys hdlength hdAccs hdKeys hInv_all hmeas hinner
      cases pendingAccs with
      | nil => simp at hlenP_accs
      | cons a restAs =>
        cases pendingExp with
        | nil => simp at hlength_p
        | cons e es =>
          cases pendingKeys with
          | nil => simp at hlenP_keys
          | cons k restKs =>
            simp only [List.length_cons, Nat.add_right_cancel_iff]
              at hlength_p hlenP_accs hlenP_keys
            simp only [modalExpandBranchesS4Keyed.processNext] at hinner
            by_cases hcl : isModalClosed bh = true
            · -- Closed branch: skip and recurse on the inner induction
              rw [if_pos hcl] at hinner
              apply ih_inner es restAs restKs (done ++ [bh]) (doneExp ++ [e]) (doneAccs ++ [a])
                (doneKeys ++ [k])
              · simpa using hlength_p
              · simpa using hlenP_accs
              · simpa using hlenP_keys
              · simp [hdlength]
              · simp [hdAccs]
              · simp [hdKeys]
              · intro i bi ei ai keysi hib hie hia hik
                apply hInv_all i bi ei ai keysi
                · convert hib using 2; simp
                · convert hie using 2; simp
                · convert hia using 2; simp
                · convert hik using 2; simp
              · convert hmeas using 2 <;> simp
              · exact hinner
            · simp only [Bool.not_eq_true] at hcl
              rw [if_neg (by simp [hcl])] at hinner
              cases hstep : modalStepBranchS4Keyed φ₀ bh e a k with
              | none =>
                -- Saturated open branch: bh/a are the returned bR/aR.
                rw [hstep] at hinner
                obtain ⟨hbeq, haeq⟩ : bh = bR ∧ a = aR := by
                  cases hinner; exact ⟨rfl, rfl⟩
                have hbeq' : bR = bh := hbeq.symm
                have haeq' : aR = a := haeq.symm
                subst hbeq'; subst haeq'
                have hbh_idx : (done ++ bR :: bt)[done.length]? = some bR := by
                  rw [List.getElem?_append_right (Nat.le_refl done.length)]; simp
                have he_idx : (doneExp ++ e :: es)[done.length]? = some e := by
                  rw [List.getElem?_append_right (by omega)]; simp [hdlength]
                have ha_idx : (doneAccs ++ aR :: restAs)[done.length]? = some aR := by
                  rw [List.getElem?_append_right (by omega)]; simp [hdAccs]
                have hk_idx : (doneKeys ++ k :: restKs)[done.length]? = some k := by
                  rw [List.getElem?_append_right (by omega)]; simp [hdKeys]
                obtain ⟨hLoopInv, hHinv, -, -⟩ :=
                  hInv_all done.length bR e aR k hbh_idx he_idx ha_idx hk_idx
                rw [modalHintikkaSetS4_eq, ← hintikka_congr_S4 φ₀ k]
                refine ⟨hcl, ?_, ?_, ?_⟩
                · -- Conjunct 2: rule-application clause for every sf ∈ bR
                  intro sf hsfmem
                  obtain ⟨s, φ, l⟩ := sf
                  cases φ with
                  | atom p =>
                    rcases modalStepBranchS4Keyed_none_saturated φ₀ bR e aR k hstep
                        ⟨s, .atom p, l⟩ hsfmem with hine | hna
                    · have hc := hHinv.hintikkaInv ⟨s, .atom p, l⟩ hine
                      simp only [modalHintikkaClauseGen] at hc
                      cases s <;> exact hc
                    · cases s <;> simp [hna]
                  | bot =>
                    rcases modalStepBranchS4Keyed_none_saturated φ₀ bR e aR k hstep
                        ⟨s, .bot, l⟩ hsfmem with hine | hna
                    · have hc := hHinv.hintikkaInv ⟨s, .bot, l⟩ hine
                      simp only [modalHintikkaClauseGen] at hc
                      cases s <;> exact hc
                    · cases s <;> simp [hna]
                  | imp a c =>
                    rcases modalStepBranchS4Keyed_none_saturated φ₀ bR e aR k hstep
                        ⟨s, .imp a c, l⟩ hsfmem with hine | hna
                    · have hc := hHinv.hintikkaInv ⟨s, .imp a c, l⟩ hine
                      simp only [modalHintikkaClauseGen] at hc
                      cases s <;> exact hc
                    · cases s <;> simp [hna]
                  | and a c =>
                    rcases modalStepBranchS4Keyed_none_saturated φ₀ bR e aR k hstep
                        ⟨s, .and a c, l⟩ hsfmem with hine | hna
                    · have hc := hHinv.hintikkaInv ⟨s, .and a c, l⟩ hine
                      simp only [modalHintikkaClauseGen] at hc
                      cases s <;> exact hc
                    · cases s <;> simp [hna]
                  | or a c =>
                    rcases modalStepBranchS4Keyed_none_saturated φ₀ bR e aR k hstep
                        ⟨s, .or a c, l⟩ hsfmem with hine | hna
                    · have hc := hHinv.hintikkaInv ⟨s, .or a c, l⟩ hine
                      simp only [modalHintikkaClauseGen] at hc
                      cases s <;> exact hc
                    · cases s <;> simp [hna]
                  | box ψ' =>
                    cases s with
                    | pos =>
                      rcases modalStepBranchS4Keyed_none_saturated φ₀ bR e aR k hstep
                          ⟨.pos, .box ψ', l⟩ hsfmem with hine | hna
                      · exact absurd (hHinv.eBoxOnlyNeg ⟨.pos, .box ψ', l⟩ hine ψ' rfl) (by simp)
                      · simp [hna]
                    | neg => trivial
                  | diamond ψ' =>
                    cases s with
                    | pos => trivial
                    | neg =>
                      rcases modalStepBranchS4Keyed_none_saturated φ₀ bR e aR k hstep
                          ⟨.neg, .diamond ψ', l⟩ hsfmem with hine | hna
                      · exact absurd (hHinv.eDiamondOnlyPos ⟨.neg, .diamond ψ', l⟩ hine ψ' rfl)
                          (by simp)
                      · simp [hna]
                · -- Conjunct 3: box-negative witness existence
                  intro ψ' w hmem
                  rcases modalStepBranchS4Keyed_none_saturated φ₀ bR e aR k hstep _ hmem
                      with hine | hna
                  · exact hHinv.eBoxNegWitness _ hine ψ' w rfl
                  · exact absurd hna (modalApplyOneS4Keyed_boxNeg_ne_notApplicable φ₀ k bR aR ψ' w)
                · -- Conjunct 4: diamond-positive witness existence (symmetric to Conjunct 3)
                  intro ψ' w hmem
                  rcases modalStepBranchS4Keyed_none_saturated φ₀ bR e aR k hstep _ hmem
                      with hine | hna
                  · exact hHinv.eDiamondPosWitness _ hine ψ' w rfl
                  · exact
                      absurd hna (modalApplyOneS4Keyed_diaPos_ne_notApplicable φ₀ k bR aR ψ' w)
              | some step =>
                obtain ⟨newBs, newExps, newAcc, keys'⟩ := step
                rw [hstep] at hinner
                have hstepEq :
                    modalStepBranchS4Keyed φ₀ bh e a k = some (newBs, newExps, newAcc, keys') :=
                  hstep
                have hbh_idx : (done ++ bh :: bt)[done.length]? = some bh := by
                  rw [List.getElem?_append_right (Nat.le_refl done.length)]; simp
                have he_idx : (doneExp ++ e :: es)[done.length]? = some e := by
                  rw [List.getElem?_append_right (by omega)]; simp [hdlength]
                have ha_idx : (doneAccs ++ a :: restAs)[done.length]? = some a := by
                  rw [List.getElem?_append_right (by omega)]; simp [hdAccs]
                have hk_idx : (doneKeys ++ k :: restKs)[done.length]? = some k := by
                  rw [List.getElem?_append_right (by omega)]; simp [hdKeys]
                obtain ⟨hLoopInv, hHinv, hKW, hWC⟩ :=
                  hInv_all done.length bh e a k hbh_idx he_idx ha_idx hk_idx
                obtain ⟨newExp, hNewExpEq⟩ :=
                  modalStepBranchS4Keyed_newExps_const φ₀ bh e a k newBs newExps newAcc keys'
                    hstepEq
                subst hNewExpEq
                have hstepEq' : modalStepBranchS4Keyed φ₀ bh e a k =
                    some (newBs, newBs.map (fun _ => newExp), newAcc, keys') := hstepEq
                obtain ⟨hLoopInvAll, hKWAll, hWCAll⟩ :=
                  modalStepBranchS4_preserves_S4LoopInv φ₀ bh e a k newBs
                    (newBs.map (fun _ => newExp)) newAcc keys' hLoopInv hKW hWC hstepEq'
                have hHinvAll :=
                  modalStepBranchS4Keyed_preserves_S4KeyedHintikkaInv φ₀ bh e a k newBs
                    (newBs.map (fun _ => newExp)) newAcc keys' hLoopInv hHinv hstepEq'
                have hstep_lt := modalExpMeasure_step_lt_S4Keyed φ₀ k keys' done bt newBs
                  doneExp es newExp bh e a newAcc hdlength.symm hLoopInv.bClosure
                  hLoopInv.accKnown hWC hLoopInv.keysTotal hLoopInv.keysDistinct
                  hLoopInv.keysInUniverse hstepEq'
                apply ih (done ++ newBs ++ bt) (doneExp ++ newBs.map (fun _ => newExp) ++ es)
                  (doneAccs ++ List.replicate newBs.length newAcc ++ restAs)
                  (doneKeys ++ List.replicate newBs.length keys' ++ restKs)
                · simp only [List.length_append, List.length_map, hdlength]
                  omega
                · simp only [List.length_append, List.length_replicate, hdAccs]
                  omega
                · simp only [List.length_append, List.length_replicate, hdKeys]
                  omega
                · omega
                · intro i bi ei ai keysi hib hie hia hik
                  rcases Nat.lt_or_ge i done.length with hlt1 | hge1
                  · apply hInv_all i bi ei ai keysi
                    · rw [List.append_assoc, List.getElem?_append_left hlt1] at hib
                      rwa [List.getElem?_append_left hlt1]
                    · rw [List.append_assoc, List.getElem?_append_left (by omega)] at hie
                      rwa [List.getElem?_append_left (by omega)]
                    · rw [List.append_assoc, List.getElem?_append_left (by omega)] at hia
                      rwa [List.getElem?_append_left (by omega)]
                    · rw [List.append_assoc, List.getElem?_append_left (by omega)] at hik
                      rwa [List.getElem?_append_left (by omega)]
                  · rcases Nat.lt_or_ge i (done.length + newBs.length) with hlt2 | hge2
                    · -- Region: newBs (all sharing newExp/newAcc/keys')
                      have hj : i - done.length < newBs.length := by omega
                      have hbi_newBs : newBs[i - done.length]? = some bi := by
                        rw [List.append_assoc, List.getElem?_append_right hge1] at hib
                        rwa [List.getElem?_append_left hj] at hib
                      have hbi_mem : bi ∈ newBs := List.mem_of_getElem? hbi_newBs
                      have hei_eq : ei = newExp := by
                        rw [List.append_assoc,
                            List.getElem?_append_right (by omega : doneExp.length ≤ i)] at hie
                        rw [List.getElem?_append_left
                              (by simp only [List.length_map]; omega)] at hie
                        rw [List.getElem?_map,
                            show newBs[i - doneExp.length]? = some bi from by
                              rw [show i - doneExp.length = i - done.length from by omega]
                              exact hbi_newBs] at hie
                        simp only [Option.map_some, Option.some.injEq] at hie
                        exact hie.symm
                      have hei_eq' : newExp = ei := hei_eq.symm
                      subst hei_eq'
                      have hai_eq : ai = newAcc := by
                        rw [List.append_assoc,
                            List.getElem?_append_right (by omega : doneAccs.length ≤ i)] at hia
                        rw [List.getElem?_append_left
                              (by simp only [List.length_replicate]; omega)] at hia
                        exact List.eq_of_mem_replicate (List.mem_of_getElem? hia)
                      subst hai_eq
                      have hkeysi_eq : keysi = keys' := by
                        rw [List.append_assoc,
                            List.getElem?_append_right (by omega : doneKeys.length ≤ i)] at hik
                        rw [List.getElem?_append_left
                              (by simp only [List.length_replicate]; omega)] at hik
                        exact List.eq_of_mem_replicate (List.mem_of_getElem? hik)
                      subst hkeysi_eq
                      have hnewExp_mem : newExp ∈ newBs.map (fun _ => newExp) :=
                        List.mem_map.mpr ⟨bi, hbi_mem, rfl⟩
                      exact ⟨hLoopInvAll bi hbi_mem newExp hnewExp_mem,
                        hHinvAll bi hbi_mem newExp hnewExp_mem, hKWAll bi hbi_mem,
                        hWCAll bi hbi_mem⟩
                    · -- Region: bt (shifted index)
                      have hbi_bt : bt[i - done.length - newBs.length]? = some bi := by
                        rw [List.append_assoc, List.getElem?_append_right hge1] at hib
                        rw [List.getElem?_append_right
                              (by omega : newBs.length ≤ i - done.length)] at hib
                        exact hib
                      have hei_es : es[i - done.length - newBs.length]? = some ei := by
                        rw [List.append_assoc,
                            List.getElem?_append_right (by omega : doneExp.length ≤ i)] at hie
                        rw [List.getElem?_append_right
                              (by simp only [List.length_map]; omega :
                                (newBs.map (fun _ => newExp)).length ≤ i - doneExp.length)] at hie
                        rwa [show i - doneExp.length - (newBs.map (fun _ => newExp)).length =
                              i - done.length - newBs.length from by
                            simp only [List.length_map]; omega] at hie
                      have hai_restAs : restAs[i - done.length - newBs.length]? = some ai := by
                        rw [List.append_assoc, List.getElem?_append_right (by omega :
                              doneAccs.length ≤ i)] at hia
                        rw [List.getElem?_append_right
                              (by simp only [List.length_replicate]; omega :
                                (List.replicate newBs.length newAcc).length ≤
                                  i - doneAccs.length)] at hia
                        rwa [show i - doneAccs.length -
                              (List.replicate newBs.length newAcc).length =
                              i - done.length - newBs.length from by
                            simp only [List.length_replicate]; omega] at hia
                      have hki_restKs : restKs[i - done.length - newBs.length]? = some keysi := by
                        rw [List.append_assoc, List.getElem?_append_right (by omega :
                              doneKeys.length ≤ i)] at hik
                        rw [List.getElem?_append_right
                              (by simp only [List.length_replicate]; omega :
                                (List.replicate newBs.length keys').length ≤
                                  i - doneKeys.length)] at hik
                        rwa [show i - doneKeys.length -
                              (List.replicate newBs.length keys').length =
                              i - done.length - newBs.length from by
                            simp only [List.length_replicate]; omega] at hik
                      apply hInv_all (done.length + 1 + (i - done.length - newBs.length)) bi ei ai
                        keysi
                      · rw [List.getElem?_append_right
                              (by omega : done.length ≤
                                done.length + 1 + (i - done.length - newBs.length))]
                        rw [show done.length + 1 + (i - done.length - newBs.length) - done.length
                              = (i - done.length - newBs.length) + 1 from by omega]
                        rw [List.getElem?_cons_succ]; exact hbi_bt
                      · rw [List.getElem?_append_right
                              (by omega : doneExp.length ≤
                                done.length + 1 + (i - done.length - newBs.length))]
                        rw [show done.length + 1 + (i - done.length - newBs.length) -
                              doneExp.length = (i - done.length - newBs.length) + 1 from by omega]
                        rw [List.getElem?_cons_succ]; exact hei_es
                      · rw [List.getElem?_append_right
                              (by omega : doneAccs.length ≤
                                done.length + 1 + (i - done.length - newBs.length))]
                        rw [show done.length + 1 + (i - done.length - newBs.length) -
                              doneAccs.length = (i - done.length - newBs.length) + 1 from by omega]
                        rw [List.getElem?_cons_succ]; exact hai_restAs
                      · rw [List.getElem?_append_right
                              (by omega : doneKeys.length ≤
                                done.length + 1 + (i - done.length - newBs.length))]
                        rw [show done.length + 1 + (i - done.length - newBs.length) -
                              doneKeys.length = (i - done.length - newBs.length) + 1 from by omega]
                        rw [List.getElem?_cons_succ]; exact hki_restKs
                · exact hinner

/-! ## Ordered Top-Loop Induction — `modalExpandBranchesS4KeyedOrdered_hintikka`

Structural port of `modalExpandBranchesS4Keyed_hintikka` above to the ordered driver
`modalExpandBranchesS4KeyedOrdered`. Uses the bundled `S4OrderedFuelInv` as the per-index
hypothesis and `modalStepBranchS4KeyedOrdered_preserves_S4OrderedFuelInv` as the single step
lemma, in place of the unordered proof's separate `_preserves_S4LoopInv` /
`_preserves_S4KeyedHintikkaInv` invocations -- strictly less bookkeeping, since the step lemma's
conclusion is already the exact `S4OrderedFuelInv` shape the `newBs`-region goal needs, with no
four-way reassembly required. -/

/-- **The ordered keyed top-loop Hintikka lemma**: an open branch produced by
`modalExpandBranchesS4KeyedOrdered` is a Hintikka set for the LIVE S4 rule `modalApplyOneS4 φ₀`
(bridged from the keyed rule via `hintikka_congr_S4`/`modalHintikkaSetS4_eq` at the very end, both
driver-independent and reused verbatim). Per-index hypothesis is the bundled `S4OrderedFuelInv`
(`S4LoopInv ∧ S4KeyedHintikkaInv ∧ keysWorldsKnown ∧ worldsContiguousS4 ∧ keysOriginS4`); an extra
`keyss` worklist column is threaded alongside `branches`/`expandedSets`/`accs` throughout,
mirroring `modalExpandBranchesS4KeyedOrdered`'s own `keyss`/`pendingKeys`/`doneKeys` bookkeeping.
Structural port of `modalExpandBranchesS4Keyed_hintikka` above, substituting the ordered stepper
and its already-landed ordered analogues throughout. -/
theorem modalExpandBranchesS4KeyedOrdered_hintikka (φ₀ : Proposition Atom) (fuel : Nat) :
    ∀ (branches expandedSets : List (List (SignedFormula (Proposition Atom) WorldIndex)))
      (accs : List Accessibility)
      (keyss : List (List (WorldIndex × Finset (Sign × Proposition Atom)))),
      expandedSets.length = branches.length →
      accs.length = branches.length →
      keyss.length = branches.length →
      modalExpMeasure (modalUniverseS4 φ₀) branches expandedSets ≤ fuel →
      (∀ (i : Nat) (bi ei : List (SignedFormula (Proposition Atom) WorldIndex))
          (ai : Accessibility) (keysi : List (WorldIndex × Finset (Sign × Proposition Atom))),
        branches[i]? = some bi → expandedSets[i]? = some ei → accs[i]? = some ai →
        keyss[i]? = some keysi →
        S4OrderedFuelInv φ₀ bi ei ai keysi) →
      ∀ (bR : List (SignedFormula (Proposition Atom) WorldIndex)) (aR : Accessibility),
        modalExpandBranchesS4KeyedOrdered φ₀ branches expandedSets accs keyss fuel =
          .openBranch bR aR →
        modalHintikkaSetS4 φ₀ bR aR := by
  induction fuel with
  | zero =>
    intro branches expandedSets accs keyss hlen hlenA hlenK hfuel _hInv bR aR h
    have hm : modalExpMeasure (modalUniverseS4 φ₀) branches expandedSets = 0 :=
      Nat.le_zero.mp hfuel
    have hbranches : branches = [] := by
      rcases branches with _ | ⟨bh, bt⟩
      · rfl
      · exfalso
        rcases expandedSets with _ | ⟨e, es⟩
        · simp only [List.length_nil, List.length_cons] at hlen; omega
        · simp only [modalExpMeasure, List.zip_cons_cons, List.map_cons, List.sum_cons] at hm
          have h3 := Nat.one_le_pow (modalWork (modalUniverseS4 φ₀) bh e) 3 (by omega)
          omega
    subst hbranches
    simp [modalExpandBranchesS4KeyedOrdered] at h
  | succ fuel' ih =>
    intro branches expandedSets accs keyss hlen hlenA hlenK hfuel hInv bR aR h
    simp only [modalExpandBranchesS4KeyedOrdered] at h
    suffices key : ∀ (pending pendingExp :
          List (List (SignedFormula (Proposition Atom) WorldIndex)))
        (pendingAccs : List Accessibility)
        (pendingKeys : List (List (WorldIndex × Finset (Sign × Proposition Atom))))
        (done doneExp : List (List (SignedFormula (Proposition Atom) WorldIndex)))
        (doneAccs : List Accessibility)
        (doneKeys : List (List (WorldIndex × Finset (Sign × Proposition Atom)))),
        pendingExp.length = pending.length →
        pendingAccs.length = pending.length →
        pendingKeys.length = pending.length →
        doneExp.length = done.length →
        doneAccs.length = done.length →
        doneKeys.length = done.length →
        (∀ (i : Nat) (bi ei : List (SignedFormula (Proposition Atom) WorldIndex))
            (ai : Accessibility) (keysi : List (WorldIndex × Finset (Sign × Proposition Atom))),
          (done ++ pending)[i]? = some bi → (doneExp ++ pendingExp)[i]? = some ei →
          (doneAccs ++ pendingAccs)[i]? = some ai → (doneKeys ++ pendingKeys)[i]? = some keysi →
          S4OrderedFuelInv φ₀ bi ei ai keysi) →
        modalExpMeasure (modalUniverseS4 φ₀) (done ++ pending) (doneExp ++ pendingExp) ≤
          fuel' + 1 →
        modalExpandBranchesS4KeyedOrdered.processNext φ₀ fuel' pending pendingExp pendingAccs
            pendingKeys done doneExp doneAccs doneKeys = .openBranch bR aR →
        modalHintikkaSetS4 φ₀ bR aR from
      key branches expandedSets accs keyss [] [] [] [] hlen hlenA hlenK rfl rfl rfl hInv hfuel
        (by simpa [modalExpandBranchesS4KeyedOrdered] using h)
    intro pending
    induction pending with
    | nil =>
      intro pendingExp pendingAccs pendingKeys done doneExp doneAccs doneKeys
        _ _ _ _ _ _ _ _ hinner
      simp [modalExpandBranchesS4KeyedOrdered.processNext] at hinner
    | cons bh bt ih_inner =>
      intro pendingExp pendingAccs pendingKeys done doneExp doneAccs doneKeys
        hlength_p hlenP_accs hlenP_keys hdlength hdAccs hdKeys hInv_all hmeas hinner
      cases pendingAccs with
      | nil => simp at hlenP_accs
      | cons a restAs =>
        cases pendingExp with
        | nil => simp at hlength_p
        | cons e es =>
          cases pendingKeys with
          | nil => simp at hlenP_keys
          | cons k restKs =>
            simp only [List.length_cons, Nat.add_right_cancel_iff]
              at hlength_p hlenP_accs hlenP_keys
            simp only [modalExpandBranchesS4KeyedOrdered.processNext] at hinner
            by_cases hcl : isModalClosed bh = true
            · -- Closed branch: skip and recurse on the inner induction
              rw [if_pos hcl] at hinner
              apply ih_inner es restAs restKs (done ++ [bh]) (doneExp ++ [e]) (doneAccs ++ [a])
                (doneKeys ++ [k])
              · simpa using hlength_p
              · simpa using hlenP_accs
              · simpa using hlenP_keys
              · simp [hdlength]
              · simp [hdAccs]
              · simp [hdKeys]
              · intro i bi ei ai keysi hib hie hia hik
                apply hInv_all i bi ei ai keysi
                · convert hib using 2; simp
                · convert hie using 2; simp
                · convert hia using 2; simp
                · convert hik using 2; simp
              · convert hmeas using 2 <;> simp
              · exact hinner
            · simp only [Bool.not_eq_true] at hcl
              rw [if_neg (by simp [hcl])] at hinner
              cases hstep : modalStepBranchS4KeyedOrdered φ₀ bh e a k with
              | none =>
                -- Saturated open branch: bh/a are the returned bR/aR.
                rw [hstep] at hinner
                obtain ⟨hbeq, haeq⟩ : bh = bR ∧ a = aR := by
                  cases hinner; exact ⟨rfl, rfl⟩
                have hbeq' : bR = bh := hbeq.symm
                have haeq' : aR = a := haeq.symm
                subst hbeq'; subst haeq'
                have hbh_idx : (done ++ bR :: bt)[done.length]? = some bR := by
                  rw [List.getElem?_append_right (Nat.le_refl done.length)]; simp
                have he_idx : (doneExp ++ e :: es)[done.length]? = some e := by
                  rw [List.getElem?_append_right (by omega)]; simp [hdlength]
                have ha_idx : (doneAccs ++ aR :: restAs)[done.length]? = some aR := by
                  rw [List.getElem?_append_right (by omega)]; simp [hdAccs]
                have hk_idx : (doneKeys ++ k :: restKs)[done.length]? = some k := by
                  rw [List.getElem?_append_right (by omega)]; simp [hdKeys]
                obtain ⟨hLoopInv, hHinv, -, -, -⟩ :=
                  hInv_all done.length bR e aR k hbh_idx he_idx ha_idx hk_idx
                rw [modalHintikkaSetS4_eq, ← hintikka_congr_S4 φ₀ k]
                refine ⟨hcl, ?_, ?_, ?_⟩
                · -- Conjunct 2: rule-application clause for every sf ∈ bR
                  intro sf hsfmem
                  obtain ⟨s, φ, l⟩ := sf
                  cases φ with
                  | atom p =>
                    rcases modalStepBranchS4KeyedOrdered_none_saturated φ₀ bR e aR k hstep
                        ⟨s, .atom p, l⟩ hsfmem with hine | hna
                    · have hc := hHinv.hintikkaInv ⟨s, .atom p, l⟩ hine
                      simp only [modalHintikkaClauseGen] at hc
                      cases s <;> exact hc
                    · cases s <;> simp [hna]
                  | bot =>
                    rcases modalStepBranchS4KeyedOrdered_none_saturated φ₀ bR e aR k hstep
                        ⟨s, .bot, l⟩ hsfmem with hine | hna
                    · have hc := hHinv.hintikkaInv ⟨s, .bot, l⟩ hine
                      simp only [modalHintikkaClauseGen] at hc
                      cases s <;> exact hc
                    · cases s <;> simp [hna]
                  | imp a c =>
                    rcases modalStepBranchS4KeyedOrdered_none_saturated φ₀ bR e aR k hstep
                        ⟨s, .imp a c, l⟩ hsfmem with hine | hna
                    · have hc := hHinv.hintikkaInv ⟨s, .imp a c, l⟩ hine
                      simp only [modalHintikkaClauseGen] at hc
                      cases s <;> exact hc
                    · cases s <;> simp [hna]
                  | and a c =>
                    rcases modalStepBranchS4KeyedOrdered_none_saturated φ₀ bR e aR k hstep
                        ⟨s, .and a c, l⟩ hsfmem with hine | hna
                    · have hc := hHinv.hintikkaInv ⟨s, .and a c, l⟩ hine
                      simp only [modalHintikkaClauseGen] at hc
                      cases s <;> exact hc
                    · cases s <;> simp [hna]
                  | or a c =>
                    rcases modalStepBranchS4KeyedOrdered_none_saturated φ₀ bR e aR k hstep
                        ⟨s, .or a c, l⟩ hsfmem with hine | hna
                    · have hc := hHinv.hintikkaInv ⟨s, .or a c, l⟩ hine
                      simp only [modalHintikkaClauseGen] at hc
                      cases s <;> exact hc
                    · cases s <;> simp [hna]
                  | box ψ' =>
                    cases s with
                    | pos =>
                      rcases modalStepBranchS4KeyedOrdered_none_saturated φ₀ bR e aR k hstep
                          ⟨.pos, .box ψ', l⟩ hsfmem with hine | hna
                      · exact absurd (hHinv.eBoxOnlyNeg ⟨.pos, .box ψ', l⟩ hine ψ' rfl) (by simp)
                      · simp [hna]
                    | neg => trivial
                  | diamond ψ' =>
                    cases s with
                    | pos => trivial
                    | neg =>
                      rcases modalStepBranchS4KeyedOrdered_none_saturated φ₀ bR e aR k hstep
                          ⟨.neg, .diamond ψ', l⟩ hsfmem with hine | hna
                      · exact absurd (hHinv.eDiamondOnlyPos ⟨.neg, .diamond ψ', l⟩ hine ψ' rfl)
                          (by simp)
                      · simp [hna]
                · -- Conjunct 3: box-negative witness existence
                  intro ψ' w hmem
                  rcases modalStepBranchS4KeyedOrdered_none_saturated φ₀ bR e aR k hstep _ hmem
                      with hine | hna
                  · exact hHinv.eBoxNegWitness _ hine ψ' w rfl
                  · exact absurd hna (modalApplyOneS4Keyed_boxNeg_ne_notApplicable φ₀ k bR aR ψ' w)
                · -- Conjunct 4: diamond-positive witness existence (symmetric to Conjunct 3)
                  intro ψ' w hmem
                  rcases modalStepBranchS4KeyedOrdered_none_saturated φ₀ bR e aR k hstep _ hmem
                      with hine | hna
                  · exact hHinv.eDiamondPosWitness _ hine ψ' w rfl
                  · exact
                      absurd hna (modalApplyOneS4Keyed_diaPos_ne_notApplicable φ₀ k bR aR ψ' w)
              | some step =>
                obtain ⟨newBs, newExps, newAcc, keys'⟩ := step
                rw [hstep] at hinner
                have hstepEq :
                    modalStepBranchS4KeyedOrdered φ₀ bh e a k =
                      some (newBs, newExps, newAcc, keys') :=
                  hstep
                have hbh_idx : (done ++ bh :: bt)[done.length]? = some bh := by
                  rw [List.getElem?_append_right (Nat.le_refl done.length)]; simp
                have he_idx : (doneExp ++ e :: es)[done.length]? = some e := by
                  rw [List.getElem?_append_right (by omega)]; simp [hdlength]
                have ha_idx : (doneAccs ++ a :: restAs)[done.length]? = some a := by
                  rw [List.getElem?_append_right (by omega)]; simp [hdAccs]
                have hk_idx : (doneKeys ++ k :: restKs)[done.length]? = some k := by
                  rw [List.getElem?_append_right (by omega)]; simp [hdKeys]
                obtain ⟨hLoopInv, hHinv, hKW, hWC, hKO⟩ :=
                  hInv_all done.length bh e a k hbh_idx he_idx ha_idx hk_idx
                obtain ⟨newExp, hNewExpEq⟩ :=
                  modalStepBranchS4KeyedOrdered_newExps_eq_map φ₀ bh e a k newBs newExps newAcc
                    keys' hstepEq
                subst hNewExpEq
                have hstepEq' : modalStepBranchS4KeyedOrdered φ₀ bh e a k =
                    some (newBs, newBs.map (fun _ => newExp), newAcc, keys') := hstepEq
                have hAllInv := modalStepBranchS4KeyedOrdered_preserves_S4OrderedFuelInv φ₀ bh e a
                  k newBs (newBs.map (fun _ => newExp)) newAcc keys'
                  ⟨hLoopInv, hHinv, hKW, hWC, hKO⟩ hstepEq'
                have hstep_lt := modalExpMeasure_step_lt_S4KeyedOrdered φ₀ k keys' done bt newBs
                  doneExp es newExp bh e a newAcc hdlength.symm hLoopInv.bClosure
                  hLoopInv.accKnown hWC hLoopInv.keysTotal hLoopInv.keysDistinct
                  hLoopInv.keysInUniverse hstepEq'
                apply ih (done ++ newBs ++ bt) (doneExp ++ newBs.map (fun _ => newExp) ++ es)
                  (doneAccs ++ List.replicate newBs.length newAcc ++ restAs)
                  (doneKeys ++ List.replicate newBs.length keys' ++ restKs)
                · simp only [List.length_append, List.length_map, hdlength]
                  omega
                · simp only [List.length_append, List.length_replicate, hdAccs]
                  omega
                · simp only [List.length_append, List.length_replicate, hdKeys]
                  omega
                · omega
                · intro i bi ei ai keysi hib hie hia hik
                  rcases Nat.lt_or_ge i done.length with hlt1 | hge1
                  · apply hInv_all i bi ei ai keysi
                    · rw [List.append_assoc, List.getElem?_append_left hlt1] at hib
                      rwa [List.getElem?_append_left hlt1]
                    · rw [List.append_assoc, List.getElem?_append_left (by omega)] at hie
                      rwa [List.getElem?_append_left (by omega)]
                    · rw [List.append_assoc, List.getElem?_append_left (by omega)] at hia
                      rwa [List.getElem?_append_left (by omega)]
                    · rw [List.append_assoc, List.getElem?_append_left (by omega)] at hik
                      rwa [List.getElem?_append_left (by omega)]
                  · rcases Nat.lt_or_ge i (done.length + newBs.length) with hlt2 | hge2
                    · -- Region: newBs (all sharing newExp/newAcc/keys')
                      have hj : i - done.length < newBs.length := by omega
                      have hbi_newBs : newBs[i - done.length]? = some bi := by
                        rw [List.append_assoc, List.getElem?_append_right hge1] at hib
                        rwa [List.getElem?_append_left hj] at hib
                      have hbi_mem : bi ∈ newBs := List.mem_of_getElem? hbi_newBs
                      have hei_eq : ei = newExp := by
                        rw [List.append_assoc,
                            List.getElem?_append_right (by omega : doneExp.length ≤ i)] at hie
                        rw [List.getElem?_append_left
                              (by simp only [List.length_map]; omega)] at hie
                        rw [List.getElem?_map,
                            show newBs[i - doneExp.length]? = some bi from by
                              rw [show i - doneExp.length = i - done.length from by omega]
                              exact hbi_newBs] at hie
                        simp only [Option.map_some, Option.some.injEq] at hie
                        exact hie.symm
                      have hei_eq' : newExp = ei := hei_eq.symm
                      subst hei_eq'
                      have hai_eq : ai = newAcc := by
                        rw [List.append_assoc,
                            List.getElem?_append_right (by omega : doneAccs.length ≤ i)] at hia
                        rw [List.getElem?_append_left
                              (by simp only [List.length_replicate]; omega)] at hia
                        exact List.eq_of_mem_replicate (List.mem_of_getElem? hia)
                      subst hai_eq
                      have hkeysi_eq : keysi = keys' := by
                        rw [List.append_assoc,
                            List.getElem?_append_right (by omega : doneKeys.length ≤ i)] at hik
                        rw [List.getElem?_append_left
                              (by simp only [List.length_replicate]; omega)] at hik
                        exact List.eq_of_mem_replicate (List.mem_of_getElem? hik)
                      subst hkeysi_eq
                      have hnewExp_mem : newExp ∈ newBs.map (fun _ => newExp) :=
                        List.mem_map.mpr ⟨bi, hbi_mem, rfl⟩
                      exact hAllInv bi hbi_mem newExp hnewExp_mem
                    · -- Region: bt (shifted index)
                      have hbi_bt : bt[i - done.length - newBs.length]? = some bi := by
                        rw [List.append_assoc, List.getElem?_append_right hge1] at hib
                        rw [List.getElem?_append_right
                              (by omega : newBs.length ≤ i - done.length)] at hib
                        exact hib
                      have hei_es : es[i - done.length - newBs.length]? = some ei := by
                        rw [List.append_assoc,
                            List.getElem?_append_right (by omega : doneExp.length ≤ i)] at hie
                        rw [List.getElem?_append_right
                              (by simp only [List.length_map]; omega :
                                (newBs.map (fun _ => newExp)).length ≤ i - doneExp.length)] at hie
                        rwa [show i - doneExp.length - (newBs.map (fun _ => newExp)).length =
                              i - done.length - newBs.length from by
                            simp only [List.length_map]; omega] at hie
                      have hai_restAs : restAs[i - done.length - newBs.length]? = some ai := by
                        rw [List.append_assoc, List.getElem?_append_right (by omega :
                              doneAccs.length ≤ i)] at hia
                        rw [List.getElem?_append_right
                              (by simp only [List.length_replicate]; omega :
                                (List.replicate newBs.length newAcc).length ≤
                                  i - doneAccs.length)] at hia
                        rwa [show i - doneAccs.length -
                              (List.replicate newBs.length newAcc).length =
                              i - done.length - newBs.length from by
                            simp only [List.length_replicate]; omega] at hia
                      have hki_restKs : restKs[i - done.length - newBs.length]? = some keysi := by
                        rw [List.append_assoc, List.getElem?_append_right (by omega :
                              doneKeys.length ≤ i)] at hik
                        rw [List.getElem?_append_right
                              (by simp only [List.length_replicate]; omega :
                                (List.replicate newBs.length keys').length ≤
                                  i - doneKeys.length)] at hik
                        rwa [show i - doneKeys.length -
                              (List.replicate newBs.length keys').length =
                              i - done.length - newBs.length from by
                            simp only [List.length_replicate]; omega] at hik
                      apply hInv_all (done.length + 1 + (i - done.length - newBs.length)) bi ei ai
                        keysi
                      · rw [List.getElem?_append_right
                              (by omega : done.length ≤
                                done.length + 1 + (i - done.length - newBs.length))]
                        rw [show done.length + 1 + (i - done.length - newBs.length) - done.length
                              = (i - done.length - newBs.length) + 1 from by omega]
                        rw [List.getElem?_cons_succ]; exact hbi_bt
                      · rw [List.getElem?_append_right
                              (by omega : doneExp.length ≤
                                done.length + 1 + (i - done.length - newBs.length))]
                        rw [show done.length + 1 + (i - done.length - newBs.length) -
                              doneExp.length = (i - done.length - newBs.length) + 1 from by omega]
                        rw [List.getElem?_cons_succ]; exact hei_es
                      · rw [List.getElem?_append_right
                              (by omega : doneAccs.length ≤
                                done.length + 1 + (i - done.length - newBs.length))]
                        rw [show done.length + 1 + (i - done.length - newBs.length) -
                              doneAccs.length = (i - done.length - newBs.length) + 1 from by omega]
                        rw [List.getElem?_cons_succ]; exact hai_restAs
                      · rw [List.getElem?_append_right
                              (by omega : doneKeys.length ≤
                                done.length + 1 + (i - done.length - newBs.length))]
                        rw [show done.length + 1 + (i - done.length - newBs.length) -
                              doneKeys.length = (i - done.length - newBs.length) + 1 from by omega]
                        rw [List.getElem?_cons_succ]; exact hki_restKs
                · exact hinner

/-! ## Groundwork: Keyed-Driver Initial-Branch Membership Persistence -/

/-- **Keyed-driver initial-branch membership persistence**: mirrors
`modalExpandBranchesGen_openBranch_initial_mem` (`CompletenessLoop.lean`) for the bespoke
`modalExpandBranchesS4Keyed` driver -- needed since that driver is not an instance of
`modalExpandBranchesGen`, so the generic lemma does not apply directly. Consumed by
`modalTableauS4Keyed_complete` (`FrameCompleteness.lean`) to recover `F(φ0)@0 ∈ b` from the
final open branch. Uses `modalStepBranchS4Keyed_branch_superset` (old branch content survives
into every child) in place of the generic `modalStepBranchGen_mem_preserved`, and the
territory-local `modalStepBranchS4Keyed_newExps_const` for the length-matching step. -/
theorem modalExpandBranchesS4Keyed_openBranch_initial_mem
    (φ₀ : Proposition Atom) (fuel : Nat)
    (sf : SignedFormula (Proposition Atom) WorldIndex) :
    ∀ (branches expandedSets : List (List (SignedFormula (Proposition Atom) WorldIndex)))
      (accs : List Accessibility)
      (keyss : List (List (WorldIndex × Finset (Sign × Proposition Atom)))),
      expandedSets.length = branches.length →
      accs.length = branches.length →
      keyss.length = branches.length →
      (∀ b₀ ∈ branches, sf ∈ b₀) →
      ∀ (bR : List (SignedFormula (Proposition Atom) WorldIndex)) (aR : Accessibility),
        modalExpandBranchesS4Keyed φ₀ branches expandedSets accs keyss fuel = .openBranch bR aR →
        sf ∈ bR := by
  induction fuel with
  | zero =>
    intro branches expandedSets accs keyss _hlen _hlenA _hlenK hAll bR aR h
    simp only [modalExpandBranchesS4Keyed] at h
    cases hfs : (branches.zip accs).findSome? (fun (b, a) =>
        if isModalClosed b then none else some (b, a)) with
    | none => simp only [hfs] at h; exact absurd h (by simp)
    | some p =>
      obtain ⟨pb, pa⟩ := p
      simp only [hfs] at h
      injection h with hp1 hp2
      obtain ⟨q, hqmem, hf⟩ := List.exists_of_findSome?_eq_some hfs
      obtain ⟨qb, qa⟩ := q
      simp only [] at hf
      by_cases hcl : isModalClosed qb = true
      · rw [if_pos hcl] at hf
        exact absurd hf (by simp)
      · rw [if_neg hcl] at hf
        have hq0mem : qb ∈ branches := (List.of_mem_zip hqmem).1
        have hqp : (qb, qa) = (pb, pa) := Option.some.inj hf
        have hqfst : qb = bR := by
          have : qb = pb := congrArg Prod.fst hqp
          rw [this]; exact hp1
        rw [hqfst] at hq0mem
        exact hAll bR hq0mem
  | succ fuel' ih =>
    intro branches expandedSets accs keyss hlen hlenA hlenK hAll bR aR h
    simp only [modalExpandBranchesS4Keyed] at h
    suffices key : ∀ (pending pendingExp :
          List (List (SignedFormula (Proposition Atom) WorldIndex)))
        (pendingAccs : List Accessibility)
        (pendingKeys : List (List (WorldIndex × Finset (Sign × Proposition Atom))))
        (done doneExp : List (List (SignedFormula (Proposition Atom) WorldIndex)))
        (doneAccs : List Accessibility)
        (doneKeys : List (List (WorldIndex × Finset (Sign × Proposition Atom)))),
        pendingExp.length = pending.length →
        pendingAccs.length = pending.length →
        pendingKeys.length = pending.length →
        doneExp.length = done.length →
        doneAccs.length = done.length →
        doneKeys.length = done.length →
        (∀ bp ∈ pending, sf ∈ bp) →
        (∀ bd ∈ done, sf ∈ bd) →
        modalExpandBranchesS4Keyed.processNext φ₀ fuel' pending pendingExp pendingAccs pendingKeys
            done doneExp doneAccs doneKeys = .openBranch bR aR →
        sf ∈ bR from
      key branches expandedSets accs keyss [] [] [] [] hlen hlenA hlenK rfl rfl rfl hAll (by simp)
        (by simpa [modalExpandBranchesS4Keyed] using h)
    intro pending
    induction pending with
    | nil =>
      intro pendingExp pendingAccs pendingKeys done doneExp doneAccs doneKeys
        _ _ _ _ _ _ _ _ hinner
      simp [modalExpandBranchesS4Keyed.processNext] at hinner
    | cons bh bt ih_inner =>
      intro pendingExp pendingAccs pendingKeys done doneExp doneAccs doneKeys
        hlength_p hlenP_accs hlenP_keys hdlength hdAccs hdKeys hAll_p hAll_d hinner
      cases pendingAccs with
      | nil => simp at hlenP_accs
      | cons a restAs =>
        cases pendingExp with
        | nil => simp at hlength_p
        | cons e es =>
          cases pendingKeys with
          | nil => simp at hlenP_keys
          | cons k restKs =>
            simp only [List.length_cons, Nat.add_right_cancel_iff] at hlength_p
            simp only [List.length_cons, Nat.add_right_cancel_iff] at hlenP_accs
            simp only [List.length_cons, Nat.add_right_cancel_iff] at hlenP_keys
            simp only [modalExpandBranchesS4Keyed.processNext] at hinner
            by_cases hcl : isModalClosed bh = true
            · rw [if_pos hcl] at hinner
              have hAll_bt : ∀ bp ∈ bt, sf ∈ bp := fun bp hbp => hAll_p bp (by simp [hbp])
              have hAll_done_bh : ∀ bd ∈ done ++ [bh], sf ∈ bd := by
                intro bd hbd
                simp only [List.mem_append, List.mem_singleton] at hbd
                rcases hbd with hd | heq
                · exact hAll_d bd hd
                · subst heq; exact hAll_p bd (by simp)
              exact ih_inner es restAs restKs (done ++ [bh]) (doneExp ++ [e]) (doneAccs ++ [a])
                (doneKeys ++ [k]) hlength_p hlenP_accs hlenP_keys
                (by simp [hdlength]) (by simp [hdAccs]) (by simp [hdKeys])
                hAll_bt hAll_done_bh hinner
            · simp only [Bool.not_eq_true] at hcl
              rw [if_neg (by simp [hcl])] at hinner
              cases hstep : modalStepBranchS4Keyed φ₀ bh e a k with
              | none =>
                rw [hstep] at hinner
                have hbeq : bh = bR ∧ a = aR := by cases hinner; exact ⟨rfl, rfl⟩
                exact hbeq.1 ▸ hAll_p bh (by simp)
              | some step =>
                obtain ⟨newBs, newExps, newAcc, keys'⟩ := step
                rw [hstep] at hinner
                have hbh_sf : sf ∈ bh := hAll_p bh (by simp)
                have hNewBs_sf : ∀ b' ∈ newBs, sf ∈ b' :=
                  fun b' hb' => modalStepBranchS4Keyed_branch_superset φ₀ bh e a k newBs newExps
                    newAcc keys' hstep b' hb' sf hbh_sf
                have hLenNBE : newExps.length = newBs.length := by
                  obtain ⟨newExp, hEq⟩ :=
                    modalStepBranchS4Keyed_newExps_const φ₀ bh e a k newBs newExps newAcc keys'
                      hstep
                  simp [hEq]
                exact ih (done ++ newBs ++ bt) (doneExp ++ newExps ++ es)
                  (doneAccs ++ List.replicate newBs.length newAcc ++ restAs)
                  (doneKeys ++ List.replicate newBs.length keys' ++ restKs)
                  (by simp [hdlength, hlength_p, hLenNBE])
                  (by simp [hdAccs, hlenP_accs])
                  (by simp [hdKeys, hlenP_keys])
                  (fun b' hb'_mem => by
                    simp only [List.mem_append] at hb'_mem
                    rcases hb'_mem with (hd | hn) | hbt
                    · exact hAll_d b' hd
                    · exact hNewBs_sf b' hn
                    · exact hAll_p b' (by simp [hbt]))
                  bR aR hinner

/-! ## Ordered Groundwork: Keyed-Driver Initial-Branch Membership Persistence -/

/-- **Ordered-driver form of `modalExpandBranchesS4Keyed_openBranch_initial_mem`.** Mirrors
`modalExpandBranchesGen_openBranch_initial_mem` (`CompletenessLoop.lean`) for the ordered driver
`modalExpandBranchesS4KeyedOrdered` -- needed since that driver is not an instance of
`modalExpandBranchesGen`, so the generic lemma does not apply directly. Consumed by
`modalTableauS4KeyedOrdered_complete` (`FrameCompleteness.lean`) to recover `F(φ0)@0 ∈ b` from
the final open branch. Uses `modalStepBranchS4KeyedOrdered_branch_superset` (old branch content
survives into every child) in place of the generic `modalStepBranchGen_mem_preserved`, and
Phase 2's relocated `modalStepBranchS4KeyedOrdered_newExps_eq_map` for the length-matching
step. -/
theorem modalExpandBranchesS4KeyedOrdered_openBranch_initial_mem
    (φ₀ : Proposition Atom) (fuel : Nat)
    (sf : SignedFormula (Proposition Atom) WorldIndex) :
    ∀ (branches expandedSets : List (List (SignedFormula (Proposition Atom) WorldIndex)))
      (accs : List Accessibility)
      (keyss : List (List (WorldIndex × Finset (Sign × Proposition Atom)))),
      expandedSets.length = branches.length →
      accs.length = branches.length →
      keyss.length = branches.length →
      (∀ b₀ ∈ branches, sf ∈ b₀) →
      ∀ (bR : List (SignedFormula (Proposition Atom) WorldIndex)) (aR : Accessibility),
        modalExpandBranchesS4KeyedOrdered φ₀ branches expandedSets accs keyss fuel =
          .openBranch bR aR →
        sf ∈ bR := by
  induction fuel with
  | zero =>
    intro branches expandedSets accs keyss _hlen _hlenA _hlenK hAll bR aR h
    simp only [modalExpandBranchesS4KeyedOrdered] at h
    cases hfs : (branches.zip accs).findSome? (fun (b, a) =>
        if isModalClosed b then none else some (b, a)) with
    | none => simp only [hfs] at h; exact absurd h (by simp)
    | some p =>
      obtain ⟨pb, pa⟩ := p
      simp only [hfs] at h
      injection h with hp1 hp2
      obtain ⟨q, hqmem, hf⟩ := List.exists_of_findSome?_eq_some hfs
      obtain ⟨qb, qa⟩ := q
      simp only [] at hf
      by_cases hcl : isModalClosed qb = true
      · rw [if_pos hcl] at hf
        exact absurd hf (by simp)
      · rw [if_neg hcl] at hf
        have hq0mem : qb ∈ branches := (List.of_mem_zip hqmem).1
        have hqp : (qb, qa) = (pb, pa) := Option.some.inj hf
        have hqfst : qb = bR := by
          have : qb = pb := congrArg Prod.fst hqp
          rw [this]; exact hp1
        rw [hqfst] at hq0mem
        exact hAll bR hq0mem
  | succ fuel' ih =>
    intro branches expandedSets accs keyss hlen hlenA hlenK hAll bR aR h
    simp only [modalExpandBranchesS4KeyedOrdered] at h
    suffices key : ∀ (pending pendingExp :
          List (List (SignedFormula (Proposition Atom) WorldIndex)))
        (pendingAccs : List Accessibility)
        (pendingKeys : List (List (WorldIndex × Finset (Sign × Proposition Atom))))
        (done doneExp : List (List (SignedFormula (Proposition Atom) WorldIndex)))
        (doneAccs : List Accessibility)
        (doneKeys : List (List (WorldIndex × Finset (Sign × Proposition Atom)))),
        pendingExp.length = pending.length →
        pendingAccs.length = pending.length →
        pendingKeys.length = pending.length →
        doneExp.length = done.length →
        doneAccs.length = done.length →
        doneKeys.length = done.length →
        (∀ bp ∈ pending, sf ∈ bp) →
        (∀ bd ∈ done, sf ∈ bd) →
        modalExpandBranchesS4KeyedOrdered.processNext φ₀ fuel' pending pendingExp pendingAccs
            pendingKeys done doneExp doneAccs doneKeys = .openBranch bR aR →
        sf ∈ bR from
      key branches expandedSets accs keyss [] [] [] [] hlen hlenA hlenK rfl rfl rfl hAll (by simp)
        (by simpa [modalExpandBranchesS4KeyedOrdered] using h)
    intro pending
    induction pending with
    | nil =>
      intro pendingExp pendingAccs pendingKeys done doneExp doneAccs doneKeys
        _ _ _ _ _ _ _ _ hinner
      simp [modalExpandBranchesS4KeyedOrdered.processNext] at hinner
    | cons bh bt ih_inner =>
      intro pendingExp pendingAccs pendingKeys done doneExp doneAccs doneKeys
        hlength_p hlenP_accs hlenP_keys hdlength hdAccs hdKeys hAll_p hAll_d hinner
      cases pendingAccs with
      | nil => simp at hlenP_accs
      | cons a restAs =>
        cases pendingExp with
        | nil => simp at hlength_p
        | cons e es =>
          cases pendingKeys with
          | nil => simp at hlenP_keys
          | cons k restKs =>
            simp only [List.length_cons, Nat.add_right_cancel_iff] at hlength_p
            simp only [List.length_cons, Nat.add_right_cancel_iff] at hlenP_accs
            simp only [List.length_cons, Nat.add_right_cancel_iff] at hlenP_keys
            simp only [modalExpandBranchesS4KeyedOrdered.processNext] at hinner
            by_cases hcl : isModalClosed bh = true
            · rw [if_pos hcl] at hinner
              have hAll_bt : ∀ bp ∈ bt, sf ∈ bp := fun bp hbp => hAll_p bp (by simp [hbp])
              have hAll_done_bh : ∀ bd ∈ done ++ [bh], sf ∈ bd := by
                intro bd hbd
                simp only [List.mem_append, List.mem_singleton] at hbd
                rcases hbd with hd | heq
                · exact hAll_d bd hd
                · subst heq; exact hAll_p bd (by simp)
              exact ih_inner es restAs restKs (done ++ [bh]) (doneExp ++ [e]) (doneAccs ++ [a])
                (doneKeys ++ [k]) hlength_p hlenP_accs hlenP_keys
                (by simp [hdlength]) (by simp [hdAccs]) (by simp [hdKeys])
                hAll_bt hAll_done_bh hinner
            · simp only [Bool.not_eq_true] at hcl
              rw [if_neg (by simp [hcl])] at hinner
              cases hstep : modalStepBranchS4KeyedOrdered φ₀ bh e a k with
              | none =>
                rw [hstep] at hinner
                have hbeq : bh = bR ∧ a = aR := by cases hinner; exact ⟨rfl, rfl⟩
                exact hbeq.1 ▸ hAll_p bh (by simp)
              | some step =>
                obtain ⟨newBs, newExps, newAcc, keys'⟩ := step
                rw [hstep] at hinner
                have hbh_sf : sf ∈ bh := hAll_p bh (by simp)
                have hNewBs_sf : ∀ b' ∈ newBs, sf ∈ b' :=
                  fun b' hb' => modalStepBranchS4KeyedOrdered_branch_superset φ₀ bh e a k newBs
                    newExps newAcc keys' hstep b' hb' sf hbh_sf
                have hLenNBE : newExps.length = newBs.length := by
                  obtain ⟨newExp, hEq⟩ :=
                    modalStepBranchS4KeyedOrdered_newExps_eq_map φ₀ bh e a k newBs newExps newAcc
                      keys' hstep
                  simp [hEq]
                exact ih (done ++ newBs ++ bt) (doneExp ++ newExps ++ es)
                  (doneAccs ++ List.replicate newBs.length newAcc ++ restAs)
                  (doneKeys ++ List.replicate newBs.length keys' ++ restKs)
                  (by simp [hdlength, hlength_p, hLenNBE])
                  (by simp [hdAccs, hlenP_accs])
                  (by simp [hdKeys, hlenP_keys])
                  (fun b' hb'_mem => by
                    simp only [List.mem_append] at hb'_mem
                    rcases hb'_mem with (hd | hn) | hbt
                    · exact hAll_d b' hd
                    · exact hNewBs_sf b' hn
                    · exact hAll_p b' (by simp [hbt]))
                  bR aR hinner

end Cslib.Logic.Modal.Tableau

end
