# Blocker Analysis: Task #511

**Parent Task**: #511 - s4_loop_checking_termination
**Generated**: 2026-07-18
**Blocker**: Phase 7's `Decidable (s4Valid φ)` instance must run the real driver
`modalTableauS4`/`modalApplyOneS4` (guarded by the live-relevant-set comparison
`blockingWorldS4`), but the landed termination machinery (`S4LoopInv`,
`modalStepBranchS4_worldBound`, Phases 4-6) is proven only for the keyed shadow stepper
`modalStepBranchS4Keyed` (guarded by the stable birth-key comparison `blockingWorldS4Keyed`).
The world-bound guarantee does not transfer between the two.

## Root Cause

Task 511's Phases 1-6 (green, sorry-free, per
`specs/511_s4_loop_checking_termination/plans/01_s4-termination-bound-decidability.md`) build
the pigeonhole world-bound proof entirely around a keyed shadow stepper,
`modalStepBranchS4Keyed`, whose minting guard `blockingWorldS4Keyed` compares a prospective
successor's birth content against a stable, birth-frozen `keys` list. This is visible directly in
the step hypothesis of the assembly theorem `modalStepBranchS4_preserves_S4LoopInv`, which takes
`modalStepBranchS4Keyed φ₀ b e acc keys = some (newBs, newExps, newAcc, keys')` — not
`modalStepBranchS4`.

The actual decision procedure that `s4Valid`'s `Decidable` instance must run,
`modalTableauS4 := modalTableauGen (modalApplyOneS4 φ) φ`, uses `modalApplyOneS4`, whose minting
guard is `blockingWorldS4` — a comparison against the **current live** `relevantSetFinset` of
every existing known world, not the stable `keys` list.

The Phase 7 dispatch (`specs/511_s4_loop_checking_termination/handoffs/07_phase7-blocked-driver-mismatch.md`)
confirmed the two guards are not interchangeable: `S4LoopInv.keyLowerBd` gives only
`keys ⊆ relevantSetFinset` (a subset relation, not equality), so `blockingWorldS4_none_fresh`'s
live-set freshness guarantee does not imply a keys-freshness guarantee. This is the same class of
gap that forced Phase 5 to introduce `blockingWorldS4Keyed` as a *second* guard in the first
place, now re-encountered from the `Decidable`-instance side — the world-bound guarantee is
proven about a driver `modalTableauS4` does not actually run.

A related lead was investigated and found insufficient alone: task 515 (concurrent/later) already
landed a more general, rank-free top-loop lemma in `CompletenessLoop.lean` —
`modalExpandBranchesHintikka`, parametrized over an abstract `Aux : List SF → List SF →
Accessibility → Prop` (`AuxStepPreserved`/`AuxBounds`/`ModalLoopInvHintikka`), built for S5's
`ModalLoopAuxS5w`. This is real groundwork for a state-free termination interface, but does not
by itself close S4: wrapping `keys` inside an existential `Aux(b,e,acc) := ∃ keys, S4LoopInv-fields`
still requires `AuxStepPreserved` to re-derive `keysDistinct` preservation using the real
(live-set) guard's contract — the same insufficient argument. The generic interface's `apply :
RuleApply Atom` is a single fixed function per call, with no mechanism for extra per-branch
threaded state (like `keys`) to evolve across steps; only a `Prop`-valued `Aux` can be re-derived
at each point.

This was flagged as an explicit spawn point at plan-authoring time (Planner Decision 2,
`plans/01_s4-termination-bound-decidability.md` line ~472-484): the abstract termination-measure
interface is a shared-file change benefiting the B-system and generalized-tableau-soundness lines
of work, and was always intended to be spawned as a separate task rather than inlined into 511.

## Proposed New Tasks

### New Task 1: Abstract termination-measure interface for S4/B loop lemma (task 511 Phase 7 follow-on)
- **Effort**: 10-16 hours
- **Task Type**: cslib
- **Rationale**: This is the sole blocker preventing task 511 Phase 7 from closing
  `Decidable (s4Valid φ)` and `s4Valid` completeness against `Cube.S4`. It requires either
  generalizing the shared driver framework (`RuleApply`/`Accessibility` in `GenericDriver.lean`
  and the `Aux`-parametrized loop lemma in `CompletenessLoop.lean`) to carry extra opaque
  per-branch threaded state (the S4 `keys : List (WorldIndex × Finset (Sign × Proposition Atom))`
  list), or building a bespoke S4-local `processNext`-style driver directly around the
  already-landed `modalStepBranchS4Keyed`/`S4LoopInv`/`modalStepBranchS4_worldBound`
  (`LoopChecking.lean`, task 511 Phases 4-6, all sorry-free). Either resolution must also
  redefine `modalTableauS4` (or add a new `modalTableauS4Keyed` and repoint `s4Valid`'s
  `Decidable` instance to it) and re-verify that soundness (`modalTableauS4_sound`) and the
  truth lemma (`modalTruthLemmaS4`) reconnect against the keyed guard's Hintikka witnesses,
  since the currently-shipped `modalTableauS4` runs the live-set-guarded `modalApplyOneS4`, not
  the keyed guard the termination proof is about. This is a shared-file change
  (`CompletenessLoop.lean`, `GenericDriver.lean`) explicitly identified as benefiting the
  B-system and generalized-tableau-soundness lines of work, and was pre-authorized by task 511's
  plan (Planner Decision 2) to be spawned as a separate task rather than inlined.
- **Depends on**: None

## Dependency Reasoning

Only one task is proposed. No internal dependency graph is needed — this satisfies the Task
Minimization Principle (minimality: the blocker is a single, self-contained interface-design
problem; splitting it into "survey task 515's Aux machinery" and "build the interface" would
create an artificial sequencing dependency where the survey step's findings directly determine
which of the two paths — 9-A generalized interface vs. 9-B bespoke S4-local driver — the
implementation step takes; that decision is exactly the kind of implementation detail the
Sequentiality criterion says should stay inside one task rather than being split across an
artificial boundary).

**File Footprint Overlap Check**: N/A — only one new task is proposed, so there are no
cross-task pairs to check for `file_scope` overlap.

## After Completion

Once the spawned task lands the abstract termination-measure interface (or bespoke S4-local
driver) and repoints/redefines the real decision procedure, resume task 511 with
`/implement 511`.

The blocker will be resolved because: task 511 Phase 7 can then wire fuel sufficiency from the
already-landed, sorry-free `modalStepBranchS4_worldBound` (Phases 4-6, `LoopChecking.lean`)
against a decision procedure that is actually guarded by `blockingWorldS4Keyed` (either because
`modalTableauS4` was repointed to run the keyed guard, or because a new `modalTableauS4Keyed` was
substituted and `s4Valid`'s `Decidable` instance redefined against it) — closing the gap between
what the termination proof establishes and what the real driver runs.
