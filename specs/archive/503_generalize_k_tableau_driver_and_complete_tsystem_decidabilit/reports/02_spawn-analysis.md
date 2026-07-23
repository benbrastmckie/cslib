# Blocker Analysis: Task #503

**Parent Task**: #503 - Generalize the K tableau driver and complete T-system decidability
**Generated**: 2026-07-14
**Blocker**: Plan Phase 3 (generalizing `FmpMeasure.lean`'s termination/FMP measure over the
`RuleApplicationSpec` interface) cannot close: the target lemma and its ~900-line dependency
chain case-split directly on `modalApplyOne`'s four concrete `RuleResult` shapes rather than
going through any hypothesis bundle, so generalizing it is a from-scratch re-derivation, not a
mechanical substitution.

## Root Cause

Task 503 delivered Phases 1-2 CI-green with zero debt, both committed:
- `Saturation.lean` (commit `e9f350c7`): the generic driver `RuleApply`/`modalStepBranchGen`/
  `modalExpandBranchesGen`/`modalTableauGen`, plus zero-regression bridge theorems
  (`modalStepBranch_eq`/`modalExpandBranches_eq`/`modalTableau_eq`) re-deriving K as the trivial
  instantiation.
- `GenericDriver.lean` (commit `d5b24e67`, new file): `RuleApplicationSpec` — a three-field
  structural-hypothesis bundle (`freshLocal`, `outputsSubsetUniverse`, `persistentFresh`) — and
  `modalApplyOne_spec : RuleApplicationSpec modalApplyOne` (the trivial K witness), plus a
  documented downstream-reuse contract for tasks 504/505 and an explicit S4/506 exclusion note.

Phase 3 is **[BLOCKED]** per the plan's own documented fallback (plan §Phase 3, and
`handoffs/phase2-handoff.md`'s "Known Limitation" section written in advance of attempting it).
The target of Phase 3 is generalizing three lemmas in `FmpMeasure.lean` — `modalStepBranch_potential_step`
(~line 2146), `modalStepBranch_worldBound` (~line 2376), and `modalExpMeasure_step_lt`
(~line 2873) — to take an abstract `(apply, spec : RuleApplicationSpec apply)` in place of the
concrete `modalApplyOne`.

**What was tried**: the implementer read the full proof of `modalStepBranch_potential_step`
(~160 lines) plus its direct dependency chain — `modalStepBranch_exists_rank'` (~line 1058),
`modalStepBranch_knownWorlds` (~line 1901), `modalStepBranch_preserves_outDegEq` (~line 1365),
`outDeg_le_of_expandedNodup` (~line 1509), and ~10 further private helpers — spanning
`FmpMeasure.lean` lines ~1058-2415 (~900 lines total). From this reading, the Phase 2
`RuleApplicationSpec` field list (`freshLocal`/`outputsSubsetUniverse`/`persistentFresh`) was
derived and `modalApplyOne_spec` proved as the trivial K witness.

**Why it's stuck**: `modalStepBranch_potential_step`'s proof (and its whole dependency chain)
does not thread through any hypothesis bundle today. It `rcases`es directly on
`(modalApplyOne sf b acc).fst`/`.snd` at every step (e.g. lines ~2080, ~2227) and exploits the
*exact* four concrete `RuleResult` shapes (propositional/boxPos/diamondNeg/diamondPos/boxNeg)
together with fine-grained `outDeg`/`modalKnownWorlds`/rank-map bookkeeping specific to K's own
mint arms — including a `geomCap`-based potential-drop identity (lines ~2251-2270) that computes
an EXACT numeric decrease, not just a bound. The three Phase-2 spec fields are sufficient to
restate the top lemma's *type* generically but are NOT sufficient to replay its *proof*: each of
the ~10-15 helper lemmas independently case-splits on `modalApplyOne`'s concrete shapes rather
than going through the spec, so generalizing the top-level lemma requires FIRST generalizing all
of these helpers. This is a from-scratch re-derivation of an intricate potential-function
argument, sized at least on the order of the original ~900-line development — not a mechanical
`apply`-for-`modalApplyOne` substitution.

**What is needed** (per the implementer's documented recommendation, matching the plan's own
Phase 3 `[BLOCKED]` fallback clause): a dedicated follow-up task scoped specifically to
generalizing `FmpMeasure.lean` lines ~1058-2415 over `RuleApplicationSpec`, likely requiring
(a) extending `RuleApplicationSpec` with additional fields capturing the exact `outDeg`/rank-map
interaction at the fresh-world mint point (not just "a fresh edge is added", but "the fresh
edge's source `outDeg` was `< Sf` beforehand, by exactly the amount the catalog bounds"), and
(b) re-deriving `modalStepBranch_exists_rank'`/`modalStepBranch_knownWorlds`/
`modalStepBranch_preserves_outDegEq` generically BEFORE the top-level potential-step lemma can
be attempted. No `sorry`/`axiom`/vacuous placeholder was introduced; Phases 1-2 remain green and
committed. Completing this unblocks task 503's own remaining Phases 4-7 (T instantiation, T
truth lemma, `Decidable (tValid φ)`) AND is a prerequisite for downstream tasks 504 (S5/KB5) and
505 (B) which are documented to reuse the generic termination measure. Task 506 (S4) is
explicitly NOT an instance of this interface (transitive-box termination requires genuinely
different loop-checking machinery) and is out of scope here.

## Proposed New Tasks

### New Task 1: Generalize the K FMP termination measure over RuleApplicationSpec
- **Effort**: 12-16 hours (may warrant its own multi-phase plan; matches "on the order of the
  original ~900-line development" per the implementer's own sizing note)
- **Task Type**: cslib
- **Rationale**: This is the direct and sole unblock for task 503's Phase 3, and therefore for
  its remaining Phases 4-7 (T instantiation, T truth lemma, `Decidable (tValid φ)`). It completes
  exactly the deliverable Phase 3 already specifies in the 503 plan (`plans/01_generalize-tableau-driver-tsystem.md`,
  §Phase 3): generalize `modalStepBranch_potential_step` (~line 2146), `modalStepBranch_worldBound`
  (~line 2376), and `modalExpMeasure_step_lt` (~line 2873) to take `(apply, spec :
  RuleApplicationSpec apply)`, discharging each former `modalApplyOne`-specific step from the
  corresponding `spec` field — first re-deriving the ~900-line dependency chain
  (`modalStepBranch_exists_rank'` ~line 1058, `modalStepBranch_knownWorlds` ~line 1901,
  `modalStepBranch_preserves_outDegEq` ~line 1365, `outDeg_le_of_expandedNodup` ~line 1509, and
  ~10 further private helpers) generically, extending `RuleApplicationSpec` in `GenericDriver.lean`
  with whatever additional outDeg/rank-map fields the mint case requires. Keep
  `modalUniverse`/`modalWork`/`modalExpMeasure`/`modalFuel` (world-agnostic size bounds)
  unchanged — only the rule-dependent step lemmas move behind the interface. Re-instantiate K's
  termination lemmas as `<generic> modalApplyOne modalApplyOne_spec` (already-proved witness from
  Phase 2), confirming `FmpMeasure.lean`'s existing K corollaries and `CompletenessLoop.lean`'s
  uses still typecheck via the Phase-1 `_eq` bridge lemmas. Zero regression, zero sorry, zero
  axiom throughout; if any sub-piece cannot close, mark `[BLOCKED]` with the exact open lemma and
  goal state rather than introduce debt (matching the discipline already demonstrated in task
  503's own Phases 1-2).
- **Depends on**: None. Builds entirely on task 503's already-committed Phase 1 (`Saturation.lean`,
  commit `e9f350c7`) and Phase 2 (`GenericDriver.lean`, commit `d5b24e67`) — no further input from
  503's remaining phases is needed to begin this work, and no other new task is a prerequisite.

## Dependency Reasoning

- **Task 1 has no dependencies**: everything Task 1 needs — the generic driver definitions
  (`modalStepBranchGen`/`modalExpandBranchesGen`/`modalTableauGen`) and the `RuleApplicationSpec`
  interface with its trivial K witness (`modalApplyOne_spec`) — is already committed and CI-green
  from task 503's Phases 1-2. Task 1 is free-standing: it operates entirely within
  `FmpMeasure.lean` (extending `GenericDriver.lean`'s `RuleApplicationSpec` as needed), reusing
  but not modifying the Phase-1/2 deliverables.

Only one task is proposed because the blocker has a single, well-scoped root cause (one file,
one proof chain, one interface to extend) rather than several independent sub-problems — per the
Task Minimization Principle, splitting this further (e.g. one task per helper lemma) would create
artificial dependencies where the same person/agent must hold the whole ~900-line proof chain's
context simultaneously to design the correct extended `spec` fields; a single task scoped to the
full chain is the minimal correct decomposition. If, once inside the task, the ~900-line
re-derivation still cannot close in one run, the task's own plan should sequence itself into
phases (mirroring the discipline already used for task 503 itself) rather than being pre-split
into multiple sibling spawn tasks now, since the correct phase boundaries can only be identified
once the extended `spec` field set is designed against the real proof.

## After Completion

Once the new task is complete, resume task 503 with `/implement 503` to execute Phases 4-7 (T
driver instantiation, T truth lemma, `Decidable (tValid φ)`, and final documentation/CI), which
were left `[NOT STARTED]` specifically because they depend sequentially on Phase 3's generic
termination measure.

The blocker will be resolved because: the new task delivers exactly the missing piece — a
`RuleApplicationSpec`-generic termination/FMP measure with K re-derived as the trivial
instantiation — that Phase 3 of task 503's plan specifies but could not complete in-run. With
that measure in place, task 503's Phase 4 can instantiate the generic driver with the
already-proved `modalApplyOneT` and proceed through completeness/decidability exactly as planned,
and downstream tasks 504 (S5/KB5) and 505 (B) gain the same reusable termination measure their
own plans already assume will exist.
