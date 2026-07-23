# Implementation Summary: Well-founded maximalisation carrier + FLO invariant (Phase 1)

- **Task**: 517 - labelled_bounded_context_cs5_completeness
- **Status**: [COMPLETED] (Phase 1 of plan v5 only; plan v5 overall remains [IMPLEMENTING])
- **Started**: 2026-07-18T20:59:18Z
- **Completed**: 2026-07-18T21:13:30Z
- **Effort**: 1 dispatch (single-phase, hard mode)
- **Dependencies**: None (all Phase 1-4 landed assets from the v4/v5 lineage were already in
  place)
- **Artifacts**: plans/12_wellfounded-zorn-oldlabel-reconstruction.md (Phase 1 heading updated to
  `[COMPLETED]`), probes/chain-union-reflection-probe.lean (extended)

## Overview

Implemented Phase 1 of plan v5 (`plans/12_wellfounded-zorn-oldlabel-reconstruction.md`): the
well-founded maximalisation carrier and the FLO ("fresh-labels-only extension") invariant, landed
as new definitions and sorried theorem signatures appended to
`probes/chain-union-reflection-probe.lean`. This is the first phase of the "Phase 4.5"
reconstruction that replaces Mathlib's non-constructive `zorn_le₀` in `primeC_exists_maximal`
with a step-indexed/well-founded (transfinite) Lindenbaum construction, per the divergence audit
that motivated plan v5.

## What Changed

- Added `import Mathlib.SetTheory.Ordinal.Arithmetic` to the probe.
- `Stage : Type (u+1) := Ordinal.{u}` — the transfinite stage-index type.
- `FloTask` — an inductive enumerating one single-step extension task (`formula`, `diaWitness`,
  `redundantEdge`, `skip`), reusing the landed `Context.addFormula`/`addDiaWitness`/
  `addRedundantEdge` operations.
- `stepExt` — the total single-step extension function (classical case-splits, falling back to
  the identity when a precondition fails).
- `stepExt_le` — **sorry-free**: `stepExt` never shrinks the context.
- `FloSeq` — a staged FLO construction: an ordinal-indexed sequence of contexts extending `G₀`,
  built by `stepExt` at successor stages and raw chain-union at limit stages.
- `rankOf` — the derived birth-rank function (`sInf` of the set of stages at which a label
  appears).
- `rankOf_base` — **sorry-free**: base labels have rank `0`.
- `FLO` — the non-vacuous invariant structure bundling FLO-0 (base)/FLO-1 (fresh-at-birth,
  cases (a)/(b))/FLO-2 (edge locality), stated relative to a `FloSeq` and a stage.
- Four sorried downstream obligations, matching the plan's task list exactly: `flo_succ`
  (Phase 2), `flo_limit` (Phase 3), `primeC'_exists_maximal` (Phase 4), `flo_oldlabel_transport`
  (Phase 5).

## Decisions

- **Mechanism decision (SETTLED for Phases 2-6)**: route (i), explicit well-founded/`Ordinal`
  recursion producing a genuine staged sequence `H : Stage → Context`. Rejected route (ii)
  (`zorn_le₀` over an FLO-enriched carrier) because the plan's own Phase 1 task list calls for a
  genuine staged sequence with successor/limit structure, which route (i) supplies directly and
  route (ii) does not without duplicating the already-landed `ChainCtx` machinery. Recorded in the
  probe's module docstring.
- **FLO-1(a)'s freshness source left abstract**: rather than committing to a specific "reserve
  pool" predicate for raw fresh-label draws (an ambiguity in reconciling the plan Overview's
  literal `V'ᶜ` phrasing against `Context`'s existing `V'`-confinement invariant, which requires
  *every* domain label to satisfy `Label.InW V'`), FLO-1(a) is stated as "not of `dwitness` form
  and absent at the immediately preceding stage," with a docstring note deferring the precise
  source-pool pinning to Phase 2 (which must prove `stepExt` preserves `primeC`'s own
  `V'`-confinement side condition regardless). This is a scoping choice appropriate to a
  DEFINITIONS-only phase, not a resolved mathematical claim.
- **`FloSeq.limit_eq` stated via raw `Set` union**, not by invoking `ChainCtx.unionContext` at
  definition time (which would require `H` already proved `Monotone` on `{τ // τ < σ}` — a proof
  obligation Phase 3 discharges, not a definitional fact available at Phase 1).

## Impacts

- Phases 2-6 of plan v5 can now proceed by discharging the four sorried signatures in order
  (Phase 2/3 in parallel per the plan's Wave 2, then Phase 4, then Phase 5, then Phase 6 to close
  the two pre-existing `deriv_reflect`/`dwitness_mem_of_maximal` sorries).
- No `Cslib/` mainline file was touched; the zero-debt invariant holds. `primeLemma`'s axiom
  footprint is unchanged (`propext`, `sorryAx`, `Classical.choice`, `Quot.sound`) — no regression.
- Guardrail modules (`cs5_symmetric_tail_box_gap`, `cs5Incest_forces_symm`,
  `cs5TwoSidedR_iff_cs5Tail`, task-512 atom-sum) are untouched (not read or modified this
  dispatch).

## Follow-ups

- Phase 2 (`flo_succ`) and Phase 3 (`flo_limit`) are independently dispatchable (parallel, Wave 2
  per the plan's dependency table).
- Phase 5 (`flo_oldlabel_transport`) is flagged in the plan as the mathematical crux and may split
  into 5.1/5.2 sub-phases.

## Plan Deviations

None. All five Phase 1 checklist items were executed exactly as specified: `--lit` grounding read,
mechanism decision made and recorded, `Stage`/task enumeration/`stepExt`/`FloSeq` defined reusing
the landed operations, `FLO` defined as a non-vacuous structure, and all four downstream
obligations stated as sorried signatures.

## References

- `specs/517_labelled_bounded_context_cs5_completeness/plans/12_wellfounded-zorn-oldlabel-reconstruction.md`
  (Phase 1 heading and checklist)
- `specs/517_labelled_bounded_context_cs5_completeness/probes/chain-union-reflection-probe.lean`
  (new module section, "Task 517 Plan v5 Phase 1")
- `specs/517_labelled_bounded_context_cs5_completeness/.orchestrator-handoff.json`
- Literature: `/home/benjamin/Projects/Literature/simpson_1994_intuitionisticmodallogic/chunk_0102.md`,
  `chunk_0103.md`
