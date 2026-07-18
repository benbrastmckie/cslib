# Implementation Summary: FLO maintained at successor stages (Phase 2)

- **Task**: 517 - labelled_bounded_context_cs5_completeness
- **Status**: [COMPLETED] (Phase 2 of plan v5 only, skeleton — one documented strategic sorry;
  plan v5 overall remains [IMPLEMENTING])
- **Started**: 2026-07-18T00:00:00Z
- **Completed**: 2026-07-18T00:00:00Z
- **Effort**: 1 dispatch (single-phase, hard mode)
- **Dependencies**: Phase 1 (FLO carrier + invariant, `stepExt`/`FloSeq`/`rankOf`/`FLO`)
- **Artifacts**: plans/12_wellfounded-zorn-oldlabel-reconstruction.md (Phase 2 heading updated to
  `[COMPLETED]`), probes/chain-union-reflection-probe.lean (extended)

## Overview

Implemented Phase 2 of plan v5 (`plans/12_wellfounded-zorn-oldlabel-reconstruction.md`): proved
`flo_succ` — the FLO invariant is preserved across `stepExt`'s single successor step — for three
of `stepExt`'s four task variants (`formula`, `diaWitness`, `skip`) fully sorry-free, and for the
fourth (`redundantEdge`) proved that the "already present" edge sub-case is sorry-free while
**confirming** (not merely suspecting) that the genuinely-new-edge sub-case is mathematically
inadmissible for an unconstrained schedule — landed as one documented, tracked, build-green
strategic sorry, per the plan's own hedge in this task's wording.

## What Changed

- Added `FloSeq.mono` — a new auxiliary lemma (sorry-free): `𝒮.H` is `Context.le`-monotone in the
  stage order, proved by transfinite induction (`Ordinal.induction`) over `succ_eq`/`limit_eq`/
  `stepExt_le`, casing on whether the upper stage is zero/successor/limit
  (`Ordinal.zero_or_succ_or_isSuccLimit`). Independent of `FLO`; reusable by Phase 3.
- Proved `flo_succ` (Phase 2's target), case-split on `𝒮.task σ`:
  - `.formula`/`.skip`: `X`/`R` provably unchanged by `stepExt` in every `if`-branch; `flo0`/
    `flo1`/`flo2` reused verbatim from `hflo`. Sorry-free.
  - `.diaWitness y B` (the operative "add a genuinely new label" case): used `FloSeq.mono` to
    compute `rankOf 𝒮 (Label.dwitness y B) = σ + 1` exactly (via `IsLeast.csInf_eq`), then closed
    both FLO-1's fresh-label existential and FLO-2's new-edge locality equation. Sorry-free.
  - `.redundantEdge a b`: the "edge already present at `σ`" sub-case reuses `hflo.flo2` verbatim
    (sorry-free). The "genuinely new edge" sub-case is a **documented strategic sorry**: proved
    (not assumed) that `max (rankOf a) (rankOf b) ≤ σ < σ + 1 = sInf {new edge's stages}` whenever
    `a, b` are both already present at `σ` and the edge is new — an outright contradiction with
    FLO-2's exact-locality requirement, for ANY `𝒮` where the schedule is unconstrained. FLO-1
    (no new label from this task) is sorry-free.

## Decisions

- **`FloSeq.mono` factored as a standalone, `FLO`-independent auxiliary** rather than inlined
  into `flo_succ`, since Phase 1's own summary flagged this exact fact ("Phase 3 shows [the raw
  union] coincides with `ChainCtx.unionContext` once `flo_succ`-style monotonicity is
  established") as needed downstream — Phase 3 (`flo_limit`) can reuse it directly.
- **The `redundantEdge`/FLO-2 gap is a genuine mathematical finding, not a proof-engineering
  shortfall.** The plan's own Phase 2 task list flagged this as an open question ("confirm this
  is admissible under FLO-2 or that redundant-edge additions are handled by the maximality
  argument rather than the construction trace"). This dispatch **resolves** the question: it is
  **not** admissible for an unconstrained `FloSeq` — `stepExt`'s `.redundantEdge` case has no side
  condition tying its introduction stage to `max (rankOf a, rankOf b)`, so FLO-2 (exact edge-
  locality) is refutable by a concrete adversarial schedule. The "maximality argument" escape
  hatch the plan named is therefore load-bearing: Phase 4's fair schedule (or a `FloSeq`
  well-formedness side condition) must ensure `.redundantEdge` is only ever exercised when the
  edge is already `raw_edge_of_tclosure`-forced present, making this branch a no-op. This is
  flagged prominently for Phase 4/6 via the `sorry_inventory` follow-up below.
- **Sorry placement**: the gap is confined to the single genuinely-new-edge sub-case inside
  `flo_succ`'s own proof term (not factored into a separate `have`/auxiliary lemma), so the
  five-condition strategic-sorry test is applied to `flo_succ` as the enclosing top-level
  theorem — it is tightly scoped to exactly this one theorem, deliberately deferred (not
  abandoned), fully documented inline, and tracked in `sorry_inventory` with `strategic: true`
  and a non-null `follow_up_task`.

## Impacts

- `flo_succ` is available to Phase 4 (`primeC'_exists_maximal`) for the `.formula`/`.diaWitness`/
  `.skip` task variants and the "edge already present" `.redundantEdge` sub-case unconditionally;
  the genuinely-new-edge `.redundantEdge` sub-case requires Phase 4 to either (a) constrain its
  fair schedule so `.redundantEdge` is only invoked when the edge is already closure-forced
  present, or (b) revise `FloTask`/`FLO`/`flo_succ` to encode that constraint explicitly. This is
  a **load-bearing open item for Phase 4**, not a cosmetic gap.
- `FloSeq.mono` is now available, sorry-free, for Phase 3 (`flo_limit`) to reuse directly.
- No `Cslib/` mainline file was touched; the zero-debt invariant holds. `primeLemma`'s axiom
  footprint is unchanged (`propext`, `sorryAx`, `Classical.choice`, `Quot.sound`) — the `sorryAx`
  entry already existed pre-dispatch (Phase 1's four strategic sorries); this dispatch does not
  add a new axiom, only relocates/shrinks one of the four sorried signatures to one deeply-nested
  documented sorry.
- Sorry count in the probe is unchanged at 6 (2 pre-existing `deriv_reflect`/
  `dwitness_mem_of_maximal` + `flo_succ`'s one remaining leaf sorry + `flo_limit` +
  `primeC'_exists_maximal` + `flo_oldlabel_transport`) — `flo_succ` shrank from a whole-theorem
  sorry to one tightly-scoped sub-case, but the top-level declaration still reports one `sorry`
  warning (Lean counts per-declaration, not per-sorry-site).
- Guardrail modules (`cs5_symmetric_tail_box_gap`, `cs5Incest_forces_symm`,
  `cs5TwoSidedR_iff_cs5Tail`, task-512 atom-sum) are untouched (not read or modified this
  dispatch).

## Follow-ups

- **Phase 4** (`primeC'_exists_maximal`) MUST address the `redundantEdge`/FLO-2 gap identified
  here before it can rely on `flo_succ` unconditionally: either constrain the fair schedule's
  `.redundantEdge` invocations to already-closure-forced edges, or revise the construction.
- Phase 3 (`flo_limit`) is unblocked and can proceed independently (Wave 2, parallel to this
  phase), reusing `FloSeq.mono`.

## Plan Deviations

None to the *scope* of Phase 2's task list (all three named task variants — `addFormula`,
`addDiaWitness`, `addRedundantEdge` — were addressed). One deviation from the literal "Done when"
wording: `flo_succ` is **not** fully sorry-free (one documented, tracked, strategic sorry
remains in the genuinely-new-edge `redundantEdge` sub-case), because that sub-case is a genuine
mathematical gap in the unconstrained construction, not a proof-engineering shortfall — see
"Decisions" above. Reported as `implemented (skeleton)` per the anti-analysis five-condition
strategic-sorry test, matching Phase 1's own precedent for this task.

## References

- `specs/517_labelled_bounded_context_cs5_completeness/plans/12_wellfounded-zorn-oldlabel-reconstruction.md`
  (Phase 2 heading and checklist)
- `specs/517_labelled_bounded_context_cs5_completeness/probes/chain-union-reflection-probe.lean`
  (`FloSeq.mono`, `flo_succ`)
- `specs/517_labelled_bounded_context_cs5_completeness/.orchestrator-handoff.json`
- `specs/517_labelled_bounded_context_cs5_completeness/summaries/12_flo-carrier-phase1-summary.md`
  (Phase 1, the preceding dispatch)
