# Implementation Summary: FLO maintained at limit stages (Phase 3)

- **Task**: 517 - labelled_bounded_context_cs5_completeness
- **Status**: [COMPLETED] (Phase 3 of plan v5 only, fully sorry-free — no strategic sorry needed
  for this phase; plan v5 overall remains [IMPLEMENTING])
- **Started**: 2026-07-18T00:00:00Z
- **Completed**: 2026-07-18T00:00:00Z
- **Effort**: 1 dispatch (single-phase, hard mode)
- **Dependencies**: Phase 1 (FLO carrier + invariant, `stepExt`/`FloSeq`/`rankOf`/`FLO`); parallel
  with Phase 2 (`FloSeq.mono`/`flo_succ`) — not depended upon in the end (see Decisions)
- **Artifacts**: `plans/12_wellfounded-zorn-oldlabel-reconstruction.md` (Phase 3 heading updated to
  `[COMPLETED]`), `probes/chain-union-reflection-probe.lean` (extended)

## Overview

Implemented Phase 3 of plan v5 (`plans/12_wellfounded-zorn-oldlabel-reconstruction.md`): proved
`flo_limit` — the FLO invariant (FLO-0/1/2) is preserved at limit stages, where `FloSeq.limit_eq`
defines the stage's `Context` as a raw chain-union (`Set.iUnion`/existential-over-predecessors)
rather than a `stepExt` step. Fully sorry-free.

## What Changed

- Proved `flo_limit` (Phase 3's target, probe line 1592), sorry-free:
  - FLO-0: reused `rankOf_base` verbatim (identical to every other flo-clause proof in the file).
  - FLO-1: destructed `limit_eq`'s `hX` equation; a label `x ∈ (𝒮.H σ).G.X` at the limit stage `σ`
    unpacks (`Set.mem_iUnion.mp`) to a witnessing predecessor stage `τ < σ` with `x ∈ (𝒮.H τ).G.X`.
    Since FLO-1's conclusion is a statement purely about `𝒮`/`rankOf 𝒮 x`/`(𝒮.H τ').G.X` for some
    existentially-quantified `τ'` — it does not mention `σ` — `(hflo τ hτσ).flo1 x hxτ hx0` (FLO at
    the smaller stage `τ`, from the phase's `hflo : ∀ τ < σ, FLO 𝒮 τ` hypothesis) closes the goal
    for `σ` directly, with no further massaging.
  - FLO-2: symmetric argument on `limit_eq`'s `hR` equation. `(𝒮.H σ).G.R x y` unpacks to a
    witnessing `τ < σ` with `(𝒮.H τ).G.R x y`; FLO-2's conclusion (`max (rankOf x) (rankOf y) =
    sInf {τ' | (𝒮.H τ').G.R x y}`) is likewise independent of `σ`, so `(hflo τ hτσ).flo2 x y hxyτ`
    closes it directly.

## Decisions

- **No dependency on `FloSeq.mono` (Phase 2) or `ChainCtx.unionContext`/`chain_closure`**: the
  plan's task list anticipated reusing `ChainCtx.unionContext`/`chain_closure` "where they
  transfer" and establishing rank well-definedness as a separate step. Neither was needed. The
  reason is structural: `FLO`'s three clauses are stated as properties of `𝒮` and a *fixed* label/
  edge, universally quantified over all stages via the ambient `rankOf 𝒮`/`sInf {τ | ...}`
  expressions — the stage `σ` being proved at appears **only** on the LHS (`x ∈ (𝒮.H σ).G.X` / `(𝒮.H
  σ).G.R x y`), never inside the RHS conclusion. `FloSeq.limit_eq`'s raw union directly supplies a
  witnessing predecessor stage for that LHS membership/relatedness, and the corresponding instance
  of `FLO` at that smaller stage (from the phase's own `hflo : ∀ τ < σ, FLO 𝒮 τ` hypothesis)
  supplies the RHS conclusion unchanged. No monotonicity, no `ChainCtx` scaffolding, and no
  separate "rank is well-defined" lemma were required — `rankOf` was already globally well-defined
  (Phase 1) independent of any particular stage.
- **This resolves the "not by invoking `ChainCtx.unionContext` at *definition* time" design note**
  on `FloSeq` (probe, Phase 1): that note flagged `ChainCtx.unionContext` as a *possible*
  downstream identification, not a required proof route for `flo_limit` itself — the raw union in
  `limit_eq` is sufficient on its own for FLO-preservation, without first establishing coincidence
  with `ChainCtx.unionContext`.

## Impacts

- `flo_limit` is now available to Phase 4 (`primeC'_exists_maximal`) unconditionally — no
  outstanding caveat or scheduling constraint (unlike Phase 2's `flo_succ`, which carries the
  `redundantEdge`/FLO-2 open item for Phase 4 — unaffected by, and unrelated to, this phase).
  Phase 3 was independently dispatchable in parallel with Phase 2 and did not end up needing
  `FloSeq.mono`.
- No `Cslib/` mainline file was touched; the zero-debt invariant holds. `primeLemma`'s axiom
  footprint is unchanged in kind (`propext`, `Classical.choice`, `Quot.sound`, plus `sorryAx` for
  the remaining strategic sorries) — this dispatch closes one of the six pre-dispatch sorries
  (`flo_limit`), shrinking the probe's total sorry count from 6 to 5, and adds no new axiom.
- `lean_verify` on `flo_limit`: axioms `[propext, Classical.choice, Quot.sound]` — no `sorryAx`,
  confirming the theorem itself is genuinely closed, not merely typechecking via a hidden sorry
  elsewhere in its proof term.
- Guardrail modules (`cs5_symmetric_tail_box_gap`, `cs5Incest_forces_symm`,
  `cs5TwoSidedR_iff_cs5Tail`, task-512 atom-sum) are untouched (not read or modified this
  dispatch).

## Follow-ups

- **Phase 4** (`primeC'_exists_maximal`) can now rely on both `flo_succ` (Phase 2, modulo its one
  documented `redundantEdge` caveat) and `flo_limit` (Phase 3, unconditionally) to assemble the
  maximal FLO context via well-founded recursion over `Stage`.
- The Phase 2 `redundantEdge`/FLO-2 finding (fair-schedule side condition needed before
  `.redundantEdge` scheduling is safe) remains open and is entirely Phase 4's concern — untouched,
  unaffected, and not re-litigated by this dispatch.

## Plan Deviations

Task-list wording deviation only (not a scope or "Done when" deviation): the plan's Phase 3 task
list suggested reusing `ChainCtx.unionContext`/`ChainCtx.chain_closure` "where they transfer" and
separately establishing rank well-definedness. Neither sub-step was needed — see "Decisions"
above for the structural reason (`FLO`'s clauses are `σ`-independent on the RHS, so direct descent
through `FloSeq.limit_eq`'s raw union suffices). The phase's actual contract — `flo_limit`
sorry-free, probe build green — is fully met, and met more directly than anticipated; no
mathematical content from the plan's suggested route was skipped, since that route was never
load-bearing for this particular obligation (it remains available for Phase 7's mainline
transcription discussion if a `ChainCtx`-flavored proof is later preferred there).

## References

- `specs/517_labelled_bounded_context_cs5_completeness/plans/12_wellfounded-zorn-oldlabel-reconstruction.md`
  (Phase 3 heading and checklist)
- `specs/517_labelled_bounded_context_cs5_completeness/probes/chain-union-reflection-probe.lean`
  (`flo_limit`, probe line 1592)
- `specs/517_labelled_bounded_context_cs5_completeness/.orchestrator-handoff.json`
- `specs/517_labelled_bounded_context_cs5_completeness/summaries/12_flo-succ-phase2-summary.md`
  (Phase 2, the preceding dispatch)
