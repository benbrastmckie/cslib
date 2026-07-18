# Execution Summary: Task 517 Phase 6 — `primeLemma` fully sorry-free

- **Task**: 517 - labelled_bounded_context_cs5_completeness
- **Plan**: `plans/12_wellfounded-zorn-oldlabel-reconstruction.md`, Phase 6
- **Status**: [COMPLETED] — the Phase 4.5 completion milestone (`primeLemma` sorry-free and
  axiom-clean) is met.

## What was done

Closed both of Phase 6's target strategic sorries in
`probes/chain-union-reflection-probe.lean`:

1. **`ChainCtx.deriv_reflect`**: had no prior proof skeleton (a bare `sorry`). Closed via a new
   `GChain` (graph-only chain, dropping `Context`'s `dwitnessMem`/`coinfinite` obligations, which
   `NIK` never reads) and a master structural-induction theorem `NIK.reflectChain` that reflects
   an arbitrary `NIK`-derivation over a chain's union graph down to a single member. The
   `(□I)`/`(◇E)` cofinite cases pick one witness fresh w.r.t. the whole union (drawn from the
   chain's shared reserve `V'ᶜ`), recurse into an extended chain (`GChain.addEdgeAll`), and
   rebuild the *entire* cofinite family from the single reflected instance via
   `NIK.oldLabelTransport`.
2. **`dwitness_mem_of_maximal`**'s diamond "old label" sub-case: closed via
   `NIK.diaWitnessTransportOld` applied directly to `H.G` — no `FloSeq` routing needed.

Both transports are new, **graph-generic** lemmas built directly from `NIK.relabelFresh`
(Phase 5's `substFn`, relocated earlier in the file so both use sites can reach it before
`FloSeq`/`FLO` are even defined):

- `NIK.oldLabelTransport`: one-directional (`substFn`) transport of a `NIK`-derivation witnessed
  at a fresh source label `y₀` to ANY target label `y'` — fresh or already present, no side
  condition on the target at all.
- `NIK.diaWitnessTransportOld`: the `diaE`-premise-shaped analogue.

## The corrected finding (why this closes more than expected)

The prior "Joint follow-up dispatch" diagnosis (recorded at length in the probe's module
docstring preceding `deriv_reflect`) concluded the old-label obstacle needs "route (a)" — the
FLO/`FloSeq` transfinite reconstruction — because every technique it tested (an involutive
`swapFn` swap, or reusing the induction hypothesis with a different chain index per label)
genuinely fails for old labels. **Neither obstacle applies to a one-directional relabeling**:
`substFn a b` (unlike `swapFn a b`) never sends `b ↦ a`, so it never disturbs whatever structure
the target already has — it only needs the *source* fresh, never the target. This was Phase 5's
finding for `flo_oldlabel_transport`; Phase 6 discovered the *same* fact, generalized off `FloSeq`
to an arbitrary `Graph`, closes both remaining sorries **without needing FLO at all**.

Consequently: **`primeLemma` is assembled from `primeC_exists_maximal` (the plain `zorn_le₀`
Zorn maximalisation), not `primeC'_exists_maximal` (the FLO reconstruction)** — it never depended
on FLO. `primeLemma` is now fully sorry-free and axiom-clean independent of `primeC'_exists_maximal`'s
own remaining `Maximal`-conjunct sorry and `flo_succ`'s superseded `redundantEdge` sorry. Both of
those are pre-existing, documented, and explicitly out of this phase's scope (Postmortem
Constraints: "MUST preserve... `flo_succ`... verbatim"; the `Maximal`-conjunct gap is a separate,
deeper undertaking the plan's own Rollback/Contingency section anticipates). They remain landed,
build-green, untouched.

## New hypothesis: `hx₀ : x₀ ∈ G₀.G.X`

Closing `dwitness_mem_of_maximal` surfaced one genuinely new requirement: the excluded label `x₀`
must differ from the freshly-adjoined diamond witness `v`, else the transported conclusion's
label would move out from under `x₀`. This is discharged by adding an explicit hypothesis
`hx₀ : x₀ ∈ G₀.G.X` to `dwitness_mem_of_maximal`, `diamond_of_maximal`, and `primeLemma`. This
is a standard well-formedness assumption — Simpson's own statement of `Γ ⊬_G x:A` presupposes `x`
is a label of `G`, matching the convention `Context.ctxSubset` already enforces for `Γ`'s own
labels — not a weakening of any FLO- or old-label-related argument. `primeLemma`'s downstream
callers (Phase 7+, not yet written) will need to supply this hypothesis.

Also added `Label.ne_dwitness_self` (a diamond-witness label is never its own pivot, by
structural recursion on `Label`) to separate the diamond's pivot label from its own witness.

## Verification

- `lake env lean` on the probe: exit 0, zero errors.
- Sorry count: 2 (both pre-existing, documented, out-of-scope — see above). Down from 4 at the
  start of this dispatch.
- `lean_verify` (axioms `[propext, Classical.choice, Quot.sound]`, no `sorryAx`) confirmed
  individually for: `ChainCtx.deriv_reflect`, `dwitness_mem_of_maximal`, `diamond_of_maximal`,
  and **`primeLemma`** (the headline result).
- Zero new `axiom` declarations; zero vacuous definitions.

## Plan Deviations

- `ChainCtx.deriv_reflect`: altered from "use `flo_oldlabel_transport` directly" (the plan's
  anticipated fix) to a graph-generic `NIK.reflectChain` induction, since `deriv_reflect` is
  stated over the abstract `ChainCtx`/`Preorder ι`, not a `FloSeq` — see plan Phase 6, task 1.
- `dwitness_mem_of_maximal`: altered similarly (graph-generic `NIK.diaWitnessTransportOld`
  instead of routing through `FloSeq`/`primeC'_exists_maximal`), plus a new `hx₀` hypothesis not
  anticipated by the plan — see plan Phase 6, task 2.
- The `primeC'_exists_maximal` Maximal-conjunct sorry (probe line ~2292) was **not** attempted
  this dispatch: it is not on `primeLemma`'s dependency path (the finding above), so closing it
  is not required for this phase's "Done when" milestone. It remains open, documented, tracked
  below for a future dispatch if the FLO apparatus is needed for other purposes.

## Files Modified

- `specs/517_labelled_bounded_context_cs5_completeness/probes/chain-union-reflection-probe.lean`
  (+~590 lines net: relocated `substFn`/`NIK.relabelFresh`; added `GChain`, `NIK.reflectChain`,
  `TClosure.reflectChain`, `exists_fresh_var`, `NIK.oldLabelTransport`,
  `NIK.diaWitnessTransportOld`, `Label.ne_dwitness_self`, `exists_index_of_subset_unionΓ`; closed
  `deriv_reflect` and `dwitness_mem_of_maximal`; threaded `hx₀` through `diamond_of_maximal`/
  `primeLemma`)
- `specs/517_labelled_bounded_context_cs5_completeness/plans/12_wellfounded-zorn-oldlabel-reconstruction.md`
  (Phase 6 marked `[COMPLETED]`; Preserved Assets table's `primeLemma` row updated)

## Remaining Gaps (tracked, non-blocking)

1. `flo_succ`'s `redundantEdge` branch (probe ~line 1961) — superseded by the sorry-free
   `flo_succ_fair`; preserved verbatim per Postmortem Constraints, not touched.
2. `primeC'_exists_maximal`'s `Maximal`-conjunct (probe ~line 2292) — needs a cofinal,
   precondition-aware fairness hypothesis plus an ordinal/cardinality-stabilization argument;
   genuinely deeper proof content, not attempted this dispatch (see that theorem's docstring for
   the exact remaining goal). **Confirmed non-blocking for `primeLemma`.**

## Next Steps

Phase 7: transcribe `primeLemma` (and, if still desired for completeness of the exploratory FLO
line, the FLO machinery) from the probe into `Cslib/` mainline. Since `primeLemma` does not
depend on the FLO apparatus, Phase 7 could transcribe `primeLemma` alone (via
`primeC_exists_maximal`/`zorn_le₀`) without the FLO carrier, simplifying the mainline
transcription relative to the plan's original scope — flagged here for the orchestrator/user to
confirm before Phase 7 begins, analogous to the Phase 4 T-Comp flag already recorded in the plan.
