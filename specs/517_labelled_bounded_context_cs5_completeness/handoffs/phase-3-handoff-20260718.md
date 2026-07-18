# Phase 3 handoff — chain-union / cofinite-encoding obstacle

## Immediate Next Action

Read `probes/chain-union-reflection-probe.lean`'s `ChainCtx.deriv_reflect` docstring (the theorem
carries the full diagnosis inline). Either (a) dispatch Phase 4 first and, once the Zorn
construction's concrete extension-step invariant exists ("each step adjoins only a
reserve-drawn/fresh label"), return to discharge `deriv_reflect`'s sorry using that invariant, or
(b) attempt route (b) from the docstring directly (a monotonicity-based argument for "old" labels
`y ∈ (C i).G.X`) without waiting on Phase 4, if a dispatch wants to close Phase 3 fully before
starting Phase 4.

## Current State

- `specs/517_labelled_bounded_context_cs5_completeness/probes/chain-union-reflection-probe.lean`
  (NEW file, ~340 lines): fully self-contained, sorry-free except for ONE theorem.
  - `swapFn`/`swapFn_left`/`swapFn_right`/`swapFn_other`/`swapFn_swapFn` — the label-swap
    transposition and its involution property. **Proven, sorry-free.**
  - `TClosure.map` — 𝒯-closure transport along an arbitrary relation-pushforward. **Proven,
    sorry-free, zero axioms.**
  - `NIK.swap_relabel` — **the crux**: Prop. 4.4.1 (Simpson `chunk_0087.md`/`chunk_0088.md`)
    specialized to a two-label-swap bijection, by structural induction mirroring
    `NIK.weaken`. **Proven, sorry-free.** Axiom footprint `[propext, Classical.choice,
    Quot.sound]` (the development's existing baseline; no new axioms).
  - `List.map_swapFn_eq_self`, `NIK.freshWitness_transport` — the corollary the reflection
    argument actually consumes (transport a derivation at one fresh witness to any other fresh
    label). **Proven, sorry-free.**
  - `ChainCtx` (structure), `ChainCtx.unionG`, `ChainCtx.unionΓ` — the chain/union scaffold,
    mirroring Simpson's own setup (a SINGLE shared coinfinite `V'` for the whole chain, per
    `chunk_0102.md`'s "Let `V'` be some coinfinite subset ... Consider the set `C` ... contained
    in `W(V')`"). **Proven, sorry-free.**
  - `ChainCtx.deriv_reflect` — the reflection theorem proper. **ONE documented strategic sorry.**
    See its docstring for the full five-condition justification and the precise remaining gap.
  - `ChainCtx.chain_closure` — Phase 3 Task 3's literal deliverable, an immediate corollary of
    `deriv_reflect`. Compiles (inherits the one sorry via `deriv_reflect`).
- No `Cslib/` files were touched. `Labelled/Context.lean`, `Labelled/Deduction.lean`,
  `CS5Canonical.lean`, `CKExtension.lean` are all unchanged from Phase 2's landed state.
- Build verified via `lake env lean specs/.../probes/chain-union-reflection-probe.lean`: exits
  clean except for the single expected `declaration uses 'sorry'` warning at `deriv_reflect`.
  `#print axioms` on every OTHER declaration in the file shows no `sorryAx` and no axioms beyond
  `[propext, Classical.choice, Quot.sound]`.

## Key Decisions Made

1. **Bijective (not general) graph-morphism transport.** Simpson's Prop. 4.4.1 states the
   general-function form; this file diagnosed (and the diagnosis is recorded in the module
   docstring) that a general function cannot rebuild `boxI`/`diaE`'s cofinite premise at a new
   chain index, because it need not be surjective off any finite set. The bijective (swap)
   specialization is what's actually needed and is what's proven.
2. **`ChainCtx` fixes a single shared coinfinite `V'`** across the whole chain, matching
   Simpson's own Zorn-poset setup verbatim (not "each member has *some* coinfinite `V'`" — a
   weaker, insufficient reading that would NOT give the uniform freshness reserve
   `freshWitness_transport` needs).
3. **All Phase 3 work lives in `probes/`**, per the plan's own artifact scoping for this phase
   ("Probes: the inhabitedness gate (Phase 2) and any exploratory chain-union work (Phase 3)").
   No mainline transcription was attempted or is appropriate yet.

## What NOT to Try

- **Do not attempt a fully general (non-bijective) `f` for the reflection lemma** — this was
  analyzed and shown insufficient for `boxI`/`diaE` before landing the swap-based approach; see
  the module docstring's "Diagnosis" section for the exact argument (a general morphism has no
  guaranteed preimage off a finite set).
- **Do not try to prove `deriv_reflect` by extending `freshWitness_transport` to arbitrary
  (non-reserve) `y`** without first either (a) constraining the chain's construction (Phase 4) to
  only ever extend by fresh labels, or (b) finding a genuinely different argument for "old"
  labels. A direct attempt hits the same swap-collision problem diagnosed in the theorem's
  docstring.
- **Do not introduce an axiom** to discharge the sorry. The plan's own Phase 3 contingency
  explicitly prohibits this ("do NOT introduce an axiom or a vacuous placeholder").

## Remaining Goals (verbatim from plan, Phase 3 Task 3)

> Prove chain closure: `(⋃G_i, ⋃Γ_i) ∈ C`.

Mechanized as `ChainCtx.chain_closure`, currently gated on `ChainCtx.deriv_reflect`'s sorry.

## References

- Plan: `specs/517_labelled_bounded_context_cs5_completeness/plans/11_tprime-repair-cs5-completeness.md`
  (Phase 3 body, marked `[PARTIAL]`).
- Progress file: `specs/517_labelled_bounded_context_cs5_completeness/progress/phase-3-progress.json`.
- New probe: `specs/517_labelled_bounded_context_cs5_completeness/probes/chain-union-reflection-probe.lean`.
- Literature: `chunk_0087.md`, `chunk_0088.md` (Prop. 4.4.1, graph morphisms),
  `chunk_0102.md`/`chunk_0103.md` (Lemma 5.3.1, the elided chain-union step), at
  `/home/benjamin/Projects/Literature/simpson_1994_intuitionisticmodallogic/`.
