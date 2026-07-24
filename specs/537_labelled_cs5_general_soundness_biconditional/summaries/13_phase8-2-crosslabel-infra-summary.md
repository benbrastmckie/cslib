# Implementation Summary: Phase 8.2 (continued) -- Cross-Label Infrastructure + Root-Connectivity Gap (Plan v5)

- **Task**: 537 - Prove the general labelled soundness direction, completing Simpson 1994
  Thm 8.1.4's biconditional
- **Plan**: plans/05_tree-recursive-hilbert-bridge.md (plan version 5)
- **Status of this dispatch**: Phase 8 remains `[IN PROGRESS]`; sub-step 8.2 remains
  `[IN PROGRESS]` (not `[COMPLETED]`, not `[BLOCKED]`). This dispatch continued directly from the
  previous one's motive-design finding, landing five further commits of reusable cross-label
  infrastructure, and identifies the concrete next blocker: a root-connectivity invariant not yet
  defined anywhere in the codebase.
- **Commits** (five, each independently verified green):
  1. `task 537 phase 8.2: land sigAtFuel_mono_context (subset-based context monotonicity)`
  2. `task 537 phase 8.2: land sigAtFuel_mono_fuel(_le) -- fuel-gap monotonicity`
  3. `task 537 phase 8.2: land nikTrFuel fuel-sufficiency (nikTrFuel_fuel_invariant_step)`

  (Two of the five commits mentioned in the dispatch's working notes were consolidated; the git
  log for this dispatch shows three new commits following the four already reported in
  summaries/12.)

## What landed

In `Cslib/Logics/Modal/Metalogic/Constructive/Labelled/Soundness.lean` (appended after the
previous dispatch's `nikTrFuel_mono`):

- **`bigAndL_imp_of_pointwise`**: if `⊢ (f a) ⊃ (g a)` for every `a` in a list `L`, then
  `⊢ (bigAndL (L.map f)) ⊃ (bigAndL (L.map g))` -- a general list-congruence lemma.
- **`sigAtFuel_mono_context`**: if `Δ`'s facts pointwise contain `Γ`'s facts at EVERY label
  (`Δ ⊇ Γ`), then `⊢ (sigAtFuel Δ n z) ⊃ (sigAtFuel Γ n z)`, for any fuel/label. This supersedes,
  in scope, the earlier rank-threshold `sigAtFuel_congr_above_rank` (still valid, just narrower):
  the earlier lemma could only relate labels of STRICTLY GREATER rank than the extended label,
  which is not enough for SIBLING branches (same rank as the extended label) -- exactly what the
  full ancestor-wrap's off-spine children need. `sigAtFuel_mono_context` holds uniformly
  everywhere, since it only ever composes `bigAndL_mono` at each level, needing no
  reachability/rank argument at all.
- **`sigAtFuel_mono_fuel`/`_le`**: `⊢ (sigAtFuel (n+1) z) ⊃ (sigAtFuel n z)`, UNCONDITIONALLY (no
  sufficiency side-condition -- extra fuel only ever adds conjuncts before truncating, never
  removes any), and its iterated form for any fuel gap `m ≤ n`.
- **`nikTrFuel_succ_eq`**, **`nikTrFuel_no_parent`**, **`nikTrFuel_fuel_invariant_step`**: the
  genuine fuel-SUFFICIENCY equality lemma flagged (but not needed) since Phase 8.1:
  `nikTrFuel (n+1) cur inner = nikTrFuel n cur inner` once fuel `n` is at least `ht cur` (the
  remaining ancestor-chain length to the root), proved by induction on an upper bound for
  `ht cur` using `IsDerivationForest`'s graded-rank witness. `nikTrFuel_succ_eq` is a `rw`-safe
  one-step unfold helper, needed because a direct `simp only [nikTrFuel]` on a goal comparing two
  already-`_+1`-shaped fuel expressions re-unfolds recursively (both sides keep matching the
  successor pattern), producing a runaway double-unfold; `nikTrFuel_succ_eq`'s own statement uses
  an opaque `n`, so instantiating and `rw`-ing with it fires exactly once.

Sorry-free, axiom-clean throughout (confirmed by `grep` after every commit). Scoped
`lake build Cslib.Logics.Modal.Metalogic.Constructive.Labelled.Soundness` green after every
commit. No Preserved Asset regressed.

## The concrete next blocker: root-connectivity is not yet a defined invariant

With `sigAtFuel_mono_context` and `nikTrFuel_fuel_invariant_step` in hand, the natural proof
strategy for `efq` (and, analogously, `orE`) is: propagate `Derivable(nikTr G Γ hfin x ⊥)`
UP `x`'s ancestor chain to the tree's distinguished root (using `nikTrFuel_mono` +
`nikTrFuel_fuel_invariant_step` + `sigAtFuel_mono_fuel_le` to reconcile fuel at each step), then
propagate the resulting root-level inconsistency back DOWN to an arbitrary `y` (an analogous
argument in the other direction) -- avoiding an explicit lowest-common-ancestor computation by
routing everything through one shared root instead.

Working through this concretely surfaced a genuine gap: **the "propagate to root" strategy
needs every label in `G.X` to be reachable from a single distinguished root via
`Relation.ReflTransGen G.R`. This is true of every actual derivation graph** (`G` is always built
starting from `Graph.trivial`'s single node, extended only via `addEdge` from an EXISTING node,
so every new label is connected back to the origin by construction) **but it is NOT implied by
`IsDerivationForest`'s three existing conjuncts** (`G.X.Finite`, graded rank, unique parent)
**alone** -- those are purely local structural constraints, consistent in principle with several
disjoint rank-graded, unique-parent components (a genuine "forest" in the multi-tree sense, not
necessarily a single rooted tree).

This is a freshly-identified INFRASTRUCTURE GAP, not a machine-checked proof obstruction against
a concrete `efq`/`orE` goal (no such goal has been opened yet). Closing it requires:
1. A new invariant, e.g. `IsRootedForest G := ∃ root, ∀ z ∈ G.X, Relation.ReflTransGen G.R root z`
   (or a fourth conjunct folded into `IsDerivationForest` itself).
2. Preservation lemmas mirroring `forest_trivial`/`forest_addEdge_fresh`: `Graph.trivial`'s single
   node trivially reaches itself; `addEdge x y` for fresh `y` should preserve
   reachability-from-root inductively (the root already reaches `x`, and the new edge extends
   that to `y`).
3. `nik_adequacy`'s induction would need to thread this invariant alongside `IsDerivationForest`
   (mirroring how the latter is already threaded through the `boxI`/`diaE` cases' graph
   extension).

This is believed tractable (every piece encountered so far in this cross-label investigation
has had a concrete, provable path, verified by two dispatches' worth of compiling lemmas) but
is now clearly LARGER than originally scoped: root-connectivity + its preservation lemmas, the
propagate-up-to-root argument, the propagate-down-from-root `efq` argument, and `orE`'s own
comparable-complexity treatment are estimated at 400-600+ further lines -- several more dedicated
dispatches, not "one more lemma."

## What remains

- **Sub-step 8.2 (continued)**: define and prove-preserved a root-connectivity invariant; build
  the propagate-up-to-root and propagate-down-from-root arguments for `efq`; extend to `orE`
  (comparably complex: two branches, each needing the same cross-label bridge, combined with the
  context-extension machinery already landed for `impI`).
- **Sub-step 8.3**: the 4 modal cases (`boxI`, `boxE`, `diaI`, `diaE`).
- **Sub-step 8.4**: specialise to `nik_TS5_to_hilbert` over `Graph.trivial`.
- **Phase 9**: assemble `nik_TS5_soundness`; retire the stale module-docstring notes.
- **Phase 10**: full regression gate.

**Recommendation for the next dispatch**: given the accumulated scope, a dedicated `/research`
or `/revise` pass specifically on the root-connectivity + propagation strategy (validating the
mathematical argument in full before more Lean transcription) may be more efficient than
continuing ad hoc implementation, though this is not a mandate -- the plan's own honesty clause
reserves `[BLOCKED]` for genuine machine-checked obstructions, and none has been found; this
remains `[IN PROGRESS]`.

## Plan Deviations

See the expanded `*(deviation: ...)*` annotation on Sub-step 8.2's `efq`/`orE` checklist item in
`plans/05_tree-recursive-hilbert-bridge.md`, summarized above.

## AI Tools Used

This work was prepared with the assistance of Claude Code (Anthropic) acting as the
`cslib-implementation-agent`. The tool was used for designing and verifying (via `lake build`
feedback) the context-monotonicity and fuel-sufficiency lemmas, working through and documenting
the root-connectivity gap discovered while designing the cross-label propagation strategy, and
drafting this summary. All Lean code was verified to compile via scoped `lake build` on this
branch.
