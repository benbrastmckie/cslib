# Handoff: Task 515 -- Phase 4 `bClosure`/`eClosure` BLOCKED on a Missing Contiguity Invariant

**Date**: 2026-07-15
**Session**: sess_1784103256_616c12 (cycle 2, resumed after a quota-halt stash recovery)
**Status**: Phase 3 COMPLETED; Phase 4 4/6 fields landed (`eNodup`/`accFresh`/`accKnown`/`outDegEq`),
`bClosure`/`eClosure` **BLOCKED**; Phase 6 COMPLETED (pigeonhole world bound).

## What landed this dispatch

1. **Recovered stashed WIP** (`task515-cycle2-WIP`, ~364 lines) for `modalStepBranchS5g_preserves_accFresh`
   and `_preserves_accKnown` -- both built cleanly with no fixes needed beyond what was stashed.
2. **Fixed `modalStepBranchS5g_preserves_outDegEq`'s outstanding build error** (the stashed draft
   was mid-fix when cut off). Root cause: `rw [modalApplyOne_outDeg_step ..., ← modalApplyOneS5_eshape_eq ...]`
   failed because Lean compiles each syntactically-identical `match ... with` expression appearing
   in a *different* lemma's statement to a *distinct* auto-generated matcher-auxiliary constant --
   `rw`'s `kabstract` cannot unify two such matches even when their scrutinee, arms, and printed
   text are identical, whereas `exact`/term-mode elaboration succeeds via `isDefEq` (which unfolds
   matcher auxiliaries during whnf). Fix: bridge the two lemmas via
   `have hfull := (modalApplyOne_outDeg_step ...).trans (congrArg (fun l => ...) (modalApplyOneS5_eshape_eq ...).symm)`
   (a term composition that typechecks through defeq, not syntactic rw), then `rw [hfull]` and
   case-split cleanly. This is a **reusable pattern** -- watch for it anywhere two lemmas each
   state their own literal `match ... with` over the same scrutinee/arms and you need to equate them.
3. **Landed Phase 6 in full**: `modalKnownWorlds_length_le_worldBoundS5`, a **static** lemma (no
   step-preservation reasoning) taking `keysTotal`/`keysDistinct`/`keysInUniverse` directly as
   hypotheses on a fixed `(b, keys)` pair. Proof: inject each known world into
   `(signedSubfmls φ₀).powerset` via a classical choice of its birth key (`keysTotal`), show the
   injection via `keysDistinct`, show the codomain membership via `keysInUniverse`, then
   `Finset.card_le_card_of_injOn` + `List.toFinset_card_of_nodup` + the pre-existing
   `signedSubfmls_powerset_card_le` (`LoopChecking.lean`; `modalWorldBoundS5 φ₀` is definitionally
   `modalWorldBoundS4 φ₀`, both `2 ^ (2 * (modalSubfmls φ₀).length)`, so the S4-authored powerset
   bound transfers by `rfl`). Added `modalKnownWorlds_nodup_S5` +
   `modalKnownWorlds_fold_nodup_S5` as local re-derivations of `FmpMeasure.lean`'s private
   `modalKnownWorlds_nodup` (unavailable cross-file, mirrors the file's existing `_S5`-suffixed
   local-re-derivation pattern for `modalKnownWorlds_fold_spec`/`mem_modalKnownWorlds`/
   `modalKnownWorlds_mono_append`).

Commits: `db5b837a` (accFresh/accKnown/outDegEq), `8e4a17ba` (Phase 6 pigeonhole).

Full CI green at both commits: `lake build` (3236/3236), `lake exe checkInitImports`,
`lake exe lint-style`, `lake lint` (0 new warnings; the 1 pre-existing `PrimeExclusion.lean`
error is untouched/unrelated), `lake test`, `lake shake` (0 new import-minimization suggestions
for `S5Simplification.lean`). Zero `sorry`, zero new axioms in `S5Simplification.lean`.

## Why `bClosure`/`eClosure` are BLOCKED, not just "not started"

The prior handoff (`01_phase4-generic-field-preservation.md`) correctly flagged these as
"entangled with Phase 6's pigeonhole bound" and recommended proving the pigeonhole bound first,
then using it to close `bClosure`/`eClosure`'s mint-case obligation. **I did that** -- Phase 6 is
now fully landed -- but consuming it does NOT close the gap, because of a mismatch in what the
pigeonhole bound actually proves versus what `bClosure`/`eClosure`'s mint case needs:

- **What Phase 6 gives you**: `(modalKnownWorlds b).length ≤ modalWorldBoundS5 φ₀` -- a bound on
  the *count* of distinct known worlds.
- **What `bClosure`'s mint case needs**: when a step mints a fresh formula at label
  `modalNextWorld b`, showing that formula `∈ modalUniverseS5 φ₀` requires
  `modalNextWorld b ≤ modalWorldBoundS5 φ₀` -- a bound on the *numeric value* of the fresh label
  itself (since `modalUniverseS5 φ₀ := (List.range (modalWorldBoundS5 φ₀ + 1)).flatMap (...)`,
  i.e. membership requires the label to literally be `≤ modalWorldBoundS5 φ₀`).

**A count bound does not imply a value bound** unless you also know the known-world *labels*
form a contiguous range `{0, ..., modalMaxWorld b}` with no gaps (so that
`modalMaxWorld b + 1 = (modalKnownWorlds b).length`, and hence
`modalNextWorld b = modalMaxWorld b + 1 = (modalKnownWorlds b).length ≤ modalWorldBoundS5 φ₀`
follows from Phase 6 directly). Without contiguity, the known worlds could in principle be a
small-count but large-value sparse set (e.g. `{0, 1000000}`), and Phase 6's count bound alone says
nothing about `modalNextWorld b`'s value.

**This contiguity fact is TRUE for this driver** (worlds are only ever minted at exactly
`modalNextWorld b = modalMaxWorld b + 1`, both by `modalApplyOne`'s per-call K rule semantics and
by `modalStepBranchS5gKeyed`'s own mint-case construction; blocked/loop-back steps leave `b`
unchanged so `modalMaxWorld b` is stable across them). But **it is not yet a proven, threaded
invariant anywhere in this codebase**:

- Confirmed via grep (`modalMaxWorld.*length`, `length.*modalMaxWorld`, `modalKnownWorlds.*range`,
  etc. across `FmpMeasure.lean`/`LoopChecking.lean`/`S5Simplification.lean`/`GenericDriver.lean`)
  that only a ONE-DIRECTIONAL per-element fact exists:
  `modalKnownWorlds_le_modalMaxWorld : w ∈ modalKnownWorlds b → w ≤ modalMaxWorld b`
  (`FmpMeasure.lean:1766`, private). There is no existing lemma of the form
  `modalMaxWorld b + 1 = (modalKnownWorlds b).length` (or even the weaker inequality
  `modalMaxWorld b < (modalKnownWorlds b).length` this argument actually needs) anywhere.
- The K-driver's own termination technique (`CompletenessLoop.lean`'s
  `modalMaxWorld_lt_worldBound_of_phiBound`) uses a COMPLETELY DIFFERENT mechanism (a
  `phiBound`/`modalPotential` measure threaded through fuel induction), not a known-worlds-count
  pigeonhole argument at all -- so there is no existing template to copy for this specific
  connection.
- S4's `LoopChecking.lean` documents the identical pigeonhole plan (`modalKnownWorlds_length_le_worldBoundS4`)
  but per the plan's own framing ("S4 also never landed [Phase 6]"), S4 never got far enough to
  need (or discover) this same gap either.

## What is needed to unblock (concrete next step)

Add a **12th `S5LoopInv` field**, e.g.:

```lean
worldsContiguous : modalMaxWorld b + 1 = (modalKnownWorlds b).length
```

(or the weaker `modalMaxWorld b < (modalKnownWorlds b).length`, whichever is easier to thread --
the strict inequality is all `bClosure`/`eClosure`'s mint case actually needs, combined with
Phase 6's `modalKnownWorlds_length_le_worldBoundS5`, to get `modalNextWorld b ≤ modalWorldBoundS5 φ₀`
via `omega`.)

Then prove it is preserved across a `modalStepBranchS5gKeyed` step, by the SAME case split
`modalStepBranchS5gKeyed_acc_shape` already gives (blocked / non-blocked):

- **Blocked case**: `newBs = [b]` (`b` literally unchanged) -- both `modalMaxWorld` and
  `modalKnownWorlds b`'s length are trivially unchanged, so the invariant carries over unchanged.
- **Non-blocked, non-minting case** (`.persistent`/`.notApplicable` on `(modalApplyOneS5 sf b acc).fst`):
  `newBs = [nf ++ b]` where `nf`'s formulas are all at KNOWN labels (never mint), so
  `modalMaxWorld (nf ++ b) = modalMaxWorld b` (needs: appending formulas at already-known labels
  doesn't raise the max) and `modalKnownWorlds (nf ++ b)` has the SAME length as `modalKnownWorlds b`
  (no new labels introduced -- needs a `modalKnownWorlds_length_append_of_known`-style lemma, not
  yet in the codebase either, but should be a short direct consequence of
  `modalKnownWorlds_mono_append_S5` plus a converse "no NEW element added" argument via
  `mem_modalKnownWorlds_S5`).
- **Non-blocked, minting case** (`.linear`/`.branching`): `newBs`'s branches are `nf ++ b` where
  `nf`'s head formula (`x0`) is at label `modalNextWorld b` (fresh, per `modalNextWorld_gt`/
  `modalApplyOne_knownWorlds_step`'s mint disjunct). So `modalMaxWorld (nf ++ b) = modalNextWorld b
  = modalMaxWorld b + 1` (needs: appending a formula at the CURRENT next-world label raises the max
  by exactly 1, a `modalMaxWorld`-specific fact -- check `LoopChecking.lean`/`FmpMeasure.lean` for
  an existing `modalMaxWorld_append_single`-style lemma; the prior dispatch's handoff mentions this
  possibility already for `accFresh` but I did not need it there since `accFresh` only needed the
  INEQUALITY direction, not exact equality). And `modalKnownWorlds (nf ++ b)`'s length is
  `(modalKnownWorlds b).length + 1` (exactly one NEW label, `modalNextWorld b`, is added -- needs
  `modalNextWorld_not_mem_modalKnownWorlds`, already available at `FmpMeasure.lean:1773` but
  PRIVATE, so needs a local `_S5` re-derivation like the others in this file's "Local
  Re-Derivations" section).

**Estimated scope**: this is itself roughly a Phase-4-sized sub-task (a handful of new lemmas plus
threading the 12th field through the `S5LoopInv` structure and its constructor call sites). It was
not attempted this dispatch given the remaining budget and the priority of leaving a clean,
fully-verified, well-documented stopping point rather than a half-finished 12th-field addition.

**Prohibited workarounds** (per task constraints, NOT used): `sorry`, `def bClosure := True`, or
any vacuous placeholder. `bClosure`/`eClosure` are left as `[ ]` NOT STARTED / BLOCKED tasks in the
plan, not marked complete.

## Phase 7 (soundness bridge) -- not attempted this dispatch

Per the resume task's framing, Phase 7 (`FrameSoundness.lean`) is independent of Phases 3-6 and was
flagged as "attempt if time permits". Given the unexpected depth of the `bClosure`/`eClosure`
investigation above (which consumed the remaining budget for this dispatch), Phase 7 was not
attempted. It remains a good candidate for the next dispatch, in parallel with or instead of the
12th-invariant-field work above, since it does not depend on it.

## Recommended next dispatch order

1. Add the 12th `S5LoopInv` field (`worldsContiguous` or equivalent) and its preservation lemma --
   unlocks `bClosure`/`eClosure` (Phase 4) directly, and very likely also `keysTotal`/`keysInUniverse`
   preservation's mint-case obligations (Phase 5), which the prior handoff already flagged as
   sharing "the same pigeonhole-adjacent reasoning as Phase 4's `bClosure`".
2. Once Phase 4 and Phase 5 are fully green, Phase 6 is already done, so the full termination chain
   (Phases 3-6) closes.
3. Phase 7 (soundness bridge) can be attempted independently at any point, per the plan's own
   framing ("forks after P1, runs parallel to P3-P6").
