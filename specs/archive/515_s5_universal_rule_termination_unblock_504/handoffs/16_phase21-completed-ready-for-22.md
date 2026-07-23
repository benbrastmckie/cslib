# Handoff 16: Phase 21 fully COMPLETED -- ready for Phase 22 (KB5)

**Task**: 515 - s5_universal_rule_termination_unblock_504
**Plan**: plans/07_s5-termination-machinery.md (v6)
**Phase**: 21 -- now `[COMPLETED]` (was `[PARTIAL]` after handoffs/15)
**Commits landed this dispatch**: `69d5f657`, `6eefff80`, `ee112b41`, `f1fa2965`, `245e2157`,
`31398911`

## What landed this dispatch

The full four-step Hintikka-wall recipe recorded in the prior dispatch's BLOCKER note (plans/07's
Phase 21 section, handoffs/15). See `summaries/16_phase21-hintikka-wall-landed-completed.md` for
the complete declaration-by-declaration account, the `e`-aware refinement rationale, and full
verification results (sorry-free, axioms `[propext, Classical.choice, Quot.sound]` only, full CI
green, live regression probe confirming the route is genuinely at `fiveFC`).

`modalTableauFive_complete` and `instDecidableFiveValid` are landed, green, and sorry-free.
Task 504's re-scoped deliverable's first half (`fiveValid` decidability) is now fully shipped.

## Resume point for the next dispatch

1. **Do NOT re-derive** any of: `expandedRootTagsFive`/`FiveWorldInvE`/
   `modalApplyOneFive_worldGrowth`/`modalStepBranchFive_preserves_worldInv`
   (`FiveSimplification.lean`), or `ModalLoopAuxFive`/`_bounds`/`_stepPreserved`/
   `modalLoopInvHintikkaFive_initial`/`modalTableauFive_complete`/`fiveValid_decides`/
   `instDecidableFiveValid` (`FrameCompleteness.lean`) -- all landed, green, sorry-free.
2. **Phase 22 (KB5 rule + soundness)** is next per the plan's dependency graph (`Depends on: 21`).
   Read plans/07's Phase 22 section in full before starting.
3. **Phase 22 heading currently reads `[NOT STARTED]` in the last commit** (`31398911`), though
   the *working tree* (uncommitted) carries a stray `[IN PROGRESS]` marker on Phase 22/23 headings
   from a concurrent/prior source -- this was deliberately left untouched again this dispatch (see
   "Stray uncommitted markers" below). Whichever dispatch picks up Phase 22 should reconcile this
   marker as part of its own preflight (mark `[IN PROGRESS]` for real, or investigate whether the
   stray marker reflects actual in-flight work from another session).
4. Per the plan's own note on Phase 22: "reuses the Route-1-corrected + Route-(a)-guarded Five
   pattern (the same root/non-root propagation split AND the same root-aware mint-arm guard)."
   If KB5's mint-arm guard shares Five's root/non-root double-mint structure, KB5's own
   termination argument will likely need an analogue of this dispatch's `expandedRootTagsFive`
   `e`-aware refinement -- budget for that possibility rather than assuming a naive port of
   `FiveWorldInv`-style (`e`-independent) bookkeeping will step-preserve cleanly (it will not, for
   the same reason Five's did not; see `summaries/16_*`'s "e-aware refinement" section for the
   exact trace that revealed this).
5. Resolve every declaration by name (`lean_local_search`/`lean_declaration_file`/grep), not by
   plan line-number citations.
6. Do NOT touch `S5Simplification.lean`'s shared `S5w*` declarations.
7. When staging the plan file, `git diff` it first; if stray concurrent markers are present
   again, use the `git hash-object -w` + `git update-index --cacheinfo` technique (against
   `git show HEAD:<path>` plus your own edits applied to that clean base) rather than
   `git add -p`, which cannot reliably split hunks that interleave your own edits with adjacent
   stray lines (this dispatch found `git add -p`'s hunk splitting insufficient for this exact
   situation -- see commit `31398911`'s message for the technique that worked).

## Stray uncommitted markers (unchanged from handoffs/15, still present)

`specs/515_s5_universal_rule_termination_unblock_504/plans/07_s5-termination-machinery.md`'s
Phase 22/23 headings carry a stray, pre-existing, uncommitted `[IN PROGRESS]` marker from an
unrelated/concurrent source, present since at least handoffs/14. Left untouched again this
dispatch (confirmed via the plumbing-based staging technique in point 7 above, which explicitly
verified the committed blob does NOT include these stray markers).

## Environment notes

- Mathlib cache warm; `lake exe cache get` is a no-op on this branch.
- Concurrent sessions may be active: scope `git add` narrowly to specific files touched, never
  `git add -A` / `git add .`.
- Scoped checks: `lake build Cslib.Logics.Modal.Tableau.FrameCompleteness` (also rebuilds
  `FiveSimplification` transitively). Verify axioms with authoritative `#print axioms` via
  `lake env lean <scratch>.lean`, not `lean_verify` alone.
- `lake lint`/`lake shake`/`lake test` all rebuild/scan the whole default `Cslib` target
  regardless of a module argument -- budget several minutes for each.
