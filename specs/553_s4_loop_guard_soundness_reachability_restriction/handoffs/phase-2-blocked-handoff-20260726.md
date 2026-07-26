# Handoff: Task 553, Phase 2 (Decision Gate) BLOCKED

## Immediate Next Action

**Escalate to the user.** This phase was the ancestor-only-blocking route's decision gate: prove
or fail to prove that adding an ancestor back-edge `src -> a` preserves `branchSatisfiableIn
s4FC`. It failed. Per the phase's own "Done when" clause, a `[BLOCKED]` verdict here means **the
route does not close and must be escalated to the user before Phase 3** -- do not resume Phases
3-14 of `plans/03_ancestor-only-blocking.md`, and do not attempt to "soften" this into a partial
success or route around it silently.

## Current State

- `Cslib/Logics/Modal/Tableau/FrameSoundness.lean`: one new lemma landed,
  `branchSatisfiableIn_s4FC_ancestor_redirect` (line 1220), plus a local re-derivation
  `hasEdge_addEdge_cases_anc` (line ~1198, mirrors `Soundness.lean`'s private
  `hasEdge_addEdge_cases`, same pattern as this file's existing
  `hasEdge_mem_successorsOf_origin`). The lemma contains **one `sorry`** (line 1244), landed
  deliberately as a documented strategic skeleton per this dispatch's Recovery Discipline
  ("if genuinely blocked, land a documented strategic-sorry skeleton rather than discarding
  structure") -- this differs from this task's own Phase 10 precedent (which fully reverted its
  scratch lemma); here the instruction was explicit to keep the structure.
- `lake build Cslib.Logics.Modal.Tableau.FrameSoundness` is clean except for the one expected
  `declaration uses 'sorry'` warning at line 1220 (the lemma's start). No other new sorries; a
  repo-wide grep confirms this is the only real `sorry` under `Cslib/Logics/Modal/Tableau/`
  (all other `sorry` string hits are prose in docstrings/comments referencing historical or
  other files' status).
- `lake exe checkInitImports` passes (no new file was added).
- Plan file `plans/03_ancestor-only-blocking.md`: Phase 2 heading is now `[BLOCKED]`; the plan's
  top-level `- **Status**` field is now `BLOCKED`; a new `#### Phase 2 Verdict` subsection
  records the full reasoning, the exact `lean_goal` state at the sorry, and resolves the two
  `NOT-YET-VERIFIED — Phase 2 gate` mapping-table rows (originally lines 178-179) as REFUTED /
  MOOT respectively.
- Committed: `task 553 phase 2: decision gate — ancestor back-edge lemma BLOCKED` (this dispatch's
  sole commit; staged only `Cslib/Logics/Modal/Tableau/FrameSoundness.lean` and the plan file,
  never `git add -A`).
- Territory respected: `LoopChecking.lean`, `FrameCompleteness.lean`, `Rules.lean` untouched
  (read-only reference during this dispatch).

## Key Decisions Made

- Stated the lemma as the **single-hop case** (`hanc : acc.hasEdge a src = true`, i.e. `a` is
  `src`'s direct parent on the spine) rather than a full multi-hop `ReflTransGen` chain. This is
  a deliberate simplification, not a scope-narrowing that dodges the obligation: the general
  multi-hop ancestor case is a strict generalization of this one (more edges to justify, not
  fewer), so if the single-hop base case is unprovable, the general case is unprovable *a
  fortiori*. No further generalization was attempted once the base case blocked.
- Evaluated `blockedRedirect_boxctx_mem_of_boxOrigin` / `blockedRedirect_diaNeg_mem_of_diaOrigin`
  (`LoopChecking.lean:1466,1506`) as the dispatch instructed. Read both in full: they are true,
  sorry-free, but **both require the edge `u → wBlock` to already be recorded in `acc`** before
  they can fire (they derive *syntactic* branch-content transfer via mint-readiness, given an
  existing edge). They characterize what becomes available *after* a redirect edge exists, not a
  route to justifying the edge's *own* addition — the actual Phase 2 obligation. Not reusable as
  a starting point for this lemma.
- The **predicted failure mode never materialized.** The dispatch predicted the proof would
  stall on `keyLowerBd` yielding unwrapped `T(ψ)@a` rather than boxed `T(□ψ)@a`, with a Phase 2b
  boxed-birth-content refinement as the escape hatch. The actual proof reaches a **prior, deeper**
  obstruction: `branchSatisfiableIn`'s witness model is existentially arbitrary, so the very first
  step of extending `m.r` to relate `f(src)`/`f(a)` (forced because `IsTrans` binds the concrete
  relation, not a derived notion) requires transitively closing over *every* ambient predecessor
  of `f(src)`, not just spine-recorded ones -- a family no standalone hypothesis set controls.
  Adopting boxed birth content would not fix this, so **no Phase 2b was added** (the plan
  explicitly permits skipping that task when its trigger condition is not met).
- Recognized (and documented, citing the exact prior comment) that this is the **same
  obstruction** already on record in this file: the `branchPropAdequateIn` module comment states
  that a redirect edge to an existing, reused world "breaks `branchSatisfiableIn`'s edge
  conjunct... outright" -- written for Route P's identical redirect shape. Ancestor-only blocking
  redirects to an existing world in exactly the same way; restricting the target to a spine
  ancestor does not change this.
- Did **not** invoke the `Gore1999` escalation branch: the blocker is not that Massacci's
  literature treatment is insufficient (Prop 8.1 / Technique 8.2 / Pruning Lemma 8.2 were read in
  full and correctly characterized in the plan's own overview as giving only the free
  ancestor->descendant direction). The obstruction is a structural fact about how
  `branchSatisfiableIn` is encoded in this codebase (existentially arbitrary witness models),
  independent of which paper is consulted.

## What NOT to Try

- Do not retry this lemma with a richer `hboxback`/`hdianeg` (e.g. boxed variants, or extending to
  cover more formulas) -- the blocker is not about *which* formulas transfer from `src` to `a`, it
  is about *predecessors of `src` other than `src` itself* that the hypotheses cannot name at all.
- Do not attempt to weaken the goal to `branchPropAdequateIn` "to make Phase 2 pass" -- that is
  exactly the fallback the Preserved Assets table (P9) already anticipates for a BLOCKED verdict;
  it is a different (already-existing, already-landed) invariant, not a repair of this lemma.
  Re-deriving it here would just re-litigate Route P's already-settled retirement question.
- Do not assume the multi-hop spine case might somehow succeed where the single-hop case failed
  -- it strictly adds more edges needing the same unavailable justification.
- Do not sequence Phases 3-14 "around" this blocker (e.g. skipping straight to the spine data
  component on the theory that Phase 2 can be revisited later) -- the phase's own done-condition
  is explicit that a BLOCKED verdict here stops the plan.

## What Would Change the Verdict

Only two avenues were identified as potentially viable, and both require a scope change beyond
this standalone lemma:

1. **A full Hintikka/canonical-model truth lemma** built directly from the branch's own
   saturation invariants (mint-readiness, `S4KeyedHintikkaInv`-style completeness), rather than
   reusing an arbitrary `branchSatisfiableIn` witness. This is driver-dependent by nature (it
   needs the actual completeness/saturation facts the driver maintains) and was explicitly
   excluded from this phase's scope ("no dependence on any driver definition"). It is comparable
   in size to `FrameCompleteness.lean`'s own completeness machinery.
2. **Accepting `branchPropAdequateIn`** (the already-landed weaker invariant) as the target
   instead of full `branchSatisfiableIn`, i.e. reopening the same trade-off Route P already faced
   and the audit already adjudicated. This is not "fixing" the ancestor route -- it is abandoning
   the audit's option (c) in favour of something closer to option (b), a mandate-level decision
   for the user, not this dispatch.

## Remaining Goals (verbatim from plan, Phase 2 — now BLOCKED, not to be resumed without new
user guidance)

- [x] State the lemma (done: `branchSatisfiableIn_s4FC_ancestor_redirect`)
- [x] Attempt the cluster construction (done: reaches the goal state recorded in `#### Phase 2
      Verdict`)
- [x] Evaluate the two `LoopChecking.lean` starting-point lemmas (done: not reusable)
- [ ] Adopt boxed birth content (Phase 2b) -- **not triggered**, see above
- [x] Record the verdict (`#### Phase 2 Verdict`, mapping table resolved)

## References

- Plan: `specs/553_s4_loop_guard_soundness_reachability_restriction/plans/03_ancestor-only-blocking.md`
  (`#### Phase 2 Verdict` section has the full writeup, exact goal state, and mapping-table
  resolution)
- New lemma: `Cslib/Logics/Modal/Tableau/FrameSoundness.lean:1220`
  (`branchSatisfiableIn_s4FC_ancestor_redirect`), local helper at `:1198`
  (`hasEdge_addEdge_cases_anc`)
- Prior obstruction on record: `Cslib/Logics/Modal/Tableau/FrameSoundness.lean`, module comment
  introducing `branchPropAdequateIn` (~30 lines after the new lemma)
- Read-only reference (not modified): `Cslib/Logics/Modal/Tableau/LoopChecking.lean:1466,1506`
  (`blockedRedirect_boxctx_mem_of_boxOrigin`, `blockedRedirect_diaNeg_mem_of_diaOrigin`),
  `LoopChecking.lean:1279` (`keysOriginS4`)
