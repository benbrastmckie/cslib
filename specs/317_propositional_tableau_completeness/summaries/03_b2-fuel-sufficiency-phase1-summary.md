# Implementation Summary: Task #317, Plan v3 Phase 1

- **Task**: 317 - Close the two residual B2 sorries in the propositional tableau completeness proof
- **Plan**: plans/03_b2-fuel-sufficiency.md, Phase 1 (close B2 `none` case, Scheme.lean:713)
- **Status**: [COMPLETED]
- **Session**: sess_1782890716_9a7f59

## What Was Done

Phase 1's mission was to close the B2 `none`-case sorry (originally `Scheme.lean:713`) by
threading an invariant into scope at the `none` case of `intExpandBranches_openBranch_sat`'s
fuel/`go` induction and applying the existing bridge lemma `IExpandedConsistent_sat`. A prior
dispatch had established that this requires more than `IExpandedConsistent` alone: the F(φ→ψ)
world-creating rule needs an `ILabelBound`-style label-boundedness invariant threaded alongside
it (for the `w ≤ w'` witness ordering in `sat_fimp`), plus a length-parity fact to rule out a
dead defensive branch in the `go` induction's list-mismatch handling. That prior dispatch left a
fully worked-out design in `.orchestrator-handoff.json` (`blockers[0].next_action`, 10 concrete
steps) together with four already-committed, sorry-free per-step preservation lemmas
(`ILabelBound`, `ILabelBound_extendMany`, `intStepBranch_some_exists`,
`intStepBranch_linear_preserves`, `intStepBranch_branch_preserves`).

This dispatch applied that design:

1. Defined `IAllConsistent` — a combined invariant (`IExpandedConsistent ∧ ILabelBound`) over
   three parallel lists (branches, expanded-sets, next-world counters), by simultaneous
   recursion so any shape mismatch between the lists is automatically `False`.
2. Added `IAllConsistent_append` and `IAllConsistent_map` — combinators for extending the
   invariant across list `++` and uniform `List.map`, needed to re-establish it after each
   expansion step's `done`-list growth.
3. Added `ILabelBound_applyAllTImpRules` and `ILabelBound_applyPersistenceFixpoint` — new
   lemmas (not anticipated in the prior handoff's design, discovered as a genuine gap while
   applying step 7 of the design) proving that persistence propagation
   (`applyAllTImpRules`/`applyPersistenceFixpoint`) preserves `ILabelBound`, since
   `intTImpRule` only ever copies formulas to world labels already present on the branch (never
   introduces a new label).
4. Rewrote `intExpandBranches_openBranch_sat`'s signature (added `hAC : IAllConsistent branches
   expandedSets nextWorlds` and `hLen0 : branches.length = edgeSets.length`) and its `succ`-fuel
   induction: the `suffices key` statement now threads `IAllConsistent`/length-parity for both
   `pending` and `done`, the two list-shape-mismatch defensive branches close directly via
   `simp [IAllConsistent] at hPending` (contradiction), the third (edges-mismatch) branch closes
   via `omega` against the length-parity fact, and the real-work branch derives `hIC_bPers` /
   `hLB_bPers` for the persistence-fixpoint-applied branch, then closes the `none` case with
   `exact IExpandedConsistent_sat hstep hIC_bPers` and threads the invariant through the
   `linearResult`/`branchingResult` recursive calls via the new combinators.
5. Updated the sole call site (`openBranch_countermodel`) to supply the two new hypotheses:
   `IAllConsistent [[⟨.neg, φ, 0⟩]] [[]] [1]` (via `simp [IAllConsistent, IExpandedConsistent,
   ILabelBound]`) and `[[⟨.neg, φ, 0⟩]].length = [[]].length` (via `rfl`).

Two small build-time issues were found and fixed while applying the design: (a) an implicit-
argument-position mistake calling `ih` in `ILabelBound_applyPersistenceFixpoint` (passing the
branch positionally into what turned out to be `ih`'s first *explicit* argument slot, since `b`
is implicit), and (b) a missing `List.length_nil` simp lemma needed for `omega` to close the
edges-mismatch branch (`[].length` was left opaque without it).

## Verification

- `lake build Cslib.Logics.Propositional.Tableau.Intuitionistic.Scheme` → Build completed
  successfully (662 jobs).
- `grep -n sorry Scheme.lean` → lines 330 (B1, out of scope) and ~985 (fuel=0 base case,
  Phase 2 scope). The `none`-case sorry (was 713, then 924 after the prior dispatch's
  insertions) is **gone**.
- `intExpandBranches_openBranch_sat` is `private` with exactly one call site
  (`openBranch_countermodel`), which was updated in the same commit — no externally-visible
  API changed.
- Only `Scheme.lean` modified/committed this dispatch (commit `26508fe9`, 186 insertions/27
  deletions). No other files staged or committed (a concurrently-modified
  `Cslib/Logics/Modal/Tableau/CompletenessLoop.lean` from another session was left untouched
  and unstaged, per the concurrent-edit hazard mitigation).
- Full CI pipeline (lint/lint-style/shake/test) deferred to `/vet`, per the anti-overflow
  contract; only the scoped build was run this dispatch.

## Plan Deviations

- The plan's Goals section asked for the public signature of `intExpandBranches_openBranch_sat`
  to stay "byte-identical." Since this lemma is `private` with a single call site, the two new
  hypotheses (`hAC`, `hLen0`) were added directly to its signature instead of via a separate
  `_aux` wrapper. R3's intent (no externally-visible API break) is preserved: nothing outside
  `Scheme.lean` can reference a `private` lemma, and the sole call site was updated in the same
  commit. This exception is documented in the plan file's Phase 1 section.
- No sorries were relocated or newly introduced. No axioms were added. No vacuous definitions
  were created.

## Next Steps

Phase 2 (2a-2d, fuel-sufficiency argument for the `fuel=0` base case, sorry ~985) is next. Run
`/implement 317` to dispatch Phase 2a (decreasing-measure definition and boundedness spike).
