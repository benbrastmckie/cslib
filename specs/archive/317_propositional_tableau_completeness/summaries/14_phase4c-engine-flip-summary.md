# Phase 4C Summary: Flip Entry Points + Retire Old Engine + Corpus Gate

- **Task**: 317 - Fill the remaining propositional/intuitionistic tableau completeness sorries
- **Plan**: plans/14_fuel-materialization-repair.md, Phase 4C
- **Status**: [COMPLETED]
- **Started**: TBD
- **Completed**: TBD
- **Artifacts**: TBD
- **Standards**: TBD

## What Was Done

Phase 4C flips the tableau entry points onto the per-branch-fuel engine built in Phases 4A/4B
and retires the old global-fuel engine. Dispatch start found objectives 1-4 already landed
**uncommitted** in the working tree from a prior interrupted 4C dispatch: `intuitionisticTableau`/
`minimalTableau` had already been moved from `Expansion.lean` into `Scheme.lean` and redefined on
the renamed `intExpandBranches` (formerly `intExpandBranchesB`) engine, and the fuel-0 sorry had
already been materialized into the per-branch engine's exhaustion arm. The tree was RED: downstream
consumers in `Soundness.lean` and `Minimal/Soundness.lean` still referenced the old
global-fuel-typed `intExpandBranches`/`intuitionisticTableau`, which no longer existed with that
signature.

This dispatch completed the flip:

1. **Verified** the pre-existing uncommitted work (objectives 1-4, and the private-lemma bodies
   for objective 5) was correct and complete.
2. **Retired dead old-engine code** (objective 6): deleted the old-signature
   `intExpandBranches_closed_unsat` and `intuitionisticTableau_sound` from
   `Intuitionistic/Soundness.lean` (735 lines), and the old `minimalTableau_sound` from
   `Minimal/Soundness.lean` (49 lines) — both duplicated theorems already relocated to
   `Scheme.lean` and were type-broken by the engine's `fuel : Nat -> fuels : List Nat` signature
   change.
3. **Fixed fallout**: an `omit [Hashable Atom] in` clause needed to move before (not after) a
   docstring; module-level docstrings in both Soundness files were refreshed to stop claiming
   ownership of theorems that now live in `Scheme.lean`.
4. **Repointed the corpus import** (objective 7): `CslibTests/TableauConformance.lean` now
   imports `Intuitionistic.Scheme` instead of `Intuitionistic.Expansion` (both `import` and
   `public meta import` lines).
5. **Fixed three `lake shake` findings** caused by the flip: dropped the now-unused
   `Cslib.Logics.Propositional.Subformula` import from `Expansion.lean`; added it to
   `Scheme.lean` (where the content that needs it now lives); added `Mathlib.Data.List.Basic`
   to `Soundness.lean`.
6. **Ran the full CI gate and the 44-row corpus timing gate** (objective 8).

No 4A parity-probe section was found in the tree to remove — that task item was a no-op.

## Verification

- `lake build`: green, 3311/3311 jobs.
- `lake build CslibTests`: green; `CslibTests.TableauConformance` fresh-compiled in 5.7s (this
  includes executing all 44 `#eval` corpus rows at elaboration time, including the
  divergence-witness row 20).
- `lake test`: 3.4s total wall time. **TIMING GATE**: budget is ≤3 minutes or ≤5× the Phase 4A
  baseline, whichever is looser — passes with a very large margin.
- `lake exe checkInitImports`: exit 0.
- `lake lint`: 0 findings in `Tableau/Intuitionistic`, `Tableau/Minimal`, or
  `TableauConformance.lean` (pre-existing findings elsewhere in the repo are out of territory
  and untouched).
- `lake exe lint-style`: exit 0.
- `lake shake --add-public --keep-implied --keep-prefix`: 0 remaining findings in territory
  after the three import fixes.
- Sorry census: exactly 4, unchanged from Phase 4B.
- `lean_verify`:
  - `intuitionisticTableau_sound`: sorry-free, `{propext, Classical.choice, Quot.sound}`.
  - `minimalTableau_sound`: sorry-free, `{propext, Classical.choice, Quot.sound}`.
  - `tableau_complete`: carries `sorryAx` (expected — transitively via the fuel-0 strategic
    sorry).
  - `openBranch_countermodel`: carries `sorryAx` (expected, same reason).

## Sorry Inventory (unchanged from Phase 4B, exactly 4)

| File | Line | Statement | Discharge |
|------|------|-----------|-----------|
| `Intuitionistic/Scheme.lean` | 551 | `truthLemma` T-imp case | Phase 7 |
| `Intuitionistic/Scheme.lean` | 4479 | fuel-0 exhaustion arm of `intExpandBranches_openBranch_sat` (moved 1-for-1 from the retired global-fuel lemma's fuel-0 case) | Phase 6 |
| `Intuitionistic/Completeness.lean` | 133 | DP-3 intuitionistic validity bridge | task 430 |
| `Minimal/Completeness.lean` | 125 | DP-4 minimal validity bridge | task 430 |

## Plan Deviations

- The plan's Phase 4C task list did not anticipate that a prior dispatch would leave the flip
  half-done, uncommitted, in the working tree. This dispatch treated that state as a resume
  point rather than starting the flip from scratch — no plan step was skipped, but the
  bookkeeping (which lemmas needed retiring in `Soundness.lean`/`Minimal/Soundness.lean`) had
  to be re-derived from the actual diff rather than the plan's task list alone, since the task
  list describes the target state, not the incremental steps a partially-completed flip still
  needs.
- A stray `[IN PROGRESS]` marker on the Phase 5 heading (also left over from the same prior
  interrupted session, and not caused by this dispatch's own work) was reverted to
  `[NOT STARTED]` since Phase 5 has no content yet and this dispatch did not touch it —
  correcting a false status marker for the next dispatch, per single-phase-focus discipline.

## Files Modified

- `Cslib/Logics/Propositional/Tableau/Intuitionistic/Expansion.lean`
- `Cslib/Logics/Propositional/Tableau/Intuitionistic/Scheme.lean`
- `Cslib/Logics/Propositional/Tableau/Intuitionistic/Soundness.lean`
- `Cslib/Logics/Propositional/Tableau/Minimal/Soundness.lean`
- `CslibTests/TableauConformance.lean`
- `specs/317_propositional_tableau_completeness/plans/14_fuel-materialization-repair.md`
- `specs/317_propositional_tableau_completeness/progress/phase-4C-progress.json`

## Next Phase

Phase 5: `hUniv`/`hNW` threading invariants (division point DP-2). Not started.
