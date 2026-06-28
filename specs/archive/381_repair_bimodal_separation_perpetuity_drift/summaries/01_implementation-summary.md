# Task 381 — Implementation Summary

## Result: COMPLETE (defined scope: 4 modules) — sorry-free, scoped builds green

Repaired the Mathlib/toolchain-drift failures in the 4 modules named in the task description.
All fixes mechanical; no statement changes, no new lemmas/axioms, no sorry.

## Fixes (5 phases, incremental commits)

| Phase | File | Edits | Fix |
|-------|------|-------|-----|
| 1 | `Separation/Duality.lean` | 2 (l.357,362) | add `Formula.neg, PropositionalConnectives.neg` to simp sets |
| 2 | `Separation/DedekindZ/QLemma.lean` | 1 (l.192) | add `Formula.or, Formula.neg, PropositionalConnectives.neg` |
| 3 | `Separation/Eliminations.lean` | 19 (6 theorems) | add `PropositionalConnectives.neg` to stalled simp sets (3 more sites than planned, in `elim_case_4_gen`) |
| 4 | `Theorems/Perpetuity/Bridge.lean` | 1 (l.101) | raw `swapTemporal` → structural `Bimodal.Formula.swapTemporal_allFuture` |
| 5 | — | — | zero-debt verification |

**Root cause:** under v4.31.0, naming only `Formula.neg` in a simp set unfolds one abbrev
layer (`Formula.neg → PropositionalConnectives.neg`) then stalls, so purity predicates never
see the `.imp` head. Adding `PropositionalConnectives.neg` resolves modules 1-3; Bridge is a
distinct structural-lemma substitution.

## Verification
- All 4 target modules build green (scoped `lake build` per phase).
- Zero sorries in all 4 files; `lake exe lint-style` passes; `lake lint` clean on modified files.
- Commits `3e5938ca` (P1) → `c1e8455b` (P4) → `a67387d8` (complete), linear, no interleaving.

## ⚠️ Newly-surfaced follow-up breakage (out of task-381 scope)
With 381's 4 modules now building, two *downstream* modules in the same Separation cluster —
previously masked because the build stopped at the earlier failures — now surface as failing:
- `Cslib/Logics/Bimodal/Metalogic/Separation/TemporalClosure.lean`
- `Cslib/Logics/Bimodal/Metalogic/Separation/DedekindZ/Cases.lean`

These are almost certainly the same drift family (`PropositionalConnectives.neg` simp-stall).
They were not in task 381's description (which named only Duality/Eliminations/QLemma/Bridge).
**Action:** confirm via a full build after task 364 completes, then repair as a 381 follow-up
(likely trivial — same idiom). Tracked in the orchestrator's running notes.
