# Task 382 — Implementation Summary

## Result: COMPLETE — Separation subtree builds green, sorry-free

Follow-up to task 381. The drift cascade extended beyond the 2 initially-identified modules
into 3 more Hierarchy modules; all repaired with the same verified idiom.

## Modules fixed (5, incremental scoped commits)

| Module | Commit |
|--------|--------|
| `Separation/TemporalClosure.lean` (l.283) | `09aab273` |
| `Separation/DedekindZ/Cases.lean` (l.164,283,720,1062,1067-8,1664-7 + cascade) | `8083373a` |
| `Separation/Hierarchy/HierarchyDefs.lean` (l.116) | `62da576e` |
| `Separation/Hierarchy/HierarchyCaseSep.lean` (l.51,248+ many) | `62da576e` |
| `Separation/Hierarchy/HierarchyInduction.lean` (6 sites) | `8054d1c1` |

**Idiom:** add `PropositionalConnectives.neg` (+ `Formula.allFuture/someFuture/top`,
`PropositionalConnectives.top` where applicable) to stalled simp sets so purity predicates
reach the `.imp` head. Same root as task 381.

## Verification (per agent, at completion)
- Separation subtree builds green — 794 jobs.
- Zero sorries in all 5 modified files; zero new axioms; `lake exe lint-style` + `lake lint` clean.
- Authoritative full-tree re-verification deferred until task 364 (Modal/Tableau/Soundness) lands,
  to avoid concurrent-build contention.
