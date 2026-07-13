# Task 317 Phase 6 Summary: `intUniverse` + `intWork` (PARTIAL)

## Status

**PARTIAL.** Landed `intSubfmls`, `intSubfmls_length_le`, `intUniverse`, `intUniverse_length_le`,
and `intWork`, all sorry-free. Deferred `intExpandBranches_world_bound` to a continuation
(Phase 6.2) per the plan's explicit escape valve for a ballooning world-bound proof.

## What Was Done

Added (additive-only, end of `Scheme.lean`, after `tableau_complete`):

- `intSubfmls : Proposition Atom → List (Proposition Atom)` — structural subformula list,
  mirroring `modalSubfmls` (`FmpMeasure.lean:73-80`) restricted to the propositional connective
  set (`atom`/`bot`/`imp`/`and`/`or`, no `box`/`diamond`).
- `intSubfmls_length_le : (intSubfmls φ).length ≤ 2 * φ.complexity + 1` — mirrors
  `modalSubfmls_length_le`.
- `intUniverse : Proposition Atom → List (ISF Atom)` — the fixed finite `(sign, subformula,
  world)` cell universe, world range `0 .. φ.complexity + 1` (mirrors `modalUniverse`,
  `FmpMeasure.lean:149-152`, using the intuitionistic linear world bound in place of
  `modalWorldBound`).
- `intUniverse_length_le : (intUniverse φ).length ≤ 2 * (2 * φ.complexity + 1) * (φ.complexity
  + 2)` — exactly the exponent `intFuel φ := 3 ^ (2 * (2 * φ.complexity + 1) * (φ.complexity +
  2))` (task 317 phase 5) was pre-sized against. Proved via `sum_map_le_length_mul`
  (`Cslib.Foundations.Logic.Tableau.Measure`), mirroring `modalUniverse_length_le` line-for-line.
- `intWork : List (ISF Atom) → List (ISF Atom) → List (ISF Atom) → Nat` — the per-branch
  counting measure `R(b,e) := |U\b| + |U\e|`, mirroring `modalWork`'s `countP`/`any` pattern
  exactly (`FmpMeasure.lean:190-193`) rather than the plan-sketch's `List.diff` form.

Two new imports added to `Scheme.lean`: `Cslib.Foundations.Logic.Tableau.Measure` (for
`sum_map_le_length_mul`) and `Mathlib.Tactic.Ring` (needed explicitly — `Measure.lean`'s own
`Mathlib.Tactic.Ring` import is private and not re-exported transitively; the build failed with
an "unknown tactic" error on `ring` until this was added).

## Verification

- `lake build Cslib.Logics.Propositional.Tableau.Intuitionistic.Scheme`: GREEN.
- `lake build Cslib.Logics.Propositional.Tableau.Intuitionistic.Completeness
  Cslib.Logics.Propositional.Tableau.Minimal.Completeness`: GREEN (807/807 jobs).
- `lake exe checkInitImports`: exit 0.
- Sorry count: 4, unchanged in location (line-shifted +2 within `Scheme.lean` from the new
  imports: `533→535`, `1386→1388`; `Completeness.lean:133` and `Minimal/Completeness.lean:125`
  untouched).
- No new axioms, no vacuous definitions.

## Plan Deviations

1. **`intWork` uses `countP`/`any`, not `List.diff`.** The plan's Lean-syntax sketch (report 07
   §Q4) wrote `intWork U b e := (U.diff b).length + (U.diff e).length`, but the dispatch
   instructions' primary contract was "mirror `modalWork` (`FmpMeasure.lean:180-196`)", which
   uses `countP (fun sf => !(b.any (· == sf)))`. Chose the proven repo pattern over the
   unverified `List.diff` API sketch — same semantics, lower risk.
2. **`intExpandBranches_world_bound` deferred, not proved.** This is the substantive deviation.
   See `.orchestrator-handoff.json` `blockers[0]` for the full mathematical analysis: the naive
   "ancestor-chain depth" argument is insufficient because `F`-or and `T`-and are ALPHA
   (non-branching) rules in this calculus (confirmed by reading `Rules.lean` directly), so a
   single branch can accumulate multiple sibling worlds at the same depth. The bound is still
   true (an occurrence-tracking argument over the monotonically-growing `expanded` set
   establishes it), but formalizing that argument is comparable in difficulty to Phase 7's
   `intExpMeasure_step_lt` and was not force-fit into this dispatch. No `sorry` was introduced —
   the declaration was simply not added, and the deferral is fully documented in the plan file
   and the handoff's `continuation_context`/`blockers`.

## Artifacts

- `Cslib/Logics/Propositional/Tableau/Intuitionistic/Scheme.lean` (modified, +110 lines)
- `specs/317_propositional_tableau_completeness/plans/06_route-a-frame-plumbing.md` (Phase 6
  heading updated to `[PARTIAL]` with resolution note)
- `specs/317_propositional_tableau_completeness/.orchestrator-handoff.json` (overwritten)

## Commit

`37befd2f` — `task 317 phase 6: intUniverse + intWork + linear world bound`
