# Task 317 -- Phase 7.2 (`intExpMeasure_step_lt_branch`) + Phase 8 (blocked) Summary

## Scope

Hard-mode dispatch (orchestrator per-phase mode) targeting two closely-related `Scheme.lean`
pieces for Wave B: the deferred Phase 7 BETA-arm wiring lemma, and Phase 8's initial-measure
fuel-sufficiency bound. Both required to land in `Scheme.lean` (R7 single-writer), sequentially,
as two separate green commits.

## Commit 1 (landed): Phase 7.2 -- `intExpMeasure_step_lt_branch`

- Completes `intExpMeasure_step_lt`'s coverage of `intStepBranch`'s `.branchingResult` arm
  (F-or/T-and), which Phase 7 deferred as a small follow-up.
- Mirrors `modalExpMeasure_step_lt`'s branching case (`FmpMeasure.lean:2921-2937`): case-splits
  on `intApplyRuleFull`'s two branching constructors (`.pos,.or` and `.neg,.and`, both literal
  2-element lists of singletons per `Rules.lean:254,260`), applies the already-committed
  `intWork_drop` twice (once per sub-branch, `hsub` trivial) and combines via
  `pow3_two_add_one_le` (`Measure.lean:117`).
- Required one new additive helper not needed by Phase 7's linear-arm lemma:
  `intExpMeasure_const_exp` (mirrors `modalExpMeasure_const_exp`, `FmpMeasure.lean:2856`, using
  `List.map_prod_left_eq_zip` to collapse `intExpMeasure U newBs (newBs.map (fun _ => newExp))`
  into a plain sum), needed because the branching arm's expanded-set list is
  `branches'.map (fun _ => newExp)` (a genuinely non-trivial multi-element constant map), unlike
  Phase 7's single-successor case.
- ~128 lines, additive, sorry-free. Committed `Scheme.lean` only:
  `task 317 phase 7.2: intExpMeasure_step_lt_branch (BETA arm)` (`b5d2fc86`).
- Verification: scoped build of `Intuitionistic.Completeness` + `Minimal.Completeness` GREEN;
  `lake exe checkInitImports` exit 0; `lean_verify` on the new lemma reports only
  `[propext, Classical.choice, Quot.sound]` (no new axioms); four inventory sorries unchanged
  (`Scheme.lean:535,1388`; `Completeness.lean:133`; `Minimal/Completeness.lean:125`).

## Commit 2 (NOT landed): Phase 8 -- `intExpMeasure_init_le_fuel` BLOCKED

Before touching `Scheme.lean` for Phase 8 (per the H2 anti-analysis read budget, verification was
done via `lean_run_code #eval`, not by reading files), the literal target goal was checked
directly:

```
intExpMeasure_init_le_fuel φ : intExpMeasure (intUniverse φ) [[⟨.neg, φ, 0⟩]] [[]] ≤ intFuel φ
```

This is **mathematically false** against the current `intFuel`/`intUniverse`/`intWork`
definitions -- verified with two concrete examples:

| `φ` | `\|intUniverse φ\|` | `intFuel φ` | `intWork_init` | `intExpMeasure_init` |
|---|---|---|---|---|
| `atom "p"` (complexity 0) | 4 | `3^4 = 81` | 7 | `3^7 = 2187` |
| `atom "p" → atom "q"` (complexity 1) | 18 | `3^18 = 387,420,489` | 35 | `3^35 = 50,031,545,098,999,707` |

Both examples exactly match the closed form `intWork_init = 2 · |intUniverse φ| - 1`: `intWork`'s
second term (`|U \ e|`) equals the FULL `|U|` when `e = []` (nothing is "in" an empty exclusion
list), and the first term (`|U \ b|`) is `|U| - 1` for the singleton initial branch. So the true
initial value of the measure scales as `~2·|U|`, not `~|U|`.

`intFuel`'s exponent (`Expansion.lean:462-463`, landed Phase 5: `2 * (2·φ.complexity + 1) *
(φ.complexity + 2)`) was pre-sized to exactly EQUAL `intUniverse_length_le`'s bound
(`Scheme.lean:1894-1897`'s doc comment: "exactly the exponent `intFuel φ` ... was pre-sized
against"), with no doubling. This appears to be an oversight carried since Phase 5 -- it was not
computable until Phase 6 fixed `intUniverse`'s concrete size and Phase 7 fixed `intWork`'s
concrete formula.

The Modal-K template does **not** have this gap: `modalFuel`'s exponent
(`4 * (2·modalComplexity φ + 1) * (modalWorldBound φ + 1)`, `FmpMeasure.lean:232-233`) is already
2x `modalUniverse_length_le`'s bound -- see `modalExpMeasure_entry_le_fuel`'s own `hexp`/`heq`
derivation (`FmpMeasure.lean:231-242`), which explicitly computes `2 · |modalUniverse φ|` as the
needed quantity before invoking `Nat.pow_le_pow_right`.

**No sorry, no vacuous placeholder, and no weakened restatement of `intExpMeasure_init_le_fuel`
was introduced.** No edit to `Scheme.lean` was made for Phase 8; the phase is marked `[BLOCKED]`
in the plan with the full numeric evidence and recommended fix (see plan file, Phase 8 section).

### World-bound necessity finding (as separately requested by the dispatch)

This blocker is a pure scalar exponent-sizing gap in `intFuel`, orthogonal to
`intExpandBranches_world_bound` (Phase 6's deferred distinct-label-count fact). The planned
Phase 8 proof strategy (`intUniverse_length_le` + `sum_map_le_length_mul`/geometric caps) never
references distinct-world counting. This confirms and extends Phase 7's own finding:
`intExpandBranches_world_bound` remains unnecessary for the fuel-sufficiency chain.

### Recommended next step

A new **Phase 8.0** (out of this dispatch's territory -- `Expansion.lean`, not `Scheme.lean`):
double `intFuel`'s exponent (e.g. `4 * (2 * φ.complexity + 1) * (φ.complexity + 2)`, mirroring
the Modal-K factor-of-2 pattern exactly), then re-audit all fuel-pinned callers per Phase 5's own
audit note (`Soundness.lean` both variants, `DecisionProcedure.lean` both variants, `Scheme.lean`'s
hardcoded fuel-literal call sites). This should be a safe increase (more fuel only helps
termination) but must be re-verified, not assumed. Only after Phase 8.0 lands green should Phase 8
proper be re-attempted with the same strategy (`intUniverse_length_le` + geometric caps), which
should then close since `2·|U| - 1 ≤ 4·(2c+1)·(c+2) - 1` comfortably fits under the doubled
exponent.

## Verification

- `lake build Cslib.Logics.Propositional.Tableau.Intuitionistic.Scheme` -- GREEN.
- `lake build Cslib.Logics.Propositional.Tableau.Intuitionistic.Completeness
  Cslib.Logics.Propositional.Tableau.Minimal.Completeness` -- GREEN.
- `lake exe checkInitImports` -- exit 0.
- `grep -rn '\bsorry\b'` across the three modules -- 4 sorries, unchanged locations
  (`Scheme.lean:535,1388`; `Completeness.lean:133`; `Minimal/Completeness.lean:125`).
- `lean_verify Cslib.Logic.PL.intExpMeasure_step_lt_branch` -- `[propext, Classical.choice,
  Quot.sound]` only.

## Plan Deviations

- Phase 8 was NOT completed as specified; it is BLOCKED pending a new Phase 8.0
  (`Expansion.lean` exponent fix). This is a deviation from the dispatch's Commit-2 expectation,
  justified by a verified mathematical falsity of the target goal (not a proof-difficulty issue),
  documented with concrete numeric counterexamples rather than left as an unexplained gap.
- No `Scheme.lean` changes were made for Phase 8; only the plan file and orchestrator handoff
  were updated to reflect the blocker.

## Artifacts

- `Cslib/Logics/Propositional/Tableau/Intuitionistic/Scheme.lean` -- `intExpMeasure_const_exp`,
  `intExpMeasure_step_lt_branch` (new, additive, sorry-free).
- `specs/317_propositional_tableau_completeness/plans/06_route-a-frame-plumbing.md` -- Phase 7
  resolution note extended with 7.2; Phase 8 rewritten to `[BLOCKED]` with full evidence.
- `specs/317_propositional_tableau_completeness/.orchestrator-handoff.json` -- updated.
- Commit `b5d2fc86`: `task 317 phase 7.2: intExpMeasure_step_lt_branch (BETA arm)`.
