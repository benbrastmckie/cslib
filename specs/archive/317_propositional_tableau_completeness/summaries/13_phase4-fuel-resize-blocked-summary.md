# Phase 4 Summary: `intFuel` Resize BLOCKED (fuel materialization infeasibility)

- **Task**: 317 (propositional_tableau_completeness)
- **Plan**: `plans/13_fuel-sufficiency-skeleton.md`, Phase 4
- **Status**: [BLOCKED] — no Lean edits landed; build/test remain green at the Phase 3 state
- **Started**: TBD
- **Completed**: TBD
- **Artifacts**: TBD
- **Standards**: TBD
- **Session**: sess_1785275816_a84520_317

## What Happened

Phase 4 required (jointly, as done-criteria): resize `intFuel φ` to dominate
`intExpMeasure (intUniverseExt φ) [[⟨.neg, φ, 0⟩]] [[]]` (target shape
`3 ^ (2 * |intUniverseExt φ|)`-class), prove `intExpMeasureExt_init_le_fuel`, and keep
`lake test` green with no flipped corpus rows.

The pre-edit Scope Hypothesis check (mandated by the phase spec) revealed the phase is
unimplementable as specified. The plan's mitigation — "early exit on saturation/closure
means fuel is a bound, not a step count; `#eval` cost is unaffected" — conflates fuel
*consumption* (which early exit does bound) with fuel *materialization* (which is
unconditional): `intuitionisticTableau` strictly binds `let fuel := intFuel φ`
(`Expansion.lean:522-525`) before `intExpandBranches` runs, so every `#eval` corpus row
must represent the full fuel numeral as a GMP bignum.

## Empirical Defect Record

Probe against the **landed** `WBound`/`intSubfmls` definitions
(`s = (intSubfmls φ).toFinset.card`; `WBound φ = (s+1)^(2^s·s+1)`; resize exponent
`e = 4·(2·complexity+1)·(WBound φ+1)`), run via `lake env lean`:

| Corpus row | φ | s | complexity | WBound digits | e digits | Resized fuel |
|---|---|---|---|---|---|---|
| 1 | `a → a` | 2 | 1 | 5 | 6 | `3^236208` — 112,700 digits, **feasible** |
| 2 | `a → (b → a)` | 4 | 2 | 46 | 47 | needs ≈ 8.6e46 bits ≈ 1e37 GB — **infeasible** |
| 4 | `((a→b)∧a) → b` | 5 | 3 | 126 | 127 | infeasible |
| 6 | `(a→(b→c))→((a→b)→(a→c))` | 9 | 6 | 4610 | 4611 | infeasible |
| — | `(a→b)∨(b→a)` class | 5 | 3 | 126 | 127 | infeasible |

19 of 20 propositional corpus rows fall in the infeasible class. A bounded
materialization attempt of row 2's resized fuel (`% 7`, 4 GB / 90 s cap) aborted with
`lean::exception: failed to create thread` (allocation failure).

## Root Cause (structural)

`WBound` is necessarily doubly-exponential in `s` (tree bound = branching^depth), so
`|intUniverseExt φ| = Θ(WBound φ)` and any fuel satisfying the domination requirement is
a numeral of ≥ ~1e46 bits for `s ≥ 4`. This is not an artifact of Phase 2/3 constant
choices: (a) fuel ≥ enlarged initial measure and (b) `#eval`-ability of
`intuitionisticTableau` are jointly unsatisfiable under the current single-global-fuel
engine architecture. Both are Phase 4 done-criteria.

## Repair Candidates (planner-level)

1. **Per-branch fuel restructuring** of `intExpandBranches`: sufficiency then needs only
   `2·|intUniverseExt φ|`-class fuel values (≤ ~4,700-digit numerals for all corpus rows —
   materializable). Engine + R1 restatement change.
2. **Well-founded recursion on the measure** (fuel-free engine): removes `intFuel` from
   the computational path entirely. Larger refactor.
3. **Split proof-side procedure from `#eval` corpus procedure**: changes what the corpus
   certifies and what `openBranch_countermodel` states; currently a plan non-goal.

The choice gates Phases 6-7, which consume this phase's `intExpMeasureExt_init_le_fuel`
at the `openBranch_countermodel` call-site repair.

## Plan Deviations

None. No Lean edits were attempted; per plan-compliance for `.lean` files, the
unimplementable step was escalated as a blocker rather than substituted with an
alternative design. The full four-element defect record lives in the plan's Phase 4
BLOCKER section.

## Verification State at Exit

- Working tree: no changes to `Cslib/` or `CslibTests/` from this dispatch
- Build/test: green at the Phase 3 commit state (scoped + full build, `lake test`,
  `checkInitImports` all passed at Phase 3 exit; unchanged since)
- Subtree bare-sorry count: 4, unchanged, all pre-existing (`Scheme.lean:619`,
  `Scheme.lean:3055`, `Intuitionistic/Completeness.lean:133`,
  `Minimal/Completeness.lean:125`)
