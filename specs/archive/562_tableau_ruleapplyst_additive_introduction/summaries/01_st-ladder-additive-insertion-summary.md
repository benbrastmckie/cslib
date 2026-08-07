# Implementation Summary: Introduce `RuleApplySt` Additively and Bridge `modalExpandBranchesGen`

- **Task**: 562 - Introduce RuleApplySt additively and bridge modalExpandBranchesGen
- **Plan**: `specs/562_tableau_ruleapplyst_additive_introduction/plans/01_st-ladder-additive-insertion.md`
- **Status**: Implemented, all three phases `[COMPLETED]`

## What Was Done

Landed the nine machine-verified declarations of the State-Threading Ladder into
`Cslib/Logics/Modal/Tableau/Saturation.lean`, immediately before
`end Cslib.Logic.Modal.Tableau`:

- `RuleApplySt`, `liftRuleApply`, `modalStepBranchGenSt`, `findSome?_map_comm`,
  `modalStepBranchGen_eq_St`, `modalExpandBranchesGenSt`, `modalExpandBranchesGen_eq_St`,
  `modalTableauGenSt`, `modalTableauGen_eq_St`.

**Phase 1** pasted the pre-verified artifact (`artifacts/st-ladder-verified.lean`) verbatim,
renaming the section marker from `(ADDITIVE PROBE)` to the landing form. `git diff` confirmed a
pure addition (164 insertions, 0 deletions) with the `public import` block untouched.
`lake build Cslib` came back green at exactly 3313 jobs, matching the measured baseline.

**Phase 2** expanded all nine placeholder docstrings to `Saturation.lean`'s house style (why a
definition has its shape, not just what it does), added a `## Main Definitions` entry to the
module docstring for the ladder, and added a forward pointer in the section marker naming
`modalExpandBranchesS4Keyed` as the intended first consumer (migration is a separate, later
task). `lake build Cslib.Logics.Modal.Tableau.Saturation` came back green.

**Phase 3** ran the full CI gate and confirmed every measured baseline held exactly:

| Gate | Baseline | Measured | Match |
|------|----------|----------|-------|
| `lake build Cslib` | 3313 jobs green | 3313 jobs green | Yes |
| Modal/Tableau sorry census | 1 (`branchSatisfiableIn_s4FC_ancestor_redirect`) | 1 (same site, `FrameSoundness.lean:1251`) | Yes |
| New `axiom` declarations | 0 | 0 (verified via `git diff` against pre-task HEAD) | Yes |
| Bridge axiom dependencies | `propext`, `Quot.sound` only | `propext`, `Quot.sound` only (all 3 bridges, via `lean_verify`) | Yes |
| `lake exe checkInitImports` | exit 0 | exit 0 | Yes |
| `lake exe lint-style` | exit 0 | exit 0 | Yes |
| `lake lint` | 145 findings (delta 0), 0 in `Saturation.lean` | 145 findings, 0 in `Saturation.lean` | Yes |
| `lake shake` | 9 findings, none in Modal/Tableau | 9 findings, none in Modal/Tableau | Yes |
| `lake test` | exit 0, incl. `S4LoopGuardRegression`, `ModalFrameSeparation` | exit 0, both passed (9378 jobs) | Yes |
| Vacuous definitions | 0 | 0 | Yes |

## Plan Deviations

None. All phase task-checklist items were executed as specified; no steps skipped, altered, or
deferred.

## Constraints Honored

- Purely additive: zero existing declarations edited, zero imports added (confirmed by `git diff`
  against the pre-task HEAD across the whole task, not just per-phase).
- `RuleApply = RuleApplySt Unit` was never attempted as a definitional equality; the explicit
  `liftRuleApply` embedding plus the three proved bridges is what landed, exactly as the plan
  and its docstrings state (bridged, never claimed definitional).
- The `fuel = 0` case of `modalExpandBranchesGen_eq_St` uses the in-file
  `simp only [modalExpandBranchesGen, modalExpandBranchesGenSt]` form (valid because both
  declarations live in the same module), not the standalone-module form from
  `artifacts/st_probe.lean`.
- `modalStepBranchGen_eq_St` was proved via `findSome?_map_comm`, not induction on the branch.
- The state list uses `accs.map fun _ => ()`, never `List.replicate accs.length ()`.
- No `StateM`/`StateT` introduced; the subsystem remains monad-free and computable.
- No out-of-scope work started: `modalExpandBranchesS4Keyed` re-expression, `keys'`
  double-derivation retirement, `modalStepBranchS4Keyed` retirement, `S4LoopInv.outDegEq`
  removal, `modalHintikkaSetGenSt`, box-plus key enrichment, and `Rules.lean`/`Branch.lean` edits
  were all left untouched.
- Zero `sorry`, zero new axioms, zero vacuous definitions.

## Files Modified

- `Cslib/Logics/Modal/Tableau/Saturation.lean` — nine new declarations plus expanded docstrings
  and an updated module-docstring `## Main Definitions` list. Two commits (Phase 1 atomic-batch
  insertion, Phase 2 docstring expansion).

## Commits

- `task 562 phase 1: insert verified St ladder`
- `task 562 phase 2: expand docstrings and module docstring`

## Next Steps

`modalExpandBranchesS4Keyed`'s migration onto `modalExpandBranchesGenSt` (threading `keyss` as
the abstract state, per the forward pointer in the section marker) is a separate, later task —
not started here, per the plan's explicit non-goals.
