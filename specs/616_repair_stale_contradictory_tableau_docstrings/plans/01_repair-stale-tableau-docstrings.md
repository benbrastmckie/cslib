# Implementation Plan: Repair Stale and Self-Contradictory Tableau Docstrings

- **Status**: IMPLEMENTING
- **Task**: 616
- **Source**: specs/616_repair_stale_contradictory_tableau_docstrings/reports/01_repair-stale-tableau-docstrings.md

## Scope

DOCUMENTATION ONLY. No `.lean` proof term, statement, or definition may change. Verification
gate: `git diff` shows only comment/docstring hunks; `lake build` green; `CslibTests/` untouched.

Phase decomposition taken directly from the research report's Section 9 (committed scope:
Phases 1-6; Phase 7 explicitly optional, deferred).

## Phases

### Phase 1: Part 1 -- rewrite Scheme.lean:9603-9611 and :9732-9733 [COMPLETED]

- [ ] **Task 1.1**: Keep the frame-adequacy table and "REFUTED" verdict; retarget the evidence
  citation from `WitnessProbe.lean` to `BetaSplitRefutation.lean`'s `fimpWitnesses = [1]` and its
  raw edge list; fix the two companion citations (`:304`->`:318-320`, `:387`->`:377`/`:407-409`).
- [ ] **Task 1.2**: Apply the identical fix at the duplicate site (`:9732-9733`).

### Phase 2: Part 2 (a)(b) -- re-tense present-tense claims [COMPLETED]

- [ ] **Task 2.1**: Re-tense `Scheme.lean:909-915` (copy channel) as PRE-REPAIR historical,
  noting reinstatement per `Expansion.lean:121-127`.
- [ ] **Task 2.2**: Re-tense `Scheme.lean:930-944` (sorry claim) as PRE-REPAIR; `truthLemma` is
  proved at `:1005`. Leave the verbatim quotation at `:921` untouched.

### Phase 3: Part 2 (c)(d)(e) [COMPLETED]

- [ ] **Task 3.1**: Fix `Scheme.lean:4899` (`intExpMeasure_step_lt` proved at `:5097`).
- [ ] **Task 3.2**: Fix `Scheme.lean:7296-7299` (`IAugMembers_persist` landed at `:7917`).
- [ ] **Task 3.3**: Narrow `Expansion.lean:698-700` directive: keep world-bound/`hnw`
  prohibition; strike `hUniv`/`IAllUniv` (now threaded/discharged at `Scheme.lean:9658-9663`).

### Phase 4: Part 2 (f)(g) [COMPLETED]

- [ ] **Task 4.1**: Drop the `sorryAx` parenthetical at `Minimal/DecisionProcedure.lean:22-23`.
- [ ] **Task 4.2**: Replace the dangling task-number reference at `IntDecidability.lean:71-72`
  and `MinDecidability.lean:74-75` with a durable anchor (no task-number citation).

### Phase 5: Part 3 (h)(i) plus sibling S1 [COMPLETED]

- [ ] **Task 5.1**: Fix `Minimal/Completeness.lean:58-61` attribution (live route is `hpersAug`
  over augmented frame per `Scheme.lean:9725-9727`; correct the false "zero references" framing
  for `openBranch_rawEdges_upward_closed`).
- [ ] **Task 5.2**: Fix `Minimal/Completeness.lean:137-138` and `:164-166` parenthetical
  attribution to `minOpenBranch_countermodel`; copy framing from
  `Intuitionistic/Completeness.lean:119-121`.
- [ ] **Task 5.3**: Fix sibling S1 at `Minimal/DecisionProcedure.lean:49-51` (same false
  dependency on `minOpenBranch_countermodel`).

### Phase 6: Part 4 stale line numbers plus siblings S2-S4 [NOT STARTED]

- [ ] **Task 6.1**: Fix `Scheme.lean` self-reference citations per report Section 5.1 and S2/S3.
- [ ] **Task 6.2**: Fix `Rules.lean` cross-reference citations per report Section 5.2 (including
  the `:5148` label swap).
- [ ] **Task 6.3**: Fix `Expansion.lean:514-516` citation (Section 5.3).
- [ ] **Task 6.4**: Fix `Scheme.lean:745` "11th conjunct" -> "7th conjunct" (Section 5.4).
- [ ] **Task 6.5**: Fix sibling S4 duplicate off-target citation at `Scheme.lean:2289`/`:2396`.
- [ ] **Task 6.6**: Apply "keep the name, drop the number" convention where practical for the
  sites touched above.

### Phase 7: Optional -- FmpMeasure.lean citations (Section 5.5) [NOT STARTED]

Explicitly optional and low value per report. Deferred unless time permits after Phases 1-6 are
verified green.

## Verification Protocol

Per report Section 10:
1. Statement-invariance check: `git diff -U0 -- Cslib/` shows only comment/docstring hunks.
2. `lake build` on the three terminal modules in scope, then full `lake build`.
3. `lake test` -- `CslibTests/` must be untouched.
4. `lake exe lint-style`.
5. Task-number lint: no `\b317\b` remains in the two decidability files.
6. Re-resolve corrected citations against their named declarations.
