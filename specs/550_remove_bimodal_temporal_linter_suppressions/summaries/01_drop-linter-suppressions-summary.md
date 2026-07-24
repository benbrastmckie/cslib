# Implementation Summary: Remove Bimodal/Temporal Linter Suppressions

- **Task**: 550 - Remove ported set_option linter suppressions in Bimodal/Temporal propositional-reasoning files
- **Plan**: specs/550_remove_bimodal_temporal_linter_suppressions/plans/01_drop-linter-suppressions.md
- **Status**: Implemented (all 5 phases complete, CSLib CI green)

## What Was Done

All nine Bimodal/Temporal files identified by the research report had their ported
`set_option linter.* false` suppressions resolved, following the report's empirical
per-file classification and mandated fix ordering.

### Phase 1 — Drop DEAD suppressions (6 files, zero code change)
- `Cslib/Logics/Bimodal/Metalogic/Core/MCSProperties.lean`: removed 3 file-scoped lines (`emptyLine`, `setOption`, `flexible`).
- `Cslib/Logics/Bimodal/Theorems/Perpetuity/Helpers.lean`: removed `longLine`.
- `Cslib/Logics/Bimodal/Theorems/Propositional/Core.lean`: removed `emptyLine`, `longLine`.
- `Cslib/Logics/Bimodal/Theorems/TemporalDerived.lean`: removed `unusedSimpArgs`, `emptyLine`, `longLine`.
- `Cslib/Logics/Temporal/Metalogic/GeneralizedNecessitation.lean`: removed only the file-scoped `emptyLine`; kept the three already-narrowed scoped `... in` lines (`flexible` at a `simp` site, two `unusedSimpArgs`).
- `Cslib/Logics/Temporal/Metalogic/PropositionalHelpers.lean`: removed `emptyLine`.

### Phase 2 — Combinators (wrap 6 long lines, drop 2 suppressions)
Wrapped the 6 lines exceeding the 100-Unicode-column limit at whitespace-safe break
points (original numbering L82, L108, L140, L164, L184, L185; 108/108/101/107/102/118
columns), then dropped the file-scoped `emptyLine` (dead) and `longLine` (real)
suppressions.

### Phase 3 — Perpetuity/Principles (remove 5 blank lines, drop 2 suppressions)
Removed the 5 stray blank lines inside the `persistence` proof and adjacent
declarations (original numbering L158, L167, L184, L187, L196), then dropped the
file-scoped `longLine` (dead) and `emptyLine` (real, resolved last per the
clean-slate gating mechanic) suppressions.

### Phase 4 — Connectives (narrow flexible, drop 4 suppressions)
Added `set_option linter.flexible false in` immediately before `def iffElimLeft` and
`def iffElimRight` (the two declarations whose `simp` side-conditions trigger
`flexible`), matching the already-narrowed pattern in GeneralizedNecessitation.
Then dropped the file-scoped `flexible`, `setOption` (its trigger removed once
`flexible` was scoped), `emptyLine` (dead), and `longLine` (dead) lines.

### Phase 5 — Whole-task verification
- `lake build` (full library, 3255+ jobs): completed successfully; zero warnings on
  any of the nine target files. All warnings observed are pre-existing and confined
  to unrelated files (`Propositional/SequentCalculus`, `Propositional/Tableau`, etc.).
- `lake exe checkInitImports`: clean (no output).
- `lake lint`: "Linting passed for Cslib."
- `lake exe lint-style`: clean (no output).
- `lake test`: exit code 0, zero error-level output; none of the nine target files
  appear in the test-run output.
- `lake exe mk_all --module`: "No update necessary."
- `lake shake --add-public --keep-implied --keep-prefix`: pre-existing import-shape
  findings across the broader library only; none of the nine target files appear.

## Files Modified

- `Cslib/Logics/Bimodal/Metalogic/Core/MCSProperties.lean`
- `Cslib/Logics/Bimodal/Theorems/Combinators.lean`
- `Cslib/Logics/Bimodal/Theorems/Perpetuity/Helpers.lean`
- `Cslib/Logics/Bimodal/Theorems/Perpetuity/Principles.lean`
- `Cslib/Logics/Bimodal/Theorems/Propositional/Connectives.lean`
- `Cslib/Logics/Bimodal/Theorems/Propositional/Core.lean`
- `Cslib/Logics/Bimodal/Theorems/TemporalDerived.lean`
- `Cslib/Logics/Temporal/Metalogic/GeneralizedNecessitation.lean`
- `Cslib/Logics/Temporal/Metalogic/PropositionalHelpers.lean`

## Final State of Suppressions

- 13 of the ~17 file-scoped suppression lines: deleted with zero code change.
- Combinators: 2 file-scoped suppressions deleted; 6 lines reformatted (wrapped).
- Perpetuity/Principles: 2 file-scoped suppressions deleted; 5 blank lines removed.
- Connectives: 4 file-scoped suppressions deleted; 2 new scoped
  `set_option linter.flexible false in` lines added on `iffElimLeft`/`iffElimRight`.
- GeneralizedNecessitation: 1 file-scoped suppression deleted; its 3 pre-existing
  scoped `... in` suppressions (`flexible`, 2x `unusedSimpArgs`) kept unchanged.

No `sorry`, no new axioms, no vacuous definitions, and no semantic proof changes were
introduced anywhere in the nine files.

## Verification Results

- `sorry_count` (nine target files): 0
- `vacuous_count` (nine target files): 0
- `axiom_count` (nine target files): 0 (no axioms added; full-repo baseline unchanged)
- `build_passed`: true (full `lake build`, zero warnings on target files)
- `ci_pipeline_passed`: true (all 7 CSLib CI steps clean or pre-existing-only)

## Plan Deviations

None. All phase task-checklist items were executed exactly as specified in the plan,
including the mandated fix ordering (narrow/drop `flexible` before `setOption`;
resolve `emptyLine` last in files with other real findings).

## Parallel-Safety Note

Per delegation-context instructions, this implementation touched only the nine
Bimodal/Temporal files named in the plan plus this task's `specs/` directory. The
concurrently-modified `Cslib/Logics/Modal/Metalogic/Intuitionistic/CanonicalModel.lean`
and `TruthLemma.lean` (owned by a parallel implementation agent) were never read or
edited. All git commits staged only this task's own files by explicit path — no
`git add -A` / `git add .` was used at any point.
