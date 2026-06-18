# Implementation Summary: Revise PR #649 to LTL-only

- **Task**: 233 - Revise PR #649 to include LTL only per reviewer comment
- **Session**: sess_1781823963_4f9f03
- **Date**: 2026-06-18
- **Branch**: feat/temporal-formula-propositional
- **Status**: [PR READY]

## Phases Completed

### Phase 1: Rebase and Strip Temporal Content [COMPLETED]

**Changes made**:
- `Cslib/Foundations/Logic/Connectives.lean`: Removed `HasSince` class and `TemporalConnectives`
  bundle class. Updated module docstring to reflect LTL-only scope. Kept `HasUntil`, `HasNext`,
  `FutureTemporalConnectives`, `LTLConnectives`.
- `Cslib/Logics/LTL/Syntax/Formula.lean`: Removed `public import Cslib.Logics.Temporal.Syntax.Formula`
  and removed the `Formula.toTemporal` function with its docstring.
- `Cslib.lean`: Removed `public import Cslib.Logics.Temporal.Syntax.Formula`.
- `references.bib`: Removed `GPSS1980` entry (past-time fairness paper, deferred to Temporal PR).
- `Cslib/Logics/Temporal/Syntax/Formula.lean`: Removed from git tracking (`git rm`).

**Note**: Full rebase onto `feat/propositional-v2` was not necessary — instead, a new commit on
top of the existing PR commit achieves the same result. The diff vs `feat/propositional-v2` now
shows only LTL-related files.

### Phase 2: Update LTL Notation [COMPLETED]

**Changes made** in `Cslib/Logics/LTL/Syntax/Formula.lean`:
- Changed `scoped infix:40 " U "` to `scoped infix:40 " 𝓤 "` (U+1D4E4, `\MCU`)
- Changed `scoped prefix:40 "X"` to `scoped prefix:40 "◯"` (U+25EF, `\bigcirc`)
- Changed `scoped prefix:40 "𝐅"` to `scoped prefix:40 "◇"` (U+25C7, `\Diamond`)
- Changed `scoped prefix:40 "𝐆"` to `scoped prefix:40 "□"` (U+25A1, `\Box`)
- Added `Formula.leadsto` abbreviation: `p ⇝ q := □(p → ◇q)`
- Added `scoped infix:20 " ⇝ "` notation for `Formula.leadsto`
- Updated docstrings for `someFuture` and `allFuture` to use new symbols
- Updated module docstring notation table and main definitions list
- Added `Mathlib.Order.Notation` import (needed for `Bot`/`Top` instances after removing
  the transitive dependency via `Temporal.Syntax.Formula`)

### Phase 3: Include LTL Semantics and Verify Build [COMPLETED]

**Changes made**:
- Created `Cslib/Logics/LTL/Semantics/Satisfies.lean` (new file, 64 LOC)
  - Defines `Satisfies v i φ` over omega-words (standard Kripke/Pnueli LTL semantics)
  - Defines `Valid` and `Satisfiable`
  - Uses Burgess convention for `until`: φ is event, ψ is guard
- Added `public import Cslib.Logics.LTL.Semantics.Satisfies` to `Cslib.lean`

**Build verification**:
- `lake build Cslib.Logics.LTL.Syntax.Formula`: passed (449 jobs)
- `lake build Cslib.Logics.LTL.Semantics.Satisfies`: passed (450 jobs)
- `lake build` (full): passed (2733 jobs)
- `lake exe checkInitImports`: passed (no output = success)
- `lake exe lint-style`: passed (warning about missing nolints-style.txt is expected)

### Phase 4: Update PR Description [COMPLETED]

- Created `specs/233_revise_pr649_ltl_only/pr-description.md` with updated title and body
- Title: `feat(Logics/LTL): LTL formula type and semantics over omega-words`
- Covers: LTL-only scope, notation table, new files, semantics, AI disclosure

## Git Diff Summary (vs feat/propositional-v2)

Files in PR diff:
1. `Cslib.lean` — adds `LTL.Semantics.Satisfies` import
2. `Cslib/Foundations/Logic/Connectives.lean` — LTL-only classes (no HasSince/TemporalConnectives)
3. `Cslib/Logics/LTL/Semantics/Satisfies.lean` — new file, satisfaction over omega-words
4. `Cslib/Logics/LTL/Syntax/Formula.lean` — updated notation, leadsto, no toTemporal
5. `references.bib` — LTL references only (no GPSS1980)

No Temporal-specific content remains in the diff.

## Commit

Branch: `feat/temporal-formula-propositional`
Commit: `761c229c` — task 233 phase 1-3: revise PR #649 to LTL-only with standard notation

## Next Steps

The branch is ready for force-push to update the remote PR #649. Use:
```bash
git push --force-with-lease origin feat/temporal-formula-propositional
```

Then update the GitHub PR:
- Title: `feat(Logics/LTL): LTL formula type and semantics over omega-words`
- Body: See `specs/233_revise_pr649_ltl_only/pr-description.md`
