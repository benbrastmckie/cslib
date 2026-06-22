# Implementation Summary: Task #260

- **Task**: 260 - Add module-level documentation contrasting LTL and Temporal convention differences
- **Status**: [COMPLETED]
- **Date**: 2026-06-20
- **Session**: sess_1781994910_0cdf2d_260

## What Was Done

Added cross-referencing "Convention Note" sections to three Lean module docstrings so that
readers of any one module can quickly locate the other and understand the `untl` argument-order
difference (standard Pnueli vs Burgess convention).

### Files Modified

1. **`Cslib/Logics/LTL/Syntax/Formula.lean`** — added "Convention Note" section after
   "Derived Operators" explaining:
   - This module uses `untl guard event` (standard/Pnueli convention).
   - `Cslib.Logics.Temporal` uses `untl event guard` (Burgess convention).
   - `Cslib.Logics.LTL.Embedding` bridges the two via `reflexiveUntl`.

2. **`Cslib/Logics/Temporal/Syntax/Formula.lean`** — added "Convention Note" section after
   "Derived Temporal Operators" explaining:
   - This module uses `untl event guard` (Burgess convention, matching Axioms.lean).
   - `Cslib.Logics.LTL` uses `untl guard event` (standard convention).
   - `Cslib.Logics.LTL.Embedding` bridges the two.

3. **`Cslib/Foundations/Logic/Connectives.lean`** — added "Module Routing" section after
   the "Design" section with a table showing which bundled class serves which logic module,
   followed by a prose note explaining that `HasUntil` is shared but the argument order
   of `untl` differs by convention.

## CI Verification Results

| Check | Result |
|-------|--------|
| `lake build Cslib.Logics.LTL.Syntax.Formula` | pass |
| `lake build Cslib.Foundations.Logic.Connectives` | pass |
| `lake build Cslib.Logics.Temporal.Syntax.Formula` | pass |
| `lake exe checkInitImports` | pass (no output) |
| `lake exe lint-style` | pass (no output) |

## Plan Deviations

- The table in `Connectives.lean` was initially written with a fourth "Convention" column,
  which caused 4 long-line warnings (lines exceeding the 100-char limit). The column was
  removed and the convention information was moved into the prose paragraph below the table.
  No other deviations from the plan.

## Phases Completed

- Phase 1: Add Convention Documentation to Three Files [COMPLETED]
- Phase 2: Build Verification [COMPLETED]
