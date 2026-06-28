# Implementation Summary: Task #358

- **Task**: 358 - Fix Modal GenericMCSBridge outdated/self-contradictory docs
- **Status**: implemented
- **Session**: sess_1782522754_5f0817_358
- **Date**: 2026-06-27

## What Was Done

Replaced the entire module docstring body (old lines 12-160) of
`Cslib/Logics/Modal/Metalogic/GenericMCSBridge.lean` with the corrected status-note
docstring from Section 4 of the research report.

**Removed**:
- `CORRECTION NOTICE` meta-commentary (lines 14-35)
- Obsolete `## Gap Analysis` with `### Component 1/2/3` (lines 46-98)
- Obsolete `## Conclusion` table (lines 112-122) asserting the two systems "cannot replace each other"
- Obsolete `## Follow-up Tasks` (lines 124-133) recommending retiring `modalDerivationSystem`
- Trailing standalone `/-! NOTE: ... -/` block (lines 153-160)

**Added** (drop-in from research report Section 4):
- Clean status-note title: `# GenericMCS Bridge for Normal Modal Logics (status note)`
- `## The bridge IS buildable` section with corrected technical explanation
- `## Why it is not proved here yet (infrastructure gap)` section
- `## What modal logics can already use today` section with working `#check` examples
- `## Follow-up task` section pointing to task 350 scope

**Preserved verbatim**:
- Lines 1-10: copyright header, `module  -- shake: keep-all`, both `public import`s

## Verification

- `lake build Cslib.Logics.Modal.Metalogic.GenericMCSBridge`: PASSED (588/588 jobs)
- `lake lint`: pre-existing failure on unrelated `Cslib.Logics.Bimodal.Theorems.Perpetuity.Principles`
  missing `.olean` file; no new warnings from this change
- No `CORRECTION NOTICE`, `## Gap Analysis`, `### Component`, `## Conclusion`, or trailing
  `/-! NOTE ... -/` block remains in the file
- Lines 1-10 unchanged (verified by read after edit)
- File remains documentation-only: zero Lean declarations, zero sorries, zero axioms

## Plan Deviations

None. Executed exactly as planned.

## Artifacts

- Modified: `Cslib/Logics/Modal/Metalogic/GenericMCSBridge.lean`
