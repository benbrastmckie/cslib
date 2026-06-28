# Implementation Plan: Task #358

- **Task**: 358 - Fix Modal GenericMCSBridge outdated/self-contradictory docs
- **Status**: [COMPLETED]
- **Effort**: 0.5 hours
- **Dependencies**: None
- **Research Inputs**: specs/358_fix_modal_mcs_bridge_outdated_docs/reports/01_modal-mcs-bridge-docs.md
- **Artifacts**: plans/01_modal-mcs-bridge-docs.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, cslib.md
- **Type**: cslib
- **Lean Intent**: false

## Overview

`Cslib/Logics/Modal/Metalogic/GenericMCSBridge.lean` is a documentation-only file (no Lean
declarations) that self-contradicts: a `CORRECTION NOTICE` (lines 14-35) retracts the original
gap analysis as OUTDATED, but the obsolete Component 1/2/3 analysis, Conclusion table, Follow-up
Tasks, and a trailing standalone `NOTE` block (lines 37-160) remain and assert the now-retracted
claims. This plan replaces the entire docstring body (lines 12-160) with the corrected, non-self-
contradictory status note supplied verbatim in Section 4 of the research report, while preserving
lines 1-10 (copyright header, `module  -- shake: keep-all`, the two `public import`s) exactly. The
change is a pure docstring rewrite: no Lean declarations are added or removed, zero proof
obligations, zero sorry risk.

### Research Integration

The research report (Section 2) verified the CORRECTION NOTICE is the accurate account by reading
the two sibling bridge files (`Temporal/Metalogic/GenericMCSBridge.lean`,
`Bimodal/Metalogic/Core/GenericMCSBridge.lean`), which contain complete proven theorems. The
corrected understanding: the temporal-style bridge IS buildable; the genuine remaining barrier is
an infrastructure gap (no single type `S` to instantiate `algebraicDerivationSystem` at for an
arbitrary `Axioms` predicate, requiring a `HilbertOf Axioms` wrapper type), not a semantic one.
Section 3 recommends REMOVE (not archive) the obsolete text -- git history preserves it, and the
corrected docstring retains every still-accurate fact. Section 4 supplies a complete drop-in
replacement docstring; Section 5 confirms scope, build/CI expectations, and the line-1-10
preservation requirement (including `-- shake: keep-all`).

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

No ROADMAP.md consulted (no roadmap_path provided in delegation context).

## Goals & Non-Goals

**Goals**:
- Remove the obsolete, retracted gap analysis (current lines 37-160, including the trailing
  standalone `/-! NOTE ... -/` block).
- Replace the docstring body (lines 12-160) with the corrected status-note docstring from
  Section 4 of the research report.
- Preserve lines 1-10 verbatim, including `module  -- shake: keep-all` and both `public import`s.
- Keep the file documentation-only (no Lean declarations) and self-consistent.

**Non-Goals**:
- Implementing the `HilbertOf Axioms` wrapper type or any bridge theorem (deferred follow-up,
  task 350 scope).
- Updating the back-references in the Temporal (line 51) and Bimodal (line 61) bridge files that
  describe this file as "gap analysis" -- flagged as optional/nice-to-have, out of strict scope.
- Any change to other modal files or call sites.

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Nested ` ```lean ` code fences inside the doc comment fail to parse | M | L | The pattern is already used in the current file (lines 141-148) and siblings; verified to compile. Run `lake build` on the module to confirm. |
| Accidentally altering lines 1-10 (especially `-- shake: keep-all`) | M | L | Edit targets only the block from line 12 onward; verify lines 1-10 are byte-identical after the edit; `lake shake` would otherwise strip imports from this declaration-free file. |
| Unicode glyphs (`□`, `↔`, `→`) introduce parse hazards | L | L | These glyphs already appear in the current file and siblings; no new hazards introduced. |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |

Single-phase plan; no parallelism.

### Phase 1: Rewrite module docstring and verify [COMPLETED]

**Goal**: Replace the self-contradictory docstring body with the corrected status note and confirm
the file still builds and lints clean.

**Tasks**:
- [ ] Read the current file to confirm line boundaries (block to replace spans line 12
      `/-! # GenericMCS Bridge Analysis...` through line 160, end of the trailing `NOTE` block).
- [ ] Replace lines 12-160 with the corrected docstring from Section 4 of the research report
      (report lines 128-198: the `/-! # GenericMCS Bridge for Normal Modal Logics (status note) ... -/`
      block). This removes the CORRECTION NOTICE meta-commentary, the Gap Analysis (Component
      1/2/3), the Conclusion table, the obsolete Follow-up Tasks, and the standalone `NOTE` block.
- [ ] Confirm lines 1-10 are unchanged (copyright header, `module  -- shake: keep-all`, both
      `public import`s).
- [ ] Run `lake build Cslib.Logics.Modal.Metalogic.GenericMCSBridge` and confirm the doc comment
      parses.
- [ ] Run `lake lint` and confirm no new warnings (no declarations to document, so no docBlame
      impact expected).

**Timing**: 0.5 hours

**Depends on**: none

**Files to modify**:
- `Cslib/Logics/Modal/Metalogic/GenericMCSBridge.lean` - Replace docstring body (lines 12-160)
  with the corrected status-note docstring; preserve lines 1-10 verbatim.

**Verification**:
- `lake build Cslib.Logics.Modal.Metalogic.GenericMCSBridge` succeeds.
- `lake lint` reports no new warnings.
- File contains no Lean declarations (still documentation-only).
- No `CORRECTION NOTICE`, `## Gap Analysis`, `### Component`, `## Conclusion`, or trailing
  standalone `/-! NOTE ... -/` block remains.
- Lines 1-10 unchanged, including `module  -- shake: keep-all`.

---

## Testing & Validation

- [ ] `lake build Cslib.Logics.Modal.Metalogic.GenericMCSBridge` passes (doc comment parses,
      including nested ` ```lean ` fences and unicode glyphs).
- [ ] `lake lint` produces no new warnings.
- [ ] Manual read confirms the file is internally consistent (no retracted claims remain).
- [ ] Lines 1-10 preserved verbatim (`-- shake: keep-all` intact so imports are not stripped).

## Artifacts & Outputs

- Modified `Cslib/Logics/Modal/Metalogic/GenericMCSBridge.lean` (docstring-only change).

## Rollback/Contingency

The change is confined to a single file's docstring. To revert, restore the file from git
(`git checkout Cslib/Logics/Modal/Metalogic/GenericMCSBridge.lean`). Since the prior content is
committed, the obsolete analysis remains recoverable from history if needed. If the nested code
fence unexpectedly fails to parse, fall back to escaping or removing the inner ` ```lean ` example
block while keeping the prose, then re-run `lake build`.
