# Implementation Plan: Task #526

- **Task**: 526 - Fix `unusedArguments` lint error on `DerivExcludes` in PrimeExclusion.lean
- **Status**: [IMPLEMENTING]
- **Effort**: 0.4 hours
- **Dependencies**: None
- **Research Inputs**: specs/526_fix_prime_exclusion_unused_argument/.orchestrator-handoff.json (research handoff)
- **Artifacts**: plans/01_nolint-deriv-excludes.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, cslib.md, cslib-lint-fix.md, plan-compliance.md
- **Type**: cslib (Lean 4)
- **Lean Intent**: true

## Overview

Silence a `lake lint` (batteries `runLinter`) `unusedArguments` error on the `DerivExcludes`
definition in `Cslib/Foundations/Logic/Metalogic/PrimeExclusion.lean:328`. The fifth argument
`_D : DerivationSystem F` is genuinely unused in the body (which references only `E`, `T`, and
`bigOr`), and the binder is already underscore-prefixed -- but the environment `unusedArguments`
linter does not honor the `_` prefix. The fix adds an `@[nolint unusedArguments]` attribute
immediately before `def DerivExcludes`, retaining the `_D` binder to preserve signature
uniformity with its sibling definitions and its ~18 downstream call sites. This is a single-file,
no-API-change edit.

### Research Integration

Research (see the orchestrator handoff) established:
- Flagged declaration: `DerivExcludes` at `PrimeExclusion.lean:328`, argument 5
  (`_D : DerivationSystem F`).
- Root cause: the environment `unusedArguments` linter (runLinter) does not treat the `_`
  prefix as a suppression signal, so underscore-prefixing alone does not clear the error.
- Recommended fix: add `@[nolint unusedArguments]` after the docstring and before
  `def DerivExcludes`; keep `_D`.
- Rejected alternative: removing `_D` changes the public `DerivExcludes` signature, breaking
  ~18 positional call sites in `CanonicalModel.lean` and `CS5.lean` and violating the
  single-file / no-API-change constraint. `MinLindenbaum.lean` / `IntLindenbaum.lean` use only
  `prime_exclusion` (single-formula) and are unaffected.
- Precedent: 41 existing `@[nolint unusedArguments]` uses across `Cslib/` (confirmed via grep),
  including `Cslib/Logics/Temporal/Metalogic/DenseMCS.lean:202`, which pairs the attribute with
  a `--` comment explaining why the unused binder is retained to match a sibling signature.

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

No ROADMAP.md consulted for this task (no roadmap_path / roadmap_flag provided).

## Goals & Non-Goals

**Goals**:
- Clear the `DerivExcludes` `unusedArguments` lint error reported by `lake lint`.
- Keep the `_D` binder and the `DerivExcludes` signature unchanged (no downstream breakage).
- Follow the established codebase precedent (attribute plus a one-line `--` retention note).

**Non-Goals**:
- Removing or renaming the `_D` argument.
- Modifying any downstream call site (`CanonicalModel.lean`, `CS5.lean`, etc.).
- Fixing any unrelated lint categories or warnings elsewhere in the file or library.

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Attribute placement breaks parsing (wrong position relative to docstring) | M | L | Insert between the closing `-/` of the docstring and the `def` line, mirroring the DenseMCS precedent; verify with `lake build` |
| A different/second declaration is also flagged | L | L | After the edit, run `lake lint` and confirm the `DerivExcludes` error is gone and no new lint appears |
| Signature change accidentally introduced | H | L | Edit only adds an attribute line (and optional comment); the `def DerivExcludes (_D ...) ...` line is left byte-for-byte unchanged |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |

Phases within the same wave can execute in parallel.

### Phase 1: Add `@[nolint unusedArguments]` to `DerivExcludes` [COMPLETED]

**Goal**: Suppress the `unusedArguments` lint on `DerivExcludes` without changing its signature,
then verify the build and linter are clean.

**Tasks**:
- [ ] Open `Cslib/Foundations/Logic/Metalogic/PrimeExclusion.lean` and locate the `DerivExcludes`
      docstring (lines ~324-327) and `def DerivExcludes (_D : DerivationSystem F) (E : Set F) (T : Set F) : Prop`
      at line 328.
- [ ] Insert, immediately after the docstring's closing `-/` and immediately before the `def`
      line, a one-line `--` note that `_D` is retained to match the sibling signatures
      (`DeductivelyClosed D S`, `Admissible D Cons S`, `SetExcludingSupersets D Cons S E`),
      followed by the attribute line `@[nolint unusedArguments]`. Mirror the
      `DenseMCS.lean:200-202` precedent (comment above the attribute).
- [ ] Leave the `def DerivExcludes (_D : DerivationSystem F) ...` line and its body unchanged
      (no signature or binder edits).
- [ ] Run `lake build Cslib.Foundations.Logic.Metalogic.PrimeExclusion` and confirm it succeeds
      with no errors.
- [ ] Run `lake lint` and confirm the `DerivExcludes` `unusedArguments` error is gone and no new
      lint warnings/errors were introduced.

**Timing**: 0.4 hours

**Depends on**: none

**Files to modify**:
- `Cslib/Foundations/Logic/Metalogic/PrimeExclusion.lean` - add a `--` retention comment and the
  `@[nolint unusedArguments]` attribute directly before `def DerivExcludes` (line ~328); no other
  changes.

**Verification**:
- `lake build Cslib.Foundations.Logic.Metalogic.PrimeExclusion` completes without errors.
- `lake lint` no longer reports the `DerivExcludes` `unusedArguments` error and reports no new
  issues.
- `git diff` shows only the added comment/attribute lines; the `def` signature is unchanged.

---

## Testing & Validation

- [ ] `lake build Cslib.Foundations.Logic.Metalogic.PrimeExclusion` succeeds.
- [ ] `lake lint` shows the `DerivExcludes` `unusedArguments` error removed, with no new warnings.
- [ ] `git diff Cslib/Foundations/Logic/Metalogic/PrimeExclusion.lean` confirms the change is
      limited to the added attribute (and optional comment) and that the `_D` binder/signature is
      untouched.

## Artifacts & Outputs

- Modified `Cslib/Foundations/Logic/Metalogic/PrimeExclusion.lean` (attribute added).
- Execution summary at `specs/526_fix_prime_exclusion_unused_argument/summaries/01_nolint-deriv-excludes-summary.md`.

## Rollback/Contingency

The change is a single additive edit (one attribute line, one optional comment). To revert,
delete the added `@[nolint unusedArguments]` line and the accompanying `--` comment, restoring
the file to its pre-edit state. If `lake lint` still reports the error after the attribute is
added, re-check that the attribute sits immediately before `def DerivExcludes` (not before the
docstring, and not attached to an adjacent declaration), and that the linter name is spelled
exactly `unusedArguments`.
