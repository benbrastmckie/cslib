# Implementation Plan: Mixin + Bridge Refactor for BimodalConnectives

- **Task**: 229 - typeclass_diamond_resolution_lean4
- **Status**: [COMPLETED]
- **Effort**: 30 minutes
- **Dependencies**: None
- **Research Inputs**:
  - reports/01_team-research.md
  - reports/02_team-research.md
  - reports/03_bridge-design.md
- **Artifacts**: plans/04_mixin-bridge-refactor.md (this file)
- **Standards**:
  - .claude/rules/artifact-formats.md
  - .claude/rules/state-management.md
- **Type**: cslib

## Overview

Change `BimodalConnectives` to extend `TemporalConnectives` (primary) with `HasBox` as an atomic mixin, replacing the current design that extends `ModalConnectives` with `HasUntil`/`HasSince` as mixins. Add one bridge instance for `ModalConnectives` at priority 100. This follows the standard Mathlib mixin pattern and gives `BimodalConnectives` automatic synthesis of `TemporalConnectives`, `FutureTemporalConnectives`, and `PropositionalConnectives` through the primary chain.

Done when: `lake build` passes, all 8 parent instances synthesize from `[BimodalConnectives F]`, and the bridge provides `ModalConnectives`.

## Goals & Non-Goals

- **Goals**:
  - `[BimodalConnectives F]` provides `[TemporalConnectives F]` automatically (currently fails)
  - `[BimodalConnectives F]` provides `[ModalConnectives F]` via bridge instance
  - Zero downstream file changes
  - Standard Mathlib-compatible pattern
- **Non-Goals**:
  - Adopting `class abbrev` (deferred — can be done later if bridge count grows)
  - Changing any other connective class definitions
  - Modifying formula type instances

## Risks & Mitigations

- **Risk**: Projection names change (`toModalConnectives` → `toTemporalConnectives`). **Mitigation**: Grep confirms zero uses of any bundled connective projection in the codebase.
- **Risk**: Bridge instance creates synthesis loop. **Mitigation**: Empirically verified — `ModalConnectives` does not extend `BimodalConnectives`, so the bridge is one-directional.

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |

Phases within the same wave can execute in parallel.

### Phase 1: Refactor BimodalConnectives and add bridge [COMPLETED]

- **Goal**: Change primary parent to `TemporalConnectives`, add `ModalConnectives` bridge
- **Tasks**:
  - [ ] In `Cslib/Foundations/Logic/Connectives.lean`, replace the `BimodalConnectives` class definition and docstring (lines 150-153):
    - Old: `class BimodalConnectives (F : Type*) extends ModalConnectives F, HasUntil F, HasSince F`
    - New: `class BimodalConnectives (F : Type*) extends TemporalConnectives F, HasBox F`
  - [ ] Add bridge instance after the class definition:
    ```lean
    instance (priority := 100) [BimodalConnectives F] : ModalConnectives F where
      bot := HasBot.bot
      imp := HasImp.imp
      box := HasBox.box
    ```
  - [ ] Update the docstring to explain the new design
  - [ ] Run `lake build` to verify compilation
  - [ ] Run `lake exe checkInitImports` and `lake test`
- **Timing**: 30 minutes
- **Depends on**: none

## Testing & Validation

- [ ] `lake build` passes (syntax linters run during build)
- [ ] `lake exe checkInitImports` passes
- [ ] `lake test` passes
- [ ] Verify `inferInstance : TemporalConnectives F` succeeds from `[BimodalConnectives F]`
- [ ] Verify `inferInstance : ModalConnectives F` succeeds from `[BimodalConnectives F]`

## Artifacts & Outputs

- plans/04_mixin-bridge-refactor.md (this file)
- summaries/04_mixin-bridge-summary.md (after implementation)

## Rollback/Contingency

Revert the single file change in `Connectives.lean` — restore `extends ModalConnectives F, HasUntil F, HasSince F` and remove the bridge instance.
