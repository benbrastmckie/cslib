# Implementation Plan: Merge Canonical Model Infrastructure into Strong Completeness Files

- **Task**: 189 - Eliminate legacy weak completeness files by merging canonical model infrastructure into strong completeness files
- **Status**: [NOT STARTED]
- **Effort**: 1.5 hours
- **Dependencies**: None
- **Research Inputs**: specs/189_rename_completeness_to_canonical_model/reports/01_team-research.md
- **Artifacts**: plans/01_implementation-plan.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: cslib
- **Lean Intent**: true

## Overview

Merge the contents of 3 legacy weak completeness files (`Completeness.lean`, `IntCompleteness.lean`, `MinCompleteness.lean`) into their corresponding strong completeness files (`StrongCompleteness.lean`, `IntStrongCompleteness.lean`, `MinStrongCompleteness.lean`), then delete the legacy files and update the barrel. Each source file has exactly one consumer (its corresponding target), zero external declaration references, and zero name conflicts, making this a clean 1:1 collapse.

### Research Integration

Team research (3 teammates) unanimously confirmed feasibility: 19 declarations across 3 files, zero name conflicts, zero circular dependency risk, zero downstream consumer breakage. Conservative extension files, soundness files, MCS, and Lindenbaum files are completely unaffected. Merged file sizes (545, 340, 335 lines) are within CSLib norms. Import substitutions and section ordering are fully specified.

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

No ROADMAP.md found.

## Goals & Non-Goals

**Goals**:
- Merge all canonical model definitions, truth lemmas, and helpers from each legacy file into the corresponding strong completeness file
- Replace legacy imports with direct dependency imports (MCS, IntLindenbaum, MinLindenbaum)
- Install updated module docstrings on all 3 merged files
- Delete the 3 legacy files and update Cslib.lean barrel
- Pass full CI pipeline (lake build, lake test, checkInitImports, lint-style, lake shake)

**Non-Goals**:
- Renaming `canonicalValuation` to `propCanonicalValuation` (deferred, non-blocking)
- Extracting per-connective helpers from StrongCompleteness.lean (future task if file grows)
- Modifying any files outside the 4 directly involved (3 targets + barrel)

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Missing transitive imports after merge | M | L | Add explicit imports; verify with scoped build; clean with lake shake |
| Stale olean cache after file deletion | L | L | lake build handles this; lake clean as fallback |
| Incorrect mk_all timing re-adds deleted modules | L | L | Run mk_all only after file deletion, not before |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2 | 1 |

Phases within the same wave can execute in parallel.

### Phase 1: Merge Content and Update Imports [NOT STARTED]

**Goal**: Absorb all declarations from the 3 legacy files into the 3 strong completeness files, update imports, and install docstrings.

**Tasks**:
- [ ] In `StrongCompleteness.lean`: replace `import Cslib.Logics.Propositional.Metalogic.Completeness` with `import Cslib.Logics.Propositional.Metalogic.MCS`; insert `Completeness.lean` content (canonicalValuation, prop_truth_lemma_atom/bot/and/or/imp, prop_truth_lemma) before the Strong Soundness section; update module docstring
- [ ] In `IntStrongCompleteness.lean`: replace `import Cslib.Logics.Propositional.Metalogic.IntCompleteness` with `import Cslib.Logics.Propositional.Metalogic.IntLindenbaum`; insert `IntCompleteness.lean` content (IntCanonicalWorld, Preorder instance, intCanonicalVal, intCanonicalVal_upward_closed, int_truth_lemma) before the Strong Soundness section; update module docstring
- [ ] In `MinStrongCompleteness.lean`: replace `import Cslib.Logics.Propositional.Metalogic.MinCompleteness` with `import Cslib.Logics.Propositional.Metalogic.MinLindenbaum`; insert `MinCompleteness.lean` content (MinCanonicalWorld, Preorder instance, minCanonicalVal, minCanonicalVal_upward_closed, minBotForces, minBotForces_upward_closed, min_truth_lemma) before the Strong Soundness section; update module docstring
- [ ] Run scoped builds to verify each merged file compiles:
  - `lake build Cslib.Logics.Propositional.Metalogic.StrongCompleteness`
  - `lake build Cslib.Logics.Propositional.Metalogic.IntStrongCompleteness`
  - `lake build Cslib.Logics.Propositional.Metalogic.MinStrongCompleteness`

**Timing**: 1 hour

**Depends on**: none

**Files to modify**:
- `Cslib/Logics/Propositional/Metalogic/StrongCompleteness.lean` - Import swap + content insertion + docstring update
- `Cslib/Logics/Propositional/Metalogic/IntStrongCompleteness.lean` - Import swap + content insertion + docstring update
- `Cslib/Logics/Propositional/Metalogic/MinStrongCompleteness.lean` - Import swap + content insertion + docstring update

**Verification**:
- All 3 scoped builds pass without errors
- Each merged file contains all declarations from its source
- No duplicate `@[expose] public section`, `module`, `variable`, or `universe` declarations

---

### Phase 2: Delete Legacy Files and Full CI [NOT STARTED]

**Goal**: Remove the 3 legacy files, regenerate the barrel file, and verify the full CI pipeline passes.

**Tasks**:
- [ ] Delete `Cslib/Logics/Propositional/Metalogic/Completeness.lean`
- [ ] Delete `Cslib/Logics/Propositional/Metalogic/IntCompleteness.lean`
- [ ] Delete `Cslib/Logics/Propositional/Metalogic/MinCompleteness.lean`
- [ ] Run `lake exe mk_all --module` to regenerate `Cslib.lean` (removes the 3 deleted imports)
- [ ] Verify conservative extension files still build:
  - `lake build Cslib.Logics.Modal.Metalogic.Systems.K.ConservativeExtension`
  - `lake build Cslib.Logics.Temporal.ConservativeExtension`
  - `lake build Cslib.Logics.Bimodal.Metalogic.ConservativeExtension.PropositionalConservativity`
- [ ] Run full CI pipeline:
  - `lake build`
  - `lake test`
  - `lake exe checkInitImports`
  - `lake exe lint-style`
- [ ] Run `lake shake --add-public --keep-implied --keep-prefix` to detect and clean redundant imports

**Timing**: 30 minutes

**Depends on**: 1

**Files to modify**:
- `Cslib/Logics/Propositional/Metalogic/Completeness.lean` - Delete
- `Cslib/Logics/Propositional/Metalogic/IntCompleteness.lean` - Delete
- `Cslib/Logics/Propositional/Metalogic/MinCompleteness.lean` - Delete
- `Cslib.lean` - Regenerated via mk_all (removes 3 import lines)

**Verification**:
- All 3 legacy files no longer exist on disk
- `Cslib.lean` no longer references Completeness, IntCompleteness, or MinCompleteness
- `lake build` passes with zero errors
- `lake test` passes
- `lake exe checkInitImports` passes
- `lake exe lint-style` passes
- `lake shake` reports no actionable issues (or issues are resolved)

## Testing & Validation

- [ ] All 3 merged strong completeness files compile individually (scoped build)
- [ ] All 3 conservative extension files compile (downstream verification)
- [ ] Full `lake build` passes
- [ ] `lake test` passes
- [ ] `lake exe checkInitImports` passes
- [ ] `lake exe lint-style` passes
- [ ] `lake shake --add-public --keep-implied --keep-prefix` passes or redundancies cleaned

## Artifacts & Outputs

- `specs/189_rename_completeness_to_canonical_model/plans/01_implementation-plan.md` (this file)
- `specs/189_rename_completeness_to_canonical_model/summaries/01_execution-summary.md` (after implementation)

## Rollback/Contingency

All changes are confined to 4 edits + 3 deletions. If the merge causes unexpected issues:
1. `git checkout -- Cslib/Logics/Propositional/Metalogic/StrongCompleteness.lean Cslib/Logics/Propositional/Metalogic/IntStrongCompleteness.lean Cslib/Logics/Propositional/Metalogic/MinStrongCompleteness.lean Cslib.lean`
2. `git checkout -- Cslib/Logics/Propositional/Metalogic/Completeness.lean Cslib/Logics/Propositional/Metalogic/IntCompleteness.lean Cslib/Logics/Propositional/Metalogic/MinCompleteness.lean`
3. Run `lake build` to confirm rollback
