# Implementation Plan: Task #187

- **Task**: 187 - Fix remaining quality issues in Propositional/ and Foundations/
- **Status**: [NOT STARTED]
- **Effort**: 1.5 hours
- **Dependencies**: 185 (audit, completed)
- **Research Inputs**: specs/187_propositional_foundations_quality_fixes/reports/01_fix-verification.md
- **Artifacts**: plans/01_implementation-plan.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: cslib
- **Lean Intent**: true

## Overview

Research verified that 9 of 14 original audit items are already fixed. Four items remain: one missing References docstring section, one misleading theorem name with downstream consumers, one pair of simp lemma additions, and one optional subsumption helper rename. This plan addresses all four as two compact phases -- docstring and naming changes first (no build risk), then simp lemma additions with build verification.

### Research Integration

Key findings from `01_fix-verification.md`:
- Items 1-6, 8-10, 12, 14 already resolved in prior commits
- Item 7 partially resolved (4 of 5 files done; Consistency.lean still missing References)
- Item 11 (`lem` rename) confirmed misleading; 2 downstream files in Bimodal need update
- Item 13 (@[simp] lemmas) requires new simp lemmas for `Evaluate` and `IForces` base cases
- Subsumption helper rename (`toIntProp`/`toProp`) is bonus; 3 downstream call sites

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

No ROADMAP.md found.

## Goals & Non-Goals

**Goals**:
- Add References section to Consistency.lean module docstring
- Rename misleading `lem` theorem and update all downstream consumers
- Add @[simp] lemmas for Evaluate and IForces base cases
- Rename subsumption helpers to more descriptive names

**Non-Goals**:
- Lake shake import hygiene (30 files; separate task)
- Any structural refactoring beyond naming fixes
- Changes to proof logic or theorem statements

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Rename `lem` breaks downstream consumers | M | L | Grep confirms exactly 2 consumers; update atomically |
| @[simp] lemmas cause proof regressions | M | L | Add lemmas, run `lake build` to verify no regressions |
| Subsumption rename missed call site | L | L | Grep verified 3 call sites (MinLindenbaum, IntLindenbaum, CLL/Basic -- CLL is unrelated) |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2 | 1 |

Phases within the same wave can execute in parallel.

### Phase 1: Docstring and Naming Fixes [COMPLETED]

**Goal**: Fix the References docstring gap, rename misleading `lem` theorem and subsumption helpers, update all downstream references.

**Tasks**:
- [ ] Add `## References` section to `Cslib/Foundations/Logic/Metalogic/Consistency.lean` module docstring (after line 31), citing [ChagrovZakharyaschev1997] Section 5.1 for Lindenbaum's lemma and standard Zorn's lemma reference
- [ ] Rename `lem` to `neg_identity` in `Cslib/Foundations/Logic/Theorems/Propositional/Core.lean` (line 63); update docstring entry at line 18 and the theorem docstring at line 61
- [ ] Update `Cslib/Logics/Bimodal/Theorems/Propositional/Core.lean` line 44: rename `def lem` to `def neg_identity` and update the reference to `_root_.Cslib.Logic.Theorems.Propositional.Core.lem` on line 45
- [ ] Update `Cslib/Logics/Bimodal/Metalogic/Algebraic/BooleanStructure.lean` line 306: change `Theorems.Propositional.lem` to `Theorems.Propositional.neg_identity`
- [ ] Rename `MinPropAxiom.toIntProp` to `MinPropAxiom.toIntPropAxiom` in `Cslib/Logics/Propositional/ProofSystem/Axioms.lean` line 155
- [ ] Rename `IntPropAxiom.toProp` to `IntPropAxiom.toPropAxiom` in `Cslib/Logics/Propositional/ProofSystem/Axioms.lean` line 168
- [ ] Update call sites in `MinLindenbaum.lean` (lines 373, 378): `toIntProp.toProp` to `toIntPropAxiom.toPropAxiom`
- [ ] Update call site in `IntLindenbaum.lean` (line 446): `h_ax.toProp` to `h_ax.toPropAxiom`
- [ ] Run `lake build` to verify all renames compile

**Timing**: 45 minutes

**Depends on**: none

**Files to modify**:
- `Cslib/Foundations/Logic/Metalogic/Consistency.lean` - add References section to docstring
- `Cslib/Foundations/Logic/Theorems/Propositional/Core.lean` - rename `lem` to `neg_identity`
- `Cslib/Logics/Bimodal/Theorems/Propositional/Core.lean` - update lem reference
- `Cslib/Logics/Bimodal/Metalogic/Algebraic/BooleanStructure.lean` - update lem reference
- `Cslib/Logics/Propositional/ProofSystem/Axioms.lean` - rename subsumption helpers
- `Cslib/Logics/Propositional/Metalogic/MinLindenbaum.lean` - update call sites
- `Cslib/Logics/Propositional/Metalogic/IntLindenbaum.lean` - update call site

**Verification**:
- `lake build` succeeds with no errors
- `grep -rn '\.lem\b' Cslib/` returns no matches in Propositional or Foundations
- `grep -rn 'toIntProp\b\|\.toProp\b' Cslib/Logics/Propositional/` returns only the renamed versions

---

### Phase 2: Add @[simp] Lemmas [NOT STARTED]

**Goal**: Add @[simp] lemmas for Evaluate and IForces base cases to improve downstream proof automation.

**Tasks**:
- [ ] Add `@[simp] theorem Evaluate_atom` and `@[simp] theorem Evaluate_bot` after `Evaluate` definition in `Cslib/Logics/Propositional/Semantics/Basic.lean`
- [ ] Add `@[simp] theorem IForces_atom` and `@[simp] theorem IForces_bot` after `IForces` definition in `Cslib/Logics/Propositional/Semantics/Kripke.lean`
- [ ] Run `lake build` to verify no proof regressions from new simp lemmas
- [ ] Run `lake exe checkInitImports` and `lake exe lint-style` for CI compliance

**Timing**: 45 minutes

**Depends on**: 1

**Files to modify**:
- `Cslib/Logics/Propositional/Semantics/Basic.lean` - add @[simp] lemmas for Evaluate
- `Cslib/Logics/Propositional/Semantics/Kripke.lean` - add @[simp] lemmas for IForces

**Verification**:
- `lake build` succeeds with no errors
- `lake exe checkInitImports` passes
- `lake exe lint-style` passes
- New simp lemmas are callable in downstream proofs (verified via lean_goal if needed)

## Testing & Validation

- [ ] Full `lake build` passes after all changes
- [ ] `lake exe checkInitImports` passes
- [ ] `lake exe lint-style` passes
- [ ] No remaining bare `lem` references in Propositional or Foundations directories
- [ ] No remaining `toIntProp`/`toProp` (old names) in Propositional directory

## Artifacts & Outputs

- plans/01_implementation-plan.md (this file)
- summaries/01_execution-summary.md (after implementation)

## Rollback/Contingency

All changes are additive docstring edits or mechanical renames. If any rename causes unexpected build failures, revert the specific rename and investigate the missed call site via grep. The @[simp] lemmas can be individually reverted if they cause proof regressions in downstream files.
