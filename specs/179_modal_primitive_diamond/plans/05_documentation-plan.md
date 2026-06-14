# Implementation Plan: Task #179 -- Document Box-as-Primitive Design Choice

- **Task**: 179 - Document why box is primitive in classical modal logic (scope revised from primitive dia)
- **Status**: [NOT STARTED]
- **Effort**: 1.5 hours
- **Dependencies**: None
- **Research Inputs**: specs/179_modal_primitive_diamond/reports/05_team-research.md, specs/179_modal_primitive_diamond/reports/05_teammate-d-findings.md
- **Artifacts**: plans/05_documentation-plan.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: cslib

## Overview

This plan replaces the original 6-phase, 10-hour plan (plan 04) that would have added `.dia` as a primitive constructor to `Modal.Proposition`. The user has decided to defer primitive dia: bimodal logic does not need it, and no non-classical modal logics are currently formalized. Instead, this plan adds docstrings and comments explaining why box is the primitive modal operator in classical systems, citing Blackburn et al. (2001) and Chagrov & Zakharyaschev (1997). No Lean proof changes are made. Additionally, the task 181 dependency on task 179 is removed from state.json since bimodal can proceed independently.

### Research Integration

- `reports/05_team-research.md` -- Synthesized findings from 4-teammate research on box primality and deferral analysis
- `reports/05_teammate-d-findings.md` -- Specific documentation design with 8 locations, drafted comment text, and BibKey verification

### Prior Plan Reference

Plan 04 (`04_primitive-dia-plan.md`) -- 6-phase plan to add `.dia` as 5th primitive constructor. Superseded by this documentation-only plan due to scope change.

## Goals & Non-Goals

**Goals**:
- Add docstrings explaining why box (not diamond) is the primitive modal operator
- Cite Blackburn2001 and ChagrovZakharyaschev1997 (both confirmed in `references.bib`)
- Document when and why diamond should become primitive (non-classical modal logics)
- Explain the classical encoding of diamond in axiom B, 5, and D docstrings
- Update task 179 description in state.json to reflect documentation-only scope
- Remove task 179 from task 181's dependencies in state.json

**Non-Goals**:
- Adding `.dia` as a primitive constructor (deferred)
- Adding `HasDia` typeclass (deferred, not needed until non-classical logics are formalized)
- Changing any Lean proof terms or definitions
- Modifying the `Proposition` inductive type
- Updating bimodal logic files

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Docstring syntax error breaks `lake build` | L | L | Run `lake build` after changes; docstrings are comments only |
| `lint-style` rejects long docstring lines | L | M | Keep lines under 100 characters, wrap as needed |
| BibKey reference format incorrect | L | L | Format confirmed from existing codebase examples (Teammate D verified) |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2 | 1 |
| 3 | 3 | 2 |

Phases are sequential: state update first, then documentation, then verification.

---

### Phase 1: Update Task Scope and Dependencies [NOT STARTED]

**Goal**: Update state.json to reflect the revised documentation-only scope and remove the task 181 dependency on 179.

**Tasks**:
- [ ] Update task 179 description in state.json to: "Document why box is primitive in classical modal logic; add docstrings citing Blackburn2001 and ChagrovZakharyaschev1997"
- [ ] Remove task 179 from task 181's `dependencies` array in state.json (181 depends on [179, 180] -> [180])
- [ ] Regenerate TODO.md via `bash .claude/scripts/generate-todo.sh`

**Timing**: 15 minutes

**Depends on**: none

**Files to modify**:
- `specs/state.json` -- Update task 179 description and task 181 dependencies

**Verification**:
- state.json reflects new task 179 description
- Task 181 dependencies no longer include 179
- TODO.md regenerated successfully

---

### Phase 2: Add Docstrings to Modal Files [NOT STARTED]

**Goal**: Add docstrings explaining the box-as-primitive design choice at 8 specific locations across 4 files, following Teammate D's documentation design.

**Tasks**:
- [ ] **Basic.lean module docstring** (lines 22-31): Replace the "Primitives" subsection to explain that box corresponds to universal quantification over accessible worlds, preserves conjunction, supports necessitation. Note that diamond is derived as `neg box neg phi` using classical negation, and that this derivation fails in intuitionistic or minimal modal logic. Cite [Blackburn2001] Chapter 1 and [ChagrovZakharyaschev1997] Section 1.1.
- [ ] **Basic.lean `Proposition.diamond` abbrev** (line 77): Expand the one-line docstring to explain the classical dependency -- forward direction uses semantic reasoning, backward direction uses excluded middle. Note that this fails in minimal modal logic.
- [ ] **Connectives.lean `HasBox` class** (lines 70-73): Expand the class docstring to explain why box is canonical: preserves conjunction, distributes over implication (axiom K), subject of necessitation. Note that `HasBox` alone suffices for classical systems; non-classical settings need a separate `HasDia`.
- [ ] **Connectives.lean `ModalConnectives` class** (line 103): Expand to note that box is chosen as the sole primitive modal operator following [Blackburn2001], and that diamond is derived via classical negation. Non-classical modal logics require extending with `HasDia`.
- [ ] **Axioms.lean `AxiomB`** (lines 150-154): Replace docstring to explain that diamond is encoded classically as `neg box neg phi = (box(phi to bot)) to bot`, since `HasDia` is not yet part of `ModalConnectives`. Note correspondence to symmetry of accessibility.
- [ ] **Axioms.lean `Axiom5`** (lines 156-161): Replace docstring with same classical encoding explanation. Note correspondence to right-Euclideanness.
- [ ] **Axioms.lean `AxiomD`** (lines 163-167): Replace docstring with same classical encoding explanation. Note correspondence to seriality.
- [ ] **ProofSystem/Instances/D.lean `modalD`** (lines 50-53): Replace inline `where dia phi = ...` docstring with a cross-reference to `Axioms.AxiomD` and a note that the classical encoding is used. Apply same pattern to B.lean (`modalB`) and K5.lean (`modalFive`) if they have similar inline docstrings.

**Timing**: 45 minutes

**Depends on**: 1

**Files to modify**:
- `Cslib/Logics/Modal/Basic.lean` -- Module docstring "Primitives" subsection, `Proposition.diamond` docstring
- `Cslib/Foundations/Logic/Connectives.lean` -- `HasBox` class docstring, `ModalConnectives` class docstring
- `Cslib/Foundations/Logic/Axioms.lean` -- `AxiomB`, `Axiom5`, `AxiomD` docstrings
- `Cslib/Logics/Modal/ProofSystem/Instances/D.lean` -- `modalD` constructor docstring (and similar in B.lean, K5.lean if applicable)

**Verification**:
- All 8 docstring locations updated with explanatory text
- BibKey references use correct bracket notation: `[Author, *Title*][BibKey]`
- Both `Blackburn2001` and `ChagrovZakharyaschev1997` referenced where appropriate

---

### Phase 3: Build Verification [NOT STARTED]

**Goal**: Verify that all docstring changes compile and pass style checks.

**Tasks**:
- [ ] Run `lake build` to confirm docstring changes do not break compilation
- [ ] Run `lake exe lint-style` to confirm style compliance (line length, formatting)
- [ ] Fix any lint-style warnings (line wrapping, trailing whitespace)

**Timing**: 15 minutes

**Depends on**: 2

**Verification**:
- `lake build` passes with no errors
- `lake exe lint-style` passes with no errors

## Testing & Validation

- [ ] `lake build` completes without errors
- [ ] `lake exe lint-style` passes
- [ ] All 8 docstring locations contain explanatory text about box-as-primitive
- [ ] Both BibKeys (`Blackburn2001`, `ChagrovZakharyaschev1997`) are referenced
- [ ] No Lean proof terms or definitions were modified (documentation only)
- [ ] Task 181 dependencies in state.json no longer include 179

## Artifacts & Outputs

- `specs/179_modal_primitive_diamond/plans/05_documentation-plan.md` (this plan)
- Modified files: 4-6 Lean files (docstring changes only, no proof modifications)

## Rollback/Contingency

All changes are docstring-only edits to Lean source files tracked in git. Rollback via `git checkout main -- Cslib/` restores previous docstrings. Since no proof terms or definitions are changed, there is no risk of breaking any proofs. If `lint-style` rejects specific docstring formatting, wrap long lines or shorten text.
