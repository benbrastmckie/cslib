# Implementation Plan: Task #171

- **Task**: 171 - Research connective-basis design for minimal, intuitionistic, and classical propositional logic
- **Status**: [NOT STARTED]
- **Effort**: 3 hours
- **Dependencies**: 185 (completed), 186 (completed)
- **Research Inputs**: specs/171_research_connective_basis_min_int_classical/reports/01_team-research.md
- **Artifacts**: plans/01_implementation-plan.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: cslib
- **Lean Intent**: true

## Overview

The research for task 171 identified several issues with CSLib's propositional logic architecture:
the `{imp, bot}` basis was inadequate for genuine intuitionistic conjunction/disjunction, the
`botE` rule was unconditionally available making minimal logic actually intuitionistic, citations
were incorrect, and Johansson 1937 was missing from `references.bib`. Since the research was
completed, tasks 184, 185, and 186 have already resolved the most critical structural issues: the
`Proposition` type now has 5 constructors `{atom, bot, imp, and, or}`, the ND system has 10
primitive constructors with `botE` as a derived rule requiring `[IsIntuitionistic T]`, `HasAnd`
and `HasOr` typeclasses exist in `Connectives.lean`, and Johansson 1937 has been added to
`references.bib`. What remains is: (1) updating documentation in files that still reference the
old Lukasiewicz-only architecture (especially the Modal, Temporal, and Bimodal embedding modules
and `Foundations/Logic/Axioms.lean`), (2) reviewing and potentially updating the `conj'`/`disj'`
Lukasiewicz abbreviations in `Axioms.lean` and `BigConj.lean` to clarify their role as
embedding-layer helpers rather than primitive connective definitions, and (3) verifying all
citations in module docstrings are accurate after the architectural changes.

### Research Integration

The team research (4 teammates: literature verification, architecture survey, critical analysis,
strategic horizons) established that the non-interdefinability of intuitionistic connectives is a
proved theorem (Wajsberg 1938, McKinsey 1939). The architectural recommendation was to preserve
`{bot, imp}` as the basis with documentation corrections. Since then, the codebase has moved
further -- adopting full `{atom, bot, imp, and, or}` primitives -- which resolves the core
concerns raised by the research even more thoroughly than the research recommended.

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

This task aligns with the roadmap principle "every component lives at the most general level it
can compile at." The full-primitive connective set ensures that all three logic strengths
(MPL/IPL/CPL) are correctly supported at the syntax level, with logic strength controlled by
the theory parameter and proof system typeclasses.

## Goals & Non-Goals

**Goals**:
- Update documentation in embedding modules and Foundations/Logic that still references the old
  Lukasiewicz-only `{imp, bot}` architecture to accurately describe the current 5-primitive design
- Clarify the role of `conj'`/`disj'` in `Axioms.lean` as Lukasiewicz encodings used specifically
  for embedding PL into formula types that lack `and`/`or` constructors (Modal, Temporal, Bimodal)
- Verify all BibTeX citations in propositional logic module docstrings match the current
  architecture claims
- Ensure `lake build` passes after all documentation changes

**Non-Goals**:
- Changing the formula type constructors (already correct with 5 primitives)
- Refactoring proof systems (already correct after tasks 184-186)
- Adding new bridge lemmas between ND and Hilbert systems (task 186 scope)
- Addressing PR #607 (fmontesi's Operators/ proposal) -- separate future work
- Adding Mathlib algebraic typeclass alignment -- explicitly declined per research
- Modifying the `BigConj.lean` encoding (it correctly uses Lukasiewicz because it operates
  at the `HasBot`/`HasImp` typeclass level where `HasAnd` may not be available)

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Documentation edits introduce Lean build errors | M | L | Only edit comments/docstrings; run `lake build` after each phase |
| Lukasiewicz references in embedding modules are load-bearing for proofs | M | L | Read each embedding proof before editing comments; preserve mathematical accuracy |
| Citation BibKeys do not match entries in references.bib | L | L | Grep references.bib to verify each cited key exists |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1, 2 | -- |
| 2 | 3 | 1, 2 |

Phases within the same wave can execute in parallel.

### Phase 1: Update Foundations/Logic Documentation [COMPLETED]

**Goal**: Update docstrings in `Foundations/Logic/Axioms.lean`, `Foundations/Logic/Theorems/BigConj.lean`, and `Foundations/Logic/Theorems/Propositional/Core.lean` to accurately describe the role of Lukasiewicz encodings as embedding-layer helpers, not as the primary connective definitions.

**Tasks**:
- [ ] Update `Axioms.lean` docstrings for `conj'` and `disj'` (lines 47-53): clarify these are Lukasiewicz encodings used for embedding into formula types that lack `HasAnd`/`HasOr`, not the primary conjunction/disjunction definitions. The abbrevs themselves are correct and used by the modal/temporal/bimodal proof systems.
- [ ] Update `BigConj.lean` module docstring (lines 15, 34): clarify that the Lukasiewicz encoding is used here because BigConj operates at the `HasBot`/`HasImp` level for maximum generality across formula types.
- [ ] Update `Core.lean` docstrings (lines 18, 35, 62): clarify that `neg_identity` under Lukasiewicz encoding is LEM for classical systems, and note the architectural context.
- [ ] Verify all BibTeX keys cited in these files exist in `references.bib`.
- [ ] Run `lake build Cslib.Foundations.Logic.Axioms` and `lake build Cslib.Foundations.Logic.Theorems.BigConj` to verify no build errors.

**Timing**: 1 hour

**Depends on**: none

**Files to modify**:
- `Cslib/Foundations/Logic/Axioms.lean` -- update docstrings for `conj'`/`disj'`
- `Cslib/Foundations/Logic/Theorems/BigConj.lean` -- update module docstring
- `Cslib/Foundations/Logic/Theorems/Propositional/Core.lean` -- update docstrings

**Verification**:
- `lake build Cslib.Foundations.Logic.Axioms`
- `lake build Cslib.Foundations.Logic.Theorems.BigConj`
- `lake build Cslib.Foundations.Logic.Theorems.Propositional.Core`
- All cited BibKeys exist in `references.bib`

---

### Phase 2: Update Embedding Module Documentation [IN PROGRESS]

**Goal**: Update docstrings in the Modal, Temporal, and Bimodal embedding and conservative extension modules to accurately describe why Lukasiewicz encodings are used in those specific contexts (Modal/Temporal/Bimodal formula types lack `and`/`or` constructors) and to distinguish this from the propositional level where `and`/`or` are now primitives.

**Tasks**:
- [ ] Update `Cslib/Logics/Modal/FromPropositional.lean` (lines 30, 59, 64, 94, 107): clarify that Lukasiewicz encoding is used because `Modal.Proposition` has `{atom, bot, imp, box}` without `and`/`or` constructors. The encoding is sound for classical modal logic.
- [ ] Update `Cslib/Logics/Modal/Basic.lean` (line 25): update the "Lukasiewicz convention" reference to note this is specific to the modal formula type, not the propositional one.
- [ ] Update `Cslib/Logics/Temporal/FromPropositional.lean` (lines 29, 58, 64): same pattern as Modal -- Lukasiewicz encoding needed because `Temporal.Formula` lacks `and`/`or`.
- [ ] Update `Cslib/Logics/Temporal/ConservativeExtension.lean` (lines 43, 57, 67): clarify Lukasiewicz encoding context.
- [ ] Update `Cslib/Logics/Bimodal/Embedding/PropositionalEmbedding.lean` (lines 40-41, 70, 76): same pattern -- Bimodal formula type lacks `and`/`or`.
- [ ] Update `Cslib/Logics/Bimodal/Metalogic/ConservativeExtension/PropositionalConservativity.lean` (lines 56, 79, 89): same pattern.
- [ ] Run `lake build` on each modified module to verify no build errors.

**Timing**: 1 hour

**Depends on**: none

**Files to modify**:
- `Cslib/Logics/Modal/FromPropositional.lean` -- update Lukasiewicz context in docstrings
- `Cslib/Logics/Modal/Basic.lean` -- update convention reference
- `Cslib/Logics/Temporal/FromPropositional.lean` -- update Lukasiewicz context
- `Cslib/Logics/Temporal/ConservativeExtension.lean` -- update Lukasiewicz context
- `Cslib/Logics/Bimodal/Embedding/PropositionalEmbedding.lean` -- update Lukasiewicz context
- `Cslib/Logics/Bimodal/Metalogic/ConservativeExtension/PropositionalConservativity.lean` -- update Lukasiewicz context

**Verification**:
- `lake build Cslib.Logics.Modal.FromPropositional`
- `lake build Cslib.Logics.Modal.Basic`
- `lake build Cslib.Logics.Temporal.FromPropositional`
- `lake build Cslib.Logics.Temporal.ConservativeExtension`
- `lake build Cslib.Logics.Bimodal.Embedding.PropositionalEmbedding`
- `lake build Cslib.Logics.Bimodal.Metalogic.ConservativeExtension.PropositionalConservativity`

---

### Phase 3: Citation Audit and Final Verification [NOT STARTED]

**Goal**: Perform a cross-cutting citation audit of all propositional logic module docstrings, verify all BibKeys are correct, and run the full CI verification pipeline.

**Tasks**:
- [ ] Grep all files under `Cslib/Logics/Propositional/` and `Cslib/Foundations/Logic/` for BibKey references (patterns: `[XxxNNNN]`, `\cite{...}`) and verify each exists in `references.bib`.
- [ ] Verify that no module docstrings claim `{imp, bot}` as the basis for propositional logic (should now be `{atom, bot, imp, and, or}`). Check `Defs.lean`, `Connectives.lean`, `Basic.lean`, `Axioms.lean` module docstrings.
- [ ] Verify the Heyting/Gentzen/Prawitz/Troelstra-van Dalen citations are used correctly (should cite them for the full-connective tradition, not for a reduced basis).
- [ ] Verify Johansson1937 is cited in `Connectives.lean` and `NaturalDeduction/Basic.lean` where MPL is defined.
- [ ] Run full CI pipeline: `lake build && lake test && lake exe checkInitImports && lake exe lint-style`.

**Timing**: 1 hour

**Depends on**: 1, 2

**Files to modify**:
- Potentially any files where citation errors are found (expected: none or minimal)

**Verification**:
- `lake build` -- full project build passes
- `lake test` -- test suite passes
- `lake exe checkInitImports` -- import verification
- `lake exe lint-style` -- style linting
- All BibKeys in module docstrings correspond to entries in `references.bib`

## Testing & Validation

- [ ] `lake build` passes with no errors on all modified files
- [ ] `lake test` passes (no regressions)
- [ ] `lake exe checkInitImports` passes
- [ ] `lake exe lint-style` passes
- [ ] All BibKeys cited in module docstrings exist in `references.bib`
- [ ] No module docstring claims `{imp, bot}` as the propositional connective basis
- [ ] Lukasiewicz references in embedding modules correctly explain why they use that encoding
- [ ] Lukasiewicz references in Foundations correctly explain the role as embedding-layer helpers

## Artifacts & Outputs

- `specs/171_research_connective_basis_min_int_classical/plans/01_implementation-plan.md` (this file)
- Modified docstrings across ~9 Lean files (documentation-only changes)
- `specs/171_research_connective_basis_min_int_classical/summaries/01_execution-summary.md` (post-implementation)

## Rollback/Contingency

All changes are documentation-only (comments and docstrings). If any change introduces a build
error, revert the specific edit -- Lean module docstrings (`/-! ... -/`) and inline comments
(`/-- ... -/`) are syntactically inert and cannot affect compilation unless malformed. Git revert
of individual commits provides clean rollback for each phase.
