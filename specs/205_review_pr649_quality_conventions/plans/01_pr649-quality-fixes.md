# Implementation Plan: Task #205

- **Task**: 205 - Review PR #649 quality conventions
- **Status**: [COMPLETED]
- **Effort**: 2 hours
- **Dependencies**: None
- **Research Inputs**: specs/205_review_pr649_quality_conventions/reports/01_pr649-quality-review.md
- **Artifacts**: plans/01_pr649-quality-fixes.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: cslib
- **Lean Intent**: false

## Overview

Apply quality convention fixes to PR #649's Temporal/Syntax/Formula.lean and Foundations/Logic/Connectives.lean based on the research review. The review identified 3 must-fix items (BibKey reference format, missing references.bib entry, redundant Mathlib lemma), 1 should-fix item (missing module docstring sections), and 2 nice-to-have items (verbose abbrev docstrings, import consistency). This plan addresses all must-fix and should-fix items, with nice-to-have items included as a final polish phase.

### Research Integration

The research report (01_pr649-quality-review.md) compared PR #649 against established patterns in Propositional/Defs.lean, Modal/Basic.lean, NaturalDeduction/Basic.lean, and Foundations/Logic/InferenceSystem.lean. Key findings integrated:
- BibKey `[Author, *Title*][BibKey]` format is the universal standard across CSLib module docstrings
- `Nat.pair_eq_pair` from `Mathlib.Data.Nat.Pairing` is transitively available and makes the custom `nat_pair_inj` theorem redundant
- `## Main definitions` and `## Notation` sections are standard in all baseline modules

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

This task advances the **Temporal** module column in the roadmap. The Temporal Syntax infrastructure is listed as completed; this task ensures the quality of that completed work before upstream submission.

## Goals & Non-Goals

**Goals**:
- Convert Formula.lean module docstring references to BibKey format
- Add missing Gabbay et al. (1980) entry to references.bib
- Remove redundant `nat_pair_inj` theorem and replace usages with `Nat.pair_eq_pair.mp`
- Add standard `## Main definitions` and `## Notation` docstring sections to Formula.lean
- Address nice-to-have items (verbose docstrings, import consistency)

**Non-Goals**:
- Refactoring proof structure or logic (proofs were assessed as clean)
- Modifying Propositional/Defs.lean or NaturalDeduction/Basic.lean changes (those are already good)
- Changing notation precedence or scoping (assessed as correct)

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Removing `nat_pair_inj` breaks `encodeNat_injective` proof | H | L | Replace each call site with `Nat.pair_eq_pair.mp h` and verify with `lake build` |
| `Nat.pair_eq_pair` not available without new import | M | L | Research confirmed it is transitively available via `Mathlib.Logic.Encodable.Basic` |
| BibKey format for Gabbay et al. entry incorrect | L | L | Follow exact pattern from Connectives.lean and verify against references.bib format |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2 | 1 |
| 3 | 3 | 2 |

Phases within the same wave can execute in parallel.

### Phase 1: Fix references.bib and BibKey format [COMPLETED]

**Goal**: Add missing bibliography entry and convert Formula.lean references to BibKey format.

**Tasks**:
- [ ] Add `@inproceedings{GPSS1980,...}` entry to `references.bib` for Gabbay, Pnueli, Shelah, and Stavi (1980), "On the temporal analysis of fairness"
- [ ] Convert Formula.lean module docstring references from plain-text format to BibKey format:
  - `- Kamp, H. (1968)...` becomes `* [H. Kamp, *Tense Logic and the Theory of Linear Order*][Kamp1968]`
  - `- Gabbay, D., ...` becomes `* [D. Gabbay, A. Pnueli, S. Shelah, J. Stavi, *On the temporal analysis of fairness*][GPSS1980]`
- [ ] Change list marker from `-` to `*` in the `## References` section
- [ ] Verify BibKey `Kamp1968` already exists in `references.bib`

**Timing**: 20 minutes

**Depends on**: none

**Files to modify**:
- `references.bib` - Add GPSS1980 entry
- `Cslib/Logics/Temporal/Syntax/Formula.lean` - Convert reference format in module docstring

**Verification**:
- `grep -c 'GPSS1980' references.bib` returns 1
- Formula.lean references use `* [Author, *Title*][BibKey]` format
- No plain-text bibliography entries remain in the module docstring

---

### Phase 2: Remove redundant lemma and update proofs [COMPLETED]

**Goal**: Delete the custom `nat_pair_inj` theorem and replace all usages with Mathlib's `Nat.pair_eq_pair.mp`.

**Tasks**:
- [ ] Delete `nat_pair_inj` theorem definition (lines 160-164 of Formula.lean)
- [ ] Find all usage sites of `nat_pair_inj` in `encodeNat_injective` proof
- [ ] Replace each `nat_pair_inj h` with `Nat.pair_eq_pair.mp h`
- [ ] Run `lake build Cslib.Logics.Temporal.Syntax.Formula` to verify compilation
- [ ] Run full `lake build` to check no other files reference `nat_pair_inj`

**Timing**: 30 minutes

**Depends on**: 1

**Files to modify**:
- `Cslib/Logics/Temporal/Syntax/Formula.lean` - Remove theorem, update proof call sites

**Verification**:
- `lake build Cslib.Logics.Temporal.Syntax.Formula` succeeds with no errors
- `grep -r 'nat_pair_inj' Cslib/` returns no results
- `encodeNat_injective` proof compiles using `Nat.pair_eq_pair.mp`

---

### Phase 3: Module docstring sections and polish [COMPLETED]

**Goal**: Add standard docstring sections and address nice-to-have items for full convention compliance.

**Tasks**:
- [ ] Add `## Main definitions` section to Formula.lean module docstring listing:
  - `Formula` : Inductive type for temporal logic formulas
  - `encodeNat` : Injective encoding of formulas into natural numbers
  - `encodeNat_injective` : Proof that `encodeNat` is injective
  - Key abbreviations (`someFuture`, `allFuture`, `somePast`, `allPast`)
- [ ] Add `## Notation` section listing all registered notations with their precedences:
  - `¬`, `∧`, `∨`, `→`, `↔` (propositional)
  - `U`, `S` (binary temporal)
  - `𝐅`, `𝐆`, `𝐏`, `𝐇` (unary temporal)
- [ ] Reorder module docstring sections to: Main definitions, Notation, Derived Temporal Operators, References
- [ ] Consider trimming verbose derived-connective inline docstrings (move convention notes to module docstring if appropriate)
- [ ] Standardize `import` vs `public import` for `Cslib.Init` across Formula.lean and Connectives.lean (use whichever pattern is more prevalent in the codebase)
- [ ] Run `lake build` to verify no regressions
- [ ] Run `lake exe lint-style` to check style compliance

**Timing**: 40 minutes

**Depends on**: 2

**Files to modify**:
- `Cslib/Logics/Temporal/Syntax/Formula.lean` - Add docstring sections, reorder, trim verbosity
- `Cslib/Foundations/Logic/Connectives.lean` - Standardize import (if changing)

**Verification**:
- Formula.lean contains `## Main definitions` and `## Notation` sections
- Sections appear in standard order (Main definitions, Notation, domain-specific, References)
- `lake build` succeeds
- `lake exe lint-style` passes

## Testing & Validation

- [ ] `lake build` succeeds with no errors across entire project
- [ ] `lake test` passes (CslibTests suite)
- [ ] `lake exe checkInitImports` passes
- [ ] `lake exe lint-style` passes
- [ ] `grep -r 'nat_pair_inj' Cslib/` returns no results
- [ ] Formula.lean module docstring contains `## Main definitions`, `## Notation`, `## References` sections
- [ ] All references in Formula.lean use BibKey `[Author, *Title*][BibKey]` format
- [ ] `references.bib` contains entry for GPSS1980

## Artifacts & Outputs

- `specs/205_review_pr649_quality_conventions/plans/01_pr649-quality-fixes.md` (this plan)
- Modified `references.bib` with GPSS1980 entry
- Modified `Cslib/Logics/Temporal/Syntax/Formula.lean` with all fixes applied
- Potentially modified `Cslib/Foundations/Logic/Connectives.lean` (import standardization)

## Rollback/Contingency

All changes are to existing files tracked by git. If any phase introduces regressions:
1. `git diff` to identify the problematic change
2. `git checkout -- <file>` to revert the specific file
3. Re-attempt the phase with corrected approach

The `nat_pair_inj` removal is the highest-risk change. If `Nat.pair_eq_pair.mp` does not type-check at any call site, restore `nat_pair_inj` and investigate whether a different Mathlib lemma is needed or whether the custom theorem should be kept with a justification comment.
