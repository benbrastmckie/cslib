# Implementation Plan: Task #178

- **Task**: 178 - Documentation and citation corrections from task 171 research
- **Status**: [COMPLETED]
- **Effort**: 1.5 hours
- **Dependencies**: None (task 173 five-primitive refactor already on main)
- **Research Inputs**: specs/178_johansson_references_doc_corrections/reports/01_references-research.md
- **Artifacts**: plans/01_implementation-plan.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: cslib
- **Lean Intent**: false

## Overview

This task corrects stale documentation and missing citations across four files in the CSLib
propositional logic module. Task 173 refactored `Proposition` from a 3-constructor `{atom, bot, imp}`
design to a 5-constructor `{atom, bot, imp, and, or}` design, and expanded `Theory.Derivation`
from 5 to 10 primitive constructors. Several module docstrings still describe the old architecture.
Additionally, `Johansson1937` is missing from `references.bib` despite minimal logic being a
first-class citizen of the library. All changes are documentation-only; no Lean code is modified.

### Research Integration

Research report `01_references-research.md` confirmed:
- `Johansson1937` is missing from `references.bib` (Finding 1)
- `Defs.lean` lines 19-22 contain a stale `{imp, bot}` functional-completeness claim (Finding 3, HIGH severity)
- `Basic.lean` lines 43-48 contain stale "Implementation notes" claiming and/or rules are derivable (Finding 4, HIGH severity)
- `Connectives.lean` references section is missing Johansson 1937, Prawitz 1965, Troelstra & van Dalen 1988 (Finding 2, MEDIUM)
- PR #635 is CLOSED and needs no rewrite (Finding 7)
- `DerivedRules.lean`, `Axioms.lean`, `Semantics/*.lean`, and all metalogic files are already correct

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

No specific ROADMAP.md items are directly addressed. This is a maintenance/documentation task
that supports the Propositional module quality but does not advance any remaining roadmap component.

## Goals & Non-Goals

**Goals**:
- Add `Johansson1937` BibTeX entry to `references.bib`
- Optionally add `Wajsberg1938` and `McKinsey1939` entries to match prose citations in Connectives.lean
- Rewrite `Defs.lean` module docstring to reflect the 5-constructor `Proposition` type
- Rewrite `Basic.lean` "Implementation notes" to reflect the 10-constructor `Derivation` type
- Add missing citation references to `Connectives.lean`, `Defs.lean`, and `Basic.lean` reference sections
- Document the two-layer proof-system architecture (ND + Hilbert) in `Defs.lean`

**Non-Goals**:
- Modifying any Lean code (all changes are docstring/comment-only)
- Rewriting PR #635 description (PR is closed)
- Modifying `DerivedRules.lean`, `Axioms.lean`, or any semantics/metalogic files (already correct)

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Docstring changes cause lake build failure | M | L | Run `lake build` on each modified module after editing |
| BibTeX entry format does not match CSLib conventions | L | L | Follow format of existing entries (e.g., `Heyting1930`) |
| Two-layer architecture description becomes stale | L | L | Keep description high-level, reference specific files |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2, 3, 4 | 1 |
| 3 | 5 | 2, 3, 4 |

Phases within the same wave can execute in parallel.

---

### Phase 1: Add references.bib entries [COMPLETED]

**Goal**: Add missing BibTeX entries required by downstream documentation phases.

**Tasks**:
- [ ] Add `Johansson1937` entry to `references.bib` (article: "Der Minimalkalkul, ein reduzierter intuitionistischer Formalismus", Compositio Mathematica, vol 4, pp 119-136, 1937)
- [ ] Add `Wajsberg1938` entry to `references.bib` (article: "Untersuchungen uber den Aussagenkalkul von A. Heyting", Wiadomosci Matematyczne, vol 46, pp 45-101, 1938)
- [ ] Add `McKinsey1939` entry to `references.bib` (article: "Proof of the Independence of the Primitive Symbols of Heyting's Calculus of Propositions", JSL, vol 4, no 4, pp 155-158, 1939, doi 10.2307/2268715)

**Timing**: 15 minutes

**Depends on**: none

**Files to modify**:
- `references.bib` - Add three new BibTeX entries following existing format conventions

**Verification**:
- Entries are well-formed BibTeX
- BibKeys match the naming convention used by existing entries (AuthorYear format)

---

### Phase 2: Correct Defs.lean module docstring [COMPLETED]

**Goal**: Replace the stale `{imp, bot}` functional-completeness narrative with an accurate description of the 5-constructor design, update references, and add two-layer architecture overview.

**Tasks**:
- [ ] Rewrite lines 19-22 of `Cslib/Logics/Propositional/Defs.lean` to:
  - State that `Proposition` has five primitive constructors: `atom`, `bot`, `imp`, `and`, `or`
  - State that `neg`, `top`, and `iff` are derived connectives (defined as `abbrev`s)
  - Note the design follows the standard Gentzen/Prawitz/Troelstra-van Dalen full-connective tradition
  - Note that Johansson's minimal logic is formalized via `Theory.MPL`
- [ ] Add two-layer architecture overview to the module docstring:
  - Layer 1: Natural Deduction (`NaturalDeduction/Basic.lean`) with 10 primitive constructors and theory parameterization (MPL/IPL/CPL)
  - Layer 2: Hilbert System (`ProofSystem/`) with axiom predicate hierarchy (MinPropAxiom/IntPropAxiom/PropositionalAxiom)
  - Bridge: `NaturalDeduction/Equivalence.lean` establishing extensional equivalence
- [ ] Update References section (lines 40-43) to add:
  - `[Johansson1937]` for minimal logic
  - `[Gentzen1935]` for the ND tradition
  - `[Prawitz1965]` for ND reference
  - `[TroelstraVanDalen1988]` for constructive mathematics

**Timing**: 30 minutes

**Depends on**: 1

**Files to modify**:
- `Cslib/Logics/Propositional/Defs.lean` - Rewrite module docstring and references section

**Verification**:
- `lake build Cslib.Logics.Propositional.Defs` compiles without errors
- Docstring accurately describes the 5-constructor inductive
- No mention of `{imp, bot}` functional completeness remains
- All BibKey references in the docstring have corresponding entries in `references.bib`

---

### Phase 3: Correct Basic.lean implementation notes [COMPLETED]

**Goal**: Replace the stale "Implementation notes" section that incorrectly claims conjunction and disjunction rules are derivable.

**Tasks**:
- [ ] Rewrite the "Implementation notes" section (lines 43-48 of `Cslib/Logics/Propositional/NaturalDeduction/Basic.lean`) to:
  - State that the primitive inference rules include: axiom (from theory), assumption (from context), conjunction intro/elim, disjunction intro/elim, and implication intro/elim (10 constructors total)
  - State that `botE` (ex falso quodlibet) is a derived rule requiring `[IsIntuitionistic T]`
  - Note that logic strength is controlled by the theory parameter: `MPL` (minimal, Johansson 1937), `IPL` (intuitionistic), `CPL` (classical)
- [ ] Add `[Johansson1937]` to the References section (lines 50-57) for minimal logic citation

**Timing**: 20 minutes

**Depends on**: 1

**Files to modify**:
- `Cslib/Logics/Propositional/NaturalDeduction/Basic.lean` - Rewrite "Implementation notes" and update references

**Verification**:
- `lake build Cslib.Logics.Propositional.NaturalDeduction.Basic` compiles without errors
- No mention of "derivable from these primitives together with the definitions of and and or" remains
- Implementation notes match the actual `Derivation` inductive (10 constructors)
- The Derivation docstring on lines 82-85 and the Implementation notes are now consistent

---

### Phase 4: Update Connectives.lean references [COMPLETED]

**Goal**: Add missing citations to the Connectives.lean references section.

**Tasks**:
- [ ] Add the following entries to the References section (lines 42-47 of `Cslib/Foundations/Logic/Connectives.lean`):
  - `[Johansson1937]` - for minimal logic (MinimalHilbert is named after his system)
  - `[Prawitz1965]` - for full-connective ND reference
  - `[TroelstraVanDalen1988]` - for constructive mathematics with full connectives
- [ ] Optionally convert prose citations "Wajsberg 1938, McKinsey 1939" (line 31-32) to BibKey format `[Wajsberg1938]`, `[McKinsey1939]` now that the entries exist in references.bib

**Timing**: 10 minutes

**Depends on**: 1

**Files to modify**:
- `Cslib/Foundations/Logic/Connectives.lean` - Add references and optionally convert prose citations

**Verification**:
- `lake build Cslib.Foundations.Logic.Connectives` compiles without errors
- All cited authors in the docstring have corresponding BibKey references in the References section

---

### Phase 5: CI verification [COMPLETED]

**Goal**: Verify that all documentation changes pass the full CSLib CI pipeline.

**Tasks**:
- [ ] Run `lake build` to confirm no regressions from docstring changes
- [ ] Run `lake exe checkInitImports` to verify import structure
- [ ] Run `lake exe lint-style` to verify style compliance

**Timing**: 15 minutes

**Depends on**: 2, 3, 4

**Files to modify**:
- None (verification only)

**Verification**:
- All three CI commands exit with code 0
- No new warnings or errors introduced

## Testing & Validation

- [ ] `lake build` passes with no errors on all modified modules
- [ ] `lake exe checkInitImports` passes
- [ ] `lake exe lint-style` passes
- [ ] Every BibKey reference in docstrings (`[AuthorYear]`) has a corresponding entry in `references.bib`
- [ ] No stale references to `{imp, bot}` functional completeness remain in any modified file
- [ ] The `Derivation` docstring (line 82-85 of Basic.lean) and Implementation notes section are consistent

## Artifacts & Outputs

- `specs/178_johansson_references_doc_corrections/plans/01_implementation-plan.md` (this file)
- `specs/178_johansson_references_doc_corrections/summaries/01_implementation-summary.md` (after implementation)

## Rollback/Contingency

All changes are documentation-only (Lean comments and BibTeX). If any change causes issues:
- `git revert` the commit to restore previous docstrings
- No Lean code is modified, so no functional regressions are possible
- Individual phases can be reverted independently since they modify separate files
