# Implementation Plan: Propositional Foundations Quality Audit

- **Task**: 185 - Propositional Foundations Quality Audit
- **Status**: [IMPLEMENTING]
- **Effort**: 6 hours
- **Dependencies**: None (task 186 already added vanDalen2013, Fitting1969, Herbrand1930 to references.bib)
- **Research Inputs**: specs/185_propositional_foundations_quality_audit/reports/01_team-research.md
- **Artifacts**: plans/01_implementation-plan.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: cslib
- **Lean Intent**: true

## Overview

Implement HIGH and MEDIUM priority fixes from the team research quality audit of `Cslib/Logics/Propositional/` (26 files) and `Cslib/Foundations/Logic/` (16 files). The audit identified zero sorries, correct mathematical content, and excellent documentation -- but flagged import hygiene issues, bare "CZ" citation abbreviations across 14 files, naming inconsistencies, and one monolithic 241-line proof requiring decomposition. All changes are non-breaking for proof correctness (the mathematical content is fully proven); this task improves code quality, citation standards, and maintainability.

### Research Integration

The team research report (3 teammates, 8 audit dimensions) produced 22 recommendations. This plan addresses all 5 HIGH-priority items and 9 of 10 MEDIUM-priority items. Item 13 (add references to references.bib) is skipped because task 186 already completed it. Item 15 (bridge lemmas for Lukasiewicz encoding) is deferred as a separate future task due to its scope as new proof content rather than a quality fix.

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

No specific ROADMAP.md items map directly to this quality audit task. The work improves contribution readiness for propositional logic modules.

## Goals & Non-Goals

**Goals**:
- Remove unused imports and fix lake shake import moves (HIGH items 1-2)
- Replace all bare "CZ" abbreviations with proper BibKey citation format (HIGH item 3)
- Add missing citations to `set_lindenbaum`, `deductionTheorem`, and `int_prime_exclusion` (HIGH items 4-5, MEDIUM item 14)
- Decompose monolithic `prop_truth_lemma` into per-connective helper lemmas (MEDIUM item 6)
- Extract shared DNE helper in `StrongCompleteness.lean` (MEDIUM item 7)
- Rename `soundness_tautology` and `completeness_iff_tautology` with `prop_` prefix (MEDIUM items 8-9)
- Extract `h_implyK`/`h_implyS` to shared location (MEDIUM item 10)
- Fix `public import Cslib.Init` to non-public (MEDIUM item 11)
- Add BibKey citations to `MCS.lean`, `Axioms.lean`, `Derivation.lean` docstrings (MEDIUM item 12)

**Non-Goals**:
- Adding new bridge lemmas between Lukasiewicz and primitive connective encodings (item 15, separate task)
- LOW priority fixes (renaming `lem`, renaming axiom subsumption methods, bare `simp` conversion, etc.)
- Adding new references to `references.bib` (already done by task 186)
- Structural refactoring of the 3-fold Min/Int/Classical duplication pattern (intentional design)

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| `prop_truth_lemma` decomposition breaks proof due to local variable scoping | H | M | Implement helpers one connective at a time; verify each with `lean_goal` before removing from monolithic proof |
| `lake shake` import moves cause elaboration-order failures | M | L | Run `lake build` after each import change; revert if regression |
| Renaming public theorems breaks downstream consumers | M | L | Grep entire codebase for references before renaming; only 2 internal refs found |
| Citation format changes introduce docstring syntax errors | L | L | Use consistent pattern from existing files with proper BibKey format; run `lake exe lint-style` |
| Extracting `h_implyK`/`h_implyS` to shared location changes import graph | M | M | Add to `ProofSystem/Axioms.lean` which is already imported by all consumers |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1, 2 | -- |
| 2 | 3, 4 | 1 |
| 3 | 5 | 2, 3 |

Phases within the same wave can execute in parallel.

### Phase 1: Import Hygiene and Naming Fixes [COMPLETED]

**Goal**: Fix all HIGH-priority import issues and MEDIUM-priority naming inconsistencies. These are mechanical changes with low risk.

**Tasks**:
- [ ] Remove `public import Std.Tactic.BVDecide.Normalize` from `NaturalDeduction/DerivedRules.lean` (line 10)
- [ ] Remove `public import Std.Tactic.BVDecide.Normalize` from `Semantics/SemanticConsequence.lean` (line 12)
- [ ] Remove `public import ...IntSoundness` from `Metalogic/IntCompleteness.lean` (line 10)
- [ ] Add `public import Cslib.Logics.Propositional.Metalogic.IntSoundness` to `Metalogic/IntStrongCompleteness.lean`
- [ ] Remove `public import ...MinSoundness` from `Metalogic/MinCompleteness.lean` (line 10)
- [ ] Add `public import Cslib.Logics.Propositional.Metalogic.MinSoundness` to `Metalogic/MinStrongCompleteness.lean`
- [ ] Change `public import Cslib.Init` to `import Cslib.Init` in `Defs.lean` (line 9)
- [ ] Rename `soundness_tautology` to `prop_soundness_tautology` in `Metalogic/Soundness.lean` (line 89 and docstring line 24)
- [ ] Rename `completeness_iff_tautology` to `prop_completeness_iff_tautology` in `Metalogic/StrongCompleteness.lean` (line 248)
- [ ] Update reference to `soundness_tautology` in `StrongCompleteness.lean` (line 250) and `Completeness.lean` docstring (line 25)
- [ ] Run `lake build` to verify all changes compile

**Timing**: 1 hour

**Depends on**: none

**Files to modify**:
- `Cslib/Logics/Propositional/NaturalDeduction/DerivedRules.lean` - remove BVDecide import
- `Cslib/Logics/Propositional/Semantics/SemanticConsequence.lean` - remove BVDecide import
- `Cslib/Logics/Propositional/Metalogic/IntCompleteness.lean` - remove IntSoundness import
- `Cslib/Logics/Propositional/Metalogic/IntStrongCompleteness.lean` - add IntSoundness import
- `Cslib/Logics/Propositional/Metalogic/MinCompleteness.lean` - remove MinSoundness import
- `Cslib/Logics/Propositional/Metalogic/MinStrongCompleteness.lean` - add MinSoundness import
- `Cslib/Logics/Propositional/Defs.lean` - make Cslib.Init import non-public
- `Cslib/Logics/Propositional/Metalogic/Soundness.lean` - rename theorem
- `Cslib/Logics/Propositional/Metalogic/StrongCompleteness.lean` - rename theorem, update reference
- `Cslib/Logics/Propositional/Metalogic/Completeness.lean` - update docstring reference

**Verification**:
- `lake build` succeeds with zero errors
- `grep -rn "soundness_tautology\|completeness_iff_tautology" Cslib/` shows only `prop_`-prefixed versions
- `grep -rn "BVDecide" Cslib/Logics/Propositional/` returns no results

---

### Phase 2: Citation Format Standardization [IN PROGRESS]

**Goal**: Replace all bare "CZ" abbreviations with proper BibKey citation format across 14 Propositional files, and add missing citations to `set_lindenbaum`, `deductionTheorem`, `int_prime_exclusion`, and three docstrings. This is mechanical text editing with no proof changes.

**Tasks**:
- [ ] Replace "CZ" with `[A. Chagrov, M. Zakharyaschev, *Modal Logic*][ChagrovZakharyaschev1997]` in all 14 files:
  - `Metalogic/Completeness.lean`
  - `Metalogic/StrongCompleteness.lean`
  - `Metalogic/Soundness.lean`
  - `Metalogic/IntCompleteness.lean`
  - `Metalogic/IntStrongCompleteness.lean`
  - `Metalogic/IntSoundness.lean`
  - `Metalogic/IntLindenbaum.lean`
  - `Metalogic/MinCompleteness.lean`
  - `Metalogic/MinStrongCompleteness.lean`
  - `Metalogic/MinSoundness.lean`
  - `Metalogic/MinLindenbaum.lean`
  - `Semantics/Basic.lean`
  - `Semantics/Kripke.lean`
  - `Semantics/SemanticConsequence.lean`
- [ ] Add citation to `set_lindenbaum` docstring in `Foundations/Logic/Metalogic/Consistency.lean` referencing CZ Section 5.1 / Lindenbaum-Tarski
- [ ] Add citation to `deductionTheorem` docstring in `Propositional/Metalogic/DeductionTheorem.lean` referencing CZ Theorem 1.4.3
- [ ] Add citation to `int_prime_exclusion` docstring in `Metalogic/IntLindenbaum.lean` referencing CZ Lemma 5.5
- [ ] Add BibKey citations to References sections in `Metalogic/MCS.lean`, `ProofSystem/Axioms.lean`, `ProofSystem/Derivation.lean` docstrings
- [ ] Verify: `grep -rn "CZ " Cslib/Logics/Propositional/ | grep -v ChagrovZakharyaschev` returns zero results

**Timing**: 1.5 hours

**Depends on**: none

**Files to modify**:
- 14 Propositional files listed above - CZ -> BibKey format
- `Cslib/Foundations/Logic/Metalogic/Consistency.lean` - add citation to set_lindenbaum
- `Cslib/Logics/Propositional/Metalogic/DeductionTheorem.lean` - add citation to deductionTheorem
- `Cslib/Logics/Propositional/Metalogic/IntLindenbaum.lean` - add citation to int_prime_exclusion
- `Cslib/Logics/Propositional/Metalogic/MCS.lean` - add BibKey to References section
- `Cslib/Logics/Propositional/ProofSystem/Axioms.lean` - add BibKey to References section
- `Cslib/Logics/Propositional/ProofSystem/Derivation.lean` - add BibKey to References section

**Verification**:
- `grep -rn "CZ " Cslib/Logics/Propositional/ | grep -v ChagrovZakharyaschev` returns zero results
- `lake build` succeeds (docstring changes should not affect compilation)
- `lake exe lint-style` passes

---

### Phase 3: Extract Shared h_implyK/h_implyS Helpers [NOT STARTED]

**Goal**: Extract the duplicated `h_implyK`/`h_implyS` private helper definitions from 4 files into `ProofSystem/Axioms.lean` as non-private definitions, eliminating code duplication.

**Tasks**:
- [ ] Add non-private `h_implyK` and `h_implyS` definitions to `ProofSystem/Axioms.lean` for each axiom system (PropositionalAxiom, IntPropAxiom, MinPropAxiom)
- [ ] Replace `private def h_implyK`/`private def h_implyS` in `Metalogic/Completeness.lean` (lines 43-53) with usage of shared definitions
- [ ] Replace `private def sc_h_implyK`/`private def sc_h_implyS` in `Metalogic/StrongCompleteness.lean` (lines 59-68) with usage of shared definitions
- [ ] Replace `private def int_h_implyK`/`private def int_h_implyS` in `Metalogic/IntLindenbaum.lean` (lines 35-43) with usage of shared definitions
- [ ] Replace `private def min_h_implyK`/`private def min_h_implyS` in `Metalogic/MinLindenbaum.lean` (lines 47-55) with usage of shared definitions
- [ ] Update all call sites in 4 files to use the new shared names
- [ ] Run `lake build` to verify compilation

**Timing**: 1 hour

**Depends on**: 1

**Files to modify**:
- `Cslib/Logics/Propositional/ProofSystem/Axioms.lean` - add shared definitions
- `Cslib/Logics/Propositional/Metalogic/Completeness.lean` - remove private defs, use shared
- `Cslib/Logics/Propositional/Metalogic/StrongCompleteness.lean` - remove private defs, use shared
- `Cslib/Logics/Propositional/Metalogic/IntLindenbaum.lean` - remove private defs, use shared
- `Cslib/Logics/Propositional/Metalogic/MinLindenbaum.lean` - remove private defs, use shared

**Verification**:
- `lake build` succeeds
- `grep -rn "private def.*h_implyK\|private def.*h_implyS" Cslib/Logics/Propositional/Metalogic/` returns zero results

---

### Phase 4: Extract Shared DNE Helper in StrongCompleteness [NOT STARTED]

**Goal**: Extract the duplicated double-negation elimination chain (~40 lines duplicated between two branches of `prop_not_SetDerivable_union_neg_consistent`) into a shared helper lemma.

**Tasks**:
- [ ] Read `StrongCompleteness.lean` lines 89-169 to understand both branches of the DNE argument
- [ ] Define a shared helper lemma that produces `DerivationTree PropositionalAxiom ctx phi` from `DerivationTree PropositionalAxiom ctx ((neg phi).imp bot)` using EFQ + Peirce
- [ ] Refactor both branches of `prop_not_SetDerivable_union_neg_consistent` to use the shared helper
- [ ] Run `lake build Cslib.Logics.Propositional.Metalogic.StrongCompleteness` to verify

**Timing**: 0.5 hours

**Depends on**: 1

**Files to modify**:
- `Cslib/Logics/Propositional/Metalogic/StrongCompleteness.lean` - add helper, refactor both branches

**Verification**:
- `lake build Cslib.Logics.Propositional.Metalogic.StrongCompleteness` succeeds
- The proof is shorter and the two branches share the DNE logic

---

### Phase 5: Decompose prop_truth_lemma into Helper Lemmas [NOT STARTED]

**Goal**: Decompose the 241-line monolithic `prop_truth_lemma` proof in `Completeness.lean` into per-connective helper lemmas following Mathlib conventions. This is the highest-risk change in the task.

**Tasks**:
- [ ] Define `prop_truth_lemma_atom` helper for the atom case (trivial, ~5 lines)
- [ ] Define `prop_truth_lemma_bot` helper for the bot case (~5 lines)
- [ ] Define `prop_truth_lemma_and` helper for the conjunction case, taking recursive IH arguments (~50 lines)
- [ ] Define `prop_truth_lemma_or` helper for the disjunction case, taking recursive IH arguments (~65 lines)
- [ ] Define `prop_truth_lemma_imp` helper for the implication case, taking recursive IH arguments (~110 lines)
- [ ] Rewrite `prop_truth_lemma` as structural recursion dispatching to helpers
- [ ] Verify each helper compiles individually with `lean_goal` before full integration
- [ ] Run `lake build Cslib.Logics.Propositional.Metalogic.Completeness` to verify final result

**Timing**: 2 hours

**Depends on**: 2, 3

**Files to modify**:
- `Cslib/Logics/Propositional/Metalogic/Completeness.lean` - extract 5 helpers, refactor main theorem

**Verification**:
- `lake build Cslib.Logics.Propositional.Metalogic.Completeness` succeeds
- `prop_truth_lemma` theorem statement is unchanged (same type signature)
- Each helper lemma has a doc comment explaining its role
- No sorries introduced

## Testing & Validation

- [ ] `lake build` -- full project compilation with zero errors
- [ ] `lake exe checkInitImports` -- all files import Cslib.Init
- [ ] `lake exe lint-style` -- style linting passes
- [ ] `lake test` -- CslibTests suite passes
- [ ] `lake shake --add-public --keep-implied --keep-prefix` -- import analysis clean
- [ ] `grep -rn "CZ " Cslib/Logics/Propositional/ | grep -v ChagrovZakharyaschev` -- zero bare CZ references remaining
- [ ] `grep -rn "BVDecide" Cslib/Logics/Propositional/` -- zero BVDecide imports remaining
- [ ] `grep -rn "soundness_tautology\|completeness_iff_tautology" Cslib/ | grep -v prop_` -- zero unprefixed names remaining

## Artifacts & Outputs

- `specs/185_propositional_foundations_quality_audit/plans/01_implementation-plan.md` (this file)
- `specs/185_propositional_foundations_quality_audit/summaries/01_execution-summary.md` (after implementation)
- Modified files: ~25 Lean source files across Propositional/ and Foundations/

## Rollback/Contingency

All changes are git-committed per phase. To revert any phase:
- `git revert <phase-commit-hash>` for the specific phase
- The monolithic `prop_truth_lemma` (Phase 5) is the only structurally complex change; if helper extraction fails, the original proof can be preserved unchanged by reverting Phase 5 only
- Import changes (Phase 1) and citation fixes (Phase 2) are independent and can be reverted independently
- If `lake shake` import moves cause issues, revert the specific import lines and re-run `lake build`
