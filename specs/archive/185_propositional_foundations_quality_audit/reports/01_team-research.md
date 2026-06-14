# Research Report: Propositional/ and Foundations/ Quality Audit

- **Task**: 185 - Rigorous quality audit of Propositional/ and Foundations/
- **Started**: 2026-06-13T00:00:00Z
- **Completed**: 2026-06-13T00:00:00Z
- **Effort**: Team research (3 teammates, standard mode)
- **Dependencies**: None
- **Sources/Inputs**:
  - `specs/185_propositional_foundations_quality_audit/reports/01_teammate-a-findings.md` (Architecture, organization, import hygiene)
  - `specs/185_propositional_foundations_quality_audit/reports/01_teammate-b-findings.md` (Proof quality, naming conventions, notation)
  - `specs/185_propositional_foundations_quality_audit/reports/01_teammate-c-findings.md` (Literature references, mathematical rigor, contribution readiness)
  - `Cslib/Logics/Propositional/` (26 files, ~5,905 lines)
  - `Cslib/Foundations/Logic/` (16 files, ~3,977 lines)
- **Artifacts**: `specs/185_propositional_foundations_quality_audit/reports/01_team-research.md`
- **Standards**: status-markers.md, artifact-management.md, tasks.md, report-format.md

---

## Executive Summary

- The Propositional/ and Foundations/Logic/ modules are mathematically rigorous: zero sorries across all 42 audited files, all theorem statements match standard references, and all proof strategies are correct. This is the most important positive finding.
- Two HIGH-priority import hygiene issues require fixing: unused `Std.Tactic.BVDecide.Normalize` imports in two files, and four lake-shake-identified import moves between Completeness and StrongCompleteness files (Int and Min variants).
- The most prevalent HIGH-priority issue is citation format: 14 Metalogic files use the bare abbreviation "CZ" instead of the proper Lean doc-reference BibKey format `[ChagrovZakharyaschev1997]`, blocking doc-gen cross-linking.
- One MEDIUM-priority proof style issue is significant: the 241-line monolithic `prop_truth_lemma` in `Completeness.lean` should be decomposed into helper lemmas following Mathlib conventions.
- Four naming inconsistencies require renaming: two theorems missing the `prop_` prefix, one misleadingly named `lem` theorem, and two axiom subsumption method names deviating from Mathlib convention.
- The codebase is well above CSLib contribution standards in docstring coverage (100%), copyright headers (100%), notation scoping, typeclass reuse, and mathematical substance -- it significantly surpasses any other known Lean 4 propositional logic formalization.

---

## Context & Scope

**Scope**: 42 files across two directories:
- `Cslib/Logics/Propositional/` (26 files, ~5,905 lines): four subdirectories (Metalogic, NaturalDeduction, ProofSystem, Semantics) plus root `Defs.lean`
- `Cslib/Foundations/Logic/` (16 files, ~3,977 lines): two core files, two subdirectories (Metalogic, Theorems), with Theorems further subdivided by domain

**Eight audit dimensions**:
1. File organization and module structure
2. Proof style and tactic usage
3. BibTeX references in references.bib
4. Module-level docstrings following Mathlib conventions
5. Notation consistency (scoped notation, typeclass-backed operators)
6. Naming conventions (Mathlib snake_case, descriptive theorem names)
7. Import hygiene (minimal imports, no transitive leakage)
8. Redundant or duplicated lemmas across files

---

## Coverage Check: All 8 Audit Dimensions

| Dimension | Covered By | Depth |
|-----------|-----------|-------|
| 1. File organization and module structure | Teammate A (primary) | Thorough: full directory layout, barrel files, misplacements |
| 2. Proof style and tactic usage | Teammate B (primary) | Thorough: monolithic proofs, duplicated arguments, bare simp |
| 3. BibTeX references in references.bib | Teammate C (primary) | Thorough: 38-entry audit, missing references, "CZ" citation survey |
| 4. Module-level docstrings | Teammate A + C (joint) | Thorough: 100% coverage verified, quality graded |
| 5. Notation consistency | Teammate B (primary) | Thorough: scoped notation, typeclass backing, dual-encoding issue |
| 6. Naming conventions | Teammate B (primary) | Thorough: prefix inconsistencies, misleading names, variable conventions |
| 7. Import hygiene | Teammate A (primary) | Thorough: lake shake output analyzed, public vs private import analysis |
| 8. Redundant or duplicated lemmas | Teammate A + B (joint) | Thorough: 3-fold structural duplication, private helper duplication |

All 8 dimensions are covered. No gaps.

---

## Findings

### Dimension 1: File Organization and Module Structure

**Assessment**: Well-organized. No structural issues requiring immediate action.

- The Propositional/ hierarchy (Metalogic, NaturalDeduction, ProofSystem, Semantics) follows Mathlib conventions and separates concerns cleanly.
- Foundations/Logic/ is also well-organized. One anomaly: `FrameConditions.lean` is placed under `Theorems/Temporal/` but contains only typeclasses and instances, not theorems. Acceptable given downstream consumers; document in barrel docstring.
- No barrel import files exist for Propositional/ subdirectories, consistent with other CSLib modules (Modal, Temporal, Bimodal). Acceptable for current library size.
- The dual `Derivable` name in two namespaces (`InferenceSystem.Derivable` vs `PL.Derivable`) is unambiguous due to namespace separation. No action required.

### Dimension 2: Proof Style and Tactic Usage

**Assessment**: Generally high quality. Three issues warrant attention.

- **HIGH: Monolithic truth lemma** (`Completeness.lean` lines 69-310, 241 lines). The `prop_truth_lemma` proof is a single undivided structural recursion with 5 cases; the implication case alone is 111 lines. Mathlib convention decomposes such proofs into per-connective helper lemmas. Recommend extracting 6 helpers: `prop_truth_lemma_{and,or,imp}_{forward,backward}`.

- **MEDIUM: Duplicated DNE argument** (`StrongCompleteness.lean` lines 97-169). Two branches of `prop_not_SetDerivable_union_neg_consistent` perform the same double-negation elimination chain. Extract a shared helper that produces `L' ⊢ phi` from `L' ⊢ neg phi -> bot`.

- **MEDIUM: Long combinator proof** (`Combinators.lean` lines 140-271, 131 lines for `app2`/Vireo). Correct but uncommented in stages 3-5. Add strategy comments above each stage.

- **LOW: 3 bare `simp` calls** in `Consistency.lean` (lines 91, 112, 251). Convert to `simp only` with explicit lemma lists.

- **LOW: De Morgan proofs** use deeply nested `HasImp.imp` / `HasBot.bot` expressions up to 30 lines wide. Local abbreviations (`local notation`) would improve readability.

- **POSITIVE: Soundness proofs** across all three logics are exemplary: clean `cases h_ax with` dispatches, minimal and appropriate classical reasoning, no unnecessary complexity.

- **POSITIVE: Zero sorries or admits** across all 42 files.

- **POSITIVE: Classical reasoning usage** is appropriate throughout -- `Classical.propDecidable` only appears in metatheoretic proofs (Lindenbaum, completeness) where classical meta-reasoning is standard.

### Dimension 3: BibTeX References in references.bib

**Assessment**: Core references are present; citation format requires systematic repair; two standard references are missing.

- `references.bib` contains 38 entries. All key references for these modules are present: `ChagrovZakharyaschev1997`, `TroelstraVanDalen1988`, `Gentzen1935`, `Prawitz1965`, `Johansson1937`, `Heyting1930`, `Church1956`, `Blackburn2001`, `McKinsey1939`, `Wajsberg1938`.

- **HIGH: 14 files use bare "CZ" abbreviation** instead of the Lean doc-reference BibKey format. All occurrences should be replaced with `[A. Chagrov, M. Zakharyaschev, *Modal Logic*][ChagrovZakharyaschev1997], Theorem X.Y`. Files affected: `Completeness.lean`, `StrongCompleteness.lean`, `Soundness.lean`, `Semantics/Basic.lean`, `Semantics/Kripke.lean`, `Semantics/SemanticConsequence.lean`, `IntCompleteness.lean`, `IntStrongCompleteness.lean`, `IntSoundness.lean`, `IntLindenbaum.lean`, `MinCompleteness.lean`, `MinStrongCompleteness.lean`, `MinSoundness.lean`, `MinLindenbaum.lean`.

- **HIGH: `set_lindenbaum`** (`Consistency.lean`) has no citation. Should cite CZ Section 5.1 (Lindenbaum/Tarski attribution).

- **HIGH: `deductionTheorem`** (`DeductionTheorem.lean`) has no citation. Should cite CZ Theorem 1.4.3 or Herbrand (1930).

- **MEDIUM: Missing from `references.bib`**:
  - van Dalen, *Logic and Structure* (5th ed., 2013) -- standard textbook for completeness and deduction theorem
  - Fitting, *Intuitionistic Logic, Model Theory and Forcing* (1969) -- Kripke completeness for intuitionistic logic

- **MEDIUM: `MCS.lean`, `Axioms.lean`, `Derivation.lean`, `ProofSystem.lean`** have no References sections in their module docstrings despite containing mathematically substantial content.

- **MEDIUM: `int_prime_exclusion`** (`IntLindenbaum.lean`) should cite CZ Lemma 5.5 for the prime extension technique.

### Dimension 4: Module-Level Docstrings

**Assessment**: Excellent -- 100% coverage, above typical Lean library standards.

- All 42 files have `/-! ... -/` module docstrings. Coverage is complete.
- Strong docstrings (exemplary): `Defs.lean` (comprehensive architecture overview), `Connectives.lean` (design rationale with references), `MCS.lean` (parameterization documentation), `StrongCompleteness.lean` (proof strategy section).
- All 37 audited files have purpose statements and lists of main definitions/results.
- 30/42 files have explicit references sections; the 12 files without are identified in Dimension 3 above.
- **LOW: Stale axiom count** in `ProofSystem/Axioms.lean` module docstring: header says "4 axiom schemata" but the inductive has 10 constructors. Update to "10 axiom schemata".

### Dimension 5: Notation Consistency

**Assessment**: Strong. Scoped and typeclass-backed throughout, one architectural tension documented.

- All connective notations in `Defs.lean` are correctly scoped with standard symbols and appropriate precedence levels. `@[inherit_doc]` is consistently applied.
- The turnstile notation in `NaturalDeduction/Basic.lean` is properly scoped and does not conflict with other notations.
- All notation in the Propositional module is typeclass-backed (`Bot`, `Top`, `PropositionalConnectives`, `HasAnd`, `HasOr`). No unscoped notation found.
- **MEDIUM: Foundations vs Propositional encoding gap.** Foundations theorems use the Lukasiewicz encoding (`(phi -> (psi -> bot)) -> bot` for conjunction) while Propositional uses primitive constructors (`Proposition.and`). Bridge lemmas connecting the two encodings would improve interoperability. This is a known design tension, documented in the codebase.

### Dimension 6: Naming Conventions

**Assessment**: Mostly follows Mathlib conventions. Four specific issues require fixes.

- Variable naming is conventional throughout: `phi`/`psi`/`chi` for formulas, `v` for valuations, `h_`/`d_` prefixes for hypotheses/derivations. Minor inconsistency: `DeductionTheorem.lean` uses `A`/`B` for formulas -- acceptable given proof-theory textbook convention.
- `@[expose] public section` pattern is consistently applied across all files (CSLib convention).

- **MEDIUM: `soundness_tautology`** (`Soundness.lean` line 89) missing `prop_` prefix -- all sibling theorems in the file use `prop_`. Rename to `prop_soundness_tautology`.

- **MEDIUM: `completeness_iff_tautology`** (`StrongCompleteness.lean` line 248) missing `prop_` prefix -- all other theorems in file use `prop_`. Rename to `prop_completeness_iff_tautology`.

- **LOW: `lem` theorem** (`Core.lean` line 63, in Minimal section) is named as "Law of Excluded Middle" but actually proves `(phi -> bot) -> (phi -> bot)` (identity on negation). The real LEM requires classical logic. Rename to `neg_identity` and update docstring.

- **LOW: Axiom subsumption names** (`Axioms.lean` lines 154, 167): `MinPropAxiom.toIntProp` and `IntPropAxiom.toProp` use non-standard abbreviations. Rename to `MinPropAxiom.toIntPropAxiom` and `IntPropAxiom.toPropositionalAxiom`.

### Dimension 7: Import Hygiene

**Assessment**: Good overall; two concrete fixable issues identified.

- **HIGH: Unused `Std.Tactic.BVDecide.Normalize` imports** in two files:
  - `NaturalDeduction/DerivedRules.lean` line 10
  - `Semantics/SemanticConsequence.lean` line 12
  - Neither file uses `bv_decide` or `bv_omega`. Remove both imports.

- **HIGH: Four `lake shake` import fixes** (transitive leakage between Completeness and StrongCompleteness):

  | File | Action | Import |
  |------|--------|--------|
  | `Metalogic/IntCompleteness.lean` | remove | `public import ...IntSoundness` |
  | `Metalogic/IntStrongCompleteness.lean` | add | `public import ...IntSoundness` |
  | `Metalogic/MinCompleteness.lean` | remove | `public import ...MinSoundness` |
  | `Metalogic/MinStrongCompleteness.lean` | add | `public import ...MinSoundness` |

- **MEDIUM: All 68 Propositional imports are `public`; 0 are private.** Foundations uses a mixed strategy (29 public, 15 private). The `public import Cslib.Init` in `Defs.lean` propagates `Init` (linting rules, tactics) to all downstream consumers -- not ideal. Change to `import Cslib.Init` (non-public). Review other Mathlib imports for similar treatment.

### Dimension 8: Redundant or Duplicated Lemmas

**Assessment**: Three patterns of duplication identified. Two are intentional and correctly designed; one is actionable.

- **MEDIUM: `h_implyK`/`h_implyS` private helpers duplicated across 4 files** (Completeness, StrongCompleteness, IntLindenbaum, MinLindenbaum). These are trivial constructor wrappers (`fun phi psi => .implyK phi psi`) repeated with variant prefixes (`sc_`, `int_`, `min_`) to avoid name collisions. Should be extracted to `ProofSystem/Axioms.lean` as non-private definitions (one pair per axiom system), then imported where needed.

- **LOW: 3-fold Min/Int/Classical structural duplication** across 12 Metalogic files (4 proof triads). Intentional consequence of Lean 4's lack of inductive inheritance -- three distinct axiom predicates cannot be unified. The current approach is correct. A future generic `PropLogic` typeclass could address this but is a significant refactor with uncertain payoff. Mark as long-term consideration only.

- **LOW: `DerivedRules.lean` vs `HilbertDerivedRules.lean` parallel rules** (negI/hilbertNegI, etc.). Intentional: the two proof systems (Finset-context ND vs List-context Hilbert) coexist by design. The `Equivalence.lean` bridge proves extensional equivalence. No action needed.

---

## Mathematical Rigor Assessment

This is the most critical finding of the audit: **the mathematical content is entirely correct**.

All major definitions have been assessed against standard references:
- `SetDerivable`, `SemanticEntails`, `ISemanticEntails`, `IForces`, `IntDCCS`, `IntPrimeDCCS`, `MinTheory` -- all correct formulations matching standard treatments.
- All theorem statements (strong completeness for all three logics, compactness, soundness) match CZ and standard references.
- All proof strategies are correct: completeness via contrapositive + canonical model + truth lemma; soundness via structural induction on derivation trees; Lindenbaum via Zorn's lemma on consistent supersets; deduction theorem via well-founded recursion on tree height.

Two low-priority mathematical observations (not bugs):
- Universe restriction in `int_completeness` (`IValid.{u,v}` to `IValid.{u,u}`) is correct but could be documented more explicitly.
- `Classical.propDecidable` usage in metatheoretic proofs is correct and expected -- completeness proofs inherently require classical meta-reasoning regardless of object-logic constructivity.

**Comparison with prior art**: CSLib's propositional formalization surpasses all other known Lean 4 treatments. Mathlib has no propositional completeness, no Lindenbaum lemma, and no Kripke semantics. The only comparable Lean 4 work (Bentzen) covers only classical completeness without Kripke semantics, intuitionistic/minimal logics, or generic MCS frameworks.

---

## Positive Findings

The following aspects are already strong and should be preserved:

1. **Zero sorries** across all 42 files -- the library is fully proven.
2. **100% module docstring coverage** -- above typical Lean library standards.
3. **100% copyright header compliance** across all files.
4. **Correct mathematical formulations** -- every definition and theorem statement verified against standard references.
5. **Appropriate scoped notation** -- all notations are scoped and typeclass-backed; no unscoped leakage.
6. **Soundness proofs** are exemplary in all three logic variants.
7. **`IForces` parameterization** via `bot_forces` elegantly unifies intuitionistic and minimal semantics without code duplication.
8. **Typeclass reuse** -- the Propositional module systematically instantiates all Foundations abstractions (`PropositionalConnectives`, `DerivationSystem`, `InferenceSystem`, etc.).
9. **Architecture documentation** -- `Defs.lean`, `Connectives.lean`, `MCS.lean`, and `StrongCompleteness.lean` have exemplary docstrings explaining design decisions.
10. **Broader coverage than any other Lean 4 propositional formalization** -- three logic strengths, two proof systems, Kripke semantics, ND/Hilbert equivalence, and generic MCS framework in one library.

---

## Synthesis

### Conflicts Resolved

No direct conflicts between teammates. All three investigated independent dimensions and their findings were mutually consistent. One potential disagreement was examined:

- Teammate A characterized the 3-fold Min/Int/Classical duplication (F-5) as LOW priority and "intentional"; Teammate B's finding on the `h_implyK`/`h_implyS` duplication overlaps with A's F-6 but characterizes it as MEDIUM. **Resolution**: The structural duplication (F-5, 12 files) is correctly LOW -- it is inherent to Lean 4's type system. The private helper duplication (F-6/B-4.1, 4 definitions) is correctly MEDIUM -- it is extractable to a shared location. These are distinct issues with different actionability, not a conflict.

### Coverage Gaps

No gaps in audit dimension coverage. All 8 dimensions are covered thoroughly. However, two items were not verified by any teammate and remain open:

- **`lake exe lint-style` verification**: Teammate C noted this could not be run in a research context. The implementation task should run it explicitly.
- **`lake test` verification**: Similarly not run. CI status of the full test suite should be confirmed.

### Recommendations

**HIGH Priority** (fix before PR):

1. Remove `public import Std.Tactic.BVDecide.Normalize` from `NaturalDeduction/DerivedRules.lean` (line 10) and `Semantics/SemanticConsequence.lean` (line 12).
2. Apply 4 `lake shake` import moves: remove `IntSoundness` from `IntCompleteness.lean`, add to `IntStrongCompleteness.lean`; same pattern for Min variants.
3. Replace "CZ" abbreviations with full BibKey format in all 14 Metalogic files.
4. Add citation to `set_lindenbaum` in `Consistency.lean` (CZ Section 5.1 / Lindenbaum-Tarski).
5. Add citation to `deductionTheorem` in `DeductionTheorem.lean` (CZ Theorem 1.4.3 or Herbrand 1930).

**MEDIUM Priority** (strong recommendation):

6. Decompose `prop_truth_lemma` in `Completeness.lean` into 6 helper lemmas.
7. Extract shared DNE helper in `StrongCompleteness.lean` to eliminate ~40-line duplication.
8. Rename `soundness_tautology` to `prop_soundness_tautology` (`Soundness.lean`).
9. Rename `completeness_iff_tautology` to `prop_completeness_iff_tautology` (`StrongCompleteness.lean`).
10. Extract `h_implyK`/`h_implyS` helpers to `ProofSystem/Axioms.lean` as non-private definitions (eliminates duplication across 4 files).
11. Change `public import Cslib.Init` to `import Cslib.Init` in `Defs.lean`.
12. Add References sections to `MCS.lean`, `Axioms.lean`, `Derivation.lean` docstrings.
13. Add van Dalen (2013) and Fitting (1969) to `references.bib`.
14. Add citation to `int_prime_exclusion` (CZ Lemma 5.5).
15. Add bridge lemmas connecting Lukasiewicz encoding (Foundations) to primitive connectives (Propositional).

**LOW Priority** (optional improvements):

16. Rename `lem` to `neg_identity` in `Core.lean` (and update docstring).
17. Rename `MinPropAxiom.toIntProp` to `MinPropAxiom.toIntPropAxiom` and `IntPropAxiom.toProp` to `IntPropAxiom.toPropositionalAxiom`.
18. Update `Axioms.lean` module docstring from "4 axiom schemata" to "10 axiom schemata".
19. Convert 3 bare `simp` calls in `Consistency.lean` to `simp only` with explicit lemma lists.
20. Document `FrameConditions.lean` placement anomaly in `Theorems.lean` barrel docstring.
21. Add local abbreviations in De Morgan proofs (`Connectives.lean`) for readability.
22. Consider `@[simp]` attributes on base cases of `Evaluate` and `IForces`.

---

## Teammate Contributions

| Teammate | Angle | Status | Confidence |
|----------|-------|--------|------------|
| A | Architecture, organization, import hygiene | completed | high |
| B | Proof quality, naming conventions, notation | completed | high |
| C | Literature references, mathematical rigor, contribution readiness | completed | high |

All three teammates completed without timeout or failure. Findings are mutually consistent.

---

## Risks & Mitigations

- **Risk**: Citation format fixes (14 files) are mechanical but tedious -- easy to miss one. **Mitigation**: Grep for bare "CZ" patterns before closing the implementation task.
- **Risk**: The `prop_truth_lemma` decomposition is a significant proof refactor (241 lines); helper lemmas may not compose cleanly if the original proof relied on local variable scoping. **Mitigation**: Implement and verify each helper lemma independently before removing the monolithic proof.
- **Risk**: `lake shake` import changes may cause elaboration-order issues if transitive imports were relied upon implicitly. **Mitigation**: Run full `lake build` after each `lake shake` fix to confirm no regressions.
- **Risk**: Renaming public theorems (`soundness_tautology`, `completeness_iff_tautology`) is a breaking API change for any downstream consumers. **Mitigation**: Check for any files outside Propositional/ that reference these names before renaming.

---

## Appendix

### References

- Chagrov & Zakharyaschev, *Modal Logic* (1997) -- `ChagrovZakharyaschev1997` in references.bib
- Troelstra & van Dalen, *Constructivism in Mathematics* (1988) -- `TroelstraVanDalen1988`
- Gentzen, *Untersuchungen uber das logische Schliessen* (1935) -- `Gentzen1935`
- Prawitz, *Natural Deduction* (1965) -- `Prawitz1965`
- Johansson, *Der Minimalkalkul* (1937) -- `Johansson1937`
- van Dalen, *Logic and Structure* (5th ed., 2013) -- **MISSING from references.bib**
- Fitting, *Intuitionistic Logic, Model Theory and Forcing* (1969) -- **MISSING from references.bib**

### Files Audited

**Cslib/Logics/Propositional/** (26 files):
- Defs.lean, Metalogic/{Completeness,DeductionTheorem,IntCompleteness,IntLindenbaum,IntSoundness,IntStrongCompleteness,MCS,MinCompleteness,MinLindenbaum,MinSoundness,MinStrongCompleteness,Soundness,StrongCompleteness}.lean, NaturalDeduction/{Basic,DerivedRules,Equivalence,FromHilbert,HilbertDerivedRules}.lean, ProofSystem/{Axioms,Derivation,Instances,IntMinInstances}.lean, Semantics/{Basic,Kripke,SemanticConsequence}.lean

**Cslib/Foundations/Logic/** (16 files):
- Axioms.lean, Connectives.lean, InferenceSystem.lean, LogicalEquivalence.lean, ProofSystem.lean, Metalogic/{Consistency,DeductionHelpers}.lean, Theorems/{Theorems,Combinators,BigConj}.lean, Theorems/Propositional/{Core,Connectives}.lean, Theorems/Modal/{Basic,S5}.lean, Theorems/Temporal/{FrameConditions,TemporalDerived}.lean
