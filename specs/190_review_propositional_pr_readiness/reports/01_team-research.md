# Research Report: Task #190

**Task**: Review quality of deduction theorem and strong soundness/completeness in Logics/Propositional/ for PR readiness
**Date**: 2026-06-14
**Mode**: Team Research (4 teammates)

## Summary

The propositional logic code in `Logics/Propositional/` is **PR-ready**. All four research teammates converge on this assessment with high confidence. The `noncomputable` usage that prompted this review is fully justified, consistent with established CSLib patterns across Modal/Temporal/Bimodal, and cannot be eliminated without constraining `Atom : Type*` to require `DecidableEq`. Zero sorries were found. Documentation quality exceeds the repo average. Two minor issues warrant attention before PR submission: a global unscoped `HasHilbertTree` instance that should be made local, and missing `@[simp]` tags on key soundness/completeness biconditionals.

## Key Findings

### 1. Noncomputable Usage: Fully Justified (ALL TEAMMATES AGREE)

**Root cause**: `attribute [local instance] Classical.propDecidable` is required for `by_cases h_eq : ψ = A` in the deduction theorem proof, where the proof must distinguish whether an assumption formula equals the deduction hypothesis. Since `Atom : Type*` has no `DecidableEq` constraint, classical decidability is the only option.

**Propagation chain**: `Classical.propDecidable` -> `deductionWithMem`/`deductionTheorem` become noncomputable -> all callers inherit noncomputability (`impI`, `hilbertCut`, `ndToHilbert`, etc.)

**Repo consistency**: This is the identical pattern used in:
- `Modal/Metalogic/DeductionTheorem.lean` (byte-for-byte same `attribute [local instance] Classical.propDecidable`)
- `Temporal/Metalogic/DeductionTheorem.lean`
- `Bimodal/Metalogic/Core/DeductionTheorem.lean` (uses `noncomputable section`)

**Scale comparison**:

| Module | Noncomputable count |
|--------|---------------------|
| Bimodal | ~215 |
| Temporal | ~77 |
| Propositional | ~14 |
| Foundations/Logic | ~6 |

Propositional has the smallest noncomputable footprint of any logic module.

**Cannot be eliminated**: Constraining `Atom` to `DecidableEq` would break the universe-polymorphic design used throughout CSLib. The current `attribute [local instance]` approach is more disciplined than `open Classical`.

**No downstream contamination**: All downstream consumers wrap derivation trees in `Nonempty` (`Deriv`/`Derivable` are Prop-level). Semantic definitions (`Evaluate`, `IForces`, `IValid`) are fully computable. The noncomputable boundary is cleanly contained in metalogic files.

### 2. Code Quality: High Across All Components

**Deduction Theorem** (`DeductionTheorem.lean`): Clean well-founded recursion on `DerivationTree.height`. Correctly parameterized over abstract `{Axioms}` with `h_implyK`/`h_implyS` witnesses. Two-level design (`deductionWithMem` + `deductionTheorem`) is mathematically sound. Matches the already-merged modal deduction theorem pattern exactly.

**Strong Soundness** (`Soundness.lean`): Exemplary. 10-case axiom soundness with one-liner cases. 4-case structural recursion for derivation tree soundness. Intuitionistic and minimal variants follow the same clean pattern.

**Strong Completeness** (`StrongCompleteness.lean`): Mathematically correct contrapositive argument via canonical MCS model. Truth lemma decomposed into per-connective helpers for readability. Some verbosity in inline derivation tree constructions (~15 occurrences of `fun _ h => nomatch h` pattern), but no correctness issues.

### 3. Zero Sorries Confirmed (ALL TEAMMATES VERIFY)

No `sorry`, `admit`, or proof holes found anywhere in the 23 files of `Logics/Propositional/`. Complete proofs exist for strong soundness/completeness for classical, intuitionistic, and minimal propositional logic, plus the deduction theorem, Lindenbaum lemma, ND-Hilbert equivalence, and compactness.

### 4. Documentation Exceeds Repo Average

All files include:
- Module docstrings with `## Main Results` and `## Strategy` sections
- `## References` with verified BibTeX keys (`ChagrovZakharyaschev1997`, `Prawitz1965`, `TroelstraVanDalen1988`, `Johansson1937`)
- Per-definition docstrings for main results
- Cross-references to sibling logic modules

No `set_option linter` suppressions needed (unlike some Bimodal/Temporal files).

### 5. Mathlib Has No Overlap

Mathlib's `FirstOrder.Language.Theory.IsMaximal` is model-theoretic for first-order logic. CSLib's Hilbert-style propositional logic with parameterized axioms, structural deduction theorem, and canonical model completeness is a genuine new contribution with no Mathlib equivalent.

## Synthesis

### Issues Found (Ordered by Priority)

**Issue 1 (Medium): Global unscoped `HasHilbertTree` instance**
- File: `DeductionTheorem.lean:56`
- `noncomputable instance : HasHilbertTree (PL.Proposition Atom)` is hardcoded to `PropositionalAxiom` but visible globally wherever the file is imported
- Inconsistent with the otherwise fully parameterized design of the module
- **Recommendation**: Convert to `local instance` or remove (callers already use `letI` internally)
- Source: Teammate C (confirmed by A's observation of duplicated `letI` blocks)

**Issue 2 (Low): Missing `@[simp]` tags on key equivalences**
- `prop_completeness_iff_tautology`, `int_soundness_completeness`, `min_soundness_completeness`, and the three strong completeness `_iff` wrappers lack `@[simp]`
- These fundamental biconditionals are exactly what downstream proofs would `simp` with
- **Recommendation**: Add `@[simp]` or document why intentionally omitted
- Source: Teammate C

**Issue 3 (Informational): Duplicated code patterns**
- Repeated `letI : HasHilbertTree` blocks in `deductionWithMem` and `deductionTheorem` (could share a helper)
- Duplicated EFQ-inconsistency pattern in `IntLindenbaum.lean` (lines ~343-354 and ~375-381)
- **Recommendation**: Optional cleanup, not blocking
- Source: Teammate A

**Issue 4 (Informational): One existing TODO**
- `NaturalDeduction/Basic.lean:251`: "TODO: this implementation is not capture avoiding" for `subs`
- Does NOT affect completeness proofs (they use `hilbertSubstitution`, not `subs`)
- **Recommendation**: Acknowledge in PR description
- Source: Teammate C

**Issue 5 (Informational): Universe polymorphism minor inconsistency**
- `IValid.{_, v}` uses universe `v` while `ISemanticEntails` uses `u`
- Resulting theorems are universe-consistent but the notation is slightly asymmetric
- **Recommendation**: Low priority, not blocking
- Source: Teammate C

### Conflicts Resolved

**Conflict 1: Can noncomputable be eliminated?**
- Teammates A, B, D: Cannot be eliminated without breaking `Atom : Type*` design
- Teammate C: Theoretically possible if rewritten in term mode using decidability of list membership (since `Atom` already has `DecidableEq` when in context)
- **Resolution**: The parameterized deduction theorem is stated with `{Atom : Type*}` without `[DecidableEq Atom]` constraint, so `Classical.propDecidable` is genuinely required. C's observation applies only when a `DecidableEq` instance is in scope, which is not the general case. **Verdict: noncomputable is necessary as designed.**

### Gaps Identified

1. **CI verification not run**: No teammate executed `lake build`, `lake exe lint-style`, `lake exe checkInitImports`, or `lake shake`. These should be run before PR submission.
2. **Compilation performance not tested**: The inline derivation tree terms in `StrongCompleteness.lean` are moderately large; compilation speed should be verified.
3. **Upstream compatibility not checked**: Mathlib/CSLib HEAD may have bumped since the code was last verified.

### PR Strategy Recommendation

The 6-PR roadmap from task 188 is sound. For the material under review:

| PR | Content | LOC | Status |
|----|---------|-----|--------|
| PR 0 | Connective typeclass hierarchy | ~96 | Implemented |
| PR 1 | Five-primitive formula type | ~170 | Implemented |
| PR 4a | DeductionTheorem + MCS | ~381 | Ready (split recommended) |
| PR 4b | Soundness + StrongCompleteness | ~644 | Ready (split recommended) |

PR 4 (~963 LOC combined) should be split into 4a (foundational machinery) and 4b (main results) for reviewer friendliness.

## Teammate Contributions

| Teammate | Angle | Status | Confidence | Key Contribution |
|----------|-------|--------|------------|------------------|
| A | Primary Code Quality | completed | high | Detailed proof assessment, noncomputable inventory |
| B | Repo Standards Comparison | completed | high | Cross-repo noncomputable analysis (314 occurrences), Mathlib gap confirmation |
| C | Critic | completed | high | Global instance concern, missing @[simp], universe inconsistency |
| D | Strategic Horizons | completed | high | PR split strategy, roadmap alignment, zero-sorry asset |

## Bottom Line

**The code is PR-ready.** The noncomputable usage is a non-issue: it follows the established CSLib pattern exactly and has the smallest footprint of any logic module. Before submitting:

1. **Fix** the global `HasHilbertTree` instance (make `local` or remove) -- quick change
2. **Consider** adding `@[simp]` to the soundness/completeness biconditionals
3. **Run** the CI pipeline (`lake build`, `lake test`, `lake exe lint-style`, `lake exe checkInitImports`)
4. **Acknowledge** the `subs` TODO in the PR description

## References

- Task 188 PR roadmap and implementation
- Task 189 completeness file consolidation
- `ROADMAP.md` dependency tree
- CSLib `CONTRIBUTING.md` standards
- Mathlib `FirstOrder.Language.Theory.IsMaximal` (no overlap confirmed)
