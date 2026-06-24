# Refactoring Audit: Cslib/Logics/Propositional/

**Task**: 334  
**Session**: sess_1782316274_dc14fa  
**Date**: 2026-06-24  

## Executive Summary

The `Cslib/Logics/Propositional/` subtree contains 77 `.lean` files totaling approximately 18,500 lines of code. This audit identified **7 issues** across 4 severity levels: 2 high, 3 medium, and 2 low. The most critical finding is the well-documented subformula/complexity duplication between Normalization.lean and SubformulaProperty.lean, caused by a phantom Tableau.Defs import in CutElimination.lean. The broader audit reveals no additional duplication of comparable severity, but surfaces several structural improvements that would improve the dependency graph and code health.

---

## File Inventory

### Files Over 500 Lines (Candidates for Splitting)

| File | Lines | Status |
|------|-------|--------|
| `NaturalDeduction/Normalization.lean` | 1143 | **Issue 1** (contains misplaced subformula defs) |
| `SequentCalculus/LK/CutElimination.lean` | 877 | **Issue 2** (phantom import) |
| `Tableau/Intuitionistic/Soundness.lean` | 749 | 5 sorries; self-contained |
| `Semantics/Algebra/HilbertLindenbaum.lean` | 727 | Self-contained |
| `SequentCalculus/LJ/CutElimination.lean` | 711 | Self-contained |
| `Tableau/Classical/Soundness.lean` | 639 | Self-contained |
| `Metalogic/StrongCompleteness.lean` | 570 | Self-contained |
| `Semantics/Algebra/PointedBrouwerianCompleteness.lean` | 561 | Self-contained |
| `NaturalDeduction/HilbertDerivedRules.lean` | 534 | Self-contained |
| `Semantics/Algebra/BrouwerianCompleteness.lean` | 528 | Self-contained |
| `Tableau/Classical/Completeness.lean` | 509 | 3 sorries |

### Total File Count by Subdirectory

| Subdirectory | Files | Total Lines |
|-------------|-------|-------------|
| `NaturalDeduction/` | 6 | ~2,737 |
| `ProofSystem/` | 5 | ~1,113 |
| `ProofSystemEquivalence.lean` | 1 | 125 |
| `Metalogic/` | 7 | ~2,211 |
| `Semantics/` | 23 | ~5,929 |
| `SequentCalculus/` | 14 | ~4,277 |
| `Tableau/` | 13 | ~2,867 |
| `CurryHoward/` | 2 | 236 |
| `Defs.lean` | 1 | 208 |
| **Total** | **77** | **~18,500** |

---

## Issues

### Issue 1 [HIGH]: Duplicate Subformula Definitions

**Files affected**:
- `NaturalDeduction/Normalization.lean` (lines 59-145): Defines `Proposition.subformulas`, `Proposition.IsSubformula`, and 9 associated lemmas (refl, trans, and_left, and_right, or_left, or_right, imp_left, imp_right, self_mem_subformulas)
- `SequentCalculus/LK/SubformulaProperty.lean` (lines 48-134): Defines character-identical copies under different names: `Proposition.lkSubformulas`, `Proposition.LKIsSubformula`, and the same 9 lemmas

**Root cause**: SubformulaProperty.lean cannot import Normalization.lean to reuse `Proposition.subformulas` because of the `Proposition.complexity` name collision (Issue 2 below). Normalization.lean defines `Proposition.complexity` at line 149, and Tableau/Defs.lean independently defines an identical `Proposition.complexity` at line 110. SubformulaProperty.lean transitively imports Tableau/Defs.lean via CutElimination.lean, making both `complexity` definitions visible and causing a name clash that blocks direct reuse of `Proposition.subformulas`.

As a workaround, SubformulaProperty.lean redefined the entire subformula API under the `lk`-prefixed names (`lkSubformulas`, `LKIsSubformula`). The two definitions are character-for-character identical modulo the name prefix.

**Severity**: HIGH -- 135 lines of pure duplication, blocks future consumers of the subformula API, violates CSLib reuse-first principle

**Proposed fix**: Extract `Proposition.subformulas`, `Proposition.IsSubformula`, and all associated lemmas into a new standalone module `Cslib/Logics/Propositional/Subformula.lean`. This module would import only `Cslib/Logics/Propositional/Defs.lean` (no Tableau, no NaturalDeduction dependency). Both Normalization.lean and SubformulaProperty.lean would then import this shared module and delete their local copies.

### Issue 2 [HIGH]: Duplicate Proposition.complexity + Phantom Import

**Files affected**:
- `Tableau/Defs.lean` (line 110): `def Proposition.complexity`
- `NaturalDeduction/Normalization.lean` (line 149): `def Proposition.complexity` (identical definition)
- `SequentCalculus/LK/CutElimination.lean` (line 11): `public import Cslib.Logics.Propositional.Tableau.Defs`

**Root cause**: `CutElimination.lean` imports `Tableau.Defs` but uses **nothing** from it. The file uses `sizeOf` (auto-derived from the `Proposition` inductive) for its induction measure, not `Proposition.complexity`. The `CutFree` and `CutFreeLKProof` types come from `LK.Basic`. All helper theorems (`mem_of_ne_head`, `subset_insert2`, `insert_subset_swap`) are locally defined. This phantom import is the direct cause of Issue 1.

Additionally, `Proposition.complexity` is defined identically in both Tableau/Defs.lean and Normalization.lean. The definition body is the same in both files:
```lean
def Proposition.complexity : Proposition Atom -> Nat
  | .atom _ => 0
  | .bot => 0
  | .imp A B => 1 + A.complexity + B.complexity
  | .and A B => 1 + A.complexity + B.complexity
  | .or A B => 1 + A.complexity + B.complexity
```

Tableau/Defs.lean additionally provides 5 `@[simp]` lemmas for complexity that Normalization.lean does not have.

**Severity**: HIGH -- phantom import creates transitive name collision that forced the subformula duplication (Issue 1)

**Proposed fix (two parts)**:

1. **Remove phantom import**: Delete `public import Cslib.Logics.Propositional.Tableau.Defs` from CutElimination.lean. This breaks the Tableau dependency chain from the sequent calculus subtree, enabling clean imports.

2. **Consolidate complexity**: Extract `Proposition.complexity` and its simp lemmas into the same new `Subformula.lean` module (or a companion `Complexity.lean` module alongside it). Both Tableau/Defs.lean and Normalization.lean would import the shared definition.

### Issue 3 [MEDIUM]: Normalization.lean Is Overly Large (1143 Lines)

**File**: `NaturalDeduction/Normalization.lean`

The file contains four logically independent sections:
1. **Subformula infrastructure** (lines 59-145, ~87 lines): `subformulas`, `IsSubformula`, and related lemmas
2. **Complexity** (lines 149-154, ~6 lines): `Proposition.complexity`
3. **Normalization definitions and algorithm** (lines 157-928, ~771 lines): `isNormal`, `isStronglyNormal`, `reduceRoot`, `normalizeAux`, `normalize`, termination measure, fixpoint lemma, weakening preservation, `redexWeight` characterization
4. **Subformula property proofs** (lines 930-1143, ~213 lines): `subformula_property_of_isStronglyNormal`, `subformula_property`

The file also contains one sorry at line 1127 (`normalize_isStronglyNormal`).

**Severity**: MEDIUM -- violates the 500-line guideline, and parts 1-2 are pure utility code that other modules need

**Proposed fix**: After extracting subformula/complexity (Issues 1-2), the file drops to approximately 1000 lines. An additional split of the subformula property proofs (part 4) into a separate `SubformulaProperty.lean` file in `NaturalDeduction/` would bring both resulting files under 800 lines. The normalization algorithm and its correctness proofs are tightly coupled and should remain together.

### Issue 4 [MEDIUM]: Generic Finset Helpers in CutElimination.lean

**File**: `SequentCalculus/LK/CutElimination.lean` (lines 106-126)

Three generic Finset theorems are defined in the LK namespace that have nothing to do with sequent calculus:
- `mem_of_ne_head` -- wrapper around `Finset.mem_of_mem_insert_of_ne`
- `subset_insert2` -- double `Finset.subset_insert`
- `insert_subset_swap` -- insert commutativity for subsets

These are used extensively (20+ call sites) in the cut admissibility proof. They are not duplicated in LJ/CutElimination.lean (which uses different techniques).

**Severity**: MEDIUM -- misplaced utility code; not Finset API contributions but not duplicated either

**Proposed fix**: Move these to a shared `SequentCalculus/FinsetHelpers.lean` or keep them `private` in the current file. Making them `private` is the minimal fix and avoids polluting the namespace.

### Issue 5 [MEDIUM]: Tableau/Defs.lean Contains Mixed Concerns

**File**: `Tableau/Defs.lean` (177 lines)

This file bundles several concerns:
1. **Decomposition functions** (lines 49-84): `propAndOf?`, `propOrOf?`, `propImpOf?`, `propNegOf?`, `propImpOrNegOf?`
2. **Hashable instance** (lines 88-102): `instHashableProposition`
3. **Complexity measure** (lines 110-115): `Proposition.complexity` + 5 simp lemmas
4. **HasBot instance comment** (line 119): acknowledges it's already defined elsewhere
5. **Convenience lemmas** (lines 124-173): simp lemmas for decomposition functions

The complexity measure is used only in Tableau/Classical/Expansion.lean and Tableau/Intuitionistic/Expansion.lean. The decomposition functions are used throughout the Tableau subtree. The Hashable instance is needed for branch operations.

**Severity**: MEDIUM -- complexity definition collision with Normalization.lean; mixed concerns make this a problematic dependency target

**Proposed fix**: After extracting `Proposition.complexity` to the shared module (Issue 2), Tableau/Defs.lean becomes a clean tableau-specific utility file with decomposition functions, Hashable instance, and their simp lemmas. No further splitting needed.

### Issue 6 [LOW]: CutElimination.lean Commented Out in Barrel Import

**File**: `SequentCalculus/LK.lean` (line 12-13)

```lean
-- CutElimination excluded: has build errors requiring dedicated proof rewrite
-- public import Cslib.Logics.Propositional.SequentCalculus.LK.CutElimination
```

CutElimination is excluded from the barrel import due to build errors. However, SubformulaProperty.lean (which IS in the barrel) imports CutElimination directly. This means CutElimination is transitively imported anyway through the barrel file, making the comment misleading.

**Severity**: LOW -- cosmetic inconsistency; no functional impact

**Proposed fix**: Either uncomment the CutElimination barrel import (since it's transitively imported anyway through SubformulaProperty), or document that SubformulaProperty already transitively includes it.

### Issue 7 [LOW]: Sorry Inventory

**Files with sorry** (active sorries, not comments):

| File | Sorries | Context |
|------|---------|---------|
| `NaturalDeduction/Normalization.lean` | 1 | `normalize_isStronglyNormal` -- termination measure proof |
| `Tableau/Intuitionistic/Soundness.lean` | 5 | `intExpandBranches_closed_unsat` loop invariant |
| `Tableau/Intuitionistic/Completeness.lean` | 3 | Truth lemma cases |
| `Tableau/Classical/Completeness.lean` | 3 | Truth lemma cases |
| `Tableau/Minimal/Completeness.lean` | 3 | Inherited from Intuitionistic |

**Severity**: LOW for this refactoring audit -- these are known incomplete proofs, not structural issues. The refactoring proposed here should not introduce or remove any sorries.

---

## Issues NOT Found

The following potential issues were investigated and ruled out:

1. **No duplicate definitions beyond subformula/complexity**: Grep across the entire subtree found no other cases of the same definition appearing in multiple files.

2. **No transitive import collisions beyond the documented one**: The CutElimination -> Tableau.Defs chain is the only case where a transitive import creates a name collision.

3. **No namespace hygiene issues**: All definitions are properly in the `Cslib.Logic.PL` namespace. The 47 uses of `private`/`protected` are appropriate. No definitions leak into the global namespace.

4. **LJ subtree is clean**: LJ/CutElimination.lean imports only LJ.Basic (no phantom imports). The LJ subtree has no duplication issues.

5. **Semantics/Algebra/ subtree is clean**: Despite having 18 files and complex interdependencies, no duplicated definitions or misplaced code was found. The conservative extension chain files are well-organized.

6. **Proof system equivalence bridge is clean**: ProofSystemEquivalence.lean properly imports from both LK and LJ completeness.

---

## Dependency Graph Summary

### Current Problematic Chain
```
Tableau/Defs.lean  (defines Proposition.complexity)
       |
       v
LK/CutElimination.lean  (PHANTOM import of Tableau/Defs; doesn't use complexity)
       |
       v
LK/SubformulaProperty.lean  (CANNOT import Normalization.lean due to name clash)
                              (DUPLICATES subformula API with lk- prefix)
```

### Proposed Clean Chain
```
Subformula.lean  (NEW: Proposition.subformulas, IsSubformula, complexity)
   |         \
   v          v
Normalization.lean     LK/SubformulaProperty.lean
(imports shared defs)  (imports shared defs; drops lk- prefix duplication)

LK/CutElimination.lean  (removes phantom Tableau/Defs import)
```

---

## Recommended Implementation Order

1. **Create `Cslib/Logics/Propositional/Subformula.lean`**: Extract `Proposition.subformulas`, `Proposition.IsSubformula`, all associated lemmas, and `Proposition.complexity` with its simp lemmas. Import only `Cslib/Logics/Propositional/Defs.lean`.

2. **Remove phantom import from CutElimination.lean**: Delete `public import Cslib.Logics.Propositional.Tableau.Defs` from line 11. Verify the file still builds (it should, since nothing from Tableau.Defs is used).

3. **Update Normalization.lean**: Replace the subformula infrastructure section (lines 59-154) with `public import Cslib.Logics.Propositional.Subformula`. Delete the local `Proposition.subformulas`, `Proposition.IsSubformula`, all 9 subformula lemmas, and `Proposition.complexity`.

4. **Update SubformulaProperty.lean**: Replace the entire subformula infrastructure section (lines 48-134) with `public import Cslib.Logics.Propositional.Subformula`. Rewrite the proofs to use `Proposition.IsSubformula` instead of `Proposition.LKIsSubformula` (and `subformulas` instead of `lkSubformulas`). Delete the `lk`-prefixed definitions.

5. **Update Tableau/Defs.lean**: Replace the complexity section (lines 110-173) with `public import Cslib.Logics.Propositional.Subformula` (or import Subformula.lean). Delete the local `Proposition.complexity` and its simp lemmas.

6. **Make CutElimination Finset helpers private**: Add `private` to `mem_of_ne_head`, `subset_insert2`, and `insert_subset_swap`.

7. **Update barrel import**: Uncomment CutElimination in `LK.lean` or add a clarifying comment about the transitive import via SubformulaProperty.

8. **Run CI**: `lake build`, `lake exe checkInitImports`, `lake exe mk_all --module`, `lake shake`.

---

## Standards Compliance Notes

- **CONTRIBUTING.md (Reuse principle)**: The current duplication directly violates "New definitions should instantiate existing abstractions whenever appropriate." The proposed extraction creates the reusable abstraction.
- **ORGANISATION.md**: The proposed `Subformula.lean` fits naturally alongside `Defs.lean` in the `Propositional/` root, consistent with the organization of `Defs.lean` as the foundation module.
- **NOTATION.md**: No notation changes needed; the subformula infrastructure uses standard Lean notation.
