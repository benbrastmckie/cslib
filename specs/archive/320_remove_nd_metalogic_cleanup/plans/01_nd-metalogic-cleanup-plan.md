# Implementation Plan: Task #320

- **Task**: 320 - Remove ND-level metalogic superseded by Hilbert-primary results
- **Status**: [PARTIAL]
- **Effort**: 6 hours
- **Dependencies**: None
- **Research Inputs**: specs/320_remove_nd_metalogic_cleanup/reports/01_nd-metalogic-cleanup-research.md
- **Artifacts**: plans/01_nd-metalogic-cleanup-plan.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: cslib
- **Lean Intent**: false

## Overview

This plan removes ND-level algebraic completeness infrastructure that has been superseded by
Hilbert-primary results. The core challenge identified in research is that the bridge theorems
(`derivableInMplIffDerivableMin`, `derivableInIplIffDerivableInt`, `derivableInCplIffDerivableProp`)
in `HilbertConservativeGlivenko.lean` currently depend on ND completeness to connect
`DerivableIn (Theory.MPL/IPL/CPL)` with `Derivable (MinPropAxiom/IntPropAxiom/PropositionalAxiom)`.
The refactoring replaces these semantic bridges with syntactic proof-theoretic bridges that compose
`hilbert_iff_nd` with theory-weakening and axiom-admissibility lemmas. After the bridge rewrite,
`Completeness.lean`, `Lindenbaum.lean`, and `LindenbaumInstances.lean` can be deleted entirely.
Net result: removal of approximately 700-850 lines with approximately 100 lines of new syntactic
bridge proofs.

### Research Integration

Key findings from `01_nd-metalogic-cleanup-research.md`:
- ND completeness theorems are NOT trivially removable; they underpin the bridge theorems
- `hilbert_iff_nd` connects `Derivable Axioms` with `DerivableIn (AxiomTheory Axioms)`, which
  is a different ND theory than `Theory.MPL = emptyset`
- The forward bridge direction (empty-theory ND to AxiomTheory ND) is trivial via weakening
- The backward direction requires proving each axiom schema is an ND theorem of the empty theory
  (K, S, andI, andE1, andE2, orI1, orI2, orE for MPL; additionally EFQ for IPL; DNE for CPL)
- `LindenbaumInstances.lean` has zero downstream imports and can be deleted immediately
- `ConjImpConservative.lean` and `ConjImpBotConservative.lean` use `derivableInIplIffDerivableInt`
  and must be updated to use the new bridge theorem

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

No ROADMAP.md items are directly advanced by this task. The task is internal cleanup of the
propositional-level algebraic semantics module tree.

## Goals & Non-Goals

**Goals**:
- Replace ND-completeness-based bridge theorems with syntactic proof-theoretic bridges
- Delete `Completeness.lean` (277 lines), `Lindenbaum.lean` (425 lines), `LindenbaumInstances.lean` (145 lines)
- Preserve the API surface of bridge theorems (`derivableInMplIffDerivableMin` etc.) with new proofs
- Update module docstrings to reflect Hilbert-primary architecture
- Maintain a sorry-free, fully-compiling build

**Non-Goals**:
- Restructuring the Hilbert completeness pathway itself
- Modifying any modal/temporal/bimodal metalogic modules
- Changing the `hilbert_iff_nd` equivalence infrastructure in `Equivalence.lean`
- Touching the separate Hilbert Lindenbaum algebra (`HilbertLindenbaum.lean`)

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Axiom admissibility proofs are harder than expected (ND derivation of K, S, etc.) | M | L | These are standard textbook constructions; ND structural rules directly validate all MinPropAxiom schemata |
| Bridge theorem API change breaks downstream consumers | H | M | Preserve exact theorem signatures; only change proofs, not types |
| Theory weakening direction requires non-trivial infrastructure | M | L | Research confirms weakening from empty theory to AxiomTheory is trivial |
| `ConjImpConservative`/`ConjImpBotConservative` fail after bridge rewrite | M | L | The bridge theorem type signatures are preserved; only internal proofs change |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2 | 1 |
| 3 | 3 | 2 |
| 4 | 4 | 3 |
| 5 | 5 | 4 |

Phases within the same wave can execute in parallel.

---

### Phase 1: Delete LindenbaumInstances.lean and prove axiom admissibility lemmas [COMPLETED]

**Goal**: Remove the zero-consumer `LindenbaumInstances.lean` and create the syntactic
admissibility lemmas needed by Phase 2.

**Tasks**:
- [x] Delete `Cslib/Logics/Propositional/Semantics/Algebra/LindenbaumInstances.lean`
- [x] Remove the `LindenbaumInstances` import from `Cslib.lean` barrel file
- [x] Create a new file `Cslib/Logics/Propositional/NaturalDeduction/AxiomAdmissibility.lean` (326 lines) containing:
  - `Theory.Derivation.replaceAxioms`: structural induction replacing axiom uses between theories
  - `DerivableIn.replaceAxioms`: prop-level wrapper
  - MPL axiom admissibility: `nd_derivable_K`, `nd_derivable_S`, `nd_derivable_andI`, `nd_derivable_andE1`, `nd_derivable_andE2`, `nd_derivable_orI1`, `nd_derivable_orI2`, `nd_derivable_orE`
  - IPL axiom admissibility: `ipl_contains_efq` (EFQ membership in IPL)
  - CPL axiom admissibility: `nd_derivable_dne_from_axiomTheory_cl` (DNE via Peirce + EFQ) and `propositionalAxiom_admissible` (Peirce via DNE)
  - Composed equivalences: `axiomTheory_min_iff_mpl`, `axiomTheory_int_iff_ipl`, `axiomTheory_cl_iff_cpl`
- [x] Verify `lake build Cslib.Logics.Propositional.NaturalDeduction.AxiomAdmissibility` — compiles cleanly

**Timing**: 2 hours

**Depends on**: none

**Files to modify**:
- `Cslib/Logics/Propositional/Semantics/Algebra/LindenbaumInstances.lean` - delete
- `Cslib.lean` - remove LindenbaumInstances import
- `Cslib/Logics/Propositional/NaturalDeduction/AxiomAdmissibility.lean` - create (new file, 326 lines)

**Verification**:
- `LindenbaumInstances.lean` no longer exists
- New admissibility file compiles without sorry
- `lake build` succeeds (no broken imports from LindenbaumInstances deletion)

---

### Phase 2: Rewrite bridge theorems in HilbertConservativeGlivenko.lean [COMPLETED]

**Goal**: Replace the semantic (ND-completeness-based) bridge proofs with syntactic proofs
composing `hilbert_iff_nd` with the admissibility equivalences from Phase 1.

**Tasks**:
- [x] Add import for the new admissibility module to `HilbertConservativeGlivenko.lean` (line 12)
- [x] Rewrite `derivableInMplIffDerivableMin` proof: `axiomTheory_min_iff_mpl.trans hilbert_iff_nd_min.symm`
- [x] Rewrite `derivableInIplIffDerivableInt` proof: `axiomTheory_int_iff_ipl.trans hilbert_iff_nd_int.symm`
- [x] Rewrite `derivableInCplIffDerivableProp` proof: `axiomTheory_cl_iff_cpl.trans hilbert_iff_nd_cl.symm`
- [x] Remove the `import Cslib.Logics.Propositional.Semantics.Algebra.Completeness` line
- [x] `ipl_conservative_over_mpl` and `glivenko` ND corollaries work with new bridges (no changes needed)
- [x] Verify `lake build Cslib.Logics.Propositional.Semantics.Algebra.HilbertConservativeGlivenko` — compiles cleanly

**Timing**: 1.5 hours

**Depends on**: 1

**Files to modify**:
- `Cslib/Logics/Propositional/Semantics/Algebra/HilbertConservativeGlivenko.lean` - rewrite bridge proofs, update imports (~60 lines modified)

**Verification**:
- Bridge theorem signatures are unchanged
- No import of `Completeness.lean`
- File compiles without sorry
- `ConjImpConservative.lean` and `ConjImpBotConservative.lean` still compile (they consume bridge theorems by name, and signatures are preserved)

---

### Phase 3: Delete Completeness.lean and Lindenbaum.lean [COMPLETED]

**Goal**: Remove the now-orphaned ND completeness and ND Lindenbaum algebra files.

**Tasks**:
- [x] Verify no remaining imports of `Completeness.lean` exist — confirmed zero
- [x] Delete `Cslib/Logics/Propositional/Semantics/Algebra/Completeness.lean` (277 lines)
- [x] Verify no remaining imports of `Lindenbaum.lean` exist — confirmed zero
- [x] Delete `Cslib/Logics/Propositional/Semantics/Algebra/Lindenbaum.lean` (425 lines)
- [x] Remove both entries from `Cslib.lean` barrel file
- [x] Barrel file updated (AxiomAdmissibility added at line 411)
- [x] Scoped builds for all task 320 modules pass

**Timing**: 30 minutes

**Depends on**: 2

**Files to modify**:
- `Cslib/Logics/Propositional/Semantics/Algebra/Completeness.lean` - delete
- `Cslib/Logics/Propositional/Semantics/Algebra/Lindenbaum.lean` - delete
- `Cslib.lean` - remove both import entries

**Verification**:
- Both files deleted
- `grep -r "Lindenbaum\b" Cslib.lean` returns no hits for ND Lindenbaum (HilbertLindenbaum should remain)
- `grep -r "import.*Completeness" --include="*.lean" Cslib/Logics/Propositional/Semantics/Algebra/` returns no references to the deleted file
- Full `lake build` succeeds

---

### Phase 4: Update module docstrings [COMPLETED]

**Goal**: Update documentation to reflect the new Hilbert-primary architecture where ND inherits
results via equivalence rather than proving them independently.

**Tasks**:
- [x] Update `Cslib/Logics/Propositional/Semantics/Algebra.lean` docstring:
  - Added "Hilbert-Primary Architecture" section (lines 49-61)
  - No references to removed ND completeness theorems
  - States Hilbert is primary, ND inherits via syntactic bridges through AxiomAdmissibility
- [x] Update `Cslib/Logics/Propositional/Semantics/Algebra/HilbertConservativeGlivenko.lean` docstring:
  - Documented "Syntactic Bridges" section explaining composition of `hilbert_iff_nd` with axiom admissibility
  - Explains Hilbert-primary theorems vs ND corollaries via bridges
  - No references to ND algebraic completeness
- [x] `Cslib/Logics/Propositional/NaturalDeduction/AxiomAdmissibility.lean` docstring:
  - Comprehensive module doc (lines 13-45) describing `replaceAxioms`, the three equivalences, and architecture
- [x] Scoped builds pass after docstring changes

**Timing**: 45 minutes

**Depends on**: 3

**Files to modify**:
- `Cslib/Logics/Propositional/Semantics/Algebra.lean` - update module docstring
- `Cslib/Logics/Propositional/Semantics/Algebra/HilbertConservativeGlivenko.lean` - update module docstring
- `Cslib/Logics/Propositional/NaturalDeduction/AxiomAdmissibility.lean` - verify/update docstring

**Verification**:
- Docstrings accurately describe the current architecture
- No references to deleted files or theorems
- `lake build` succeeds

---

### Phase 5: Final verification and CI checks [PARTIAL]

**Goal**: Run the full CI verification pipeline to ensure the build is clean.

**Tasks**:
- [x] Verify no `sorry` in any modified or new files — confirmed zero
- [x] Verify downstream modules still compile:
  - [x] `Cslib.Logics.Propositional.Semantics.Algebra.ConjImpConservative` — clean
  - [x] `Cslib.Logics.Propositional.Semantics.Algebra.ConjImpBotConservative` — clean
  - [x] `Cslib.Logics.Propositional.ProofSystemEquivalence` — clean
  - [x] `Cslib.Logics.Propositional.Tableau.Classical.Soundness` — clean
  - [ ] `Cslib.Logics.Propositional.Tableau.Classical.Completeness` — **pre-existing errors from task 317** (not caused by task 320)
  - [x] No Tableau modules import deleted files
- [ ] Run `lake build` (full project) — **blocked by pre-existing errors** in `Tableau.Classical.Completeness` (task 317)
- [ ] Run `lake exe checkInitImports` — **blocked by same pre-existing build errors**
- [ ] Run `lake exe lint-style` — file-level runs clean on task 320 files; full run blocked
- [ ] Run `lake test` — **blocked by pre-existing build errors**
- [ ] Run `lake shake --add-public --keep-implied --keep-prefix` — **not run**

**Note**: Full CI pipeline is blocked by pre-existing errors in `Tableau/Classical/Completeness.lean` (task 317 in-progress work). These errors are unrelated to task 320 changes. All task 320 modules and their direct downstream consumers compile cleanly in scoped builds.

**Timing**: 1 hour (mostly build time)

**Depends on**: 4

**Files to modify**:
- None (verification only); minor fixups if CI flags issues

**Verification**:
- [x] Zero sorry in new/modified files
- [x] All direct downstream modules compile (ConjImpConservative, ConjImpBotConservative, ProofSystemEquivalence)
- [ ] Full CI checks blocked by pre-existing task 317 errors — not a task 320 regression
- [ ] `lake shake` not run

## Testing & Validation

- [ ] `lake build` succeeds with zero errors — **blocked by pre-existing task 317 errors**
- [ ] `lake exe checkInitImports` passes — **blocked by same**
- [ ] `lake exe lint-style` passes — **blocked by same** (file-level clean)
- [ ] `lake test` passes — **blocked by same**
- [x] No `sorry` in any modified or new files
- [x] Bridge theorem type signatures are unchanged (API compatibility)
- [x] `ConjImpConservative.lean` compiles without modification
- [x] `ConjImpBotConservative.lean` compiles without modification
- [x] No downstream module references deleted files

## Artifacts & Outputs

- `specs/320_remove_nd_metalogic_cleanup/plans/01_nd-metalogic-cleanup-plan.md` (this file)
- `Cslib/Logics/Propositional/NaturalDeduction/AxiomAdmissibility.lean` (new, 326 lines)
- Deleted: `Cslib/Logics/Propositional/Semantics/Algebra/LindenbaumInstances.lean` (145 lines)
- Deleted: `Cslib/Logics/Propositional/Semantics/Algebra/Completeness.lean` (277 lines)
- Deleted: `Cslib/Logics/Propositional/Semantics/Algebra/Lindenbaum.lean` (425 lines)
- Modified: `Cslib/Logics/Propositional/Semantics/Algebra/HilbertConservativeGlivenko.lean`
- Modified: `Cslib/Logics/Propositional/Semantics/Algebra.lean` (docstring)
- Modified: `Cslib.lean` (barrel imports)

## Rollback/Contingency

All three deleted files are tracked in git. If the bridge rewrite in Phase 2 proves infeasible
(axiom admissibility proofs are harder than expected), the fallback is Option C from the research
report: keep ND completeness as internal bridge infrastructure, deprecate public API, and update
docstrings only. This fallback requires reverting Phase 1-3 deletions and proceeding only with
Phase 4 docstring updates. The `git stash` or `git checkout` commands can restore any deleted file.
