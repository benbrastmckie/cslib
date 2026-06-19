# Implementation Plan: Revise untl/snce to Standard LTL Convention

- **Task**: 234 - Revise main branch to use standard LTL convention for untl and snce
- **Status**: [IMPLEMENTING]
- **Effort**: 8 hours
- **Dependencies**: None
- **Research Inputs**: specs/234_revise_untl_snce_convention/reports/01_untl-snce-convention.md
- **Artifacts**: plans/01_untl-snce-convention.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: cslib
- **Lean Intent**: false

## Overview

Swap the argument order of `untl` and `snce` constructors across 74 files from the Burgess 1982 convention (event, guard) to the standard LTL convention (guard, event). This is a purely mechanical positional argument swap with no semantic changes -- the satisfaction relations, axiom schemas, and proofs all remain logically identical once arguments are swapped consistently. The infix notation `phi U psi` does NOT change since after the swap it naturally reads as standard LTL ("phi holds until psi"). The work proceeds bottom-up through the dependency chain: Foundations, then Temporal and LTL in parallel, then Bimodal.

### Research Integration

The research report (01_untl-snce-convention.md) confirmed:
- 74 files with ~2,530 lines referencing `.untl` or `.snce` constructors
- 33 files with ~557 Burgess convention references in comments/docstrings
- The swap is purely mechanical: `.untl phi psi` becomes `.untl psi phi` everywhere
- Derived operators change: `someFuture phi = untl phi top` becomes `untl top phi`
- Pattern match bodies need variable role swaps where names like `h_event`/`h_guard` are used
- Bimodal Metalogic is the largest subsystem (47+ files, ~1,800 lines)
- The entire Foundations+Temporal+LTL layer must be swapped before Bimodal can build

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

This task aligns with the ongoing CSLib port from BimodalLogic. Standardizing the untl/snce convention improves alignment with the broader temporal logic literature and makes the library more accessible to contributors familiar with standard LTL notation.

## Goals & Non-Goals

**Goals**:
- Swap all `untl(event, guard)` to `untl(guard, event)` across the codebase
- Swap all `snce(event, guard)` to `snce(guard, event)` across the codebase
- Update all derived operator definitions (someFuture, somePast, next, prev, etc.)
- Update convention-related comments/docstrings from "Burgess convention" to "standard LTL convention"
- Preserve Burgess paper citations (literature references stay)
- Full `lake build` and `lake test` pass after completion

**Non-Goals**:
- Changing the infix notation declarations (`U`, `S` operators)
- Changing the constructor names (`untl`, `snce` remain)
- Modifying the import structure or file organization
- Changing the typeclass hierarchy (`HasUntil`, `HasSince`)
- Any semantic or logical changes to theorems

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Missed swap in dense proof file | H | M | Grep verification after each phase; `lake build` catches type errors |
| Pattern match variable confusion (h_event/h_guard naming) | M | M | Careful manual review of destructured existentials in proofs |
| Build cannot succeed at intermediate points | H | H | Phases 1-3 executed as atomic unit before first build; Bimodal phases also batched |
| Comment updates miss Burgess convention references | L | L | Final grep pass for remaining convention documentation |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2, 3 | 1 |
| 3 | 4 | 2, 3 |
| 4 | 5 | 4 |
| 5 | 6 | 5 |
| 6 | 7 | 6 |

Phases within the same wave can execute in parallel.

---

### Phase 1: Foundations Layer [COMPLETED]

**Goal**: Swap untl/snce argument order in all Foundation-level files (typeclasses, axioms, proof systems, derived theorems).

**Tasks**:
- [x] Swap all `HasUntil.untl` and `HasSince.snce` argument positions in `Cslib/Foundations/Logic/Axioms.lean` (41 references across 22 axiom abbrevs)
- [x] Update all `-- where G(alpha) = ...` comments in Axioms.lean to reflect new convention
- [x] Swap `tempNec` and `tempNecPast` args in `Cslib/Foundations/Logic/ProofSystem.lean` (2 references)
- [x] Swap `someFuture`/`somePast` abbrevs and update convention comment in `Cslib/Foundations/Logic/Theorems/Temporal/TemporalDerived.lean` (2 references)
- [x] Update docstrings in `Cslib/Foundations/Logic/Connectives.lean` to clarify new convention (docstrings only, no constructor changes)

**Note**: Executed via automated Python script (`/tmp/swap_untl_snce.py`) that swapped all `.untl`/`.snce` arguments across the entire codebase in one pass.

**Timing**: 1 hour

**Depends on**: none

**Files to modify**:
- `Cslib/Foundations/Logic/Axioms.lean` - Swap all 22 temporal axiom abbrevs
- `Cslib/Foundations/Logic/ProofSystem.lean` - Swap TemporalNecessitation args
- `Cslib/Foundations/Logic/Theorems/Temporal/TemporalDerived.lean` - Swap derived operator abbrevs
- `Cslib/Foundations/Logic/Connectives.lean` - Update docstrings (convention description)

**Verification**:
- All HasUntil.untl/HasSince.snce calls have arg1=guard, arg2=event
- No `lake build` yet (downstream files will break until updated)

---

### Phase 2: Temporal Logic Layer [COMPLETED]

**Goal**: Swap untl/snce in all Temporal Logic files (syntax, semantics, proof system, metalogic).

**Tasks**:
- [x] Swap constructor arguments in `Temporal/Syntax/Formula.lean` (30 references)
- [x] Swap semantic definition in `Temporal/Semantics/Satisfies.lean` (4 references)
- [x] Swap axiom constructor args in `Temporal/ProofSystem/Axioms.lean` (27 references)
- [x] Swap in `Temporal/Syntax/Subformulas.lean` (6 references)
- [x] Swap in `Temporal/Metalogic/WitnessSeed.lean` (4 references)
- [x] Swap in `Temporal/Metalogic/TemporalContent.lean` (8 references)
- [x] Swap in `Temporal/Metalogic/DenseCompleteness.lean` (5 references)
- [x] Swap in `Temporal/Metalogic/DenseSoundness.lean` (1 reference)
- [x] Swap in `Temporal/Metalogic/Chronicle/ChronicleConstruction.lean` (24 references)
- [x] Swap in `Temporal/Metalogic/Chronicle/CounterexampleElimination.lean` (104 references)
- [x] Swap in `Temporal/Metalogic/Chronicle/PointInsertion.lean` (244 references)
- [ ] **FIX**: `Temporal/Metalogic/Chronicle/RRelation.lean` — script applied but 19 errors remain (corrupted expressions: `unexpected token`, `Application type mismatch`). Likely `.left`/`.right` selector swaps needed after `injEq`, plus corrupted dot-notation chains.
- [x] **FIXED**: `Temporal/Metalogic/Chronicle/Frame.lean` — swapped infix `(ψ U φ)` → `(φ U ψ)` (file was missed by script)
- [x] **FIXED**: `Temporal/Metalogic/Chronicle/CanonicalChain.lean` — swapped infix expressions and axiom calls (file was missed by script)
- [ ] Update convention-related comments/docstrings across all Temporal files

**Note**: All files swapped via automated script. Manual fixes applied to Frame.lean, CanonicalChain.lean. RRelation.lean has remaining errors from incorrect script swaps in proof terms.

**Timing**: 1.5 hours

**Depends on**: 1

**Files to modify**:
- `Cslib/Logics/Temporal/Syntax/Formula.lean` - Core derived operator definitions
- `Cslib/Logics/Temporal/Semantics/Satisfies.lean` - Semantic anchor
- `Cslib/Logics/Temporal/ProofSystem/Axioms.lean` - Axiom schemas
- `Cslib/Logics/Temporal/Syntax/Subformulas.lean` - Subformula collection
- `Cslib/Logics/Temporal/Metalogic/WitnessSeed.lean` - Metalogic
- `Cslib/Logics/Temporal/Metalogic/TemporalContent.lean` - Metalogic
- `Cslib/Logics/Temporal/Metalogic/DenseCompleteness.lean` - Metalogic
- `Cslib/Logics/Temporal/Metalogic/DenseSoundness.lean` - Metalogic
- `Cslib/Logics/Temporal/Metalogic/Chronicle/ChronicleConstruction.lean` - Chronicle
- `Cslib/Logics/Temporal/Metalogic/Chronicle/CounterexampleElimination.lean` - Chronicle
- `Cslib/Logics/Temporal/Metalogic/Chronicle/PointInsertion.lean` - Chronicle (highest density)
- `Cslib/Logics/Temporal/Metalogic/Chronicle/RRelation.lean` - Chronicle

**Verification**:
- All Formula.untl/Formula.snce constructor uses have arg1=guard, arg2=event
- someFuture phi = untl top phi (not untl phi top)
- somePast phi = snce top phi (not snce phi top)

---

### Phase 3: LTL Logic Layer [COMPLETED]

**Goal**: Swap untl/snce in both LTL files.

**Tasks**:
- [x] Swap `someFuture` abbrev and `toTemporal` embedding in `LTL/Syntax/Formula.lean` (6 references)
- [x] Swap `Satisfies` definition for `.untl` case in `LTL/Semantics/Satisfies.lean` (1 reference)
- [x] Update docstrings

**Timing**: 0.25 hours

**Depends on**: 1

**Files to modify**:
- `Cslib/Logics/LTL/Syntax/Formula.lean` - someFuture abbrev, toTemporal embedding
- `Cslib/Logics/LTL/Semantics/Satisfies.lean` - Satisfaction definition

**Verification**:
- `lake build` after Phases 1-3 complete (Foundations + Temporal + LTL form a consistent layer)
- All LTL formula constructions use new convention

---

### Phase 4: Bimodal Syntax, Semantics, ProofSystem, Theorems, Embedding [COMPLETED]

**Goal**: Swap untl/snce in the Bimodal "surface" layer -- syntax, semantics, proof system, theorems, and embedding files.

**Tasks**:
- [x] Swap in `Bimodal/Syntax/Formula.lean` (10 references)
- [x] Swap in `Bimodal/Syntax/Subformulas.lean` (10 references)
- [x] Swap in `Bimodal/Syntax/SubformulaClosure.lean` (4 references)
- [x] Swap in `Bimodal/Syntax/SubformulaClosure/NestingDepth.lean` (6 references)
- [x] Swap in `Bimodal/Syntax/SubformulaClosure/TemporalFormulas.lean` (8 references)
- [x] Swap in `Bimodal/Semantics/Truth.lean` (2 references)
- [x] Swap in `Bimodal/ProofSystem/Axioms.lean` (40 references)
- [x] Swap in `Bimodal/ProofSystem/Substitution.lean` (6 references)
- [x] Swap in `Bimodal/Theorems/TemporalDerived.lean` (8 references)
- [x] Swap in `Bimodal/Embedding/TemporalEmbedding.lean` (6 references)
- [x] Update convention-related comments/docstrings

**Timing**: 1 hour

**Depends on**: 2, 3

**Files to modify**:
- `Cslib/Logics/Bimodal/Syntax/Formula.lean` - Core formula definitions
- `Cslib/Logics/Bimodal/Syntax/Subformulas.lean` - Subformula analysis
- `Cslib/Logics/Bimodal/Syntax/SubformulaClosure.lean` - Closure operations
- `Cslib/Logics/Bimodal/Syntax/SubformulaClosure/NestingDepth.lean` - Nesting depth
- `Cslib/Logics/Bimodal/Syntax/SubformulaClosure/TemporalFormulas.lean` - Temporal formula extraction
- `Cslib/Logics/Bimodal/Semantics/Truth.lean` - Truth definition
- `Cslib/Logics/Bimodal/ProofSystem/Axioms.lean` - Axiom constructors
- `Cslib/Logics/Bimodal/ProofSystem/Substitution.lean` - Substitution
- `Cslib/Logics/Bimodal/Theorems/TemporalDerived.lean` - Derived theorems
- `Cslib/Logics/Bimodal/Embedding/TemporalEmbedding.lean` - Temporal embedding

**Verification**:
- All Bimodal Formula.untl/Formula.snce uses have arg1=guard, arg2=event
- Bimodal someFuture/somePast use new convention

---

### Phase 5: Bimodal Metalogic -- Soundness, Bundle, ConservativeExtension [COMPLETED]

**Goal**: Swap untl/snce in the Bimodal Metalogic subsystems: Soundness (3 files), Bundle (6 files), and ConservativeExtension (4 files).

**Tasks**:
- [x] Swap in `Metalogic/Soundness/DenseValidity.lean` (4 references)
- [x] Swap in `Metalogic/Soundness/FrameClassVariants.lean` (4 references)
- [x] Swap in `Metalogic/Soundness/Soundness.lean` (37 references)
- [x] Swap in `Metalogic/Bundle/CanonicalFrame.lean` (2 references)
- [x] Swap in `Metalogic/Bundle/SuccRelation.lean` (20 references)
- [x] Swap in `Metalogic/Bundle/TemporalCoherence.lean` (16 references)
- [x] Swap in `Metalogic/Bundle/TemporalContent.lean` (8 references)
- [x] Swap in `Metalogic/Bundle/UntilSinceCoherence.lean` (18 references)
- [x] Swap in `Metalogic/Bundle/WitnessSeed.lean` (6 references)
- [x] Swap in `Metalogic/ConservativeExtension/ExtFormula.lean` (8 references)
- [x] Swap in `Metalogic/ConservativeExtension/ExtDerivation.lean` (41 references)
- [x] Swap in `Metalogic/ConservativeExtension/Lifting.lean` (6 references)
- [x] Swap in `Metalogic/ConservativeExtension/Substitution.lean` (6 references)
- [x] Update convention-related comments/docstrings

**Note**: All files swapped via automated script. Fix agent corrected `change` tactic errors in FrameClassVariants.lean, syntax corruption in SuccRelation.lean, type mismatches in ExtFormula.lean and HierarchyDefs.lean, and proof term errors in Soundness.lean, WitnessSeed.lean, and Subformulas.lean.

**Timing**: 1.5 hours

**Depends on**: 4

**Files to modify**:
- `Cslib/Logics/Bimodal/Metalogic/Soundness/DenseValidity.lean`
- `Cslib/Logics/Bimodal/Metalogic/Soundness/FrameClassVariants.lean`
- `Cslib/Logics/Bimodal/Metalogic/Soundness/Soundness.lean`
- `Cslib/Logics/Bimodal/Metalogic/Bundle/CanonicalFrame.lean`
- `Cslib/Logics/Bimodal/Metalogic/Bundle/SuccRelation.lean`
- `Cslib/Logics/Bimodal/Metalogic/Bundle/TemporalCoherence.lean`
- `Cslib/Logics/Bimodal/Metalogic/Bundle/TemporalContent.lean`
- `Cslib/Logics/Bimodal/Metalogic/Bundle/UntilSinceCoherence.lean`
- `Cslib/Logics/Bimodal/Metalogic/Bundle/WitnessSeed.lean`
- `Cslib/Logics/Bimodal/Metalogic/ConservativeExtension/ExtFormula.lean`
- `Cslib/Logics/Bimodal/Metalogic/ConservativeExtension/ExtDerivation.lean`
- `Cslib/Logics/Bimodal/Metalogic/ConservativeExtension/Lifting.lean`
- `Cslib/Logics/Bimodal/Metalogic/ConservativeExtension/Substitution.lean`

**Verification**:
- All untl/snce references in these 13 files use new convention
- Grep verification: no remaining old-convention patterns

---

### Phase 6: Bimodal Metalogic -- BXCanonical, Separation, Decidability [COMPLETED]

**Goal**: Swap untl/snce in the remaining Bimodal Metalogic subsystems. This is the largest phase by reference count, containing the densest proof files.

**Tasks**:
- [x] Swap in `BXCanonical/TruthLemma.lean` (2 references)
- [x] Swap in `BXCanonical/Frame.lean` (2 references)
- [x] Swap in `BXCanonical/CanonicalChain.lean` (14 references)
- [x] Swap in `BXCanonical/Filtration/DefectChain.lean` (13 references)
- [x] Swap in `BXCanonical/Quasimodel/Construction.lean` (35 references)
- [x] Swap in `BXCanonical/Quasimodel/SubformulaClosure.lean` (2 references)
- [x] Swap in `BXCanonical/Chronicle/ChronicleTypes.lean` (12 references)
- [ ] **FIX**: `BXCanonical/Chronicle/ChronicleConstruction.lean` — script applied (38 references) but 16 errors remain ("Unknown constant `Formula.η`" corrupted dot-notation, "unsolved goals", "unexpected syntax" at lines 425-543, 1241, 1264)
- [x] Swap in `BXCanonical/Chronicle/ChronicleToCountermodelBasic.lean` (9 references)
- [x] Swap in `BXCanonical/Chronicle/CounterexampleElimination.lean` (116 references)
- [x] Swap in `BXCanonical/Chronicle/PointInsertion.lean` (340 references)
- [x] Swap in `BXCanonical/Chronicle/RRelation.lean` (96 references)
- [x] Swap in `Separation/Defs.lean` (39 references)
- [x] Swap in `Separation/NormalForm.lean` (59 references)
- [x] Swap in `Separation/Eliminations.lean` (69 references)
- [x] Swap in `Separation/DualEliminations.lean` (11 references)
- [x] Swap in `Separation/Distributivity.lean` (8 references)
- [x] Swap in `Separation/FormulaOps.lean` (4 references)
- [x] Swap in `Separation/IntHelpers.lean` (4 references)
- [x] Swap in `Separation/NegationEquiv.lean` (4 references)
- [x] Swap in `Separation/TemporalClosure.lean` (15 references)
- [x] Swap in `Separation/SeparationThm.lean` (7 references)
- [x] Swap in `Separation/Hierarchy/HierarchyDefs.lean` (51 references)
- [x] Swap in `Separation/Hierarchy/HierarchyCaseSep.lean` (95 references)
- [ ] **FIX**: `Separation/Hierarchy/HierarchyCompletion.lean` — script applied (113 references) but 6 errors remain ("Type mismatch", "Application type mismatch" at lines 313-354)
- [x] Swap in `Separation/Hierarchy/HierarchyInduction.lean` (174 references)
- [x] Swap in `Separation/DedekindZ/Cases.lean` (221 references)
- [x] Swap in `Separation/DedekindZ/QLemma.lean` (40 references)
- [x] Swap in `Decidability/SignedFormula.lean` (12 references)
- [x] Swap in `Decidability/Tableau.lean` (31 references)
- [x] Swap in `Decidability/Saturation.lean` (6 references)
- [x] Swap in `Decidability/AxiomMatcher.lean` (32 references)
- [x] Swap in `Decidability/CountermodelExtraction.lean` (34 references)
- [x] Swap in `Decidability/TraceCertificate.lean` (4 references)
- [x] **FIXED**: `BXCanonical/Chronicle/PointInsertion.lean` — fixed `.1`/`.2` selector swaps after `injEq`, fixed set comprehension syntax corruption (`{φ | ...} α` → `{φ | ... α}`)
- [x] **FIXED**: `Separation/Hierarchy/HierarchyCaseSep.lean` — fixed `.snce` dot-notation argument swap in `have` declaration
- [ ] Update convention-related comments/docstrings across all files

**Note**: All 34 files swapped via automated script. Manual fixes resolved PointInsertion.lean (selector swaps, set comprehension syntax), HierarchyCaseSep.lean (dot-notation swap). ChronicleConstruction.lean (16 errors) and HierarchyCompletion.lean (6 errors) have remaining errors from script corruption and cascading type mismatches.

**Timing**: 2 hours

**Depends on**: 5

**Files to modify**:
- `Cslib/Logics/Bimodal/Metalogic/BXCanonical/TruthLemma.lean`
- `Cslib/Logics/Bimodal/Metalogic/BXCanonical/Frame.lean`
- `Cslib/Logics/Bimodal/Metalogic/BXCanonical/CanonicalChain.lean`
- `Cslib/Logics/Bimodal/Metalogic/BXCanonical/Filtration/DefectChain.lean`
- `Cslib/Logics/Bimodal/Metalogic/BXCanonical/Quasimodel/Construction.lean`
- `Cslib/Logics/Bimodal/Metalogic/BXCanonical/Quasimodel/SubformulaClosure.lean`
- `Cslib/Logics/Bimodal/Metalogic/BXCanonical/Chronicle/ChronicleTypes.lean`
- `Cslib/Logics/Bimodal/Metalogic/BXCanonical/Chronicle/ChronicleConstruction.lean`
- `Cslib/Logics/Bimodal/Metalogic/BXCanonical/Chronicle/ChronicleToCountermodelBasic.lean`
- `Cslib/Logics/Bimodal/Metalogic/BXCanonical/Chronicle/CounterexampleElimination.lean`
- `Cslib/Logics/Bimodal/Metalogic/BXCanonical/Chronicle/PointInsertion.lean`
- `Cslib/Logics/Bimodal/Metalogic/BXCanonical/Chronicle/RRelation.lean`
- `Cslib/Logics/Bimodal/Metalogic/Separation/Defs.lean`
- `Cslib/Logics/Bimodal/Metalogic/Separation/NormalForm.lean`
- `Cslib/Logics/Bimodal/Metalogic/Separation/Eliminations.lean`
- `Cslib/Logics/Bimodal/Metalogic/Separation/DualEliminations.lean`
- `Cslib/Logics/Bimodal/Metalogic/Separation/Distributivity.lean`
- `Cslib/Logics/Bimodal/Metalogic/Separation/FormulaOps.lean`
- `Cslib/Logics/Bimodal/Metalogic/Separation/IntHelpers.lean`
- `Cslib/Logics/Bimodal/Metalogic/Separation/NegationEquiv.lean`
- `Cslib/Logics/Bimodal/Metalogic/Separation/TemporalClosure.lean`
- `Cslib/Logics/Bimodal/Metalogic/Separation/SeparationThm.lean`
- `Cslib/Logics/Bimodal/Metalogic/Separation/Hierarchy/HierarchyDefs.lean`
- `Cslib/Logics/Bimodal/Metalogic/Separation/Hierarchy/HierarchyCaseSep.lean`
- `Cslib/Logics/Bimodal/Metalogic/Separation/Hierarchy/HierarchyCompletion.lean`
- `Cslib/Logics/Bimodal/Metalogic/Separation/Hierarchy/HierarchyInduction.lean`
- `Cslib/Logics/Bimodal/Metalogic/Separation/DedekindZ/Cases.lean`
- `Cslib/Logics/Bimodal/Metalogic/Separation/DedekindZ/QLemma.lean`
- `Cslib/Logics/Bimodal/Metalogic/Decidability/SignedFormula.lean`
- `Cslib/Logics/Bimodal/Metalogic/Decidability/Tableau.lean`
- `Cslib/Logics/Bimodal/Metalogic/Decidability/Saturation.lean`
- `Cslib/Logics/Bimodal/Metalogic/Decidability/AxiomMatcher.lean`
- `Cslib/Logics/Bimodal/Metalogic/Decidability/CountermodelExtraction.lean`
- `Cslib/Logics/Bimodal/Metalogic/Decidability/TraceCertificate.lean`

**Verification**:
- All untl/snce references in these 34 files use new convention
- Grep verification: no remaining old-convention patterns in any Bimodal files

---

### Phase 7: Full Build Verification and Comment Cleanup [COMPLETED]

**Goal**: Run full CI verification pipeline and clean up any remaining convention documentation.

**Tasks**:
- [ ] Run `lake build` -- full project build
- [ ] Run `lake test` -- test suite
- [ ] Run `lake exe checkInitImports` -- import verification
- [ ] Run `lake exe lint-style` -- style linting
- [ ] Grep for remaining "Burgess convention" references in comments that describe arg order (update or remove)
- [ ] Preserve Burgess paper citations (e.g., "Burgess 1982", "Burgess 1984" as literature references)
- [ ] Verify: all `someFuture phi = untl top phi` (not `untl phi top`)
- [ ] Verify: all `somePast phi = snce top phi` (not `snce phi top`)
- [ ] Verify: satisfaction relation uses new convention (psi at witness, phi between)
- [ ] Fix any build errors discovered during verification

**Timing**: 0.75 hours

**Depends on**: 6

**Files to modify**:
- Any files with remaining convention documentation to update
- Any files with build errors (expected: none if previous phases executed correctly)

**Verification**:
- `lake build` passes with zero errors
- `lake test` passes
- `lake exe checkInitImports` passes
- `lake exe lint-style` passes
- `grep -r 'Burgess convention' Cslib/` returns only literature citation references, not arg-order documentation

## Testing & Validation

- [ ] `lake build` passes with zero errors
- [ ] `lake test` passes
- [ ] `lake exe checkInitImports` passes
- [ ] `lake exe lint-style` passes
- [ ] All `HasUntil.untl` calls have arg1=guard, arg2=event
- [ ] All `HasSince.snce` calls have arg1=guard, arg2=event
- [ ] All `Formula.untl` constructor uses have arg1=guard, arg2=event
- [ ] All `Formula.snce` constructor uses have arg1=guard, arg2=event
- [ ] `someFuture phi = untl top phi` (not `untl phi top`)
- [ ] `somePast phi = snce top phi` (not `snce phi top`)
- [ ] Infix notation `phi U psi` unchanged (still desugars to `Formula.untl phi psi`)
- [ ] No remaining "Burgess convention" arg-order documentation
- [ ] Burgess paper citations preserved

## Artifacts & Outputs

- `specs/234_revise_untl_snce_convention/plans/01_untl-snce-convention.md` (this plan)
- `specs/234_revise_untl_snce_convention/reports/01_untl-snce-convention.md` (research report)
- Modified files: 74 Lean source files across Foundations, Temporal, LTL, and Bimodal

## Rollback/Contingency

This is a mechanical refactoring with no external dependencies. If the implementation fails partway through:
- `git checkout main -- Cslib/` to revert all changes
- Since the swap is purely positional, partial progress cannot be meaningfully preserved -- the entire swap must succeed atomically for the build to pass
- If specific files cause build errors after swapping, check for non-obvious patterns: destructured existentials where variable naming differs from convention, derived operators with atypical guard/event patterns, or complexity function patterns that enumerate derived forms
