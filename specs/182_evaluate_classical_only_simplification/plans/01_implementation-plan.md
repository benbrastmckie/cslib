# Implementation Plan: Task #182

- **Task**: 182 - Revert Modal/, Temporal/, and Bimodal/ to purely classical systems with minimal formula constructors
- **Status**: [NOT STARTED]
- **Effort**: 24 hours
- **Dependencies**: None (tasks 173-177 completed; Propositional/ and Foundations/ theorems stable)
- **Research Inputs**: reports/01_classical-simplification-tradeoffs.md, reports/02_team-research.md, reports/02_teammate-a-findings.md, reports/02_teammate-b-findings.md, reports/02_teammate-c-findings.md
- **Artifacts**: plans/01_implementation-plan.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: cslib
- **Lean Intent**: true

## Overview

Revert the primitive `and`/`or` constructors added by tasks 175-177 to the Modal, Temporal, and Bimodal layers, restoring Lukasiewicz abbreviations (`and phi psi := neg (imp phi (neg psi))`, `or phi psi := imp (neg phi) psi`). The Propositional layer is unchanged (keeps 5 primitives with 3-tier completeness). The revert touches ~126 files across three layers, removing ~55% of axiom constructors per system. After the revert, three deliverables validate correctness: updated syntactic embeddings (FromPropositional), verified axiom inheritance via Foundations theorems, and conservative extension proofs showing each upper layer introduces no new propositional truths.

The strategy is per-file selective restore from baseline commits (not `git revert`) because the commit history is interleaved across tasks 174-178. The plan organizes work into 8 phases following the layer dependency order: formula types first, then foundations, embeddings, per-layer bulk restore, and finally conservative extension proofs.

### Research Integration

Five research reports inform this plan:

1. **Decision report** (01): Confirmed classical-only direction with Lukasiewicz abbreviations. Propositional retains full primitives; upper layers use abbreviations.
2. **Git revert strategy** (02-A): Per-file selective restore recommended. Baseline commits: `8b2a470d` (Modal), `de59f56b`/`abd1aa15^` (Temporal), `c4e75ad4`/`c38fe3d6^` (Bimodal), `1852de3a` (Foundations/orchestration files).
3. **Axiom inheritance** (02-B): Zero gaps -- all and/or reasoning derivable from ClassicalHilbert via Foundations theorems (pairing, lce_imp, rce_imp, classical_merge, De Morgan). Helper files simplify ~40%.
4. **Conservative extension** (02-C): Modal K is 3-line composition of existing infrastructure. Temporal needs ~30-50 lines (new semantic bridge). Bimodal needs ~80-150 lines (syntactic projection approach recommended).

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

This plan advances the Bimodal porting project by simplifying the axiom and formula infrastructure across Modal, Temporal, and Bimodal layers. Conservative extension proofs are new metalogic results for each layer.

## Goals & Non-Goals

**Goals**:
- Remove `.and`/`.or` constructors from Modal, Temporal, and Bimodal formula inductive types
- Restore `abbrev` definitions using Lukasiewicz encoding for and/or/neg/top
- Remove all `.and`/`.or` pattern match arms, axiom constructors, soundness cases, truth lemma cases, and semantic satisfaction clauses
- Update FromPropositional embeddings to map PL's primitive and/or to upper-layer abbreviations
- Verify Foundations theorems provide complete and/or reasoning via ClassicalHilbert
- Prove conservative extension of each upper layer over CPL
- Zero sorries target (except pre-existing task-36 sorries in Bimodal)
- Clean `lake build` after each phase

**Non-Goals**:
- Modifying the Propositional layer (unchanged; retains 5 primitives and 3-tier completeness)
- Modifying Foundations/Logic/Theorems/ (already uses Lukasiewicz encoding; no changes needed)
- Re-adding intuitionistic support (deferred; forward path documented in research)
- Proving conservative extension for systems beyond K, BX, and the base Bimodal F
- Optimizing proof performance or refactoring beyond what the revert requires

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Bimodal layer size (~50+ files) makes Phase 6 the largest single phase | H | H | Split into sub-directory groups; commit after each group; track progress incrementally |
| FromPropositional semantic coherence proofs require new Lean code | M | M | Use Peirce's law + classical_merge; Foundations Core theorems cover the cases; research confirms straightforward |
| Bimodal conservative extension approach selection (syntactic vs semantic) | M | M | Audit `lift_derivation_qfree` before starting Phase 8; fall back to direct semantic bridge if projection fails |
| Post-revert build failures from incomplete phase sequences | H | M | Run `lake build` after every phase; never start next phase on broken build |
| Subformulas.lean may have new content beyond baseline | L | M | Read before Phase 5/6; use targeted editing if clean restore insufficient |
| Universe mismatch in Modal conservative extension composition | L | L | Instantiate `k_soundness_derivable` at universe 0 explicitly if needed |
| `Cslib.Init` import chain references removed symbols | L | M | Run `lake exe checkInitImports` after phases that remove axiom instances |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2 | 1 |
| 3 | 3, 4 | 2 |
| 4 | 5 | 3, 4 |
| 5 | 6 | 4, 5 |
| 6 | 7 | 3 |
| 7 | 8 | 5, 6, 7 |

Phases within the same wave can execute in parallel.

---

### Phase 1: Formula Type and Foundations Revert [NOT STARTED]

**Goal**: Remove `.and`/`.or` constructors from all three formula inductive types and restore Lukasiewicz abbreviations. Revert Foundations files that added `[HasAnd F] [HasOr F]` constraints.

**Tasks**:
- [ ] Restore `Cslib/Logics/Modal/Basic.lean` formula type from baseline `8b2a470d`: remove `.and`/`.or` constructors, restore `abbrev Proposition.and`, `abbrev Proposition.or`, `abbrev Proposition.neg`, `abbrev Proposition.top`
- [ ] Restore `Cslib/Logics/Temporal/Syntax/Formula.lean` from baseline `abd1aa15^`: remove `.and`/`.or` constructors, restore abbreviations
- [ ] Restore `Cslib/Logics/Bimodal/Syntax/Formula.lean` from baseline `c38fe3d6^`: remove `.and`/`.or` constructors, restore abbreviations
- [ ] Restore `Cslib/Foundations/Logic/Axioms.lean` from baseline `1852de3a`: remove `[HasAnd F] [HasOr F]` from Temporal section variable block, restore `conj'`/`disj'` Lukasiewicz helpers in BX axiom definitions
- [ ] Restore `Cslib/Foundations/Logic/ProofSystem.lean` from baseline `1852de3a`: remove `[HasAnd F] [HasOr F]` from `TemporalBXHilbert` and `BimodalTMHilbert` class declarations
- [ ] Restore `Cslib/Foundations/Logic/Theorems/Temporal/TemporalDerived.lean` from baseline `1852de3a`
- [ ] Verify the 6 files compile individually (expect downstream build errors; this phase sets the foundation)

**Timing**: 1 hour

**Depends on**: none

**Files to modify**:
- `Cslib/Logics/Modal/Basic.lean` -- remove .and/.or constructors, restore abbrevs
- `Cslib/Logics/Temporal/Syntax/Formula.lean` -- remove .and/.or constructors, restore abbrevs
- `Cslib/Logics/Bimodal/Syntax/Formula.lean` -- remove .and/.or constructors, restore abbrevs
- `Cslib/Foundations/Logic/Axioms.lean` -- remove HasAnd/HasOr from temporal section
- `Cslib/Foundations/Logic/ProofSystem.lean` -- remove HasAnd/HasOr from class declarations
- `Cslib/Foundations/Logic/Theorems/Temporal/TemporalDerived.lean` -- restore pre-orchestration version

**Verification**:
- Each of the 6 files compiles individually without errors
- Formula types have the target constructor counts: Modal 4, Temporal 5, Bimodal 6
- Abbreviations `and`/`or`/`neg`/`top` are defined using `imp`/`bot`

---

### Phase 2: Embedding Updates (FromPropositional + Cross-Layer) [NOT STARTED]

**Goal**: Update all embedding files so PL's 5-constructor formulas map correctly to the upper layers' reduced constructor sets plus Lukasiewicz abbreviations. This is the only phase requiring genuinely new proof code.

**Tasks**:
- [ ] Update `Cslib/Logics/Modal/FromPropositional.lean`: map `PL.and`/`PL.or` to Modal abbreviations (Lukasiewicz encoding). Update `modal_satisfies_toModal_iff_evaluate` to handle and/or cases via abbreviation unfolding. Prove and/or cases reduce through `imp`/`bot` satisfaction semantics (use `by_contra` or `Classical.em` for classical equivalence)
- [ ] Update `Cslib/Logics/Temporal/FromPropositional.lean`: map `PL.and`/`PL.or` to Temporal abbreviations. Update or create semantic coherence lemmas for the and/or abbreviation cases
- [ ] Update `Cslib/Logics/Bimodal/Embedding/PropositionalEmbedding.lean`: map `PL.and`/`PL.or` to Bimodal abbreviations. Update semantic coherence proofs
- [ ] Restore `Cslib/Logics/Bimodal/Embedding/ModalEmbedding.lean` from baseline `1852de3a`: remove .and/.or cases from Modal-to-Bimodal embedding
- [ ] Restore `Cslib/Logics/Bimodal/Embedding/TemporalEmbedding.lean` from baseline `1852de3a`: remove .and/.or cases from Temporal-to-Bimodal embedding
- [ ] Run `lake build` on embedding files to verify compilation

**Timing**: 2 hours

**Depends on**: 1

**Files to modify**:
- `Cslib/Logics/Modal/FromPropositional.lean` -- map PL and/or to abbreviations, update semantic bridge
- `Cslib/Logics/Temporal/FromPropositional.lean` -- map PL and/or to abbreviations
- `Cslib/Logics/Bimodal/Embedding/PropositionalEmbedding.lean` -- map PL and/or to abbreviations
- `Cslib/Logics/Bimodal/Embedding/ModalEmbedding.lean` -- remove .and/.or cases
- `Cslib/Logics/Bimodal/Embedding/TemporalEmbedding.lean` -- remove .and/.or cases

**Verification**:
- All 5 embedding files compile
- `toModal`, `toTemporal`, `toBimodal` handle all 5 PL constructors (atom, bot, imp, and, or)
- Semantic bridge lemma (`modal_satisfies_toModal_iff_evaluate`) passes for all cases
- `lake build` succeeds on embedding module

---

### Phase 3: Modal Layer Bulk Revert [NOT STARTED]

**Goal**: Remove all `.and`/`.or` match arms, axiom constructors, soundness cases, and related infrastructure from the Modal layer (~51 files). Restore from baseline `8b2a470d`.

**Tasks**:
- [ ] Restore `Cslib/Logics/Modal/Denotation.lean`: remove .and/.or satisfaction/denotation cases
- [ ] Restore `Cslib/Logics/Modal/LogicalEquivalence.lean`: remove .and/.or equivalence cases
- [ ] Restore `Cslib/Logics/Modal/Metalogic/DerivationTree.lean`: remove andI/andE1/andE2/orI1/orI2/orE constructors
- [ ] Restore all 15 `Modal/ProofSystem/Instances/*.lean` files: remove 6 HasAxiomAnd*/HasAxiomOr* instance registrations per file
- [ ] Restore all 15 `Modal/Metalogic/Systems/*/Soundness.lean` files: remove 6 and/or axiom soundness cases + 2 formula induction cases per file
- [ ] Restore all 15 `Modal/Metalogic/Systems/*/Completeness.lean` files: remove .and/.or truth lemma cases
- [ ] Restore `Cslib/Logics/Modal/Metalogic/Soundness.lean` (parameterized): remove .and/.or cases
- [ ] Restore `Cslib/Logics/Modal/Metalogic/Completeness.lean` (parameterized): remove .and/.or cases
- [ ] Restore `Cslib/Logics/Modal/Metalogic/MCS.lean`: remove mcs and/or helpers if present
- [ ] Run `lake build Cslib.Logics.Modal` to verify full Modal layer compiles

**Timing**: 2 hours

**Depends on**: 2

**Files to modify**:
- `Cslib/Logics/Modal/Denotation.lean` -- remove .and/.or cases
- `Cslib/Logics/Modal/LogicalEquivalence.lean` -- remove .and/.or cases
- `Cslib/Logics/Modal/Metalogic/DerivationTree.lean` -- remove 6 axiom constructors
- `Cslib/Logics/Modal/ProofSystem/Instances/*.lean` (15 files) -- remove 6 instances each
- `Cslib/Logics/Modal/Metalogic/Systems/*/Soundness.lean` (15 files) -- remove soundness cases
- `Cslib/Logics/Modal/Metalogic/Systems/*/Completeness.lean` (15 files) -- remove truth lemma cases
- `Cslib/Logics/Modal/Metalogic/Soundness.lean` -- remove parameterized .and/.or cases
- `Cslib/Logics/Modal/Metalogic/Completeness.lean` -- remove parameterized .and/.or cases
- `Cslib/Logics/Modal/Metalogic/MCS.lean` -- remove mcs and/or helpers

**Verification**:
- `lake build Cslib.Logics.Modal` succeeds with zero errors
- No `.and`/`.or` constructor references remain in `Cslib/Logics/Modal/`
- `lake exe checkInitImports` passes

---

### Phase 4: Temporal Layer Revert [NOT STARTED]

**Goal**: Remove all `.and`/`.or` match arms, axiom constructors, soundness cases, MCS helpers, truth lemma cases, and related infrastructure from the Temporal layer (~14 files). Restore helpers to use Foundations theorems directly.

**Tasks**:
- [ ] Read `Cslib/Logics/Temporal/Syntax/Subformulas.lean` to check for task-176 content beyond baseline; restore or edit accordingly
- [ ] Restore `Cslib/Logics/Temporal/ProofSystem/Axioms.lean` from baseline `1852de3a`: remove andI/andE1/andE2/orI1/orI2/orE axiom constructors
- [ ] Restore `Cslib/Logics/Temporal/ProofSystem/Instances.lean` from baseline `1852de3a`: remove 6 HasAxiomAnd*/HasAxiomOr* instance registrations
- [ ] Restore `Cslib/Logics/Temporal/Semantics/Satisfies.lean` from baseline `1852de3a`: remove .and/.or satisfaction clauses
- [ ] Restore `Cslib/Logics/Temporal/Metalogic/Soundness.lean` from baseline `1852de3a`: remove 6 axiom soundness cases + 2 formula induction cases
- [ ] Restore `Cslib/Logics/Temporal/Metalogic/MCS.lean`: remove `temporal_or_resolve_left` or re-prove using `implication_property` (since `or phi psi = imp (neg phi) psi`, `implication_property` handles this directly)
- [ ] Update `Cslib/Logics/Temporal/Metalogic/PropositionalHelpers.lean`: remove `pairing`, `lceImp`, `rceImp`, `demorganDisjNegBackward` (delegate to Foundations theorems via wrap/unwrap). Keep `wrap`/`unwrap`, `impTrans`, `identity`, `doubleNegation`, `dni`, `contraposition`
- [ ] Restore remaining Temporal/Metalogic files (DerivationTree, CompletenessHelpers, TemporalContent, Chronicle/*.lean): remove .and/.or cases from all pattern matches and inductions
- [ ] Run `lake build Cslib.Logics.Temporal` to verify full Temporal layer compiles

**Timing**: 2 hours

**Depends on**: 2

**Files to modify**:
- `Cslib/Logics/Temporal/Syntax/Subformulas.lean` -- remove .and/.or or targeted edit
- `Cslib/Logics/Temporal/ProofSystem/Axioms.lean` -- remove 6 axiom constructors
- `Cslib/Logics/Temporal/ProofSystem/Instances.lean` -- remove 6 instances
- `Cslib/Logics/Temporal/Semantics/Satisfies.lean` -- remove .and/.or satisfaction clauses
- `Cslib/Logics/Temporal/Metalogic/Soundness.lean` -- remove soundness cases
- `Cslib/Logics/Temporal/Metalogic/MCS.lean` -- re-prove or_resolve using implication_property
- `Cslib/Logics/Temporal/Metalogic/PropositionalHelpers.lean` -- simplify (~40% reduction)
- `Cslib/Logics/Temporal/Metalogic/DerivationTree.lean` -- remove .and/.or constructors
- `Cslib/Logics/Temporal/Metalogic/CompletenessHelpers.lean` -- remove .and/.or cases
- `Cslib/Logics/Temporal/Metalogic/Chronicle/*.lean` -- remove .and/.or cases from truth lemma and related files

**Verification**:
- `lake build Cslib.Logics.Temporal` succeeds with zero errors
- No `.and`/`.or` constructor references remain in `Cslib/Logics/Temporal/`
- PropositionalHelpers delegates all and/or reasoning to Foundations theorems

---

### Phase 5: Bimodal Layer Revert -- Syntax, ProofSystem, Semantics, Theorems [NOT STARTED]

**Goal**: Remove `.and`/`.or` from the non-metalogic portions of the Bimodal layer: syntax infrastructure, proof system, semantics, and theorems. This is the first half of the Bimodal revert, covering the foundational files that the metalogic depends on.

**Tasks**:
- [ ] Read `Cslib/Logics/Bimodal/Syntax/Subformulas.lean` and `SubformulaClosure.lean` to check for task-177 content beyond baseline; restore or edit accordingly
- [ ] Restore `Cslib/Logics/Bimodal/Syntax/Context.lean`: remove .and/.or cases
- [ ] Restore `Cslib/Logics/Bimodal/ProofSystem/Axioms.lean` from baseline `c38fe3d6^`: remove andI/andE1/andE2/orI1/orI2/orE axiom constructors
- [ ] Restore `Cslib/Logics/Bimodal/ProofSystem/Instances.lean` from baseline `c38fe3d6^`: remove 6 HasAxiomAnd*/HasAxiomOr* instances
- [ ] Restore `Cslib/Logics/Bimodal/ProofSystem/Derivation.lean`: remove .and/.or DerivationTree constructors
- [ ] Restore `Cslib/Logics/Bimodal/ProofSystem/Substitution.lean`: remove .and/.or substitution cases
- [ ] Restore `Cslib/Logics/Bimodal/Semantics/Truth.lean` from baseline `1852de3a`: remove .and/.or satisfaction clauses
- [ ] Update `Cslib/Logics/Bimodal/Theorems/Perpetuity/Helpers.lean`: remove `combineImpConj`, `lceImp`, `rceImp` (delegate to Foundations). Keep wrap/unwrap and modal/temporal-specific helpers
- [ ] Update `Cslib/Logics/Bimodal/Theorems/Propositional/Core.lean`: re-prove `ldi`, `rdi`, `lem` using Lukasiewicz encoding (`lem` becomes `identity (neg A)`, `ldi` becomes `raa`, `rdi` becomes `ImplyK`)
- [ ] Update `Cslib/Logics/Bimodal/Theorems/Propositional/Connectives.lean`: update `iffIntro`, `contraposeIff`, `iffNegIntro`, De Morgan proofs to use Foundations theorems via wrap/unwrap instead of primitive and/or axioms
- [ ] Restore `Cslib/Logics/Bimodal/Theorems/Combinators.lean`: remove and/or-specific combinators
- [ ] Restore `Cslib/Logics/Bimodal/Theorems/TemporalDerived.lean`: remove .and/.or cases
- [ ] Run partial `lake build` on Bimodal syntax/ProofSystem/Semantics/Theorems modules

**Timing**: 2 hours

**Depends on**: 3, 4

**Files to modify**:
- `Cslib/Logics/Bimodal/Syntax/Subformulas.lean` -- remove .and/.or cases
- `Cslib/Logics/Bimodal/Syntax/SubformulaClosure.lean` -- remove .and/.or cases
- `Cslib/Logics/Bimodal/Syntax/Context.lean` -- remove .and/.or cases
- `Cslib/Logics/Bimodal/ProofSystem/Axioms.lean` -- remove 6 axiom constructors
- `Cslib/Logics/Bimodal/ProofSystem/Instances.lean` -- remove 6 instances
- `Cslib/Logics/Bimodal/ProofSystem/Derivation.lean` -- remove .and/.or constructors
- `Cslib/Logics/Bimodal/ProofSystem/Substitution.lean` -- remove .and/.or cases
- `Cslib/Logics/Bimodal/Semantics/Truth.lean` -- remove .and/.or satisfaction
- `Cslib/Logics/Bimodal/Theorems/Perpetuity/Helpers.lean` -- simplify helpers
- `Cslib/Logics/Bimodal/Theorems/Propositional/Core.lean` -- re-prove ldi/rdi/lem
- `Cslib/Logics/Bimodal/Theorems/Propositional/Connectives.lean` -- update De Morgan, iff proofs
- `Cslib/Logics/Bimodal/Theorems/Combinators.lean` -- remove and/or combinators
- `Cslib/Logics/Bimodal/Theorems/TemporalDerived.lean` -- remove .and/.or cases

**Verification**:
- Bimodal syntax, proof system, semantics, and theorems modules compile
- All Perpetuity helpers delegate and/or reasoning to Foundations
- `ldi`/`rdi`/`lem` proofs are sorry-free using Lukasiewicz encoding

---

### Phase 6: Bimodal Layer Revert -- Metalogic [NOT STARTED]

**Goal**: Remove `.and`/`.or` from the Bimodal metalogic: soundness, completeness (algebraic, bundle, BX canonical), MCS, separation, conservative extension (F+ over F), and decidability. This is the largest single-phase change (~34 metalogic files).

**Tasks**:
- [ ] Restore `Cslib/Logics/Bimodal/Metalogic/Core/*.lean`: remove .and/.or cases from DeductionTheorem, MCS theory
- [ ] Restore `Cslib/Logics/Bimodal/Metalogic/Soundness/*.lean`: remove 6 axiom soundness cases + formula induction cases from all soundness files (DenseValidity, FrameSoundness, etc.)
- [ ] Update `Cslib/Logics/Bimodal/Metalogic/Core/MCSProperties.lean`: remove `mcs_or_resolve` or re-prove using `implication_property` (since `or phi psi = imp (neg phi) psi`)
- [ ] Restore `Cslib/Logics/Bimodal/Metalogic/Bundle/*.lean`: remove .and/.or cases from bundle construction and completeness
- [ ] Restore `Cslib/Logics/Bimodal/Metalogic/Algebraic/*.lean`: remove .and/.or cases from LindenbaumQuotient and algebraic completeness. Re-prove `provEquiv_or_congr` using Lukasiewicz encoding: `orI1` becomes `raa`, `orI2` becomes `ImplyK`, `orE` derives from `classical_merge`
- [ ] Restore `Cslib/Logics/Bimodal/Metalogic/BXCanonical/*.lean`: remove .and/.or cases from truth lemma and canonical model construction
- [ ] Restore `Cslib/Logics/Bimodal/Metalogic/Separation/*.lean`: remove .and/.or cases
- [ ] Restore `Cslib/Logics/Bimodal/Metalogic/ConservativeExtension/*.lean`: remove .and/.or cases from F+ over F proof
- [ ] Restore `Cslib/Logics/Bimodal/Metalogic/Decidability/*.lean` and `FMP/*.lean`: remove .and/.or cases from tableau decision procedure and finite model property
- [ ] Restore `Cslib/Logics/Bimodal/Metalogic/Completeness.lean`: remove .and/.or cases
- [ ] Run `lake build Cslib.Logics.Bimodal` to verify full Bimodal layer compiles

**Timing**: 2 hours

**Depends on**: 4, 5

**Files to modify**:
- `Cslib/Logics/Bimodal/Metalogic/Core/*.lean` (~5 files) -- remove .and/.or cases
- `Cslib/Logics/Bimodal/Metalogic/Soundness/*.lean` (~5 files) -- remove soundness cases
- `Cslib/Logics/Bimodal/Metalogic/Core/MCSProperties.lean` -- re-prove mcs_or_resolve
- `Cslib/Logics/Bimodal/Metalogic/Bundle/*.lean` (~3 files) -- remove .and/.or cases
- `Cslib/Logics/Bimodal/Metalogic/Algebraic/*.lean` (~4 files) -- re-prove provEquiv_or_congr
- `Cslib/Logics/Bimodal/Metalogic/BXCanonical/*.lean` (~5 files) -- remove .and/.or cases
- `Cslib/Logics/Bimodal/Metalogic/Separation/*.lean` (~3 files) -- remove .and/.or cases
- `Cslib/Logics/Bimodal/Metalogic/ConservativeExtension/*.lean` (~3 files) -- remove .and/.or cases
- `Cslib/Logics/Bimodal/Metalogic/Decidability/*.lean` + `FMP/*.lean` (~5 files) -- remove .and/.or cases
- `Cslib/Logics/Bimodal/Metalogic/Completeness.lean` -- remove .and/.or cases

**Verification**:
- `lake build Cslib.Logics.Bimodal` succeeds with zero errors
- No `.and`/`.or` constructor references remain in `Cslib/Logics/Bimodal/`
- No new sorries introduced (pre-existing task-36 sorries acceptable)
- `lake exe checkInitImports` passes

---

### Phase 7: Modal and Temporal Conservative Extension Proofs [NOT STARTED]

**Goal**: Prove that Modal K and Temporal BX are conservative extensions of CPL. Modal K is a 3-line composition of existing infrastructure. Temporal BX requires a new semantic bridge lemma (~30-50 lines).

**Tasks**:
- [ ] Create or update file for Modal K conservative extension theorem: compose `k_soundness_derivable` -> `toModal_valid_implies_tautology` -> `prop_completeness`. Handle universe compatibility (instantiate at `Type` if needed). Place in `Cslib/Logics/Modal/Metalogic/ConservativeExtension.lean` or `Cslib/Logics/Modal/FromPropositional.lean` (choose based on existing structure)
- [ ] Prove `temporal_satisfies_toTemporal_iff_evaluate`: structural induction on phi; cases are atom (direct), bot (direct), imp (inductive), and/or (unfold abbreviation, use `by_contra`/classical logic). ~15-20 lines
- [ ] Prove `toTemporal_valid_implies_tautology`: construct single-point temporal model using `Int` (has `LinearOrder`, `NoMaxOrder`, `NoMinOrder` in Mathlib) with constant valuation. ~10-15 lines
- [ ] Prove `temporal_conservative_extension`: compose `soundness_thderivable` -> `toTemporal_valid_implies_tautology` -> `prop_completeness`. ~5-10 lines
- [ ] Run `lake build` on the conservative extension files

**Timing**: 2 hours

**Depends on**: 3

**Files to modify**:
- `Cslib/Logics/Modal/Metalogic/ConservativeExtension.lean` (new) or `Cslib/Logics/Modal/FromPropositional.lean` -- Modal K conservative extension theorem
- `Cslib/Logics/Temporal/FromPropositional.lean` or new file -- Temporal semantic bridge + conservative extension

**Verification**:
- `modal_conservative_extension` type-checks and is sorry-free
- `temporal_conservative_extension` type-checks and is sorry-free
- Both theorems state: `Derivable UpperAxiom (phi.toUpper) -> Derivable PropositionalAxiom phi`
- `lake build` passes for Modal and Temporal modules

---

### Phase 8: Bimodal Conservative Extension and CI Verification [NOT STARTED]

**Goal**: Prove that the base Bimodal system F is a conservative extension of CPL. Then run the full CSLib CI pipeline to confirm zero regressions.

**Tasks**:
- [ ] Audit `Cslib/Logics/Bimodal/Metalogic/ConservativeExtension/` to confirm whether `lift_derivation_qfree` can be adapted for propositional-fragment projection (Approach A). If the existing lifting infrastructure covers formulas without box/untl/snce, use syntactic projection to Modal K
- [ ] If Approach A is viable: prove syntactic projection from Bimodal to Modal for propositional-fragment formulas (~50-100 lines), then compose with `modal_conservative_extension`
- [ ] If Approach A is not viable: fall back to Approach B (direct semantic bridge) -- construct single-point task model with trivial frame, prove `truthAt_toBimodal_iff_evaluate`, compose with `prop_completeness` (~80-120 lines)
- [ ] Prove `bimodal_conservative_extension`: final composition theorem (~10-20 lines)
- [ ] Run full CI pipeline: `lake build`, `lake test`, `lake exe checkInitImports`, `lake exe lint-style`
- [ ] Run `lake shake --add-public --keep-implied --keep-prefix` to verify dependency graph is clean after axiom removals
- [ ] Verify zero new sorries (grep for `sorry` excluding known task-36 locations)

**Timing**: 2 hours

**Depends on**: 5, 6, 7

**Files to modify**:
- `Cslib/Logics/Bimodal/Metalogic/ConservativeExtension/` -- new file(s) for CPL conservativity
- `Cslib/Logics/Bimodal/Embedding/PropositionalEmbedding.lean` -- possible additions for semantic bridge

**Verification**:
- `bimodal_conservative_extension` type-checks and is sorry-free
- `lake build` passes (full project)
- `lake test` passes
- `lake exe checkInitImports` passes
- `lake exe lint-style` passes
- `lake shake` reports no issues
- `grep -r "sorry" Cslib/Logics/ --include="*.lean"` shows only pre-existing task-36 sorries

---

## Testing & Validation

- [ ] `lake build` succeeds after each phase (8 checkpoints)
- [ ] `lake test` passes (full CslibTests suite)
- [ ] `lake exe checkInitImports` verifies no broken imports from removed symbols
- [ ] `lake exe lint-style` passes style checks
- [ ] `lake shake --add-public --keep-implied --keep-prefix` verifies clean dependencies
- [ ] No new `sorry` entries (grep confirmation)
- [ ] Formula constructor counts verified: Modal 4 (`atom, bot, imp, box`), Temporal 5 (`atom, bot, imp, untl, snce`), Bimodal 6 (`atom, bot, imp, box, untl, snce`)
- [ ] Lukasiewicz abbreviations verified: `and`, `or`, `neg`, `top` are `abbrev` definitions using `imp`/`bot` in all three layers
- [ ] Conservative extension theorems verified: `modal_conservative_extension`, `temporal_conservative_extension`, `bimodal_conservative_extension` all type-check sorry-free
- [ ] No `HasAxiomAndI`/`HasAxiomAndE1`/`HasAxiomAndE2`/`HasAxiomOrI1`/`HasAxiomOrI2`/`HasAxiomOrE` instances remain in Modal, Temporal, or Bimodal layers

## Artifacts & Outputs

- `specs/182_evaluate_classical_only_simplification/plans/01_implementation-plan.md` (this plan)
- `specs/182_evaluate_classical_only_simplification/summaries/01_execution-summary.md` (after completion)
- Modified Lean files across `Cslib/Logics/Modal/`, `Cslib/Logics/Temporal/`, `Cslib/Logics/Bimodal/`, and `Cslib/Foundations/Logic/` (~126 files)
- New conservative extension proof files (3 theorems across Modal, Temporal, Bimodal)

## Rollback/Contingency

The revert itself is to a known-good baseline state. If the implementation encounters irrecoverable issues:

1. **Per-phase rollback**: Each phase commits independently; `git revert` of the latest phase commit restores the previous phase state. Phases are designed so that partial completion leaves the codebase in a compilable state (the previous phase's `lake build` checkpoint serves as the recovery target).

2. **Full rollback**: The current HEAD (`8b2a470d`) is the pre-task-182 baseline. A `git reset` to this commit restores the full primitive and/or constructor state. No data is lost since task 182 is pure subtraction plus the conservative extension proofs.

3. **Conservative extension deferral**: If any conservative extension proof (especially Bimodal) proves more complex than estimated, the revert phases (1-6) can be completed and committed independently. The conservative extension proofs can be deferred to a follow-up task without blocking the revert.
