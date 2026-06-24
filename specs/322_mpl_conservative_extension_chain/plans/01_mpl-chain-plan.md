# Implementation Plan: Task #322

- **Task**: 322 - MPL Conservative Extension Chain
- **Status**: [NOT STARTED]
- **Effort**: 1.5 hours
- **Dependencies**: 311 (dual-ordering research), 312
- **Research Inputs**: specs/322_mpl_conservative_extension_chain/reports/01_mpl-chain-research.md
- **Artifacts**: plans/01_mpl-chain-plan.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: cslib
- **Lean Intent**: true

## Overview

Complete the `MplConservativeChain.lean` file by adding three categories of missing declarations: (1) the standalone validity-level theorem `GHAValid_implies_BrouwerianValid_direct` extracting the algebraic core of the existing `hilbertMplConservativeOverConjImp_direct`, (2) subsumption lemmas `derivableConjImpOfDerivableMin` and `derivableImpOfDerivableMin` providing the reverse direction of the conservativity results, and (3) a unified summary section documenting how the MPL chain relates to the IPL chain. The file already contains 4 sorry-free theorems; this plan adds approximately 40-60 lines to complete the algebraic picture.

### Research Integration

Research confirmed that all building blocks exist: `MPL.hilbert_alg_complete`, `brouwerianEmbeddingLemma`, `conjImp_brouwerian_complete`, `liftDerivationTree`, `hilbertConjImpConservativeOverImp`, and `IsImpTopOnly_implies_IsOrBotFree`. Each new proof is 1-5 lines composing existing theorems. The direct route avoids IPL by instantiating `GHAValid` at `LowerSet B` (a GHA) with `LowerSet.Iic ∘ v`, then applying `brouwerianEmbeddingLemma`.

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

No ROADMAP.md items directly map to this task.

## Goals & Non-Goals

**Goals**:
- Add `GHAValid_implies_BrouwerianValid_direct` as a standalone validity-level theorem
- Add `derivableConjImpOfDerivableMin` and `derivableImpOfDerivableMin` subsumption lemmas
- Ensure all proofs are direct (no IPL references per independence constraint)
- Maintain sorry-free compilation
- Update module docstring to reflect all declarations

**Non-Goals**:
- Modifying `ConservativeChain.lean` or other existing files
- Adding ND corollaries (those belong in `ConservativeChain.lean`)
- Proving new algebraic infrastructure lemmas

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| `GHAValid` instantiation at `LowerSet B` has typeclass issues | M | L | Pattern already works in `hilbertMplConservativeOverConjImp_direct`; extract rather than re-derive |
| `liftDerivationTree` subsumption chain `ImpAxiom → ConjImpAxiom → MinPropAxiom` missing coercions | L | L | `.toConjImpAxiom.toMinPropAxiom` chain already used in `mplAxiom_iff_conjImpAxiom` backward direction |
| H8 violation: phase too large for one agent run | L | L | Task is ~40-60 lines total; single phase is well within bounds |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2 | 1 |

Phases within the same wave can execute in parallel.

### Phase 1: Core Declarations [NOT STARTED]

**Goal**: Add the three missing theorem categories to `MplConservativeChain.lean`.

**Tasks**:
- [ ] Add `GHAValid_implies_BrouwerianValid_direct` theorem after the existing `/-! ## Direct MPL→ConjImp Conservativity -/` section header, before `hilbertMplConservativeOverConjImp_direct`. This extracts the algebraic core: for or-bot-free `phi`, `GHAValid phi` implies `BrouwerianValid phi`. Proof: `intro B _ v; have hGHA := h (LowerSet B) _ (LowerSet.Iic . v) bot; exact (brouwerianEmbeddingLemma v phi hOBF).mpr hGHA`.
- [ ] Add `derivableConjImpOfDerivableMin` subsumption lemma in a new `/-! ## Subsumption (Reverse Direction) -/` section after the biconditionals. Proof: `obtain <d> := h; exact <liftDerivationTree (fun _ h_psi => h_psi.toMinPropAxiom) d>`.
- [ ] Add `derivableImpOfDerivableMin` subsumption lemma composing `derivableConjImpOfDerivableMin` is not needed -- use direct `liftDerivationTree` with `fun _ h_psi => h_psi.toConjImpAxiom.toMinPropAxiom`. Proof: `obtain <d> := h; exact <liftDerivationTree (fun _ h_psi => h_psi.toConjImpAxiom.toMinPropAxiom) d>`.
- [ ] Refactor `hilbertMplConservativeOverConjImp_direct` to use `GHAValid_implies_BrouwerianValid_direct` internally (optional, reduces duplication).
- [ ] Update module docstring `## Main Results` to list all 7 declarations.
- [ ] Verify file compiles: `lake build Cslib.Logics.Propositional.Semantics.Algebra.MplConservativeChain`

**Timing**: 1 hour

**Depends on**: none

**Files to modify**:
- `Cslib/Logics/Propositional/Semantics/Algebra/MplConservativeChain.lean` - add ~40-60 lines of new declarations and update docstring

**Verification**:
- `lake build Cslib.Logics.Propositional.Semantics.Algebra.MplConservativeChain` succeeds with no errors
- `grep -c "sorry" MplConservativeChain.lean` returns 0
- All 7 theorems present: `GHAValid_implies_BrouwerianValid_direct`, `hilbertMplConservativeOverConjImp_direct`, `mplAxiom_iff_conjImpAxiom`, `hilbertMplConservativeOverImp_direct`, `mplAxiom_iff_impAxiom`, `derivableConjImpOfDerivableMin`, `derivableImpOfDerivableMin`
- No references to `IntPropAxiom`, `IPL`, `HAValid`, `hilbertIplConservative*`, or `derivableMinOfDerivableInt` in proofs (independence constraint)

---

### Phase 2: CI Verification [NOT STARTED]

**Goal**: Verify full project builds and passes CI checks.

**Tasks**:
- [ ] Run `lake build` (full project) to check no downstream breakage
- [ ] Run `lake exe checkInitImports` to verify import structure
- [ ] Run `lake exe lint-style` to check style compliance
- [ ] Verify `lean_verify` on key declarations for axiom-freeness

**Timing**: 0.5 hours

**Depends on**: 1

**Files to modify**:
- None (verification only); potential minor style fixes if lint-style flags issues

**Verification**:
- All CI commands pass without errors
- No new warnings introduced

## Testing & Validation

- [ ] `lake build Cslib.Logics.Propositional.Semantics.Algebra.MplConservativeChain` compiles
- [ ] `lake build` (full project) succeeds
- [ ] `lake exe checkInitImports` passes
- [ ] `lake exe lint-style` passes
- [ ] Zero `sorry` in `MplConservativeChain.lean`
- [ ] Independence constraint: `grep -E 'IntPropAxiom|IPL|HAValid|hilbertIplConservative|derivableMinOfDerivableInt' MplConservativeChain.lean` returns only docstring references, not proof terms

## Artifacts & Outputs

- `Cslib/Logics/Propositional/Semantics/Algebra/MplConservativeChain.lean` - completed file with 7 theorems
- `specs/322_mpl_conservative_extension_chain/plans/01_mpl-chain-plan.md` - this plan

## Rollback/Contingency

The file already exists and compiles. If new additions cause issues, revert the edits to restore the 4-theorem version. Since no other files are modified, rollback is confined to a single file `git checkout -- Cslib/Logics/Propositional/Semantics/Algebra/MplConservativeChain.lean`.
