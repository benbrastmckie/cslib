# Implementation Plan: Task #322

- **Task**: 322 - MPL Conservative Extension Chain
- **Status**: [COMPLETED]
- **Effort**: 1.5 hours
- **Dependencies**: None (all building blocks exist and file compiles)
- **Research Inputs**: specs/322_mpl_conservative_extension_chain/reports/01_mpl-chain-research.md
- **Artifacts**: plans/01_mpl-chain-plan.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: cslib
- **Lean Intent**: true

## Overview

Complete the `MplConservativeChain.lean` file by adding three categories of missing declarations: (1) the standalone validity-level theorem `GHAValid_implies_BrouwerianValid_direct` extracting the algebraic core from the existing `hilbertMplConservativeOverConjImp_direct`, (2) subsumption lemmas `derivableConjImpOfDerivableMin` and `derivableImpOfDerivableMin` providing the axiom-lifting direction, and (3) missing BibKey entries in `references.bib`. The file currently contains 4 sorry-free, building theorems; this plan adds approximately 40-60 lines and 2 BibTeX entries to complete the algebraic picture.

### Research Integration

Research report (01_mpl-chain-research.md) identified:

1. **Build status**: The research report claimed the file does NOT build due to a typeclass diamond. However, empirical verification shows the file DOES build successfully with the current `attribute [-instance] BrouwerianSemilattice.toHilbertAlgebra` / `attribute [instance] BrouwerianSemilattice.toHilbertAlgebra` pair (lines 117 and 142). The global instance suppression approach works -- the research was testing an earlier version that used the scoped `in` syntax.

2. **Missing declarations confirmed**: `GHAValid_implies_BrouwerianValid_direct` (referenced in docstring but not yet a standalone theorem), `derivableConjImpOfDerivableMin`, `derivableImpOfDerivableMin`.

3. **All building blocks verified**: `MPL.hilbert_alg_complete`, `brouwerianEmbeddingLemma`, `conjImp_brouwerian_complete`, `liftDerivationTree`, `hilbertConjImpConservativeOverImp`, `IsImpTopOnly_implies_IsOrBotFree`, `ConjImpAxiom.toMinPropAxiom`, `ImpAxiom.toConjImpAxiom`.

4. **BibKey gaps**: `Nemitz1965` and `Kohler1981` cited in docstring but missing from `references.bib`.

### Prior Plan Reference

The prior plan (v1) correctly identified the 3 missing declarations and had a reasonable 2-phase structure. Lessons learned:
- The prior plan assumed no build issue existed, which is correct for the current file version.
- Effort estimate of 1.5 hours is well-calibrated.
- The `GHAValid_implies_BrouwerianValid_direct` theorem must be placed INSIDE the `attribute [-instance]` region (between lines 117 and 142) since it uses `LowerSet.Iic` which is subject to the same diamond.
- The subsumption lemmas do NOT need the instance suppression since they use `liftDerivationTree` (pure tree manipulation, no typeclass resolution on `LowerSet`).

### Roadmap Alignment

No ROADMAP.md found.

## Goals & Non-Goals

**Goals**:
- Add `GHAValid_implies_BrouwerianValid_direct` as a standalone validity-level theorem
- Add `derivableConjImpOfDerivableMin` and `derivableImpOfDerivableMin` subsumption lemmas
- Refactor `hilbertMplConservativeOverConjImp_direct` to use `GHAValid_implies_BrouwerianValid_direct`
- Add missing BibKey entries (`Nemitz1965`, `Kohler1981`) to `references.bib`
- Update module docstring to list all 7 declarations
- Maintain sorry-free compilation and IPL-independence constraint

**Non-Goals**:
- Modifying `ConservativeChain.lean` or other existing files beyond `references.bib`
- Adding ND corollaries (those belong in `ConservativeChain.lean`)
- Proving new algebraic infrastructure lemmas
- Refactoring the `attribute [-instance]` approach (it works as-is)

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| `GHAValid_implies_BrouwerianValid_direct` placed outside `attribute [-instance]` region triggers diamond | H | M | Place between lines 117-142, inside the suppression region; verify with `lake build` immediately after |
| Refactoring `hilbertMplConservativeOverConjImp_direct` to call new theorem changes proof term shape | L | L | The new theorem has the same proof core; composition is direct |
| `liftDerivationTree` subsumption chain needs different coercion path than expected | L | L | Coercion chains `.toMinPropAxiom` and `.toConjImpAxiom.toMinPropAxiom` already used inline in biconditionals |
| BibKey format inconsistent with existing entries | L | L | Follow existing `references.bib` formatting conventions |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2 | 1 |
| 3 | 3 | 2 |

Phases within the same wave can execute in parallel.

### Phase 1: Add Core Declarations to MplConservativeChain.lean [COMPLETED]

**Goal**: Add the 3 missing theorems, refactor to use the new validity lemma, and update the module docstring.

**Tasks**:
- [ ] Add `GHAValid_implies_BrouwerianValid_direct` theorem INSIDE the `attribute [-instance]` region (after line 117, before `hilbertMplConservativeOverConjImp_direct`). Signature: `{phi : PL.Proposition Atom} -> (hOBF : phi.IsOrBotFree = true) -> GHAValid phi -> BrouwerianValid phi`. Proof extracts the algebraic core from `hilbertMplConservativeOverConjImp_direct`: `intro B _ v; have hGHA := h (LowerSet B) _ (LowerSet.Iic . v) bot; exact (brouwerianEmbeddingLemma v phi hOBF).mpr hGHA`.
- [ ] Refactor `hilbertMplConservativeOverConjImp_direct` to use `GHAValid_implies_BrouwerianValid_direct` internally: `conjImp_brouwerian_complete hOBF (GHAValid_implies_BrouwerianValid_direct hOBF (MPL.hilbert_alg_complete.mp h))`.
- [ ] Add `derivableConjImpOfDerivableMin` after the biconditional section (AFTER `attribute [instance]` restore, outside the suppression region). Signature: `Derivable (@ConjImpAxiom Atom) phi -> Derivable (@MinPropAxiom Atom) phi`. Proof: `fun ⟨d⟩ => ⟨liftDerivationTree (fun _ h => h.toMinPropAxiom) d⟩`.
- [ ] Add `derivableImpOfDerivableMin` similarly. Signature: `Derivable (@ImpAxiom Atom) phi -> Derivable (@MinPropAxiom Atom) phi`. Proof: `fun ⟨d⟩ => ⟨liftDerivationTree (fun _ h => h.toConjImpAxiom.toMinPropAxiom) d⟩`.
- [ ] Update module docstring `## Main Results` to list all 7 declarations including the new ones.
- [ ] Verify: `lake build Cslib.Logics.Propositional.Semantics.Algebra.MplConservativeChain`

**Timing**: 0.75 hours

**Depends on**: none

**Files to modify**:
- `Cslib/Logics/Propositional/Semantics/Algebra/MplConservativeChain.lean` - add ~40-60 lines of new declarations, refactor existing proof, update docstring

**Verification**:
- `lake build Cslib.Logics.Propositional.Semantics.Algebra.MplConservativeChain` succeeds
- `grep -c "sorry" Cslib/Logics/Propositional/Semantics/Algebra/MplConservativeChain.lean` returns 0
- All 7 theorems present in file
- No references to `IntPropAxiom`, `IPL`, `HAValid`, `hilbertIplConservative*`, or `derivableMinOfDerivableInt` in proof terms

---

### Phase 2: Add Missing BibKey Entries [COMPLETED]

**Goal**: Add `Nemitz1965` and `Kohler1981` to `references.bib` so docstring citations resolve.

**Tasks**:
- [ ] Add `@article{Nemitz1965, author = {Nemitz, William C.}, title = {Implicative semi-lattices}, journal = {Trans. Amer. Math. Soc.}, volume = {117}, year = {1965}, pages = {128--142}}` to `references.bib`
- [ ] Add `@article{Kohler1981, author = {K{\"o}hler, Peter}, title = {Brouwerian semilattices}, journal = {Trans. Amer. Math. Soc.}, volume = {268}, number = {1}, year = {1981}, pages = {103--126}}` to `references.bib`
- [ ] Verify entries are well-formed (no BibTeX parse errors)

**Timing**: 0.25 hours

**Depends on**: 1

**Files to modify**:
- `references.bib` - add 2 BibTeX entries

**Verification**:
- `grep -c 'Nemitz1965\|Kohler1981' references.bib` returns 2

---

### Phase 3: CI Verification [COMPLETED]

**Goal**: Verify full project builds and passes CI checks.

**Tasks**:
- [ ] Run `lake build` (full project) to check no downstream breakage
- [ ] Run `lake exe checkInitImports` to verify import structure
- [ ] Run `lake exe lint-style` to check style compliance
- [ ] Verify `lean_verify` on key new declarations for axiom-freeness

**Timing**: 0.5 hours

**Depends on**: 2

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
- [ ] BibKey entries present: `grep -c 'Nemitz1965\|Kohler1981' references.bib` returns 2

## Artifacts & Outputs

- `Cslib/Logics/Propositional/Semantics/Algebra/MplConservativeChain.lean` - completed file with 7 theorems
- `references.bib` - updated with 2 new BibTeX entries
- `specs/322_mpl_conservative_extension_chain/plans/01_mpl-chain-plan.md` - this plan

## Rollback/Contingency

The file already exists and compiles with 4 theorems. If new additions cause issues:
1. Revert `MplConservativeChain.lean`: `git checkout -- Cslib/Logics/Propositional/Semantics/Algebra/MplConservativeChain.lean`
2. Revert `references.bib`: `git checkout -- references.bib`

Since only 2 files are modified and both have clean git baselines, rollback is confined and safe.

## Postmortem Constraints (Hard Mode)

- **H8 Phase Sizing**: All 3 phases are well within the 100-500 lines output bound. Phase 1 produces ~40-60 lines of Lean code. Phases 2-3 are smaller.
- **Prior plan deviation log**: Research report incorrectly stated the file fails to build. The global `attribute [-instance]` approach (lines 117/142) resolves the diamond. Plan revised to account for this -- no diamond-fix phase needed.
- **Preserved assets**: All 4 existing theorems are preserved. The refactoring in Phase 1 changes the internal proof of `hilbertMplConservativeOverConjImp_direct` but not its signature or behavior.
