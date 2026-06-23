# Implementation Plan: Free Join Completion (Brouwerian Semilattice to Heyting Algebra)

- **Task**: 307 - Free Join Completion (Brouwerian Semilattice to Heyting Algebra)
- **Status**: [COMPLETED]
- **Effort**: 1 hour
- **Dependencies**: Tasks 302 (BrouwerianSemilattice), 303 (AlgEvaluate/FragmentPredicates)
- **Research Inputs**: specs/307_free_join_completion/reports/01_free-join-completion-research.md
- **Artifacts**: plans/01_free-join-completion-plan.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: cslib
- **Lean Intent**: true

## Overview

Construct a `HeytingAlgebra` from any `BrouwerianSemilattice` via the `LowerSet` (downset) completion and prove the embedding lemma for or-bot-free formulas. The `LowerSet B` type already has a `HeytingAlgebra` instance in Mathlib via `CompletelyDistribLattice`. The principal downset embedding `LowerSet.Iic` preserves `inf` and `top` (Mathlib), and the single new lemma `Iic_himp` proves it also preserves Heyting implication. The embedding lemma then follows by structural induction on or-bot-free formulas. All proofs have been verified in Lean during research. The implementation is a single file of approximately 70-90 lines.

### Research Integration

The research report (01_free-join-completion-research.md) provides:
- Complete verified Lean proof for `Iic_himp` (the key new result)
- Confirmation that `HeytingAlgebra (LowerSet B)` is available via Mathlib's `CompletelyDistribLattice.toBiheytingAlgebra`
- Existing Mathlib lemmas: `LowerSet.Iic_inf`, `LowerSet.Iic_top`, `LowerSet.Iic_injective`, `LowerSet.mem_Iic_iff`
- Verified proof sketches for the commutation lemma and embedding lemma
- Required imports list
- File structure recommendation

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

No ROADMAP.md items directly correspond to this task. This task is part of the propositional algebraic semantics infrastructure within `Cslib/Logics/Propositional/Semantics/Algebra/`.

## Goals & Non-Goals

**Goals**:
- Prove `Iic_himp`: `LowerSet.Iic (a ⇨ b) = LowerSet.Iic a ⇨ LowerSet.Iic b` for `BrouwerianSemilattice`
- Prove `Iic_eq_top_iff`: `LowerSet.Iic x = ⊤ ↔ x = ⊤` (helper)
- Prove the commutation lemma: `AlgEvaluate (LowerSet.Iic ∘ v) ⊥ φ = LowerSet.Iic (BrouwerianEvaluate v φ)` for or-bot-free formulas
- Prove the embedding lemma: `BrouwerianEvaluate v φ = ⊤ ↔ AlgEvaluate (LowerSet.Iic ∘ v) ⊥ φ = ⊤` for or-bot-free formulas
- Pass full CSLib CI pipeline (lake build, lake test, checkInitImports, lint-style)

**Non-Goals**:
- Custom `HeytingAlgebra` construction on `LowerSet` (Mathlib provides this)
- General embedding for formulas containing `or` or `bot` (only or-bot-free fragment)
- Upstream contributions to Mathlib (e.g., `Iic_himp` could be upstreamed later but is out of scope)

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Import conflicts between Mathlib.Order.CompleteBooleanAlgebra and existing CSLib imports | M | L | Standard Mathlib import; research verified no conflicts |
| Proof terms diverge from research sketches due to Lean version changes | M | L | All proofs verified in current Lean version during research |
| `CompletelyDistribLattice → HeytingAlgebra` produces non-definitional `⇨` on `LowerSet` | L | L | Proof uses `le_himp_iff` abstractly, not definitional equality |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |

Phases within the same wave can execute in parallel.

### Phase 1: Create FreeJoinCompletion.lean [COMPLETED]

**Goal**: Create the complete `FreeJoinCompletion.lean` file with all four theorems and pass CI.

**Tasks**:
- [ ] Create file `Cslib/Logics/Propositional/Semantics/Algebra/FreeJoinCompletion.lean` with module docstring and imports
- [ ] Implement `Iic_himp` theorem: `LowerSet.Iic (a ⇨ b) = LowerSet.Iic a ⇨ LowerSet.Iic b` using `le_antisymm` and `le_himp_iff`
- [ ] Implement `Iic_eq_top_iff` helper: `LowerSet.Iic x = ⊤ ↔ x = ⊤` using `Iic_injective` and `Iic_top`
- [ ] Implement commutation lemma `iic_BrouwerianEvaluate_eq_AlgEvaluate`: structural induction using `Iic_himp`, `Iic_inf`, and `IsOrBotFree` elimination
- [ ] Implement embedding lemma `brouwerian_embedding_lemma`: direct consequence of commutation lemma and `Iic_eq_top_iff`
- [ ] Register the new file in `Cslib/Init.lean` (or appropriate import root)
- [ ] Run `lake build` to verify compilation
- [ ] Run `lake test` to verify test suite
- [ ] Run `lake exe checkInitImports` to verify import registration
- [ ] Run `lake exe lint-style` to verify style compliance

**Timing**: 1 hour

**Depends on**: none

**Files to modify**:
- `Cslib/Logics/Propositional/Semantics/Algebra/FreeJoinCompletion.lean` - New file (70-90 lines)
- `Cslib/Logics/Propositional/Semantics/Algebra.lean` - Add import for FreeJoinCompletion (if module root exists)

**Verification**:
- `lake build` compiles without errors
- `lake test` passes
- `lake exe checkInitImports` passes
- `lake exe lint-style` passes
- No `sorry` in the file
- All four theorems present: `Iic_himp`, `Iic_eq_top_iff`, commutation lemma, embedding lemma

## Testing & Validation

- [ ] `lake build` compiles the new file without errors or warnings
- [ ] `lake test` passes the full CslibTests suite
- [ ] `lake exe checkInitImports` confirms proper import registration
- [ ] `lake exe lint-style` confirms style compliance
- [ ] No `sorry` remains in the file
- [ ] `lean_verify` confirms no axiom violations for key theorems

## Artifacts & Outputs

- `Cslib/Logics/Propositional/Semantics/Algebra/FreeJoinCompletion.lean` - New file with LowerSet completion and embedding lemma
- `specs/307_free_join_completion/plans/01_free-join-completion-plan.md` - This plan
- `specs/307_free_join_completion/summaries/01_free-join-completion-summary.md` - Implementation summary (created during implementation)

## Rollback/Contingency

Delete the new file and revert any import changes. Since this is a single new file with no modifications to existing files (beyond an import line), rollback is trivial: `git checkout -- Cslib/Logics/Propositional/Semantics/Algebra/FreeJoinCompletion.lean` and revert the import registration.
