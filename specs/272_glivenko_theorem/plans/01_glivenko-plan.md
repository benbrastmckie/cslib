# Implementation Plan: Glivenko's Theorem

- **Task**: 272 - glivenko_theorem
- **Status**: [NOT STARTED]
- **Effort**: 1 hour
- **Dependencies**: None (all required infrastructure exists in CSLib and Mathlib)
- **Research Inputs**: specs/272_glivenko_theorem/reports/01_glivenko-proof.md
- **Artifacts**: plans/01_glivenko-plan.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: cslib
- **Lean Intent**: true

## Overview

Prove Glivenko's theorem: if CPL proves A then IPL proves not-not-A. The proof uses the
algebraic approach via Heyting.Regular elements. Regular elements of any HeytingAlgebra form a
BooleanAlgebra (provided by Mathlib), and an embedding lemma relates evaluation in the Regular
subalgebra to double-complement evaluation in the original algebra. The research report
provides fully verified Lean 4 code that compiled against the current codebase.

### Research Integration

Key findings from the research report integrated into this plan:

1. **Proof strategy**: Lift valuation v : Atom -> H to v' : Atom -> Regular H via the
   double-complement map. BA-validity of A in Regular H implies HA-validity of not-not-A in H.
2. **Theory design**: CPL alone lacks EFQ, so the theorem uses `IPL union CPL` as the classical
   theory, enabling both `alg_complete_classical` (requires IsIntuitionistic + IsClassical) and
   `IPL.alg_complete` for the conclusion.
3. **Verified code**: All 6 declarations have been verified via `lean_run_code`. The proof uses
   only structural tactics (simp, rw, congr, change, exact, rcases/obtain).
4. **No new dependencies**: `Mathlib.Order.Heyting.Regular` is already in the dependency graph
   via `Lindenbaum.lean`.

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

No ROADMAP.md found.

## Goals & Non-Goals

**Goals**:
- Prove `glivenko_algebraic`: BA-valid implies HA-valid under double negation
- Prove `glivenko`: CPL-derivable implies IPL-derivable under double negation
- Provide the supporting embedding lemma (`eval_regular_val`) and theory instances
- Place the file at `Cslib/Logics/Propositional/Semantics/Algebra/Glivenko.lean`
- Pass all CSLib CI checks

**Non-Goals**:
- Double negation translation for arbitrary theories (only Glivenko's specific result)
- Proof-theoretic variants (sequent calculus, natural deduction direct proof)
- Generalization beyond propositional logic

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Unicode operator transcription errors | L | L | Research provides ASCII; convert methodically to Unicode, verify with lean_goal |
| Namespace resolution issues | L | L | Follow Conservative.lean pattern exactly (same open declarations, same namespace) |
| Import registration forgotten | M | L | Checklist includes `lake exe mk_all --module` and `lake exe checkInitImports` |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |

Phases within the same wave can execute in parallel.

### Phase 1: Implement Glivenko.lean and Register Import [NOT STARTED]

**Goal**: Create the Glivenko.lean file with all 6 declarations, register the barrel import,
and verify CI compliance.

**Tasks**:
- [ ] Create `Cslib/Logics/Propositional/Semantics/Algebra/Glivenko.lean` with:
  - Copyright header and module docstring (reference Glivenko 1929, Rasiowa 1974)
  - `import Cslib.Init`
  - `public import Cslib.Logics.Propositional.Semantics.Algebra.Completeness`
  - `public import Cslib.Logics.Propositional.NaturalDeduction.Basic`
  - `public import Mathlib.Order.Heyting.Regular`
  - `evalR` private abbreviation for Regular-lifted evaluation
  - `eval_regular_val` private theorem (embedding lemma, induction on formulas)
  - `glivenko_algebraic` theorem (BA-valid implies HA-valid under double negation)
  - `IsIntuitionistic (IPL union CPL)` instance
  - `IsClassical (IPL union CPL)` instance
  - `glivenko` theorem (proof-theoretic Glivenko via algebraic completeness)
- [ ] Run `lake exe mk_all --module` to register the new file in `Cslib.lean`
- [ ] Verify with `lake build Cslib.Logics.Propositional.Semantics.Algebra.Glivenko`
- [ ] Run `lake exe checkInitImports` to verify Cslib.Init import
- [ ] Run `lake exe lint-style` for style compliance
- [ ] Run `lake test` to confirm no regressions

**Timing**: 1 hour

**Depends on**: none

**Files to modify**:
- `Cslib/Logics/Propositional/Semantics/Algebra/Glivenko.lean` - New file (~100 lines)
- `Cslib.lean` - Add barrel import (via `lake exe mk_all --module`)

**Verification**:
- `lake build` succeeds with no errors
- `lake exe checkInitImports` passes
- `lake exe lint-style` passes
- `lake test` passes
- `lean_verify` confirms no sorry or axiom issues in `glivenko` and `glivenko_algebraic`

## Testing & Validation

- [ ] `lake build Cslib.Logics.Propositional.Semantics.Algebra.Glivenko` compiles without errors
- [ ] `lake exe checkInitImports` reports no missing imports
- [ ] `lake exe lint-style` reports no style violations
- [ ] `lake test` passes (no regressions in CslibTests)
- [ ] `lean_verify` on `Cslib.Logic.PL.glivenko` confirms sorry-free and axiom-clean

## Artifacts & Outputs

- `Cslib/Logics/Propositional/Semantics/Algebra/Glivenko.lean` - New proof file
- `Cslib.lean` - Updated barrel import
- `specs/272_glivenko_theorem/plans/01_glivenko-plan.md` - This plan
- `specs/272_glivenko_theorem/summaries/01_glivenko-summary.md` - Execution summary (after implementation)

## Rollback/Contingency

- Delete `Cslib/Logics/Propositional/Semantics/Algebra/Glivenko.lean`
- Revert `Cslib.lean` to previous state via `git checkout Cslib.lean`
- No other files are modified, so rollback is clean
