# Implementation Plan: Refactor Hilbert/ND Extensional Equivalence

- **Task**: 186 - Refactor the Hilbert/ND extensional equivalence
- **Status**: [COMPLETED]
- **Effort**: 2 hours
- **Dependencies**: 185
- **Research Inputs**: specs/186_hilbert_nd_equivalence_refactor/reports/01_nd-equivalence-research.md
- **Artifacts**: plans/01_implementation-plan.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: cslib
- **Lean Intent**: true

## Overview

Refactor `Equivalence.lean` to eliminate 96 lines of corollary boilerplate and 12 repetitions
of the 8-argument recursive call pattern in `ndToHilbert`. The approach introduces a
`class MinimalAxioms` typeclass bundling the 8 axiom witnesses (K, S, andI, andE1, andE2,
orI1, orI2, orE), with instances for `MinPropAxiom`, `IntPropAxiom`, and `PropositionalAxiom`.
Generic theorems (`ndToHilbert`, `hilbert_iff_nd_ctx`, `hilbert_iff_nd`) take
`[MinimalAxioms Axioms]` instead of 8 explicit parameters, reducing each corollary from
16 lines to 1-2 lines and each recursive call from 8 arguments to 0.

### Research Integration

Research (report 01) confirmed:
- EFQ problem for minimal logic is already resolved; `hilbert_iff_nd_min` compiles.
- Context-based equivalence is already implemented as `hilbert_iff_nd_ctx` and corollaries.
- Literature references (Prawitz, Troelstra & van Dalen) are already present and correct.
- No downstream breakage risk: equivalence theorems are only used within the 5 ND files.
- Primary refactoring target: corollary boilerplate (6 corollaries x 8-lambda bodies = 96 lines).
- Secondary target: `ndToHilbert` recursive call verbosity (12 x 8-argument pattern).

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

This plan advances the Propositional Logic quality improvements within the ROADMAP's
"Logics/Propositional" module area (P1: Defs, NaturalDeduction).

## Goals & Non-Goals

**Goals**:
- Eliminate corollary boilerplate by introducing a `MinimalAxioms` typeclass
- Reduce `ndToHilbert` recursive call verbosity via typeclass-implicit axiom witnesses
- Maintain all 8 existing equivalence theorems with identical statements
- Pass full CSLib CI (`lake build`, `lake test`, `lake exe checkInitImports`, `lake exe lint-style`)

**Non-Goals**:
- Bridging `AxiomTheory MinPropAxiom` to `MPL`/`IPL`/`CPL` (separate task)
- Modifying `FromHilbert.lean`, `HilbertDerivedRules.lean`, or `DerivedRules.lean`
- Adding new equivalence theorems beyond the existing 8
- Renaming existing theorem names (they follow Mathlib conventions)

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Typeclass resolution failure for `noncomputable def ndToHilbert` | H | L | Test with `lean_multi_attempt` before committing; fall back to structure with explicit `.mk` if needed |
| `noncomputable` propagation to typeclass instances | M | L | Instances are computable (just constructor wrapping); only `ndToHilbert` and dependents are noncomputable |
| Lean 4 universe issues with typeclass on `Axioms` predicate | M | L | Use `variable {Atom : Type*} [DecidableEq Atom]` matching existing scope |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2 | 1 |
| 3 | 3 | 2 |

Phases within the same wave can execute in parallel.

### Phase 1: Define MinimalAxioms typeclass and instances [COMPLETED]

**Goal**: Introduce the `MinimalAxioms` typeclass bundling 8 axiom witnesses, with 3 instances.

**Tasks**:
- [ ] Define `class MinimalAxioms (Axioms : PL.Proposition Atom -> Prop)` in `Equivalence.lean` after the `variable` declaration (line 98), with 8 fields: `h_K`, `h_S`, `h_andI`, `h_andE1`, `h_andE2`, `h_orI1`, `h_orI2`, `h_orE` matching the existing parameter types
- [ ] Add `instance : MinimalAxioms (@MinPropAxiom Atom)` using `.implyK`, `.implyS`, `.andI`, `.andE1`, `.andE2`, `.orI1`, `.orI2`, `.orE` constructors
- [ ] Add `instance : MinimalAxioms (@IntPropAxiom Atom)` with the same 8 constructors
- [ ] Add `instance : MinimalAxioms (@PropositionalAxiom Atom)` with the same 8 constructors
- [ ] Verify with `lake build Cslib.Logics.Propositional.NaturalDeduction.Equivalence`

**Timing**: 30 minutes

**Depends on**: none

**Files to modify**:
- `Cslib/Logics/Propositional/NaturalDeduction/Equivalence.lean` - add typeclass + 3 instances after line 98

**Verification**:
- Module builds without errors
- Existing theorems still compile (no changes yet to their signatures)

---

### Phase 2: Refactor ndToHilbert and generic theorems to use MinimalAxioms [COMPLETED]

**Goal**: Replace 8 explicit axiom parameters with `[MinimalAxioms Axioms]` in `ndToHilbert`, `nd_to_hilbert_deriv`, `hilbert_iff_nd`, and `hilbert_iff_nd_ctx`.

**Tasks**:
- [ ] Rewrite `ndToHilbert` signature: remove 8 explicit parameters, add `[MinimalAxioms Axioms]`; replace `h_K` with `MinimalAxioms.h_K` (or open the class) in all recursive calls and proof bodies
- [ ] Rewrite `nd_to_hilbert_deriv` signature: remove 8 explicit parameters, add `[MinimalAxioms Axioms]`; update the body to use the typeclass
- [ ] Rewrite `hilbert_iff_nd` signature: remove 8 explicit parameters, add `[MinimalAxioms Axioms]`; update the body
- [ ] Rewrite `hilbert_iff_nd_ctx` signature: remove 8 explicit parameters, add `[MinimalAxioms Axioms]`; update the body
- [ ] Verify recursive calls in `ndToHilbert` now use 0 explicit axiom arguments (just `ndToHilbert d`)
- [ ] Verify with `lake build Cslib.Logics.Propositional.NaturalDeduction.Equivalence`

**Timing**: 45 minutes

**Depends on**: 1

**Files to modify**:
- `Cslib/Logics/Propositional/NaturalDeduction/Equivalence.lean` - rewrite 4 function/theorem signatures and bodies (lines 170-312)

**Verification**:
- Module builds without errors
- Recursive calls in `ndToHilbert` reduced from `ndToHilbert h_K h_S h_andI h_andE1 h_andE2 h_orI1 h_orI2 h_orE d` to `ndToHilbert d`

---

### Phase 3: Collapse corollaries and run CI [COMPLETED]

**Goal**: Reduce 6 corollaries from 96 lines to ~12 lines total, update docstrings, run full CI.

**Tasks**:
- [ ] Replace each of the 6 corollary bodies (`hilbert_iff_nd_ctx_min`, `hilbert_iff_nd_ctx_int`, `hilbert_iff_nd_ctx_cl`, `hilbert_iff_nd_min`, `hilbert_iff_nd_int`, `hilbert_iff_nd_cl`) with a direct call to the generic theorem (e.g., `hilbert_iff_nd_ctx_min := hilbert_iff_nd_ctx` -- typeclass resolution supplies the witnesses)
- [ ] Update the module docstring to mention `MinimalAxioms` typeclass in the "Main Definitions" and "Design" sections
- [ ] Update the `ndToHilbert` docstring to reflect the typeclass-based signature
- [ ] Run full CI: `lake build`, `lake test`, `lake exe checkInitImports`, `lake exe lint-style`
- [ ] Run `lake shake --add-public --keep-implied --keep-prefix` to verify import hygiene

**Timing**: 45 minutes

**Depends on**: 2

**Files to modify**:
- `Cslib/Logics/Propositional/NaturalDeduction/Equivalence.lean` - collapse 6 corollary bodies (lines 317-413), update docstrings

**Verification**:
- All 8 equivalence theorems still exist with unchanged type signatures
- Full CI passes
- Net line reduction of approximately 70-80 lines
- `lake shake` reports no new unused imports

## Testing & Validation

- [ ] `lake build Cslib.Logics.Propositional.NaturalDeduction.Equivalence` passes
- [ ] `lake build` (full project) passes
- [ ] `lake test` passes
- [ ] `lake exe checkInitImports` passes
- [ ] `lake exe lint-style` passes
- [ ] `lake shake --add-public --keep-implied --keep-prefix` passes
- [ ] All 8 theorem names are preserved (`hilbert_iff_nd`, `hilbert_iff_nd_min`, `hilbert_iff_nd_int`, `hilbert_iff_nd_cl`, `hilbert_iff_nd_ctx`, `hilbert_iff_nd_ctx_min`, `hilbert_iff_nd_ctx_int`, `hilbert_iff_nd_ctx_cl`)

## Artifacts & Outputs

- `specs/186_hilbert_nd_equivalence_refactor/plans/01_implementation-plan.md` (this file)
- `specs/186_hilbert_nd_equivalence_refactor/summaries/01_execution-summary.md` (post-implementation)

## Rollback/Contingency

Revert the single modified file (`Equivalence.lean`) via `git checkout -- Cslib/Logics/Propositional/NaturalDeduction/Equivalence.lean`. No other files are modified. If the typeclass approach causes unexpected issues (e.g., elaboration timeouts), fall back to a plain `structure MinimalAxioms` with explicit `.mk` construction at each corollary site (still reduces boilerplate but less elegant).
