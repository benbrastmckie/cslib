# Implementation Plan: Task #330

- **Task**: 330 - Fill the sorry in LJ cutAdmissibility
- **Status**: [NOT STARTED]
- **Effort**: 6 hours
- **Dependencies**: None
- **Research Inputs**: specs/330_lj_cut_admissibility_sorry/reports/01_lj-cut-admissibility.md
- **Artifacts**: plans/01_lj-cut-admissibility-plan.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: cslib
- **Lean Intent**: true

## Overview

Fill the single sorry in `cutAdmissibility` at `LJ/CutElimination.lean:103` by adapting the
proven LK cut elimination architecture (`LK/CutElimination.lean`) to single-conclusion
intuitionistic sequents. The proof uses well-founded induction on formula complexity (primary)
with structural recursion on proof trees (secondary), decomposed into standalone principal
helpers, a mutual recursion block, and a top-level WF wrapper. The LJ version is structurally
simpler than LK due to the absence of succedent sets, `weakR`, and right-side membership proofs.

### Research Integration

The research report (`reports/01_lj-cut-admissibility.md`) provides:
- Complete case analysis for `ljCutAdm_right` (13 cases) and `ljCutAdm_left` (12 cases)
- Proof architecture: standalone helpers + mutual block + WF top-level, mirroring LK
- Key structural differences from LK: no `hsuc`, no `weakR`, `orR1`/`orR2` split
- Termination arguments: structural on d2 for helpers/mutual, `sizeOf A` for top-level
- Heartbeat estimate: 200000 should suffice (LK uses 300000 with more cases)
- Line estimate: 350-470 lines total

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

No ROADMAP.md found.

## Goals & Non-Goals

**Goals**:
- Fill the sorry in `cutAdmissibility` with a complete proof
- Maintain existing `LJProof.cutElim` theorem (it already calls `cutAdmissibility`)
- Pass `lake build` with zero sorries in the LJ module
- Follow the LK cut elimination architecture closely for maintainability

**Non-Goals**:
- Optimizing heartbeat usage beyond what is needed to compile
- Refactoring `LJProof` or `CutFreeLJProof` type definitions
- Proving the subformula property (downstream consequence, separate task)
- Adding new test cases beyond build verification

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Heartbeat overflow in mutual block | H | M | Extract all principal cases to standalone helpers first; use `set_option maxHeartbeats` |
| Finset equation failure in pattern matching | M | M | Use generic-sequent parameters with subset hypotheses (as LK does) |
| Termination checker rejects mutual block | H | L | LK pattern is proven; use same `termination_by sizeOf` annotations |
| `orR1`/`orR2` split adds unexpected complexity | L | L | Two separate delegation calls from `ljCutAdm_left`, each mirrors the single LK `orR` case |
| Context window exhaustion during implementation | M | M | 5-phase decomposition with verification checkpoints enables resume |

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

### Phase 1: LJCutIH type alias and Finset helper lemmas [IN PROGRESS]

**Goal**: Define the induction hypothesis type alias and any shared Finset helper lemmas needed
by the cut admissibility proof, establishing the foundation for all subsequent phases.

**Tasks**:
- [ ] Define `LJCutIH` type alias for subformula induction hypothesis (analogous to `CutIH` in LK)
- [ ] Define `mem_of_ne_head` helper if not already importable from LK module (check import chain)
- [ ] Add any shared Finset subset helpers needed for LJ (e.g., `subset_insert2`)
- [ ] Verify definitions compile with `lake build Cslib.Logics.Propositional.SequentCalculus.LJ.CutElimination`

**Timing**: 0.5 hours

**Depends on**: none

**Files to modify**:
- `Cslib/Logics/Propositional/SequentCalculus/LJ/CutElimination.lean` - Add definitions between the `CutFreeLJProof.mono` definition (line 85) and the current `cutAdmissibility` (line 98)

**Verification**:
- Module compiles with no new errors
- `LJCutIH` type alias is well-formed
- Helper lemmas are usable in subsequent phases

---

### Phase 2: Standalone principal helpers [NOT STARTED]

**Goal**: Implement the three standalone self-recursive helpers that handle principal connective
cases. These are extracted from the mutual block to reduce heartbeat pressure, following the
same strategy used in LK.

**Tasks**:
- [ ] Implement `ljCutAdm_principal_andR`: handles principal and-conjunction case where `A = P /\ Q` and d1 ends with `andR`. Structural recursion on d2. Cases: ax (principal + non-principal), botL, andL (principal + non-principal), andR, orL, orR1, orR2, impL, impR, weakL, cut (absurd).
- [ ] Implement `ljCutAdm_principal_orR`: handles principal or-disjunction case. Takes a sub-proof `d1sub` for the chosen disjunct. Structural recursion on d2. Cases mirror andR helper but with `orL` as the principal case instead of `andL`.
- [ ] Implement `ljCutAdm_principal_impR`: handles principal implication case where `A = P -> Q` and d1 ends with `impR`. Structural recursion on d2. Cases mirror andR helper but with `impL` as the principal case.
- [ ] Each helper: add `termination_by sizeOf d2` annotation
- [ ] Verify all three helpers compile individually

**Timing**: 2.5 hours

**Depends on**: 1

**Files to modify**:
- `Cslib/Logics/Propositional/SequentCalculus/LJ/CutElimination.lean` - Add standalone helpers after the type alias and before the mutual block

**Verification**:
- All three helpers compile without errors
- Each helper handles all LJProof constructors (match exhaustiveness)
- `termination_by sizeOf d2` is accepted by the termination checker

**Implementation notes**:

The LJ helpers are simpler than their LK counterparts because:
1. No `hsuc` parameter (no succedent set to track)
2. No `weakR` case
3. No right-side membership proofs in constructor calls
4. Only `hant : Gamma subset insert A Gamma0` subset hypothesis needed

Key signature pattern (using `ljCutAdm_principal_andR` as example):
```lean
noncomputable def ljCutAdm_principal_andR
    (P Q : Proposition Atom) (Gamma0 : Ctx Atom)
    (d1p : CutFreeLJProof (Gamma0 |- P))
    (d1q : CutFreeLJProof (Gamma0 |- Q))
    (ih : LJCutIH (P /\ Q))
    {Gamma : Ctx Atom} {C : Proposition Atom}
    (d2 : LJProof (Gamma |- C)) (hcf2 : LJCutFree d2)
    (hant : Gamma subset insert (P /\ Q) Gamma0) :
    CutFreeLJProof (Gamma0 |- C)
```

---

### Phase 3: Mutual recursion block (ljCutAdm_right + ljCutAdm_left) [NOT STARTED]

**Goal**: Implement the mutual recursion block containing `ljCutAdm_right` (structural on d2)
and `ljCutAdm_left` (structural on d1). This is the core of the cut elimination proof.

**Tasks**:
- [ ] Add `set_option maxHeartbeats 200000` before the mutual block (increase if needed)
- [ ] Implement `ljCutAdm_right`: structural recursion on d2, handles all 11 LJProof constructors. For each left-rule case where the principal formula equals A, build a reconstructed d2_new and delegate to `ljCutAdm_left`. For non-principal cases, recurse on sub-proofs with adjusted context.
- [ ] Implement `ljCutAdm_left`: structural recursion on d1, handles all 11 constructors. For right-rule cases (andR, orR1, orR2, impR) where d1 introduces A, delegate to the corresponding standalone principal helper. For left-rule cases, recurse on sub-proofs.
- [ ] Verify mutual block compiles with the given heartbeat limit

**Timing**: 2 hours

**Depends on**: 2

**Files to modify**:
- `Cslib/Logics/Propositional/SequentCalculus/LJ/CutElimination.lean` - Add mutual block after standalone helpers, before the current `cutAdmissibility` definition

**Verification**:
- Mutual block compiles within heartbeat limit
- All match arms are covered (exhaustive pattern matching)
- Mutual calls are well-founded (structural decrease on primary argument)

**Implementation notes**:

Key differences from LK mutual block:
- `ljCutAdm_right` takes only `hant` (no `hsuc`)
- No `weakR` case in either function
- `ljCutAdm_left` delegates to `ljCutAdm_principal_orR` for both `orR1` and `orR2` cases
- `ljCutAdm_right` has `orR1` and `orR2` as separate (non-principal) right-rule cases
- `impL` in `ljCutAdm_right`: left sub-proof concludes `A` (single formula), not `insert A Delta`

---

### Phase 4: Top-level cutAdmissibility and integration [NOT STARTED]

**Goal**: Replace the sorry in `cutAdmissibility` with a call to `ljCutAdm_left`, wiring the
WF recursion on `sizeOf A` to the `LJCutIH` closure. Verify that `LJProof.cutElim` compiles.

**Tasks**:
- [ ] Replace the `sorry` body of `cutAdmissibility` (line 102-103) with the actual proof body calling `ljCutAdm_left`
- [ ] Add `termination_by sizeOf A` annotation
- [ ] Update the docstring to remove the "not yet proved" status notice
- [ ] Verify `cutAdmissibility` compiles and `LJProof.cutElim` (line 114) still compiles

**Timing**: 0.5 hours

**Depends on**: 3

**Files to modify**:
- `Cslib/Logics/Propositional/SequentCalculus/LJ/CutElimination.lean` - Replace sorry at line 102-103, update docstring at lines 89-97

**Verification**:
- `cutAdmissibility` compiles with no sorry
- `LJProof.cutElim` compiles with no sorry
- `lake build Cslib.Logics.Propositional.SequentCalculus.LJ.CutElimination` succeeds
- `lean_verify` on `Cslib.Logic.PL.cutAdmissibility` shows no sorry axioms

---

### Phase 5: Full build verification and CI checks [NOT STARTED]

**Goal**: Run the full CI verification pipeline to ensure the implementation does not break
any other modules and passes all quality gates.

**Tasks**:
- [ ] Run `lake build` (full project build)
- [ ] Run `lake exe checkInitImports`
- [ ] Run `lake exe lint-style`
- [ ] Run `lake test`
- [ ] Verify zero sorries in the entire LJ module: `grep -rn "sorry" Cslib/Logics/Propositional/SequentCalculus/LJ/`

**Timing**: 0.5 hours

**Depends on**: 4

**Files to modify**:
- None (verification only)

**Verification**:
- All CI checks pass
- Zero sorries in LJ module
- No regressions in other modules

## Testing & Validation

- [ ] `lake build Cslib.Logics.Propositional.SequentCalculus.LJ.CutElimination` compiles
- [ ] `lake build` full project succeeds
- [ ] `lean_verify Cslib.Logic.PL.cutAdmissibility` shows no sorry axioms
- [ ] `lean_verify Cslib.Logic.PL.LJProof.cutElim` shows no sorry axioms
- [ ] `grep -rn "sorry" Cslib/Logics/Propositional/SequentCalculus/LJ/` returns empty
- [ ] `lake exe checkInitImports` passes
- [ ] `lake exe lint-style` passes
- [ ] `lake test` passes

## Artifacts & Outputs

- `Cslib/Logics/Propositional/SequentCalculus/LJ/CutElimination.lean` - Completed cut elimination proof
- `specs/330_lj_cut_admissibility_sorry/plans/01_lj-cut-admissibility-plan.md` - This plan
- `specs/330_lj_cut_admissibility_sorry/summaries/01_lj-cut-admissibility-summary.md` - Implementation summary (created during Phase 5)

## Rollback/Contingency

The original file with the sorry is tracked in git. If the implementation fails or introduces
regressions:
1. `git checkout -- Cslib/Logics/Propositional/SequentCalculus/LJ/CutElimination.lean`
2. This restores the sorry placeholder without affecting any other modules
3. If heartbeats are the blocker, increase `maxHeartbeats` or extract additional helpers
4. If termination checking fails, try explicit `decreasing_by` tactics or restructure recursion
