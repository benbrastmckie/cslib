# Implementation Plan: Task #256

- **Task**: 256 - Add @[simp] unfold lemmas for LTL.Satisfies
- **Status**: [NOT STARTED]
- **Effort**: 1.5 hours
- **Dependencies**: None
- **Research Inputs**: specs/256_add_ltl_satisfies_simp_lemmas/reports/01_satisfies-simp-lemmas.md
- **Artifacts**: plans/01_satisfies-simp-lemmas.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: cslib
- **Lean Intent**: true

## Overview

Add @[simp] unfold lemmas for LTL.Satisfies to match the established pattern in Temporal/Semantics/Satisfies.lean. Currently LTL's `Satisfies` is a bare `def` with no simp lemmas, forcing downstream files (GNBA.lean, OmegaRegular.lean) to use fragile `simp only [Satisfies]` calls. This plan adds five core @[simp] constructor lemmas (all `Iff.rfl` proofs) in Phase 1, then derived non-simp lemmas for `neg`, `top`, `someFuture`, and `allFuture` in Phase 2. The `leadsto_iff` lemma is included as a stretch goal in Phase 2 since its proof complexity is bounded by `allFuture_iff` and `someFuture_iff` which it composes.

### Research Integration

The research report (01_satisfies-simp-lemmas.md) confirmed:
- LTL `Satisfies` at `Cslib/Logics/LTL/Semantics/Satisfies.lean:52` is a bare def with zero @[simp] lemmas
- Temporal `Satisfies` has four @[simp] lemmas (`atom_iff`, `imp_iff`, `untl_iff`, `snce_iff`) plus derived lemmas (`bot_false`, `neg_iff`, `top_true`, `someFuture_iff`, `allFuture_iff`)
- All five core LTL lemmas are `Iff.rfl` proofs (definitional equalities), zero risk
- 14 downstream `simp only [Satisfies]` calls in GNBA.lean and OmegaRegular.lean will benefit from the new lemmas without requiring changes (backwards compatible)
- simpNF compliance is automatic since all core lemmas are `Iff.rfl`

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

No ROADMAP.md items explicitly reference this task. This is a cleanup/automation improvement for the LTL module.

## Goals & Non-Goals

**Goals**:
- Add five @[simp] constructor lemmas for LTL `Satisfies`: `atom_iff`, `bot_iff`, `imp_iff`, `next_iff`, `untl_iff`
- Add derived non-simp lemmas: `bot_false`, `neg_iff`, `top_true`, `someFuture_iff`, `allFuture_iff`
- Optionally add `leadsto_iff` if proof is straightforward
- All lemmas placed inside a `namespace Satisfies` block after the `Satisfiable` definition
- All declarations include docstrings (docBlame compliance)
- Pass `lake build Cslib.Logics.LTL.Semantics.Satisfies` and full `lake build`

**Non-Goals**:
- Refactoring downstream files (GNBA.lean, OmegaRegular.lean) to use the new lemmas -- that is a separate task
- Adding @[simp] to the derived lemmas (they are non-simp by design, matching Temporal)
- Modifying the `Satisfies` definition itself

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Derived lemma proofs fail (especially `someFuture_iff`, `allFuture_iff`) | M | L | Research provided proof sketches; Temporal file provides working template; fall back to `sorry` and mark PARTIAL |
| New @[simp] lemmas cause downstream simp loops | H | L | Core lemmas are Iff.rfl (non-looping by construction); run full `lake build` to verify |
| `leadsto_iff` proof is complex due to `ωSequence.drop_drop` re-indexing | M | M | Treat as optional; defer to follow-up task if proof exceeds 15 minutes |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2 | 1 |

Phases within the same wave can execute in parallel.

### Phase 1: Core @[simp] Constructor Lemmas [COMPLETED]

**Goal**: Add five @[simp] theorem declarations inside a `namespace Satisfies` block, all proved by `Iff.rfl`.

**Tasks**:
- [ ] Add `namespace Satisfies` block after the `Satisfiable` definition (after line 66, before `end Cslib.Logic.LTL`)
- [ ] Add section header `/-! ## Constructor Lemmas -/`
- [ ] Add `atom_iff` with @[simp] and docstring: `Satisfies v w (.atom p) <-> v p w.head` proved by `Iff.rfl`
- [ ] Add `bot_iff` with @[simp] and docstring: `Satisfies v w .bot <-> False` proved by `Iff.rfl`
- [ ] Add `imp_iff` with @[simp] and docstring: `Satisfies v w (.imp phi psi) <-> (Satisfies v w phi -> Satisfies v w psi)` proved by `Iff.rfl`
- [ ] Add `next_iff` with @[simp] and docstring: `Satisfies v w (.next phi) <-> Satisfies v w.tail phi` proved by `Iff.rfl`
- [ ] Add `untl_iff` with @[simp] and docstring: `Satisfies v w (.untl phi psi) <-> exists j, Satisfies v (w.drop j) psi /\ forall k < j, Satisfies v (w.drop k) phi` proved by `Iff.rfl`
- [ ] Run `lake build Cslib.Logics.LTL.Semantics.Satisfies` to verify compilation

**Timing**: 30 minutes

**Depends on**: none

**Files to modify**:
- `Cslib/Logics/LTL/Semantics/Satisfies.lean` - Add namespace Satisfies block with 5 @[simp] theorems after line 66

**Verification**:
- `lake build Cslib.Logics.LTL.Semantics.Satisfies` compiles without errors
- All 5 lemmas have @[simp] attribute and docstrings

---

### Phase 2: Derived Lemmas and Verification [COMPLETED]

**Goal**: Add non-simp derived lemmas for `bot_false`, `neg_iff`, `top_true`, `someFuture_iff`, `allFuture_iff`, and optionally `leadsto_iff`. Run full build to confirm no downstream breakage.

**Tasks**:
- [ ] Add section header `/-! ## Derived Connective Lemmas -/`
- [ ] Add `bot_false` with docstring: `not Satisfies v w .bot` proved by `id`
- [ ] Add `neg_iff` with docstring: `Satisfies v w (neg phi) <-> not Satisfies v w phi` proved by `simp only [Satisfies]` or `Iff.rfl`
- [ ] Add `top_true` with docstring: `Satisfies v w Formula.top` proved by `intro h; exact h`
- [ ] Add section header `/-! ## Temporal Operator Lemmas -/`
- [ ] Add `someFuture_iff` with docstring: `Satisfies v w (someFuture phi) <-> exists j, Satisfies v (w.drop j) phi` -- proof eliminates trivially true guard from untl expansion
- [ ] Add `allFuture_iff` with docstring: `Satisfies v w (allFuture phi) <-> forall j, Satisfies v (w.drop j) phi` -- proof via negation of someFuture of negation
- [ ] (Optional) Add `leadsto_iff` with docstring -- defer if proof takes more than 15 minutes
- [ ] Close `end Satisfies` namespace
- [ ] Run `lake build Cslib.Logics.LTL.Semantics.Satisfies` to verify module compilation
- [ ] Run `lake build` to verify no downstream breakage
- [ ] Run `lake exe checkInitImports` and `lake exe lint-style` for CI compliance

**Timing**: 1 hour

**Depends on**: 1

**Files to modify**:
- `Cslib/Logics/LTL/Semantics/Satisfies.lean` - Add derived lemmas inside the Satisfies namespace block

**Verification**:
- `lake build` succeeds with zero errors
- `lake exe checkInitImports` passes
- `lake exe lint-style` passes
- No sorry remaining in any lemma (verified by `lean_verify` or grep)

## Testing & Validation

- [ ] `lake build Cslib.Logics.LTL.Semantics.Satisfies` compiles after Phase 1
- [ ] `lake build` (full project) succeeds after Phase 2 -- confirms no downstream breakage
- [ ] `lake exe checkInitImports` passes
- [ ] `lake exe lint-style` passes
- [ ] All new declarations have docstrings (docBlame compliance)
- [ ] No `sorry` in any new lemma
- [ ] All @[simp] lemmas satisfy simpNF (guaranteed by Iff.rfl proofs)

## Artifacts & Outputs

- `specs/256_add_ltl_satisfies_simp_lemmas/plans/01_satisfies-simp-lemmas.md` (this plan)
- `Cslib/Logics/LTL/Semantics/Satisfies.lean` (modified: new namespace Satisfies block with 10-11 lemmas)

## Rollback/Contingency

All changes are in a single file (`Cslib/Logics/LTL/Semantics/Satisfies.lean`). To revert: `git checkout -- Cslib/Logics/LTL/Semantics/Satisfies.lean`. The changes are purely additive (new namespace block after existing definitions) so partial rollback is straightforward. If any derived lemma in Phase 2 fails, the core @[simp] lemmas from Phase 1 are independently valuable and can be committed alone.
