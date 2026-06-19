# Implementation Plan: Task #237

- **Task**: 237 - Derive weak completeness as corollaries of strong completeness for all 15 modal cube systems
- **Status**: [COMPLETED]
- **Effort**: 3 hours
- **Dependencies**: None
- **Research Inputs**: specs/237_weak_completeness_corollaries_modal_cube/reports/01_weak-completeness-corollaries.md
- **Artifacts**: plans/01_weak-completeness-corollaries.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: cslib
- **Lean Intent**: false

## Overview

Replace the direct ~30-line proofs of weak completeness (`{sys}_completeness`) in each system's `Completeness.lean` with ~5-line corollary proofs derived from `{sys}_strong_completeness` via `ModalSetDerivable_empty_iff`. The corollary is placed in `StrongCompleteness.lean`, the original theorem is removed from `Completeness.lean`, and docstrings in both files are updated. This is a pure refactoring -- theorem names, types, and the public API are preserved exactly.

### Research Integration

The research report (01_weak-completeness-corollaries.md) provides:
- Exact corollary proof terms for all 15 systems, split into two patterns: Pattern 1 (K, uses `ModalSemanticEntails_of_Valid`) and Pattern 2 (14 remaining systems, direct quantification with discarded vacuous hypothesis).
- A catalog of what infrastructure remains in each `Completeness.lean` after the move: 4 systems retain declarations (K: 3, T: 2, D: 4, TB: 3), 10 systems become empty module bodies, and S5 has an `alias completeness := s5_completeness` that must move with the theorem.
- Confirmation that no import changes are needed -- all required lemmas are already accessible in each `StrongCompleteness.lean`.

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

No ROADMAP.md found.

## Goals & Non-Goals

**Goals**:
- Move all 15 `{sys}_completeness` theorems from `Completeness.lean` to `StrongCompleteness.lean` as corollaries of strong completeness
- Replace each direct ~30-line proof with a ~5-line term-mode corollary via `ModalSetDerivable_empty_iff`
- Update module docstrings in both files for all 15 systems
- Move the S5 `alias completeness := s5_completeness` alongside its theorem
- Verify the full project builds cleanly with `lake build`

**Non-Goals**:
- Changing theorem names, signatures, or the public API
- Modifying supporting infrastructure (truth lemmas, canonical model constructions)
- Adding new theorems beyond what currently exists
- Removing `Completeness.lean` files that become empty (they serve as import targets)

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Corollary proof term has universe mismatch | M | L | All systems use `universe u` with `{Atom : Type u}` and `ModalSetDerivable_empty_iff` is universe-polymorphic; verify with `lake build` after each phase |
| Removing theorem breaks downstream import | H | L | Theorem is re-exported from `StrongCompleteness.lean` which is in the import graph; verify with full `lake build` |
| S5 alias breaks after move | M | L | Move alias with theorem; confirmed it is a simple `alias completeness := s5_completeness` |
| Empty Completeness.lean files cause lint warnings | L | L | Keep the file with imports, namespace, and updated docstring; they remain valid Lean modules |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2 | 1 |
| 3 | 3 | 2 |
| 4 | 4 | 3 |

Phases within the same wave can execute in parallel.

### Phase 1: Systems with remaining infrastructure (K, T, D, TB) [NOT STARTED]

**Goal**: Move the completeness theorem from `Completeness.lean` to `StrongCompleteness.lean` for the 4 systems that retain other declarations in `Completeness.lean`. These are the most complex edits because the surrounding infrastructure must be preserved.

**Tasks**:
- [ ] **K**: Remove `k_completeness` theorem and its section header/docstring (lines ~267-301) from `K/Completeness.lean`. Add K weak completeness corollary (Pattern 1, using `ModalSemanticEntails_of_Valid`) to `K/StrongCompleteness.lean` before `end Cslib.Logic.Modal`. Update module docstrings in both files.
- [ ] **T**: Remove `t_completeness` theorem and its section header/docstring from `T/Completeness.lean`. Add T weak completeness corollary to `T/StrongCompleteness.lean`. Update module docstrings in both files.
- [ ] **D**: Remove `d_completeness` theorem and its section header/docstring from `D/Completeness.lean`. Add D weak completeness corollary to `D/StrongCompleteness.lean`. Update module docstrings in both files.
- [ ] **TB**: Remove `tb_completeness` theorem and its section header/docstring from `TB/Completeness.lean`. Add TB weak completeness corollary to `TB/StrongCompleteness.lean`. Update module docstrings in both files.
- [ ] Run `lake build` on the 8 modified modules to verify

**Timing**: 1 hour

**Depends on**: none

**Files to modify**:
- `Cslib/Logics/Modal/Metalogic/Systems/K/Completeness.lean` - Remove completeness theorem, update docstring
- `Cslib/Logics/Modal/Metalogic/Systems/K/StrongCompleteness.lean` - Add corollary, update docstring
- `Cslib/Logics/Modal/Metalogic/Systems/T/Completeness.lean` - Remove completeness theorem, update docstring
- `Cslib/Logics/Modal/Metalogic/Systems/T/StrongCompleteness.lean` - Add corollary, update docstring
- `Cslib/Logics/Modal/Metalogic/Systems/D/Completeness.lean` - Remove completeness theorem, update docstring
- `Cslib/Logics/Modal/Metalogic/Systems/D/StrongCompleteness.lean` - Add corollary, update docstring
- `Cslib/Logics/Modal/Metalogic/Systems/TB/Completeness.lean` - Remove completeness theorem, update docstring
- `Cslib/Logics/Modal/Metalogic/Systems/TB/StrongCompleteness.lean` - Add corollary, update docstring

**Verification**:
- Each corollary compiles without errors
- Remaining infrastructure in Completeness.lean files is untouched
- Module docstrings reflect the new location of the completeness theorem

---

### Phase 2: Single-declaration systems, first batch (B, S4, S5, K4, K5) [NOT STARTED]

**Goal**: Move the completeness theorem for 5 systems whose `Completeness.lean` has only the completeness theorem (plus imports and docstring). After removal, these files become empty module bodies with just imports and an updated docstring. S5 additionally requires moving the `alias completeness := s5_completeness`.

**Tasks**:
- [ ] **B**: Remove `b_completeness` theorem from `B/Completeness.lean`. Replace module body with updated docstring noting infrastructure import role. Add corollary to `B/StrongCompleteness.lean`.
- [ ] **S4**: Same pattern for `s4_completeness`.
- [ ] **S5**: Remove `s5_completeness` theorem AND `alias completeness := s5_completeness` from `S5/Completeness.lean`. Add both to `S5/StrongCompleteness.lean`.
- [ ] **K4**: Same pattern for `k4_completeness`.
- [ ] **K5**: Same pattern for `k5_completeness`.
- [ ] Run `lake build` on the 10 modified modules to verify

**Timing**: 45 minutes

**Depends on**: 1

**Files to modify**:
- `Cslib/Logics/Modal/Metalogic/Systems/B/Completeness.lean` - Remove theorem, update docstring
- `Cslib/Logics/Modal/Metalogic/Systems/B/StrongCompleteness.lean` - Add corollary, update docstring
- `Cslib/Logics/Modal/Metalogic/Systems/S4/Completeness.lean` - Remove theorem, update docstring
- `Cslib/Logics/Modal/Metalogic/Systems/S4/StrongCompleteness.lean` - Add corollary, update docstring
- `Cslib/Logics/Modal/Metalogic/Systems/S5/Completeness.lean` - Remove theorem + alias, update docstring
- `Cslib/Logics/Modal/Metalogic/Systems/S5/StrongCompleteness.lean` - Add corollary + alias, update docstring
- `Cslib/Logics/Modal/Metalogic/Systems/K4/Completeness.lean` - Remove theorem, update docstring
- `Cslib/Logics/Modal/Metalogic/Systems/K4/StrongCompleteness.lean` - Add corollary, update docstring
- `Cslib/Logics/Modal/Metalogic/Systems/K5/Completeness.lean` - Remove theorem, update docstring
- `Cslib/Logics/Modal/Metalogic/Systems/K5/StrongCompleteness.lean` - Add corollary, update docstring

**Verification**:
- All 10 files compile without errors
- Empty-body Completeness.lean files have updated docstrings noting the infrastructure import role
- S5 alias is present and functional in StrongCompleteness.lean

---

### Phase 3: Single-declaration systems, second batch (K45, KB5, D4, D5, D45, DB) [NOT STARTED]

**Goal**: Move the completeness theorem for the remaining 6 systems. Same pattern as Phase 2.

**Tasks**:
- [ ] **K45**: Remove `k45_completeness` from `K45/Completeness.lean`. Add corollary to `K45/StrongCompleteness.lean`. Update docstrings.
- [ ] **KB5**: Same pattern for `kb5_completeness`.
- [ ] **D4**: Same pattern for `d4_completeness`.
- [ ] **D5**: Same pattern for `d5_completeness`.
- [ ] **D45**: Same pattern for `d45_completeness`.
- [ ] **DB**: Same pattern for `db_completeness`.
- [ ] Run `lake build` on the 12 modified modules to verify

**Timing**: 45 minutes

**Depends on**: 2

**Files to modify**:
- `Cslib/Logics/Modal/Metalogic/Systems/K45/Completeness.lean` - Remove theorem, update docstring
- `Cslib/Logics/Modal/Metalogic/Systems/K45/StrongCompleteness.lean` - Add corollary, update docstring
- `Cslib/Logics/Modal/Metalogic/Systems/KB5/Completeness.lean` - Remove theorem, update docstring
- `Cslib/Logics/Modal/Metalogic/Systems/KB5/StrongCompleteness.lean` - Add corollary, update docstring
- `Cslib/Logics/Modal/Metalogic/Systems/D4/Completeness.lean` - Remove theorem, update docstring
- `Cslib/Logics/Modal/Metalogic/Systems/D4/StrongCompleteness.lean` - Add corollary, update docstring
- `Cslib/Logics/Modal/Metalogic/Systems/D5/Completeness.lean` - Remove theorem, update docstring
- `Cslib/Logics/Modal/Metalogic/Systems/D5/StrongCompleteness.lean` - Add corollary, update docstring
- `Cslib/Logics/Modal/Metalogic/Systems/D45/Completeness.lean` - Remove theorem, update docstring
- `Cslib/Logics/Modal/Metalogic/Systems/D45/StrongCompleteness.lean` - Add corollary, update docstring
- `Cslib/Logics/Modal/Metalogic/Systems/DB/Completeness.lean` - Remove theorem, update docstring
- `Cslib/Logics/Modal/Metalogic/Systems/DB/StrongCompleteness.lean` - Add corollary, update docstring

**Verification**:
- All 12 files compile without errors
- Docstrings updated consistently

---

### Phase 4: Full build verification and CI checks [NOT STARTED]

**Goal**: Run the complete CSLib CI verification pipeline to confirm the refactoring introduces no regressions.

**Tasks**:
- [ ] Run `lake build` (full project) to verify all 30 files and all downstream dependents compile
- [ ] Run `lake exe checkInitImports` to verify import structure
- [ ] Run `lake exe lint-style` to verify style compliance
- [ ] Run `lake test` to verify test suite passes

**Timing**: 30 minutes

**Depends on**: 3

**Files to modify**: (none -- verification only)

**Verification**:
- `lake build` exits 0
- `lake exe checkInitImports` exits 0
- `lake exe lint-style` exits 0 or reports only pre-existing issues
- `lake test` passes

## Testing & Validation

- [ ] All 15 corollary proofs compile as term-mode expressions (no `sorry`, no `by` blocks)
- [ ] All 15 Completeness.lean files compile (those with remaining infrastructure and those with empty bodies)
- [ ] Full `lake build` passes with no new errors
- [ ] `lake exe checkInitImports` passes
- [ ] `lake exe lint-style` passes
- [ ] `lake test` passes
- [ ] Theorem names are preserved: `{sys}_completeness` for all 15 systems
- [ ] S5 `alias completeness := s5_completeness` is functional in new location

## Artifacts & Outputs

- 15 modified `StrongCompleteness.lean` files (corollary added)
- 15 modified `Completeness.lean` files (theorem removed, docstrings updated)
- specs/237_weak_completeness_corollaries_modal_cube/plans/01_weak-completeness-corollaries.md (this plan)

## Rollback/Contingency

All changes are to existing files tracked by git. Rollback via `git checkout -- Cslib/Logics/Modal/Metalogic/Systems/` restores all 30 files to their pre-refactoring state. Since the refactoring preserves theorem names and types, partial rollback (reverting individual systems) is also safe -- each system's pair of files is independent.
