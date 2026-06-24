# Implementation Plan: LawfulBEq for Proposition and SignedFormula

- **Task**: 324 - Add LawfulBEq instances for Proposition Atom and SignedFormula F L, then remove workaround lemmas
- **Status**: [IMPLEMENTING]
- **Effort**: 1 hour
- **Dependencies**: None
- **Research Inputs**: reports/01_lawfulbeq-research.md
- **Artifacts**: plans/01_lawfulbeq-plan.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: cslib
- **Lean Intent**: false

## Overview

Remove independently derived `BEq` from the `deriving` clauses of `Proposition` and `SignedFormula`, allowing Lean's `instBEqOfDecidableEq` and `instLawfulBEq` to provide lawful `BEq` automatically. Then delete the ~60-line workaround lemmas (`prop_beq_eq`, `proposition_beq_eq`) and replace all 15 call sites with standard `eq_of_beq` or `beq_iff_eq`. This is a purely mechanical refactoring with zero new proof code.

### Research Integration

Research report `01_lawfulbeq-research.md` confirmed the root cause (derived `BEq` bypasses `DecidableEq`, preventing `LawfulBEq` resolution) and verified the fix via `lean_run_code`. The report provides exact line numbers for all 15 call sites across 7 files, three replacement patterns (A: `eq_of_beq`, B: `simp [beq_iff_eq]`, C: comment cleanup), and confirmed zero risk from the bimodal codebase already using this pattern.

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

No ROADMAP.md items directly advanced. This is internal cleanup within `Logics/Propositional/` that reduces technical debt.

## Goals & Non-Goals

**Goals**:
- Remove `BEq` from `deriving` clauses of `Proposition` and `SignedFormula` so `LawfulBEq` is automatically available
- Delete `prop_beq_eq` (~30 lines) and `proposition_beq_eq` (~30 lines) workaround lemmas
- Replace all 15 call sites with standard `eq_of_beq` or `beq_iff_eq`
- Optionally add `Repr` to `Proposition` deriving clause for debugging
- Pass full CSLib CI pipeline (`lake build`, `lake test`, `lake exe checkInitImports`, `lake exe lint-style`)

**Non-Goals**:
- Changing `Sign.lean` (already has explicit `LawfulBEq` instance)
- Modifying bimodal `SignedFormula.lean` (already follows correct pattern)
- Updating test/scratch files outside the library build
- Adding new typeclass instances or abstractions

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| `instBEqOfDecidableEq` resolves to different computational behavior | L | L | Both paths do structural comparison; verified via `lean_run_code` in research |
| Downstream files fail to resolve `BEq` or `LawfulBEq` | M | L | The bimodal codebase already uses this exact pattern; typeclass resolution is well-understood |
| Missed call site causes build failure | L | L | Research cataloged all 15 sites; `lake build` catches any missed references |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2 | 1 |

Phases within the same wave can execute in parallel.

### Phase 1: Modify Deriving Clauses and Delete Workaround Lemmas [COMPLETED]

**Goal**: Change the type definitions so `LawfulBEq` resolves automatically, and remove the now-unnecessary workaround lemmas.

**Tasks**:
- [ ] In `Cslib/Logics/Propositional/Defs.lean` line 92, change `deriving DecidableEq, BEq` to `deriving DecidableEq, Repr`
- [ ] In `Cslib/Foundations/Logic/Tableau/SignedFormula.lean` line 56, change `deriving DecidableEq, BEq, Hashable` to `deriving DecidableEq, Hashable`
- [ ] Delete `private lemma prop_beq_eq` (lines 128-157) from `Cslib/Logics/Propositional/Tableau/Classical/Soundness.lean`
- [ ] Delete `lemma proposition_beq_eq` and its section header (lines 80-116) from `Cslib/Logics/Propositional/Tableau/Minimal/Soundness.lean`

**Timing**: 15 minutes

**Depends on**: none

**Files to modify**:
- `Cslib/Logics/Propositional/Defs.lean` - Remove `BEq`, add `Repr` in deriving clause
- `Cslib/Foundations/Logic/Tableau/SignedFormula.lean` - Remove `BEq` from deriving clause
- `Cslib/Logics/Propositional/Tableau/Classical/Soundness.lean` - Delete `prop_beq_eq` lemma
- `Cslib/Logics/Propositional/Tableau/Minimal/Soundness.lean` - Delete `proposition_beq_eq` lemma and section

**Verification**:
- Files compile without errors (may have downstream breakage until Phase 2)

---

### Phase 2: Replace All Call Sites and Verify Build [COMPLETED]

**Goal**: Replace all 15 references to the deleted workaround lemmas with standard `eq_of_beq` / `beq_iff_eq`, update stale comments, and verify the full build passes.

**Tasks**:
- [ ] **Pattern A replacements** (11 sites): Replace `prop_beq_eq _ _ h` and `proposition_beq_eq _ _ h` with `eq_of_beq h`:
  - `Classical/Soundness.lean` lines 461, 487
  - `Classical/Completeness.lean` lines 112, 113, 161, 255, 327, 344, 367, 388
  - `Minimal/Soundness.lean` line 150
- [ ] **Pattern A replacements** (2 sites): Replace fully-qualified `Cslib.Logic.PL.proposition_beq_eq _ _ h` with `eq_of_beq h`:
  - `Minimal/Completeness.lean` lines 111, 113
- [ ] **Pattern B replacements** (4 lines in 1 file): Replace `simp [hf, BEq.beq, instBEqProposition.beq]` with `simp [beq_iff_eq, hf]`:
  - `Intuitionistic/Soundness.lean` lines 296-299
- [ ] **Pattern C**: Update or remove stale comments referencing `proposition_beq_eq` and `instBEqProposition` in `Minimal/Soundness.lean` (line 147) and `Minimal/Completeness.lean` (lines 108-109)
- [ ] Optionally consolidate `Minimal/Completeness.lean` lines 107-113 into a single `simp only [beq_iff_eq]` call
- [ ] Run `lake build` to verify full compilation
- [ ] Run `lake test` to verify test suite
- [ ] Run `lake exe checkInitImports` and `lake exe lint-style` for CI compliance

**Timing**: 45 minutes

**Depends on**: 1

**Files to modify**:
- `Cslib/Logics/Propositional/Tableau/Classical/Soundness.lean` - Replace 2 `prop_beq_eq` calls with `eq_of_beq`
- `Cslib/Logics/Propositional/Tableau/Classical/Completeness.lean` - Replace 8 `prop_beq_eq` calls with `eq_of_beq`
- `Cslib/Logics/Propositional/Tableau/Minimal/Soundness.lean` - Replace 1 call, update comment
- `Cslib/Logics/Propositional/Tableau/Minimal/Completeness.lean` - Replace 2 fully-qualified calls, update comments, optionally consolidate simp
- `Cslib/Logics/Propositional/Tableau/Intuitionistic/Soundness.lean` - Replace 4 `simp` invocations with `beq_iff_eq` pattern

**Verification**:
- `lake build` succeeds with zero errors
- `lake test` passes
- `lake exe checkInitImports` passes
- `lake exe lint-style` passes
- No references to `prop_beq_eq`, `proposition_beq_eq`, or `instBEqProposition.beq` remain in library source

## Testing & Validation

- [ ] `lake build` compiles the full library without errors
- [ ] `lake test` passes all tests in CslibTests
- [ ] `lake exe checkInitImports` reports no missing imports
- [ ] `lake exe lint-style` reports no style violations
- [ ] `grep -r "prop_beq_eq\|proposition_beq_eq\|instBEqProposition.beq" Cslib/` returns no matches (excluding test/scratch files)

## Artifacts & Outputs

- `specs/324_lawfulbeq_proposition_signedformula/plans/01_lawfulbeq-plan.md` (this file)
- `specs/324_lawfulbeq_proposition_signedformula/summaries/01_lawfulbeq-summary.md` (post-implementation)

## Rollback/Contingency

Revert with `git checkout main -- Cslib/Logics/Propositional/Defs.lean Cslib/Foundations/Logic/Tableau/SignedFormula.lean Cslib/Logics/Propositional/Tableau/Classical/Soundness.lean Cslib/Logics/Propositional/Tableau/Classical/Completeness.lean Cslib/Logics/Propositional/Tableau/Minimal/Soundness.lean Cslib/Logics/Propositional/Tableau/Minimal/Completeness.lean Cslib/Logics/Propositional/Tableau/Intuitionistic/Soundness.lean`. All changes are confined to 7 files with no new definitions introduced, so a clean revert restores prior behavior exactly.
