# Implementation Plan: Task #326

- **Task**: 326 - Fix linter warnings across propositional tableau soundness and completeness modules
- **Status**: [COMPLETED]
- **Effort**: 1.5 hours
- **Dependencies**: 324 (LawfulBEq), 325 (dedup/dead code)
- **Research Inputs**: specs/326_tableau_lint_cleanup/reports/01_tableau-lint-research.md
- **Artifacts**: plans/01_tableau-lint-plan.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: cslib
- **Lean Intent**: false

## Overview

Fix 31 mechanical linter warnings across 4 propositional tableau files. The fixes include `omit` annotations for unused section variables, `show` to `change` replacements, `simp` to `simp only` narrowing, deprecated tactic replacement, and dead tactic block removal. No proof semantics are altered. Seven additional warnings in Classical/Completeness.lean are entangled with build errors from upstream tasks 324/325 and are explicitly out of scope.

### Research Integration

Research report `01_tableau-lint-research.md` identified 38 total warnings across 4 files. Of these, 31 are independently fixable without proof repair. The remaining 7 (unused simp arguments in Completeness.lean) are entangled with 50+ build errors caused by upstream API changes from tasks 324 and 325. The plan follows the research recommendation to address only the 31 feasible warnings and defer the remaining 7 to a proof-repair task.

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

No ROADMAP.md items directly addressed by this lint cleanup task.

## Goals & Non-Goals

**Goals**:
- Fix all 22 linter warnings in Classical/Soundness.lean
- Fix 3 linter warnings in Intuitionistic/Soundness.lean (omit annotations)
- Fix 1 linter warning in Minimal/Soundness.lean (omit annotation)
- Fix 5 independent linter warnings in Classical/Completeness.lean (2 omit + 3 dead tactic blocks)
- Verify Classical/Soundness.lean builds clean after changes

**Non-Goals**:
- Fix build errors in Classical/Completeness.lean (requires proof repair, separate task)
- Fix build errors in Intuitionistic/Soundness.lean (requires upstream investigation)
- Fix the 7 Completeness.lean warnings that are entangled with build errors
- Change any proof semantics or logic

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| `omit` annotation placement breaks build in Soundness.lean | M | L | Verify with `lake build` after each edit batch |
| `change True` not equivalent to `show True` in some context | L | L | `change` and `show` are both goal-rewriting tactics; verify no diagnostics |
| `push Not` syntax differs from `push_neg` | L | L | Check lean-lsp hover info for correct syntax; research confirms `push Not` |
| Line numbers shifted since research | M | M | Use grep/search for target identifiers rather than hard-coded line numbers |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2, 3 | 1 |

Phases within the same wave can execute in parallel.

---

### Phase 1: Classical/Soundness.lean (22 warnings) [COMPLETED]

**Goal**: Eliminate all 22 linter warnings in Classical/Soundness.lean, which builds cleanly.

**Tasks**:
- [ ] Add `omit [DecidableEq Atom] [Hashable Atom] in` before each of the 12 private `classicalApplyOne_*` lemmas (lines ~72-126), or wrap the block in a single `section`-scoped omit
- [ ] Add `omit [Hashable Atom] in` before `classicalRule_preserves_sat` (~line 130)
- [ ] Add `omit [Hashable Atom] in` before `classically_closed_unsatisfiable` (~line 401)
- [ ] Replace 4 occurrences of `show True` with `change True` (~lines 176, 179, 303, 305)
- [ ] Remove unused `SignedFormula.formula` from simp list (~line 431)
- [ ] Replace `simp [hfind] at hclosed` with `simp only [hfind] at hclosed` (~line 437)
- [ ] Replace `push_neg` with `push Not` (~line 608)
- [ ] Verify file builds with zero warnings using `lake build`

**Timing**: 45 minutes

**Depends on**: none

**Files to modify**:
- `Cslib/Logics/Propositional/Tableau/Classical/Soundness.lean` - All 22 warning fixes

**Verification**:
- `lake build` returns zero warnings and zero errors for the file
- No `sorry` introduced

---

### Phase 2: Intuitionistic + Minimal Soundness (4 warnings) [COMPLETED]

**Goal**: Add `omit` annotations to suppress unused section variable warnings in Intuitionistic/Soundness.lean and Minimal/Soundness.lean.

**Tasks**:
- [ ] Add `omit [Hashable Atom] in` before `intRule_preserves_sat` in Intuitionistic/Soundness.lean (~line 82)
- [ ] Add `omit [Hashable Atom] in` before `intClosed_unsatisfiable` in Intuitionistic/Soundness.lean (~line 276)
- [ ] Add `omit [Hashable Atom] in` before `minClosed_unsatisfiable` in Minimal/Soundness.lean (~line 67)
- [ ] Verify the `omit` annotations are syntactically correct (these files have pre-existing build errors from upstream; only lint fix correctness is verified)

**Timing**: 15 minutes

**Depends on**: 1

**Files to modify**:
- `Cslib/Logics/Propositional/Tableau/Intuitionistic/Soundness.lean` - 2 omit annotations
- `Cslib/Logics/Propositional/Tableau/Minimal/Soundness.lean` - 1 omit annotation

**Verification**:
- `omit` annotations are syntactically valid (no new errors introduced by the annotations themselves)
- Pre-existing build errors in these files are unchanged

---

### Phase 3: Classical/Completeness.lean independent fixes (5 warnings) [COMPLETED]

**Goal**: Fix the 5 lint warnings in Classical/Completeness.lean that are independent of the build errors.

**Tasks**:
- [ ] Add `omit` annotations for `mem_extendMany_of_mem` (~line 404) and `hintikka_inv_mono` (~line 415) unused section variables
- [ ] Remove 3 dead/unreachable tactic blocks (~lines 468-479)
- [ ] Verify no new errors introduced (pre-existing build errors remain unchanged)

**Timing**: 15 minutes

**Depends on**: 1

**Files to modify**:
- `Cslib/Logics/Propositional/Tableau/Classical/Completeness.lean` - 2 omit annotations + 3 dead tactic removals

**Verification**:
- `omit` annotations are syntactically valid
- Dead tactic blocks removed without affecting surrounding proof structure
- Pre-existing build errors are not worsened

## Testing & Validation

- [ ] Classical/Soundness.lean: zero warnings, zero errors via `lake build`
- [ ] Intuitionistic/Soundness.lean: 3 fewer warnings (pre-existing errors remain)
- [ ] Minimal/Soundness.lean: 1 fewer warning (blocked file may still not build)
- [ ] Classical/Completeness.lean: 5 fewer warnings (pre-existing errors remain)
- [ ] No `sorry` introduced in any file
- [ ] `lake build` succeeds for Classical/Soundness.lean module

## Artifacts & Outputs

- `specs/326_tableau_lint_cleanup/plans/01_tableau-lint-plan.md` (this file)
- `specs/326_tableau_lint_cleanup/summaries/01_tableau-lint-summary.md` (post-implementation)
- Modified files:
  - `Cslib/Logics/Propositional/Tableau/Classical/Soundness.lean`
  - `Cslib/Logics/Propositional/Tableau/Intuitionistic/Soundness.lean`
  - `Cslib/Logics/Propositional/Tableau/Minimal/Soundness.lean`
  - `Cslib/Logics/Propositional/Tableau/Classical/Completeness.lean`

## Rollback/Contingency

All changes are mechanical lint annotations and tactic replacements. If any change causes unexpected build failures, revert the individual edit. Since the changes are independent per-file, partial rollback is straightforward with `git checkout -- <file>`. The 7 entangled Completeness.lean warnings should be addressed by a separate proof-repair task.
