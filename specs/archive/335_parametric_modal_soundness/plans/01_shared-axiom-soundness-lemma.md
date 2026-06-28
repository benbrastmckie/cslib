# Implementation Plan: Task #335

- **Task**: 335 - Parametric Modal Soundness Refactor (parametric_modal_soundness)
- **Status**: [COMPLETED]
- **Effort**: 2.5 hours
- **Dependencies**: None
- **Research Inputs**: specs/335_parametric_modal_soundness/reports/01_parametric-modal-soundness.md
- **Artifacts**: plans/01_shared-axiom-soundness-lemma.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md, CONTRIBUTING.md, NOTATION.md, ORGANISATION.md
- **Type**: cslib
- **Lean Intent**: false

## Overview

Extract the 5 propositional + K axiom soundness cases (implyK, implyS, efq, peirce, modalK) that are duplicated identically across all 15 system-specific `Soundness.lean` files into 5 shared `Satisfies.*_axiom` lemmas in `Cslib/Logics/Modal/Metalogic/Soundness.lean`. Then refactor every system file to delegate those 5 cases to the shared lemmas with one-line `exact` calls. The approach requires no import changes, no axiom-type changes, and carries zero sorry risk because each shared lemma is trivially provable from the definition of `Satisfies`.

### Research Integration

The research report establishes the precise design: add 5 standalone `Satisfies.*_axiom` lemmas (full signatures provided in the report) following the existing `Satisfies.t/b/four/five/d` naming pattern already present in `Basic.lean`. The shared `Soundness.lean` already imports `Basic.lean` transitively via `DerivationTree.lean`, so `Satisfies`, `Model`, and `Proposition` are in scope. CSLib lint rule `defLemma` requires `lemma` (not `def`/`theorem`) for these `Prop`-valued declarations. The report explicitly rejects KAxiom-embedding, typeclass, sum-type, and macro alternatives as over-engineered or circular. Realistic net reduction is ~140 lines (not the ~600 in the original task framing — that target requires orthogonal out-of-scope refactorings).

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

No ROADMAP.md consulted (no roadmap_path provided; roadmap flag not set).

## Goals & Non-Goals

**Goals**:
- Add 5 shared `Satisfies.*_axiom` lemmas to `Cslib/Logics/Modal/Metalogic/Soundness.lean`.
- Refactor all 15 `Systems/*/Soundness.lean` files to delegate the 5 propositional+K cases to the shared lemmas.
- Preserve all existing theorem signatures and public API (zero downstream breakage).
- Pass the full CSLib CI pipeline (build, test, init imports, lint-style, shake).

**Non-Goals**:
- Abstracting the `_soundness` / `_soundness_derivable` wrapper theorems (separate task).
- Restructuring axiom inductives to share a common base type (separate task).
- Achieving the ~600-line reduction from the original framing (not reachable via this refactor alone).
- Touching system-specific cases (modalT, modalB, modalD, modalFour, modalFive).

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Shared lemma signature mismatch with a system's case binders | L | L | Use exact signatures from research report; verify with `lean_goal`/`lake build` per-file |
| `lemma` vs `def`/`theorem` lint violation | L | L | Use `lemma` keyword per `defLemma` rule; mirror existing `Satisfies.t` style |
| One system file has a subtly different case body | M | L | Phase 2 diffs each file's base block against the canonical block before replacing |
| K system file structure differs (no system-specific cases) | L | M | Handle K explicitly in Phase 2; delegate all 5 cases or inline per report note |
| `shake` flags newly-unused or newly-needed imports | L | L | Run full CI in Phase 3; no import changes are expected |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2 | 1 |
| 3 | 3 | 2 |

Phases within the same wave can execute in parallel. This plan is a strict linear chain (each phase depends on the prior).

### Phase 1: Add shared `Satisfies.*_axiom` lemmas [COMPLETED]

**Goal**: Introduce the 5 reusable propositional+K soundness lemmas in the shared `Soundness.lean`, compiling cleanly with no sorries.

**Tasks**:
- [ ] Read `Cslib/Logics/Modal/Metalogic/Soundness.lean` to confirm insertion point (after module docstring, before the `soundness` theorem) and confirm `Satisfies`/`Model`/`Proposition` are in scope.
- [ ] Read `Cslib/Logics/Modal/Basic.lean` lines ~280-407 to match the style/docstring convention of the existing `Satisfies.t/b/four/five/d` lemmas.
- [ ] Add `Satisfies.implyK_axiom` lemma (φ → ψ → φ pattern), with docstring.
- [ ] Add `Satisfies.implyS_axiom` lemma (distribution), with docstring.
- [ ] Add `Satisfies.efq_axiom` lemma (ex falso), with docstring.
- [ ] Add `Satisfies.peirce_axiom` lemma (Peirce's law), with docstring.
- [ ] Add `Satisfies.modalK_axiom` lemma (modal distribution), with docstring.
- [ ] Use the `lemma` keyword (not `def`/`theorem`) to satisfy the `defLemma` lint rule.
- [ ] Verify with `lean_goal` (or LSP diagnostics) that each lemma closes with no goals and no sorry.

**Timing**: 0.75 hours

**Depends on**: none

**Files to modify**:
- `Cslib/Logics/Modal/Metalogic/Soundness.lean` - add 5 `Satisfies.*_axiom` lemmas (~25 lines) between docstring section and `soundness`.

**Verification**:
- `lake build Cslib.Logics.Modal.Metalogic.Soundness` succeeds.
- No `sorry`, `admit`, or `axiom` introduced (grep the diff).
- LSP diagnostics show no errors/warnings for the new lemmas.

---

### Phase 2: Refactor all 15 system `Soundness.lean` files [COMPLETED]

**Goal**: Replace the 5 duplicated propositional+K case proof bodies in each of the 15 system files with one-line delegations to the Phase 1 lemmas, leaving system-specific cases untouched.

**Tasks**:
- [ ] Establish the canonical 5-case base block (from the research report) as the diff reference.
- [ ] For each system, confirm the file's base block matches the canonical block before editing.
- [ ] Refactor `Systems/K/Soundness.lean` (all 5 cases; handle per report note — delegate all 5).
- [ ] Refactor `Systems/T/Soundness.lean` (5 base cases delegated; keep modalT).
- [ ] Refactor `Systems/B/Soundness.lean` (keep modalB).
- [ ] Refactor `Systems/D/Soundness.lean` (keep modalD).
- [ ] Refactor `Systems/S4/Soundness.lean` (keep modalT, modalFour).
- [ ] Refactor `Systems/S5/Soundness.lean` (keep modalT, modalFour, modalB).
- [ ] Refactor `Systems/K4/Soundness.lean` (keep modalFour).
- [ ] Refactor `Systems/K5/Soundness.lean` (keep modalFive).
- [ ] Refactor `Systems/K45/Soundness.lean` (keep modalFour, modalFive).
- [ ] Refactor `Systems/KB5/Soundness.lean` (keep modalB, modalFive).
- [ ] Refactor `Systems/D4/Soundness.lean` (keep modalD, modalFour).
- [ ] Refactor `Systems/D5/Soundness.lean` (keep modalD, modalFive).
- [ ] Refactor `Systems/D45/Soundness.lean` (keep modalD, modalFour, modalFive).
- [ ] Refactor `Systems/DB/Soundness.lean` (keep modalD, modalB).
- [ ] Refactor `Systems/TB/Soundness.lean` (keep modalT, modalB).
- [ ] In each file, replace each base case body with `exact Satisfies.<name>_axiom m w <binders>` matching that file's `cases h_ax with` binder names.
- [ ] Incrementally build each modified file (or batches) to catch binder/signature mismatches early.

**Timing**: 1.25 hours

**Depends on**: 1

**Files to modify**:
- `Cslib/Logics/Modal/Metalogic/Systems/{K,T,B,D,S4,S5,K4,K5,K45,KB5,D4,D5,D45,DB,TB}/Soundness.lean` - replace 5 base case bodies with one-line `exact` delegations; leave system-specific cases unchanged.

**Verification**:
- Each modified file compiles: `lake build Cslib.Logics.Modal.Metalogic.Systems.<X>.Soundness`.
- Diff confirms only base-case bodies changed; theorem signatures and system-specific cases are byte-identical to before.
- No `sorry`/`admit` introduced anywhere (grep the full diff).

---

### Phase 3: Full CI verification [COMPLETED]

**Goal**: Confirm the entire modal metalogic subtree and the repository CI pipeline pass after the refactor.

**Tasks**:
- [ ] Run `lake build Cslib.Logics.Modal.Metalogic` (builds shared + all 15 systems).
- [ ] Run `lake build` for a full-project sanity build.
- [ ] Run `lake test` (CslibTests suite).
- [ ] Run `lake exe checkInitImports`.
- [ ] Run `lake exe lint-style`.
- [ ] Run `lake shake --add-public --keep-implied --keep-prefix` and confirm no import changes are demanded (none expected).
- [ ] Grep the complete diff for `sorry`/`admit`/new `axiom` to confirm none introduced.
- [ ] Record final line-count delta (expect ~140-line net reduction) for the summary.

**Timing**: 0.5 hours

**Depends on**: 2

**Files to modify**:
- None (verification only).

**Verification**:
- All CI commands exit 0.
- No lint, style, or shake violations.
- Net line reduction observed and recorded.

## Testing & Validation

- [ ] `lake build Cslib.Logics.Modal.Metalogic` succeeds.
- [ ] `lake build` (full project) succeeds.
- [ ] `lake test` passes.
- [ ] `lake exe checkInitImports` passes.
- [ ] `lake exe lint-style` passes.
- [ ] `lake shake --add-public --keep-implied --keep-prefix` reports no required changes.
- [ ] No `sorry`/`admit`/new `axiom` in the diff.
- [ ] All public theorem signatures unchanged (no downstream breakage).

## Artifacts & Outputs

- Modified `Cslib/Logics/Modal/Metalogic/Soundness.lean` with 5 new shared lemmas.
- 15 refactored `Systems/*/Soundness.lean` files.
- Execution summary at `specs/335_parametric_modal_soundness/summaries/01_*-summary.md` (on implement).
- ~140-line net reduction across the 16 files.

## Rollback/Contingency

All changes are mechanical proof-body replacements with equivalent lemma calls and no public API changes. If any system file fails to compile after delegation, revert that single file to its original base block (the system-specific cases are untouched, so a per-file revert is isolated) and leave the shared lemmas in place — they are independently valid. If the shared lemmas themselves fail (not expected), revert the entire change via `git checkout -- Cslib/Logics/Modal/Metalogic/` since no other files are touched.
