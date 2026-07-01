# Implementation Plan: Task #455 - Extract Tableau Measure Arithmetic

- **Task**: 455 - Extract logic-agnostic measure arithmetic into a shared `Cslib/Foundations/Logic/Tableau/Measure.lean`
- **Status**: [NOT STARTED]
- **Effort**: 3 hours
- **Dependencies**: None (independent of task 317; parent_task 317 is source-of-idea only)
- **Research Inputs**: specs/455_extract_tableau_measure_arithmetic/reports/01_tableau-measure-arithmetic-extraction.md
- **Artifacts**: plans/01_measure-arithmetic-extraction.md (this file)
- **Standards**: plan-format.md; status-markers.md; artifact-management.md; tasks.md
- **Type**: cslib
- **Lean Intent**: false

## Overview

Extract 10 logic-agnostic pure-`Nat`/`List` arithmetic declarations into a new shared module
`Cslib/Foundations/Logic/Tableau/Measure.lean` (namespace `Cslib.Logic.Tableau`), de-duplicating
the two byte-identical `pow3_*` lemmas that currently exist in both `FmpMeasure.lean` (Modal K FMP
measure) and `Classical/Completeness.lean` (classical propositional tableau), and promoting the
`modalCap` geometric-capacity family to a logic-neutral `geomCap` API. This is a copy/rename/delete
refactor of already-proven arithmetic: no proof changes, no new obligations, zero sorry risk, zero
new axioms. Definition of done: new module builds standalone; all three consumer files build after
repointing; full CI pipeline (build + checkInitImports + lint-style + mk_all + shake) passes; `grep`
finds zero remaining `modalCap` references.

### Research Integration

Report `01_tableau-measure-arithmetic-extraction.md` provides the verified extraction blueprint with
current (corrected) line numbers. Key integrated facts:
- **10 declarations to move** (report Section 5 table): `sum_map_le_length_mul` (private -> public),
  the 7-member `modalCap` family renamed to `geomCap`, and the two byte-identical `pow3_*` lemmas
  (private -> public, deleted from BOTH source files).
- **Target module needs only** `Cslib.Init` + `Mathlib.Tactic.Ring` +
  `Mathlib.Algebra.BigOperators.Group.List.Basic`; `Foundations` sits below `Logics`, so no import
  cycle (report Section 2).
- **Third consumer**: `CompletenessLoop.lean` uses `modalCap`/`modalCap_le_pow`/`modalCap_succ` at
  ~9 sites (report Section 1b) — the rename must touch it.
- **Approach A (full rename, recommended)**: rename all `modalCap*` -> `geomCap*` (report Section 5,
  rejecting the thin-alias Approach B).
- **Zero naming collisions** for `geomCap*`/`sum_map_le_length_mul`/`pow3_*` (report Section 3).
- **Visibility**: `sum_map_le_length_mul` and both `pow3_*` become public; docstrings mandatory
  (docBlame) and must be de-modalized (report Section 4).

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

No ROADMAP.md consulted (no roadmap_path / roadmap_flag in delegation context).

## Goals & Non-Goals

**Goals**:
- Create `Cslib/Foundations/Logic/Tableau/Measure.lean` holding the 10 shared decls under
  `namespace Cslib.Logic.Tableau`, all public with logic-agnostic docstrings.
- Register the new module in the aggregator (`Tableau.lean`) and the barrel (`Cslib.lean`).
- Remove all duplication: delete the moved decls from `FmpMeasure.lean` and delete both local
  `pow3_*` copies from `Classical/Completeness.lean`.
- Repoint every call site (FmpMeasure, CompletenessLoop, Classical/Completeness) to the shared
  `geomCap*` / `sum_map_le_length_mul` / `pow3_*` names.
- Pass the full CI gate with zero sorry and zero new axioms.

**Non-Goals**:
- No new "generic `3^(1+max)`" convenience lemma (report Section 1c: not required for dedup).
- No thin `abbrev modalCap := geomCap` alias (Approach B is rejected).
- No changes to proof content, measure semantics, or downstream theorem statements.
- No refactor of other `FmpMeasure`/`Completeness` code beyond the moved decls and their references.

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Missed `modalCap` reference after rename leaves a build error or dangling comment | M | M | Phase 4 runs `grep -rn "modalCap" Cslib/` and requires zero hits; per-phase builds catch code refs early |
| `geomCap` names not visible in `CompletenessLoop`/`Classical` due to non-re-exporting import | M | M | Use `public import` of `Measure` in `FmpMeasure` (re-export chain) and add a direct `import` in `Classical/Completeness`; verify with per-module builds in Phases 2-3 |
| Barrel (`Cslib.lean`) out of sync after adding a file | L | M | Regenerate with `lake exe mk_all --module`; Phase 4 verifies barrel currency |
| Missing/modal-specific docstring trips docBlame linter | L | L | Author de-modalized docstrings when creating the file (Phase 1); `lint-style` in Phase 4 confirms |
| `@[simp]` attribute on `geomCap_zero` dropped during move | L | L | Explicitly carry `@[simp]` over (report Section 8); simp-set unchanged |
| shake flags a now-unused import in a source file after deletions | L | M | Phase 4 runs `lake shake --add-public --keep-implied --keep-prefix`; apply its suggestions |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2, 3 | 1 |
| 3 | 4 | 2, 3 |

Phases within the same wave can execute in parallel. Phases 2 (Modal: FmpMeasure + CompletenessLoop)
and 3 (Propositional: Classical/Completeness) touch disjoint files once Phase 1 lands.

### Phase 1: Create and register `Measure.lean` [COMPLETED]

- **Goal:** Create the shared module with all 10 declarations (public, `geomCap*` names,
  de-modalized docstrings), register it, and confirm it builds standalone.
- **Tasks:**
  - [ ] Create `Cslib/Foundations/Logic/Tableau/Measure.lean` with the CSLib license header,
    `module` line, and imports exactly:
    `import Cslib.Init`, `import Mathlib.Tactic.Ring`,
    `import Mathlib.Algebra.BigOperators.Group.List.Basic`.
  - [ ] Open `namespace Cslib.Logic.Tableau` ... `end Cslib.Logic.Tableau` around all decls.
  - [ ] Port `sum_map_le_length_mul` from FmpMeasure:131 as a **public** `lemma` (drop `private`),
    proof verbatim, with a logic-agnostic docstring.
  - [ ] Port the 7 `modalCap`-family decls (FmpMeasure:776, 780, 782, 788, 808, 814, and 1664)
    renamed to `geomCap`, `geomCap_zero`, `geomCap_succ`, `geomCap_add_one_le_pow`,
    `geomCap_zero_le_pow`, `geomCap_le_pow`, `geomCap_mul_eq_succ_sub_one`. Keep `geomCap` a `def`
    (returns `Nat`); keep `@[simp]` on `geomCap_zero`; port proofs verbatim (names only change).
  - [ ] Port `pow3_two_add_one_le` (FmpMeasure:2991) and `pow3_add_one_le` (FmpMeasure:3002) as
    **public** lemmas (drop `private`), proofs verbatim, de-modalized docstrings (drop the
    "re-proved locally" note).
  - [ ] Add `public import Cslib.Foundations.Logic.Tableau.Measure` to the aggregator
    `Cslib/Foundations/Logic/Tableau.lean` (alongside the other `public import` lines) and add a
    bullet under its `## Contents` docstring describing the measure arithmetic.
  - [ ] Register in the barrel `Cslib.lean`: run `lake exe mk_all --module` (preferred) OR manually
    insert `public import Cslib.Foundations.Logic.Tableau.Measure` in the sorted block at lines
    100-107 (alphabetically after `...Tableau.ClosureCondition`, before `...Tableau.PropositionalRules`).
- **Timing:** ~1 hour
- **Depends on:** none
- **Verification:** `lake build Cslib.Foundations.Logic.Tableau.Measure` succeeds (module compiles
  standalone). No sorry/warnings in the new file.

---

### Phase 2: Update Modal consumers (FmpMeasure + CompletenessLoop) [COMPLETED]

- **Goal:** Remove the moved decls from `FmpMeasure.lean`, rename all `modalCap*` -> `geomCap*`
  across FmpMeasure and CompletenessLoop, and repoint the moved-utility references to the shared
  module.
- **Tasks:**
  - [ ] Add `public import Cslib.Foundations.Logic.Tableau.Measure` near the top of
    `Cslib/Logics/Modal/Tableau/FmpMeasure.lean` (public so downstream consumers of FmpMeasure — e.g.
    CompletenessLoop — transitively see `geomCap*`).
  - [ ] Delete the moved decls from `FmpMeasure.lean`: `sum_map_le_length_mul` (131), the 7
    `modalCap`-family decls (776, 780, 782, 788, 808, 814, 1664), and the local `pow3_two_add_one_le`
    (2991) + `pow3_add_one_le` (3002) copies.
  - [ ] Rename every remaining `modalCap*` occurrence in `FmpMeasure.lean` to `geomCap*`
    (~57 refs incl. comments/docstrings), and confirm `sum_map_le_length_mul` call sites (156, 166)
    and `pow3_*` call sites (3065, 3082, 3099) now resolve to the shared (bare, via
    `open Cslib.Logic.Tableau`) names.
  - [ ] Rename `modalCap`/`modalCap_le_pow`/`modalCap_succ` -> `geomCap*` in
    `Cslib/Logics/Modal/Tableau/CompletenessLoop.lean` (~9 refs at 66, 164, 166, 169, 173, 174, 184,
    1105, 1112). Verify `open Cslib.Logic.Tableau` is present (it already open-consumes FmpMeasure
    names); if `geomCap*` are not resolved, add `import Cslib.Foundations.Logic.Tableau.Measure`.
  - [ ] Confirm `FmpMeasure.lean` still `open`s / references the shared names unqualified (both
    consumer files already `open Cslib.Logic.Tableau`).
- **Timing:** ~1 hour
- **Depends on:** 1
- **Verification:**
  `lake build Cslib.Logics.Modal.Tableau.FmpMeasure Cslib.Logics.Modal.Tableau.CompletenessLoop`
  succeeds. No sorry/warnings introduced.

---

### Phase 3: Update Propositional consumer (Classical/Completeness) [COMPLETED]

- **Goal:** Delete the duplicate `pow3_*` copies from the classical file and repoint its call sites
  to the shared lemmas.
- **Tasks:**
  - [ ] Add `import Cslib.Foundations.Logic.Tableau.Measure` near the top of
    `Cslib/Logics/Propositional/Tableau/Classical/Completeness.lean`.
  - [ ] Delete the local `pow3_two_add_one_le` (674) and `pow3_add_one_le` (684) private copies.
  - [ ] Repoint call sites to the shared lemmas: `pow3_add_one_le` at 879 and 911,
    `pow3_two_add_one_le` at 904. Confirm the file has `open Cslib.Logic.Tableau` so the bare names
    resolve; if not, either add the `open` or qualify as `Cslib.Logic.Tableau.pow3_*`.
- **Timing:** ~30 minutes
- **Depends on:** 1
- **Verification:**
  `lake build Cslib.Logics.Propositional.Tableau.Classical.Completeness` succeeds. No sorry/warnings
  introduced.

---

### Phase 4: Full CI pipeline verification [PARTIAL]

- **Goal:** Prove the whole library is green, imports/lint/dependency checks pass, and no `modalCap`
  references or sorries remain.
- **Tasks:**
  - [x] **Task 4.1**: `lake exe mk_all --module` -> "No update necessary" (barrel already registered
    in Phase 1).
  - [x] **Task 4.2**: Full build: `lake build` *(deviation: FAILS -- but the only failure is
    `Cslib/Logics/Propositional/Tableau/Intuitionistic/Scheme.lean` (3 "Application type mismatch"
    errors at lines 470, 1074, 1201), a file never touched by this task and unrelated to the
    `modalCap`->`geomCap`/`Measure.lean` extraction. Confirmed pre-existing on `main`: `git diff
    619acd3a HEAD -- .../Intuitionistic/Scheme.lean` is empty (last touched by task 317 phase 1,
    commit `26508fe9`, already merged to `main` before this task began). This is a genuine,
    reproducible build break belonging to task 317's scope, not task 455's. All 4 files this task
    modified/created build individually with zero errors (see Phases 1-3 verifications, all green).)*
  - [ ] **Task 4.3**: `lake exe checkInitImports` *(deviation: blocked -- tool requires all `.olean`
    files to exist; aborts with "object file ... Scheme.olean does not exist" because the full build
    in 4.2 did not complete. Cannot run standalone since it scans the whole build output.)*
  - [x] **Task 4.4**: `lake exe lint-style` -> exits 0, no findings (text-based linter does not
    require compiled `.olean`s, so it ran to completion over the whole tree unaffected by the
    Scheme.lean build break).
  - [ ] **Task 4.5**: `lake shake --add-public --keep-implied --keep-prefix` *(deviation: blocked --
    aborts with "there are out of date oleans; run `lake build` or fetch them from a cache first",
    same root cause as 4.3.)*
  - [x] **Task 4.6**: `grep -rn "modalCap" Cslib/` -> **0 hits** (rename complete, no stale comments;
    confirmed post-Phase-2/3 `sed`-driven rename plus manual doc-comment updates).
  - [x] **Task 4.7**: `grep -n "sorry" Cslib/Foundations/Logic/Tableau/Measure.lean` -> **0 hits**;
    also confirmed 0 hits for `\bsorry\b` and 0 hits for `^axiom ` across all four files this task
    touched (`Measure.lean`, `FmpMeasure.lean`, `CompletenessLoop.lean`,
    `Classical/Completeness.lean`).
- **Timing:** ~30 minutes
- **Depends on:** 2, 3
- **Verification:** `lake exe mk_all --module`, `lake exe lint-style`, and both `grep` guards (zero
  `modalCap`, zero `sorry`/new axioms) all pass. `lake build` (full), `lake exe checkInitImports`,
  and `lake shake ...` cannot complete due to a **pre-existing, unrelated build break** in
  `Cslib/Logics/Propositional/Tableau/Intuitionistic/Scheme.lean` (task 317 scope, untouched by this
  task, already present on `main` before this task's first commit). Every module this task actually
  modified builds green in isolation (Phase 1/2/3 scoped verifications). **BLOCKER** (Phase 4):
  - **What failed**: `lake build` (whole-library), `lake exe checkInitImports`, `lake shake ...`,
    and `lake test` all abort because
    `Cslib/Logics/Propositional/Tableau/Intuitionistic/Scheme.lean` fails to compile with 3
    "Application type mismatch" errors (lines 470, 1074, 1201; each an `ih`-application inside an
    induction proof for `intExpandBranches`/persistence-fixpoint reasoning).
  - **What was tried**: Confirmed the file is byte-identical to the version at commit `619acd3a`
    (pre-task-455 HEAD) via `git diff`; ran `lake exe cache get` to rule out a stale-cache artifact
    (cache already current, "No files to download"); rebuilt the file in isolation twice to rule out
    flakiness (reproduces identically both times).
  - **Why it's stuck**: The failure lives entirely inside task 317's Intuitionistic tableau
    completeness proof (`Scheme.lean`), a file with zero import/reference relationship to this
    task's `Measure.lean`/`FmpMeasure.lean`/`CompletenessLoop.lean`/`Classical/Completeness.lean`
    changes. Fixing it requires understanding task 317's in-progress persistence-fixpoint proof
    strategy, which is out of scope for task 455 per the plan's Non-Goals ("No refactor of other
    ... code beyond the moved decls").
  - **What is needed**: Task 317 (or a dedicated fix task) needs to repair the `ih`-application
    type mismatch in `Scheme.lean` at lines 470/1074/1201. Once that lands, re-run `lake build`,
    `lake exe checkInitImports`, `lake shake --add-public --keep-implied --keep-prefix`, and
    `lake test` -- all four are expected to pass immediately given this task's changes are complete
    and self-contained.
  - **Prohibited workarounds**: Did not touch `Scheme.lean`; did not use `sorry` or any vacuous
    placeholder to paper over the unrelated failure.

## Testing & Validation

- [ ] `lake build Cslib.Foundations.Logic.Tableau.Measure` (Phase 1: standalone module compiles).
- [ ] `lake build Cslib.Logics.Modal.Tableau.FmpMeasure Cslib.Logics.Modal.Tableau.CompletenessLoop`
  (Phase 2: modal consumers green).
- [ ] `lake build Cslib.Logics.Propositional.Tableau.Classical.Completeness` (Phase 3: classical
  consumer green).
- [ ] `lake build` full-library green (Phase 4).
- [ ] `lake exe checkInitImports` passes (Phase 4).
- [ ] `lake exe lint-style` passes (Phase 4).
- [ ] `lake shake --add-public --keep-implied --keep-prefix` passes (Phase 4).
- [ ] `grep -rn "modalCap" Cslib/` returns zero matches (Phase 4).
- [ ] Zero sorry in `Measure.lean`; zero new axioms beyond existing (Phase 4).

## Artifacts & Outputs

- `Cslib/Foundations/Logic/Tableau/Measure.lean` (new module, 10 public decls).
- Modified `Cslib/Foundations/Logic/Tableau.lean` (aggregator: +1 public import + docstring bullet).
- Modified `Cslib.lean` (barrel: +1 public import).
- Modified `Cslib/Logics/Modal/Tableau/FmpMeasure.lean` (import added, 10 decls deleted, refs renamed).
- Modified `Cslib/Logics/Modal/Tableau/CompletenessLoop.lean` (~9 refs renamed).
- Modified `Cslib/Logics/Propositional/Tableau/Classical/Completeness.lean` (import added, 2 decls
  deleted, 3 call sites repointed).
- `specs/455_extract_tableau_measure_arithmetic/summaries/01_measure-arithmetic-extraction-summary.md`
  (implementation summary, produced by /implement).

## Rollback/Contingency

Pure additive-then-subtractive refactor. To revert: `git checkout -- Cslib/` (or revert the task's
commits) restores the pre-refactor state; the new `Measure.lean` is a fresh untracked/added file so
deleting it plus reverting the aggregator/barrel and three consumer edits fully undoes the change.
Because each phase ends with a scoped `lake build`, a failure is caught before proceeding, so
rollback is at most one phase of edits. No data migration or semantic change is involved.
