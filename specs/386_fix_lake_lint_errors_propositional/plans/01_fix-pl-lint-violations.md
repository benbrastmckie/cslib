# Implementation Plan: Task #386 — Fix PL-Specific lake lint Violations

- **Task**: 386 - fix_lake_lint_errors_propositional
- **Status**: [COMPLETED]
- **Effort**: 1.5 hours
- **Dependencies**: None
- **Research Inputs**: specs/386_fix_lake_lint_errors_propositional/reports/01_pl-lint-violations-fix-map.md
- **Artifacts**: plans/01_fix-pl-lint-violations.md (this file)
- **Standards**: plan-format.md; status-markers.md; artifact-management.md; tasks.md
- **Type**: cslib
- **Lean Intent**: false

## Overview

Clear the 20 remaining environment-linter violations under `Cslib/Logics/Propositional/`
(note the `s` — namespace is `Logics`, not `Logic`). All fixes are mechanical: 13
`defsWithUnderscore` renames to lowerCamelCase, 1 `defLemma` conversion (`noncomputable def`
→ `lemma`, fused with a rename), 3 `docBlame` docstring additions on nested `let rec` helpers,
2 `unusedArguments` `@[nolint]` annotations, and 1 `simpNF` `@[nolint]` annotation. There are
no proof obligations, no `sorry`, and no axiom risk. Definition of done: every module under
`Cslib/Logics/Propositional/` reports zero linter errors whose file path is in that namespace,
the full `lake build` stays green, and the repo-wide `lake lint` gate passes.

### Research Integration

Findings from `reports/01_pl-lint-violations-fix-map.md` are integrated directly:
- The exact 20-violation inventory (refreshed against the current green build) drives the phase
  task checklists. `conclusionGrounded` (unusedArguments) is **already fixed** by task 388 and
  is explicitly excluded.
- Call-site analysis: the only cross-file rename consumer is `list_deriv_to_tree`, used at
  `Metalogic/DeductionTheorem.lean:79` (same PL namespace). All 10 LK/LJ `cutAdm_*` / `ljCutAdm_*`
  helpers are intra-file only.
- Modal/Temporal/Bimodal `GenericMCSBridge.lean` copies are separate declarations in separate
  namespaces — **out of scope, do not touch**.
- Verification mechanism: `lake lint` rejects module arguments; use
  `lake exe runLinter Cslib.Logics.Propositional.<Module>` and filter to the module's own file path.
- `vars_neg`'s `simpNF` error leaks into every importing module's lint output, so it is fixed
  first to de-noise the per-module verification of the rename phases.

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

No ROADMAP.md consulted for this task (mechanical lint cleanup; no roadmap_path provided).

## Goals & Non-Goals

**Goals**:
- Eliminate all 20 PL-namespace lint violations (defsWithUnderscore, defLemma, docBlame,
  unusedArguments, simpNF).
- Keep `lake build` green after every phase; pass the repo-wide `lake lint` gate at the end.
- Update the single cross-file rename consumer (`DeductionTheorem.lean:79`) and all intra-file
  call sites / public wrappers so nothing breaks.

**Non-Goals**:
- Do **not** touch the Modal / Temporal / Bimodal `GenericMCSBridge.lean` copies (separate
  declarations, separate namespaces, separate task).
- Do **not** re-touch `conclusionGrounded` in `Normalization/Termination.lean` (already
  `@[nolint unusedArguments]` via task 388).
- Do **not** rewrite the public wrappers `cutAdmissibility` / `ljCutAdmissibility` names (they
  are already underscore-free); only update their internal references to the renamed helpers.
- No new abstractions, no proof refactoring, no behavioral changes.

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| `replace_all` on `cutAdm_right` / `ljCutAdm_right` clobbers substrings (`cutAdm_right_andR`, etc.) | M | M | Rename the longest variants first, or use unique-context single edits. Build after each file. |
| Missing the cross-file consumer `list_deriv_to_tree` at DeductionTheorem.lean:79 | H | L | Phase 2 task list pins the exact call site; verify with `grep -rn list_deriv_to_tree Cslib/` returning zero after rename. |
| `defLemma` fix leaves stale `noncomputable` keyword on `derivTreeToList` | M | L | Phase 2 explicitly drops `noncomputable` when converting `def` → `lemma`. |
| Per-module `runLinter` output polluted by leaked `vars_neg` simpNF error, masking real status | L | M | Fix `vars_neg` (simpNF) in Phase 1 before verifying rename phases. |
| Concurrent edits to DeductionTheorem.lean (P1 nolint + P2 consumer) | M | L | Phase 2 depends on Phase 1; they run sequentially, never concurrently. |
| Accidentally editing a same-named decl in Modal/Temporal/Bimodal copies | H | L | Restrict every edit to paths under `Cslib/Logics/Propositional/`; confirm file path before each edit. |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2, 3, 4 | 1 |

Phases within the same wave can execute in parallel. Phases 2, 3, and 4 touch disjoint files
(GenericMCSBridge+DeductionTheorem vs LK vs LJ) and have no cross-references, so they are
parallel-safe once Phase 1 is done. A single implementation agent may also run them
sequentially. Phase 1 must complete first: it clears the leaked `simpNF` noise that otherwise
pollutes per-module lint verification, and it owns the only other edit to `DeductionTheorem.lean`
(avoiding a concurrent-edit conflict with Phase 2).

---

### Phase 1: Attribute & docstring fixes (simpNF, docBlame, unusedArguments) [COMPLETED]

**Goal**: Clear the 6 non-rename violations — one `simpNF`, three `docBlame`, two
`unusedArguments` — via `@[nolint ...]` annotations and docstrings. No renames, no call-site
changes. Doing `vars_neg` here first de-noises later per-module lint checks.

**Tasks**:
- [ ] `Cslib/Logics/Propositional/Subformula.lean` — add `@[nolint simpNF]` to `vars_neg`
      (near line 175; the `@[simp]` attribute is around line 173). Add a one-line comment:
      LHS `a.neg.vars` is already reducible by `vars_imp` + `vars_bot` + `Finset.union_empty`,
      so the lemma is a convenience restatement kept as a named simp lemma.
- [ ] `Cslib/Logics/Propositional/Tableau/Classical/Expansion.lean` — add a `/-- ... -/`
      docstring immediately above the `let rec processNext` line inside `classicalExpandBranches`
      (linter line ~125).
- [ ] `Cslib/Logics/Propositional/Tableau/Intuitionistic/Expansion.lean` — add a `/-- ... -/`
      docstring immediately above the `let rec go` line inside `intExpandBranches`
      (linter line ~186; note the spec's old line 169 has drifted).
- [ ] `Cslib/Logics/Propositional/Tableau/Intuitionistic/Rules.lean` — add a `/-- ... -/`
      docstring immediately above the `let rec go` line inside `isAccessible` (linter line ~91).
- [ ] `Cslib/Logics/Propositional/Metalogic/DeductionTheorem.lean` — add
      `@[nolint unusedArguments]` directly above the `deductionWithMem` declaration (decl ~line 91)
      plus a comment: arg `_hA : A ∈ Γ'` is an intentional weakening witness in the API signature.
- [ ] `Cslib/Logics/Propositional/Tableau/Intuitionistic/Soundness.lean` — add
      `@[nolint unusedArguments]` directly above the `def intBotForces` line (decl at file line
      ~1647; linter reports the docstring start at ~1643 — place the attribute on the `def` line)
      plus a comment: the `ℕ` world parameter is part of the `botForces` predicate signature.
- [ ] Do NOT touch `conclusionGrounded` in `Normalization/Termination.lean` (already fixed,
      task 388).

**Timing**: ~25 minutes

**Depends on**: none

**Files to modify**:
- `Cslib/Logics/Propositional/Subformula.lean` — `@[nolint simpNF]` + comment on `vars_neg`
- `Cslib/Logics/Propositional/Tableau/Classical/Expansion.lean` — docstring on `processNext`
- `Cslib/Logics/Propositional/Tableau/Intuitionistic/Expansion.lean` — docstring on `intExpandBranches.go`
- `Cslib/Logics/Propositional/Tableau/Intuitionistic/Rules.lean` — docstring on `isAccessible.go`
- `Cslib/Logics/Propositional/Metalogic/DeductionTheorem.lean` — `@[nolint unusedArguments]` + comment on `deductionWithMem`
- `Cslib/Logics/Propositional/Tableau/Intuitionistic/Soundness.lean` — `@[nolint unusedArguments]` + comment on `intBotForces`

**Verification**:
- `lake build Cslib.Logics.Propositional.Subformula` (and the four other touched modules) stays green.
- `lake exe runLinter Cslib.Logics.Propositional.Subformula` — no `simpNF` error for `vars_neg`.
- `lake exe runLinter` on each of the three Tableau modules — no `docBlame` error for the three helpers.
- `lake exe runLinter Cslib.Logics.Propositional.Metalogic.DeductionTheorem` and
  `...Tableau.Intuitionistic.Soundness` — no `unusedArguments` error for `deductionWithMem` / `intBotForces`.

---

### Phase 2: GenericMCSBridge renames + def→lemma + cross-file consumer [COMPLETED]

**Goal**: Rename the 3 PL bridge declarations to lowerCamelCase, convert `deriv_tree_to_list`
to a `lemma` (dropping `noncomputable`), and update the one cross-file consumer plus all in-file
references and docstrings.

**Tasks**:
- [ ] In `Cslib/Logics/Propositional/Metalogic/GenericMCSBridge.lean`:
  - [ ] `deriv_tree_to_list` → `derivTreeToList`, **and** convert `noncomputable def` →
        `lemma` (drop the `noncomputable` keyword; return type is a Prop). Decl ~line 140.
  - [ ] `unfold_listImp_in_tree` → `unfoldListImpInTree` (decl ~line 170).
  - [ ] `list_deriv_to_tree` → `listDerivToTree` (decl ~line 196).
  - [ ] Update in-file call sites: `exact deriv_tree_to_list d` (~line 224),
        `unfold_listImp_in_tree` call (~line 210), `list_deriv_to_tree` call (~line 226).
  - [ ] Update in-file docstring/comment references to the old names (lines ~23, 25, 27, 49, 195)
        to keep docs accurate.
- [ ] `Cslib/Logics/Propositional/Metalogic/DeductionTheorem.lean:79` — update the consumer
      `exact list_deriv_to_tree (...)` → `exact listDerivToTree (...)`. (This is the **only**
      cross-file rename impact.)
- [ ] Do NOT touch Modal / Temporal / Bimodal `GenericMCSBridge.lean` copies.

**Timing**: ~20 minutes

**Depends on**: 1

**Files to modify**:
- `Cslib/Logics/Propositional/Metalogic/GenericMCSBridge.lean` — 3 renames + def→lemma + in-file refs
- `Cslib/Logics/Propositional/Metalogic/DeductionTheorem.lean` — line 79 consumer rename

**Verification**:
- `grep -rn 'deriv_tree_to_list\|unfold_listImp_in_tree\|list_deriv_to_tree' Cslib/Logics/Propositional/`
  returns zero matches (PL namespace only — other-logic copies are expected to remain).
- `lake build Cslib.Logics.Propositional.Metalogic.GenericMCSBridge` and
  `...Metalogic.DeductionTheorem` are green.
- `lake exe runLinter Cslib.Logics.Propositional.Metalogic.GenericMCSBridge` — no
  `defsWithUnderscore` and no `defLemma` errors for the three decls.

---

### Phase 3: LK CutElimination renames [COMPLETED]

**Goal**: Rename the 5 underscore `cutAdm_*` helpers in LK to lowerCamelCase and update all
intra-file call sites including the public wrapper `cutAdmissibility`.

**Tasks**:
- [ ] In `Cslib/Logics/Propositional/SequentCalculus/LK/CutElimination.lean`, rename
      (longest-name-first to avoid substring clobbering):
  - [ ] `cutAdm_right_andR` → `cutAdmRightAndR` (~line 147)
  - [ ] `cutAdm_right_orR` → `cutAdmRightOrR` (~line 295)
  - [ ] `cutAdm_right_impR` → `cutAdmRightImpR` (~line 439)
  - [ ] `cutAdm_right` → `cutAdmRight` (~line 588; lives in the `mutual` block, lines ~584–818)
  - [ ] `cutAdm_left` → `cutAdmLeft` (~line 712)
- [ ] Update all intra-file references, including each helper's mutual recursion calls and the
      public wrapper `cutAdmissibility` (~line 830). Keep `cutAdmissibility`'s own name unchanged.
- [ ] CAUTION with `replace_all`: `cutAdm_right` is a substring of `cutAdm_right_andR` /
      `_orR` / `_impR`. Rename the three `_andR/_orR/_impR` variants first, then `cutAdm_right`,
      then `cutAdm_left` — or use unique-context single edits.

**Timing**: ~20 minutes

**Depends on**: 1

**Files to modify**:
- `Cslib/Logics/Propositional/SequentCalculus/LK/CutElimination.lean` — 5 renames + intra-file call sites + wrapper

**Verification**:
- `grep -n 'cutAdm_' Cslib/Logics/Propositional/SequentCalculus/LK/CutElimination.lean`
  returns zero matches.
- `lake build Cslib.Logics.Propositional.SequentCalculus.LK.CutElimination` is green.
- `lake exe runLinter Cslib.Logics.Propositional.SequentCalculus.LK.CutElimination` — no
  `defsWithUnderscore` errors for the 5 helpers.

---

### Phase 4: LJ CutElimination renames [COMPLETED]

**Goal**: Rename the 5 underscore `ljCutAdm_*` helpers in LJ to lowerCamelCase and update all
intra-file call sites including the public wrapper `ljCutAdmissibility`.

**Tasks**:
- [ ] In `Cslib/Logics/Propositional/SequentCalculus/LJ/CutElimination.lean`, rename
      (longest-name-first to avoid substring clobbering):
  - [ ] `ljCutAdm_principal_andR` → `ljCutAdmPrincipalAndR` (~line 120)
  - [ ] `ljCutAdm_principal_orR` → `ljCutAdmPrincipalOrR` (~line 230)
  - [ ] `ljCutAdm_principal_impR` → `ljCutAdmPrincipalImpR` (~line 353)
  - [ ] `ljCutAdm_left` → `ljCutAdmLeft` (~line 465)
  - [ ] `ljCutAdm_right` → `ljCutAdmRight` (~line 546)
- [ ] Update all intra-file references (LJ uses per-def `termination_by`, no mutual block) and
      the public wrapper `ljCutAdmissibility` (~line 660). Keep `ljCutAdmissibility`'s own name unchanged.
- [ ] CAUTION with `replace_all`: `ljCutAdm_right` is a substring of nothing problematic here,
      but `ljCutAdm_principal_*` share the `ljCutAdm_principal` prefix — rename the full names
      via unique context. Build after editing.

**Timing**: ~20 minutes

**Depends on**: 1

**Files to modify**:
- `Cslib/Logics/Propositional/SequentCalculus/LJ/CutElimination.lean` — 5 renames + intra-file call sites + wrapper

**Verification**:
- `grep -n 'ljCutAdm_' Cslib/Logics/Propositional/SequentCalculus/LJ/CutElimination.lean`
  returns zero matches.
- `lake build Cslib.Logics.Propositional.SequentCalculus.LJ.CutElimination` is green.
- `lake exe runLinter Cslib.Logics.Propositional.SequentCalculus.LJ.CutElimination` — no
  `defsWithUnderscore` errors for the 5 helpers.

---

## Testing & Validation

- [ ] Per-phase: `lake build Cslib.Logics.Propositional.<Module>` green for each touched module.
- [ ] Per-phase: `lake exe runLinter Cslib.Logics.Propositional.<Module>` shows zero errors whose
      file path is under `Cslib/Logics/Propositional/` for that module (filter out the leaked
      `vars_neg` line until Phase 1 is done).
- [ ] Cross-file rename check: `grep -rn 'deriv_tree_to_list\|unfold_listImp_in_tree\|list_deriv_to_tree' Cslib/Logics/Propositional/`
      and `grep -n 'cutAdm_\|ljCutAdm_'` on the two CutElimination files all return zero.
- [ ] Final PL-clean sweep: run `lake exe runLinter` on all 9 touched modules; confirm zero
      PL-path errors.
- [ ] CSLib CI pipeline: `lake build`, `lake test`, `lake exe checkInitImports`,
      `lake exe lint-style`, `lake shake --add-public --keep-implied --keep-prefix`, and the
      repo-wide `lake lint` gate all pass.

## Artifacts & Outputs

- plans/01_fix-pl-lint-violations.md (this plan)
- summaries/01_fix-pl-lint-violations-summary.md (implementation summary, on completion)
- Modified Lean sources (9 files under `Cslib/Logics/Propositional/`):
  - Subformula.lean
  - Tableau/Classical/Expansion.lean
  - Tableau/Intuitionistic/Expansion.lean
  - Tableau/Intuitionistic/Rules.lean
  - Tableau/Intuitionistic/Soundness.lean
  - Metalogic/DeductionTheorem.lean
  - Metalogic/GenericMCSBridge.lean
  - SequentCalculus/LK/CutElimination.lean
  - SequentCalculus/LJ/CutElimination.lean

## Rollback/Contingency

- All changes are mechanical and isolated to 9 files under `Cslib/Logics/Propositional/`.
  Revert is a simple `git checkout -- <file>` (or `git revert` of the per-phase commits) — no
  proof state or downstream API depends on the new names except the intra-PL call sites updated
  in the same phase.
- If a rename breaks a build, the failing `grep`/`lake build` pinpoints the missed call site;
  fix forward by updating the reference rather than reverting the rename.
- If `lake shake` or `lint-style` flags something unrelated surfaced by the rebuild, log it and
  treat as out of scope (the task is lint-only for the PL namespace).
