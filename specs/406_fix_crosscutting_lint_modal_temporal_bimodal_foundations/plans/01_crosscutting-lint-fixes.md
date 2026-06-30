# Implementation Plan: Task #406 — Cross-Cutting Lint Fixes (Modal/Temporal/Bimodal/Foundations)

- **Task**: 406 - Fix cross-cutting `lake lint` violations across Modal/Temporal/Bimodal/Foundations (33)
- **Status**: [COMPLETED]
- **Effort**: 3 hours
- **Dependencies**: None (zero file overlap with task 386; 386 is [COMPLETED] and supplies canonical target names)
- **Research Inputs**: reports/01_crosscutting-lint-fixes.md
- **Artifacts**: plans/01_crosscutting-lint-fixes.md (this file)
- **Standards**: plan-format.md; status-markers.md; artifact-management.md; tasks.md
- **Type**: cslib
- **Lean Intent**: false

## Overview

Task 406 clears 33 environment-linter (`lake lint`) violations across 9 files in four
namespaces (Modal, Temporal, Bimodal, Foundations). Every violation is one of four mechanical
categories — `defLemma`, `defsWithUnderscore`, `docBlame`, `unusedArguments` — and the fix recipe
for each is already established by completed **task 386** (the Propositional copies of the same
declarations). All changes are renames (snake_case → lowerCamelCase), `def`→`lemma` conversions,
`@[nolint ...]` attributes with explanatory comments, and docstring additions. **No `sorry`, no
new axioms, no proof obligations.** Definition of done: full `lake build` succeeds, then
`lake lint` reports zero violations across these 9 files.

### Research Integration

Integrated from `reports/01_crosscutting-lint-fixes.md`:
- **Exact violation inventory** (file + line + lint type + fix) for all 33 violations.
- **Canonical camelCase targets** reused verbatim from task 386 (`derivTreeToList`,
  `unfoldListImpInTree`, `listDerivToTree`, `derivTreeToListFc`, `unfoldListImpInTreeFc`,
  `listDerivToTreeFc`, `dtInferenceSystem`).
- **Count correction**: Temporal `GenericMCSBridge.lean` has **6** underscore `def`s (not the
  task's literal x5); x6 reconciles the headline total to exactly 33. Implementer must rename all 6.
- **Single cross-file consumer**: `Cslib/Logics/Modal/Metalogic/DeductionTheorem.lean:73`
  references `list_deriv_to_tree` → must become `listDerivToTree`. This is the only rename that
  escapes a bridge file.
- **Build caveat**: `lake lint` aborts when an `.olean` is stale (the working tree currently has
  an uncommitted edit to `OmegaRegularLanguage.lean`). A full `lake build` is required before
  `lake lint` will run. The final phase enforces build-before-lint.
- **Foundations note**: `fmeLe`/`fmeEquiv` are `def`s producing `Prop` but their own type is a
  `Sort` (predicate definitions), so they are **not** `defLemma` targets — docBlame only.
- **Style note**: Foundations docstrings must be real `/-- ... -/` doc comments, not `/-! ... -/`
  section headers, to satisfy docBlame.

### Prior Plan Reference

No prior plan. Task 386 (the Propositional sibling) is [COMPLETED] and serves as the recipe
template; its commits (`3ed8c0d4`, `8b8b28cb`) establish the exact mechanical patterns. No prior
plan content is templated — 406 reuses 386's *target names* only.

### Roadmap Alignment

No `roadmap_path` provided to this invocation; ROADMAP.md not consulted. This task is repository
hygiene (CI green gate), not a roadmap-feature task.

## Goals & Non-Goals

**Goals**:
- Eliminate all 33 `lake lint` violations across the 9 enumerated files.
- Reuse task 386's exact camelCase target names so the four parallel bridge files stay
  name-consistent with the Propositional original.
- Keep the build green per phase (scoped `lake build` of touched modules after each phase).
- Confirm zero violations via full `lake build` then `lake lint` in the final phase.

**Non-Goals**:
- No new abstractions, lemmas, or refactors beyond the mechanical lint fixes.
- No changes to proof bodies (renames and attributes preserve existing proofs verbatim).
- No touching task 386's Propositional files (zero overlap; already complete).
- No fix to the unrelated `OmegaRegularLanguage.lean` working-tree edit beyond ensuring the build
  succeeds for lint to run (if that edit blocks the build, rebuild/resolve it as a prerequisite of
  the final verification, not as task-406 scope).

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Missing the single cross-file consumer (`DeductionTheorem.lean:73`) | M | M | Phase 1 explicitly edits line 73 and re-greps `list_deriv_to_tree` repo-wide after the Modal renames |
| Stopping at 5 Temporal underscore renames instead of 6 | M | M | Phase 2 lists all 6 decls with line numbers; verify count via post-rename grep for residual `_` names |
| Stale `.olean` (OmegaRegularLanguage edit) aborts `lake lint` | M | H | Final phase runs full `lake build` first; only run `lake lint` after a clean build |
| Docstring written as `/-! -/` section header (does not satisfy docBlame) | L | M | Phase 4 requires `/-- ... -/` doc comments on each of the 7 Foundations decls |
| Instance rename (`dt_inference_system`) breaks by-name references | L | L | Resolution is mostly by-type; Phase 4 greps for and updates any by-name references inside the same file |
| Residual docstring/code mentions of old snake_case names left behind | M | M | Each bridge-file phase re-greps the old names within the file after editing (docstrings + code) |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 1 | 2 | -- |
| 1 | 3 | -- |
| 1 | 4 | -- |
| 2 | 5 | 1, 2, 3, 4 |

Phases 1–4 are file-disjoint (distinct namespaces, file-local renames with one documented Modal
cross-file edit contained within Phase 1) and may run in parallel. Phase 5 is the integration
verification gate and depends on all of them. For sequential execution, run 1 → 2 → 3 → 4 → 5.

---

### Phase 1: Modal files + cross-file call site [COMPLETED]

**Goal**: Clear all 6 Modal violations and update the single cross-file consumer.

**Files to modify**:
- `Cslib/Logics/Modal/Metalogic/GenericMCSBridge.lean` — defLemma x1 + defsWithUnderscore x3
- `Cslib/Logics/Modal/Metalogic/DeductionTheorem.lean` — unusedArguments x1 + cross-file rename ref
- `Cslib/Logics/Modal/Tableau/Saturation.lean` — docBlame x1

**Tasks**:
- [ ] `GenericMCSBridge.lean` line 140: `noncomputable def deriv_tree_to_list` → `lemma derivTreeToList` (drop `noncomputable`; body is a tactic proof of a `.Deriv` `Prop`). Fixes defLemma + defsWithUnderscore.
- [ ] `GenericMCSBridge.lean` line 182: rename `unfold_listImp_in_tree` → `unfoldListImpInTree` (stays `noncomputable def`, returns `DerivationTree`).
- [ ] `GenericMCSBridge.lean` line 208: rename `list_deriv_to_tree` → `listDerivToTree` (stays `noncomputable def`).
- [ ] Update in-file docstring mentions: lines 23, 25, 49, 207.
- [ ] Update in-file code consumers: line 222 (`unfold_listImp_in_tree`), 236 (`deriv_tree_to_list`), 238 (`list_deriv_to_tree`).
- [ ] **Cross-file**: `DeductionTheorem.lean:73` — `exact list_deriv_to_tree` → `exact listDerivToTree`.
- [ ] `DeductionTheorem.lean` line 84: add `@[nolint unusedArguments]` above `noncomputable def deductionWithMem`, preceded by a `-- ` comment noting `_hA : A ∈ Γ'` (line 90) is retained to match the generic-MCS helper signature.
- [ ] `Saturation.lean` line 149: change `let rec processNext` → `let rec @[nolint docBlame] processNext` (inside `def modalExpandBranches`, line 135).
- [ ] Re-grep the three old snake_case names repo-wide to confirm no remaining references (expect only `listDerivToTree` now reachable from `DeductionTheorem.lean`).

**Timing**: 45 minutes

**Depends on**: none

**Verification**:
- `lake build Cslib.Logics.Modal.Metalogic.GenericMCSBridge Cslib.Logics.Modal.Metalogic.DeductionTheorem Cslib.Logics.Modal.Tableau.Saturation` succeeds.
- `grep -rn 'deriv_tree_to_list\|unfold_listImp_in_tree\|list_deriv_to_tree' Cslib/Logics/Modal/` returns nothing.

---

### Phase 2: Temporal files [COMPLETED]

**Goal**: Clear all 10 Temporal violations (2 defLemma + 6 defsWithUnderscore + 1 docBlame + 1 unusedArguments).

**Files to modify**:
- `Cslib/Logics/Temporal/Metalogic/GenericMCSBridge.lean` — defLemma x2 + defsWithUnderscore x6
- `Cslib/Logics/Temporal/Tableau/Saturation.lean` — docBlame x1
- `Cslib/Logics/Temporal/Metalogic/DenseMCS.lean` — unusedArguments x1

**Tasks**:
- [ ] `GenericMCSBridge.lean` line 82: `noncomputable def deriv_tree_to_list` → `lemma derivTreeToList` (defLemma + defsWithUnderscore).
- [ ] `GenericMCSBridge.lean` line 137: `unfold_listImp_in_tree` → `unfoldListImpInTree`.
- [ ] `GenericMCSBridge.lean` line 163: `list_deriv_to_tree` → `listDerivToTree`.
- [ ] `GenericMCSBridge.lean` line 286: `noncomputable def deriv_tree_to_list_fc` → `lemma derivTreeToListFc` (defLemma + defsWithUnderscore).
- [ ] `GenericMCSBridge.lean` line 325: `unfold_listImp_in_tree_fc` → `unfoldListImpInTreeFc`.
- [ ] `GenericMCSBridge.lean` line 348: `list_deriv_to_tree_fc` → `listDerivToTreeFc`.
- [ ] Update in-file docstring mentions: lines 21, 23, 25, 44, 162, 347.
- [ ] Update in-file code consumers: line 178 (`unfold_listImp_in_tree`), 191 (`deriv_tree_to_list`), 193 (`list_deriv_to_tree`), 357 (`unfold_listImp_in_tree_fc`), 368 (`deriv_tree_to_list_fc`), 369 (`list_deriv_to_tree_fc`).
- [ ] **Count check**: confirm all 6 underscore `def`s renamed (not 5 — the task's literal count is wrong; see research §Validation Math).
- [ ] `Saturation.lean` line 195: `let rec processNext` → `let rec @[nolint docBlame] processNext` (inside `def temporalExpandBranches`, line 180).
- [ ] `DenseMCS.lean` line 201: add `@[nolint unusedArguments]` + explanatory comment above `noncomputable def deductionWithMemFc` (unused arg `_hA : A ∈ Γ'` at line 203).

**Timing**: 45 minutes

**Depends on**: none

**Verification**:
- `lake build Cslib.Logics.Temporal.Metalogic.GenericMCSBridge Cslib.Logics.Temporal.Tableau.Saturation Cslib.Logics.Temporal.Metalogic.DenseMCS` succeeds.
- `grep -rn 'deriv_tree_to_list\|unfold_listImp_in_tree\|list_deriv_to_tree' Cslib/Logics/Temporal/` returns nothing.

---

### Phase 3: Bimodal files [COMPLETED]

**Goal**: Clear all 9 Bimodal violations (2 defLemma + 6 defsWithUnderscore + 1 unusedArguments).

**Files to modify**:
- `Cslib/Logics/Bimodal/Metalogic/Core/GenericMCSBridge.lean` — defLemma x2 + defsWithUnderscore x6
- `Cslib/Logics/Bimodal/Metalogic/Core/DeductionTheorem.lean` — unusedArguments x1

**Tasks**:
- [ ] `GenericMCSBridge.lean` line 94: `noncomputable def deriv_tree_to_list` → `lemma derivTreeToList`.
- [ ] `GenericMCSBridge.lean` line 161: `unfold_listImp_in_tree` → `unfoldListImpInTree`.
- [ ] `GenericMCSBridge.lean` line 187: `list_deriv_to_tree` → `listDerivToTree`.
- [ ] `GenericMCSBridge.lean` line 314: `noncomputable def deriv_tree_to_list_fc` → `lemma derivTreeToListFc`.
- [ ] `GenericMCSBridge.lean` line 359: `unfold_listImp_in_tree_fc` → `unfoldListImpInTreeFc`.
- [ ] `GenericMCSBridge.lean` line 383: `list_deriv_to_tree_fc` → `listDerivToTreeFc`.
- [ ] Re-grep this file for in-file consumers (docstrings + the `*_iff_algebraic` / `*_iff_algebraic_fc` theorems, structurally identical to Temporal/Modal) and update each occurrence of all 6 old names.
- [ ] `DeductionTheorem.lean` line 112: add `@[nolint unusedArguments]` + explanatory comment above `noncomputable def deductionWithMem` (unused arg `_hA : A ∈ Γ'` at line 114).

**Timing**: 40 minutes

**Depends on**: none

**Verification**:
- `lake build Cslib.Logics.Bimodal.Metalogic.Core.GenericMCSBridge Cslib.Logics.Bimodal.Metalogic.Core.DeductionTheorem` succeeds.
- `grep -rn 'deriv_tree_to_list\|unfold_listImp_in_tree\|list_deriv_to_tree' Cslib/Logics/Bimodal/` returns nothing.

---

### Phase 4: Foundations files [COMPLETED]

**Goal**: Clear all 8 Foundations violations (7 docBlame + 1 defsWithUnderscore).

**Files to modify**:
- `Cslib/Foundations/Order/HilbertAlgebra/FreeMeetExtension.lean` — docBlame x7
- `Cslib/Foundations/Logic/Metalogic/DeductionCharacterization.lean` — defsWithUnderscore x1

**Tasks**:
- [ ] `FreeMeetExtension.lean` line 50: add `/-- ... -/` docstring above `abbrev fld` (multiset right-fold of `⇨`).
- [ ] `FreeMeetExtension.lean` line 106: add docstring above `def fmeLe` (pre-order on multisets). Note: stays `def` — predicate definition, NOT a defLemma target.
- [ ] `FreeMeetExtension.lean` line 123: add docstring above `def fmeEquiv` (antisymmetric closure). Stays `def`.
- [ ] `FreeMeetExtension.lean` line 125: add docstring above `def fmeSetoid`.
- [ ] `FreeMeetExtension.lean` line 152: add docstring above `def FreeMeetExtension` (quotient type).
- [ ] `FreeMeetExtension.lean` line 159: add docstring above `def mk` (quotient constructor).
- [ ] `FreeMeetExtension.lean` line 257: add docstring above `def freeMeetEmbed` (singleton embedding `a ↦ mk {a}`).
- [ ] Ensure all 7 docstrings are real `/-- ... -/` doc comments (not `/-! ... -/` section headers).
- [ ] `DeductionCharacterization.lean` line 109: rename `instance dt_inference_system` → `dtInferenceSystem`. Grep within this file for any by-name references and update them (instance resolution is by-type, so this is safe).

**Timing**: 30 minutes

**Depends on**: none

**Verification**:
- `lake build Cslib.Foundations.Order.HilbertAlgebra.FreeMeetExtension Cslib.Foundations.Logic.Metalogic.DeductionCharacterization` succeeds.
- `grep -rn 'dt_inference_system' Cslib/Foundations/` returns nothing.

---

### Phase 5: Full build + `lake lint` green verification [COMPLETED]

**Goal**: Confirm zero `lake lint` violations remain across all 9 touched files.

**Tasks**:
- [ ] Run full `lake build` (resolves the stale `OmegaRegularLanguage.olean` so lint can run). Confirm it succeeds. If the build fails due to the pre-existing uncommitted `OmegaRegularLanguage.lean` edit, rebuild until clean before proceeding.
- [ ] Run `lake lint` and confirm zero violations in the 9 task-406 files.
- [ ] Run the rest of the CSLib CI pipeline if applicable: `lake test`, `lake exe checkInitImports`, `lake exe lint-style`.
- [ ] Spot-check that no proof bodies changed (the only edits are names, attributes, docstrings) and no `sorry`/axioms were introduced.

**Timing**: 20 minutes

**Depends on**: 1, 2, 3, 4

**Verification**:
- `lake build` exits 0.
- `lake lint` reports 0 violations for the 9 files (defLemma 5, defsWithUnderscore 16, docBlame 9, unusedArguments 3 — all cleared; 33 total).

---

## Testing & Validation

- [ ] Per-phase scoped `lake build` of touched modules succeeds (Phases 1–4).
- [ ] Per-phase grep confirms no residual snake_case names in the namespace just edited.
- [ ] Final full `lake build` succeeds (prerequisite for lint).
- [ ] Final `lake lint` reports zero violations across the 9 files.
- [ ] `lake test`, `lake exe checkInitImports`, `lake exe lint-style` pass (CSLib CI gate).
- [ ] No `sorry`, no new axioms, no proof-body changes introduced.

## Artifacts & Outputs

- `specs/406_fix_crosscutting_lint_modal_temporal_bimodal_foundations/plans/01_crosscutting-lint-fixes.md` (this plan)
- Edits to 9 source files (Modal x3, Temporal x3, Bimodal x2, Foundations x2)
- `specs/406_fix_crosscutting_lint_modal_temporal_bimodal_foundations/summaries/01_crosscutting-lint-fixes-summary.md` (on completion)

## Rollback/Contingency

All changes are mechanical and file-local (one documented Modal cross-file edit). If any phase
breaks the build: `git checkout -- <file>` reverts that file's edits without affecting other
phases (phases are file-disjoint). Because there are no proof obligations, a failed build after a
rename almost always indicates a missed consumer reference — re-grep the old name and update the
remaining call site rather than reverting. The single highest-risk cross-file edit
(`DeductionTheorem.lean:73`) is isolated to Phase 1 and verified by repo-wide grep.
