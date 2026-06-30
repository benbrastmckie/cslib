# Research Report: Cross-Cutting Lint Fixes (Modal/Temporal/Bimodal/Foundations)

**Task**: 406 — Fix 33 pre-existing `lake lint` violations blocking CI globally
**Date**: 2026-06-30
**Agent**: cslib-research-agent
**Status**: researched

## Executive Summary

Task 406 clears 33 environment-linter violations across 9 files in four namespaces. Every
violation falls into one of four mechanical categories — `defLemma`, `defsWithUnderscore`,
`docBlame`, `unusedArguments` — and the fix recipe for each is already established by the
completed **task 386** (Propositional `GenericMCSBridge`/`DeductionTheorem`). This task is the
direct generalization of 386 to the Modal, Temporal, Bimodal, and Foundations copies of the same
declarations. **There is zero file overlap with task 386** (386 touched only
`Cslib/Logics/Propositional/`), so no rename conflicts exist; instead 386 supplies the canonical
target names to reuse verbatim.

**Key correction (high-value finding):** the task description's inline count for Temporal
`GenericMCSBridge.lean` says `defsWithUnderscore x5`, but static inspection finds **6**
underscore-named `def`s (3 base + 3 `_fc`). Using x6 reconciles the headline total exactly:
Modal 6 + Temporal 10 + Bimodal 9 + Foundations 8 = **33**. The implementer should rename all 6.

**Zero-debt note:** all fixes are renames, `def`→`lemma` conversions, `@[nolint ...]` attributes,
and docstring additions. No `sorry`, no new axioms, no proof obligations. CI-green is achievable
mechanically.

**Build caveat:** `lake lint` could not be run to re-confirm the live violation set because the
working tree has an uncommitted edit to `Cslib/Computability/Languages/OmegaRegularLanguage.lean`,
leaving its `.olean` stale (`lake lint` aborts: *"object file ... OmegaRegularLanguage.olean ...
does not exist"*). All findings below are from authoritative static inspection of current file
contents. The implementer must run a full `lake build` before `lake lint` can verify green.

## Reuse Check (CSLib reuse-first)

No new abstractions are introduced or needed. This is pure lint hygiene on existing declarations.
The canonical camelCase target names were already chosen by task 386 and must be reused identically
across the parallel copies for consistency:

| Snake-case (current) | camelCase target (from 386) |
|----------------------|-----------------------------|
| `deriv_tree_to_list` | `derivTreeToList` |
| `unfold_listImp_in_tree` | `unfoldListImpInTree` |
| `list_deriv_to_tree` | `listDerivToTree` |
| `deriv_tree_to_list_fc` | `derivTreeToListFc` |
| `unfold_listImp_in_tree_fc` | `unfoldListImpInTreeFc` |
| `list_deriv_to_tree_fc` | `listDerivToTreeFc` |
| `dt_inference_system` | `dtInferenceSystem` |

The three bridge files live in **distinct namespaces** (`Cslib.Logic.Modal`,
`Cslib.Logic.Temporal`, `Cslib.Logic.Bimodal.Metalogic.Core`) and each **defines its own copy** of
these helpers — they are not cross-imported. Therefore renames are file-local with one documented
exception (Modal `DeductionTheorem.lean`, below). A grep showing the same name across files reflects
independent definitions, not shared references.

## Task 386 Pattern Reference (the recipe template)

386's completed commits establish the exact mechanical recipes:

- **`def`→`lemma` (defLemma)**: a Prop-valued `noncomputable def deriv_tree_to_list ... : (...).Deriv Γ φ`
  becomes `lemma derivTreeToList ...` (drop `noncomputable`; `.Deriv` is a `Prop`). Commit `3ed8c0d4`.
- **`defsWithUnderscore`**: rename declaration to lowerCamelCase; update the docstring mentions and
  every in-file consumer (and the one cross-file consumer). Commit `3ed8c0d4`.
- **`docBlame` on a `let rec`**: insert the attribute inline:
  `let rec @[nolint docBlame] processNext ...`. Commit `8b8b28cb`.
- **`docBlame` on a top-level decl**: add a `/-- ... -/` docstring immediately above it.
- **`unusedArguments`**: add `@[nolint unusedArguments]` attribute above the decl with an
  explanatory comment noting the argument is part of an interface/signature. Commit `8b8b28cb`.

## Complete Violation Inventory (by file)

### MODAL — 6 violations

#### M1. `Cslib/Logics/Modal/Metalogic/GenericMCSBridge.lean` — defLemma x1 + defsWithUnderscore x3
Namespace `Cslib.Logic.Modal` (lines 68–268). No `_fc` variants exist here (confirmed: 0 `_fc`).

| Decl | Line | Lints | Fix |
|------|------|-------|-----|
| `deriv_tree_to_list` | 140 | defLemma + defsWithUnderscore | `noncomputable def deriv_tree_to_list` → `lemma derivTreeToList` |
| `unfold_listImp_in_tree` | 182 | defsWithUnderscore | rename → `unfoldListImpInTree` (stays `noncomputable def`, returns `DerivationTree`) |
| `list_deriv_to_tree` | 208 | defsWithUnderscore | rename → `listDerivToTree` (stays `noncomputable def`) |

In-file consumers to update (docstrings + code):
- Docstring mentions: lines 23, 25, 49, 207.
- Code: line 222 (`unfold_listImp_in_tree`), 236 (`deriv_tree_to_list`), 238 (`list_deriv_to_tree`).

**Cross-file consumer (the only one in the whole task):**
`Cslib/Logics/Modal/Metalogic/DeductionTheorem.lean:73` — `exact list_deriv_to_tree` must become
`exact listDerivToTree`.

#### M2. `Cslib/Logics/Modal/Tableau/Saturation.lean` — docBlame x1
- Target: `modalExpandBranches.processNext`, declared as `let rec processNext` at **line 149**
  (inside `def modalExpandBranches`, line 135).
- Fix: `let rec @[nolint docBlame] processNext`.
- Note: git status flagged this file as modified at session start, but the current working tree has
  **no diff** for it (`git diff`/`git diff --cached` both empty) — the violation is still present
  (line 149 is plain `let rec processNext`).

#### M3. `Cslib/Logics/Modal/Metalogic/DeductionTheorem.lean` — unusedArguments x1
- Target: `deductionWithMem` (line 84). The unused argument is `_hA : A ∈ Γ'` (line 90) — already
  underscore-prefixed for the compiler, but the env linter still flags it.
- Fix: add `@[nolint unusedArguments]` above `noncomputable def deductionWithMem` with a comment
  explaining `_hA` is retained to match the generic-MCS helper signature.

### TEMPORAL — 10 violations (NOT 9; see count correction)

#### T1. `Cslib/Logics/Temporal/Metalogic/GenericMCSBridge.lean` — defLemma x2 + defsWithUnderscore x6
Namespace `Cslib.Logic.Temporal` (lines 56–371). Has both base and `_fc` families.

| Decl | Line | Lints | Fix |
|------|------|-------|-----|
| `deriv_tree_to_list` | 82 | defLemma + defsWithUnderscore | → `lemma derivTreeToList` |
| `unfold_listImp_in_tree` | 137 | defsWithUnderscore | → `unfoldListImpInTree` |
| `list_deriv_to_tree` | 163 | defsWithUnderscore | → `listDerivToTree` |
| `deriv_tree_to_list_fc` | 286 | defLemma + defsWithUnderscore | → `lemma derivTreeToListFc` |
| `unfold_listImp_in_tree_fc` | 325 | defsWithUnderscore | → `unfoldListImpInTreeFc` |
| `list_deriv_to_tree_fc` | 348 | defsWithUnderscore | → `listDerivToTreeFc` |

**Count correction:** task text says `defsWithUnderscore x5`; static inspection finds **6**
underscore `def`s. The headline "33" total only reconciles with x6 (see Validation Math below).
The Bimodal sibling file (B1) is described in the task itself as `defsWithUnderscore x6` with the
identical 6-decl structure, corroborating x6 here.

In-file consumers to update:
- Docstring mentions: lines 21, 23, 25, 44, 162, 347.
- Code: 178 (`unfold_listImp_in_tree`), 191 (`deriv_tree_to_list`), 193 (`list_deriv_to_tree`),
  357 (`unfold_listImp_in_tree_fc`), 368 (`deriv_tree_to_list_fc`), 369 (`list_deriv_to_tree_fc`).
- No external consumers (grep for `*_fc` names outside bridge files returned nothing).

#### T2. `Cslib/Logics/Temporal/Tableau/Saturation.lean` — docBlame x1
- Target: `temporalExpandBranches.processNext`, `let rec processNext` at **line 195** (inside
  `def temporalExpandBranches`, line 180).
- Fix: `let rec @[nolint docBlame] processNext`.

#### T3. `Cslib/Logics/Temporal/Metalogic/DenseMCS.lean` — unusedArguments x1
- Target: `deductionWithMemFc` (declared line 201). Unused argument `_hA : A ∈ Γ'` at **line 203**.
- Fix: `@[nolint unusedArguments]` + comment above `noncomputable def deductionWithMemFc`.

### BIMODAL — 9 violations

#### B1. `Cslib/Logics/Bimodal/Metalogic/Core/GenericMCSBridge.lean` — defLemma x2 + defsWithUnderscore x6
Namespace `Cslib.Logic.Bimodal.Metalogic.Core` (lines 66–406). Same 6-decl structure as Temporal.

| Decl | Line | Lints | Fix |
|------|------|-------|-----|
| `deriv_tree_to_list` | 94 | defLemma + defsWithUnderscore | → `lemma derivTreeToList` |
| `unfold_listImp_in_tree` | 161 | defsWithUnderscore | → `unfoldListImpInTree` |
| `list_deriv_to_tree` | 187 | defsWithUnderscore | → `listDerivToTree` |
| `deriv_tree_to_list_fc` | 314 | defLemma + defsWithUnderscore | → `lemma derivTreeToListFc` |
| `unfold_listImp_in_tree_fc` | 359 | defsWithUnderscore | → `unfoldListImpInTreeFc` |
| `list_deriv_to_tree_fc` | 383 | defsWithUnderscore | → `listDerivToTreeFc` |

In-file consumers: implementer must re-grep within this file (the `*_iff_algebraic` /
`*_iff_algebraic_fc` theorems and docstrings) — structurally identical to Temporal/Modal. No
external consumers found.

#### B2. `Cslib/Logics/Bimodal/Metalogic/Core/DeductionTheorem.lean` — unusedArguments x1
- Target: `deductionWithMem` (declared line 112). Unused argument `_hA : A ∈ Γ'` at **line 114**.
- Fix: `@[nolint unusedArguments]` + comment above `noncomputable def deductionWithMem`.

### FOUNDATIONS — 8 violations

#### F1. `Cslib/Foundations/Order/HilbertAlgebra/FreeMeetExtension.lean` — docBlame x7
(Path note: file is under `Foundations/Order/HilbertAlgebra/`, not `Foundations/Mathlib/...`.)
All 7 decls confirmed to lack a `/-- ... -/` docstring (preceding line is blank or a `/-! -/`
section header, which does not satisfy docBlame):

| Decl | Line | Kind | Fix |
|------|------|------|-----|
| `fld` | 50 | `abbrev` | add docstring (multiset right-fold of `⇨`) |
| `fmeLe` | 106 | `def ... : Prop` | add docstring (pre-order on multisets) |
| `fmeEquiv` | 123 | `def ... : Prop` | add docstring (antisymmetric closure) |
| `fmeSetoid` | 125 | `def ... : Setoid` | add docstring |
| `FreeMeetExtension` | 152 | `def` (quotient type) | add docstring |
| `mk` | 159 | `def` | add docstring (quotient constructor) |
| `freeMeetEmbed` | 257 | `def` | add docstring (singleton embedding `a ↦ mk {a}`) |

**Note (not a violation):** `fmeLe`/`fmeEquiv` are `def`s producing `Prop` but their *own* type is
`Multiset H → Multiset H → Prop` (a `Sort`, not a `Prop`), so they are **not** `defLemma` targets —
they are predicate definitions and correctly remain `def`. Task is right to list only docBlame here.

#### F2. `Cslib/Foundations/Logic/Metalogic/DeductionCharacterization.lean` — defsWithUnderscore x1
- Target: `instance dt_inference_system` at **line 109** (`InferenceSystem (DtSystem D hdt) F`).
- Fix: rename → `dtInferenceSystem`. Only consumer is this same file (grep: no other file
  references `dt_inference_system`). Check downstream uses of the instance are by-type (instance
  resolution), so the rename is safe; update any explicit by-name references inside this file.

## Validation Math (reconciles the "33")

| Namespace | defLemma | defsWithUnderscore | docBlame | unusedArguments | Subtotal |
|-----------|----------|--------------------|----------|-----------------|----------|
| Modal | 1 | 3 | 1 | 1 | 6 |
| Temporal | 2 | **6** | 1 | 1 | **10** |
| Bimodal | 2 | 6 | 0 | 1 | 9 |
| Foundations | 0 | 1 | 7 | 0 | 8 |
| **Total** | 5 | 16 | 9 | 3 | **33** |

Using the task's literal Temporal `x5` yields 32, off by one from the stated 33. The x6 reading
(matching the structurally identical Bimodal file) yields exactly 33. **Adopt x6.**

## Fix Recipes (mechanical, per lint type)

1. **defLemma** (`deriv_tree_to_list*` only): change `noncomputable def <snake>` to `lemma <camel>`
   (delete `noncomputable`; the body is a tactic proof of a `.Deriv` `Prop`). This simultaneously
   discharges the defsWithUnderscore warning on the same decl.
2. **defsWithUnderscore** (rename): replace the declaration name with the camelCase target from the
   reuse table, then update (a) the decl's own docstring, (b) all in-file consumers, (c) the single
   cross-file consumer (Modal `DeductionTheorem.lean:73`). Use the line maps above; re-grep each
   file after renaming to catch docstring mentions.
3. **docBlame on `let rec`** (`processNext` ×2): insert `@[nolint docBlame]` between `let rec` and
   the name: `let rec @[nolint docBlame] processNext`.
4. **docBlame on top-level decls** (FreeMeetExtension ×7): add a one-to-three line `/-- ... -/`
   docstring directly above each decl.
5. **unusedArguments** (`deductionWithMem`/`deductionWithMemFc`, ×3): add
   `@[nolint unusedArguments]` above the `noncomputable def`, preceded by a `-- ` comment explaining
   `_hA` is kept to match the deduction-theorem helper signature.

## Recommended Implementation Ordering

Suggest grouping by namespace (each independently buildable), bridge files first since they carry
the rename ripple:

1. **Modal** — GenericMCSBridge renames + def→lemma → fix `DeductionTheorem.lean:73` cross-ref →
   Saturation docBlame → DeductionTheorem nolint. Build Modal.
2. **Temporal** — GenericMCSBridge (all 6 renames + 2 def→lemma) → Saturation docBlame →
   DenseMCS nolint. Build Temporal.
3. **Bimodal** — Core/GenericMCSBridge (6 renames + 2 def→lemma) → Core/DeductionTheorem nolint.
   Build Bimodal.
4. **Foundations** — FreeMeetExtension 7 docstrings → DeductionCharacterization instance rename.
   Build Foundations.
5. Full `lake build` then `lake lint` to verify zero violations remain in these 9 files.

## Cross-Check Against Task 386

- 386 (`[COMPLETED]`) applied the identical rename set + def→lemma to
  `Cslib/Logics/Propositional/Metalogic/{GenericMCSBridge,DeductionTheorem}.lean` and the LK/LJ
  `CutElimination` files. **None of 406's 9 files were touched by 386** → no rename collisions.
- 406 must **reuse 386's exact camelCase targets** (table above) so the four parallel bridge files
  stay name-consistent with the Propositional original.
- ABSORBS stale task 394 (per task description). No 394 artifacts need preservation here.

## Risks / Watch-Items for Implementer

- **Stale build blocks lint**: run `lake build` (resolving the OmegaRegularLanguage olean) before
  trusting any `lake lint` output. Until then, lint aborts with the olean-missing exception.
- **Modal cross-file ref**: `DeductionTheorem.lean:73` is the single rename that escapes its bridge
  file — easy to miss; it is the only `list_deriv_to_tree` consumer outside the bridges.
- **Instance rename safety**: `dt_inference_system` is resolved by typeclass search at most use
  sites, so renaming the binder name is safe; only by-name references (within its own file) need
  edits.
- **Count discrepancy**: trust x6 for Temporal defsWithUnderscore; do not stop at 5.
- **Docstring style**: FreeMeetExtension docstrings must be real `/-- -/` doc comments (not `/-! -/`
  section headers) to satisfy docBlame.

## Tactic Survey

Not applicable — no proof goals are created or modified. All changes are signature/attribute/name/
docstring edits that preserve existing proof bodies verbatim.
