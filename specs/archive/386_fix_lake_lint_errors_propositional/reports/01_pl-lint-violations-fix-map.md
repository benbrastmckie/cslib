# Research Report: Fix PL-Specific lake lint Violations (Task 386)

- **Task**: 386 — fix_lake_lint_errors_propositional
- **Session**: sess_1782817543_eee5ae_386
- **Agent**: cslib-research-agent
- **Date**: 2026-06-30
- **Status**: research complete (RESEARCHED)

## Executive Summary

The task description targets `Cslib/Logic/Propositional/`, but the actual namespace
path is **`Cslib/Logics/Propositional/`** (note the `s`). All declarations were located
by name (line numbers in the pre-merge spec have drifted in places). The environment
linter was re-run per-module via `lake exe runLinter <Module>` against the current
(green) build to refresh the exact violation set.

**Refreshed violation count: 20 remaining (not 21).** One target — `conclusionGrounded`
(unusedArguments) — is **already fixed**: it carries `@[nolint unusedArguments]` (added by
task 388, commit 5d2a87b2). All other 20 violations are confirmed present.

No rename in this task crosses a module boundary into another logic namespace
(Modal/Temporal/Bimodal). The only cross-file rename impact is **within** the Propositional
namespace: `list_deriv_to_tree` is consumed by `Metalogic/DeductionTheorem.lean:79`.

The task description's reference to "task (403)" for coordinating GenericMCSBridge renames is
**stale**: task 403 in current numbering is "Rename specs 384 to 402" (COMPLETED, bookkeeping
only). The PL GenericMCSBridge declarations are independent of the Modal/Temporal/Bimodal
copies, so no cross-task coordination is actually required for task 386 to proceed.

## How to Refresh / Verify the Violation Set

`lake lint` (no args) drives `batteries/runLinter` over the default target and does **not**
accept a module argument (`lake lint Cslib.X` errors with "unexpected arguments").
Use the underlying executable directly to scope to a module:

```bash
lake exe runLinter Cslib.Logics.Propositional.<Module>
```

Note: `runLinter <Module>` reports violations for declarations in the module's full import
closure (e.g. `vars_neg` from `Subformula` surfaces in every importing module). When counting
"this module's own" violations, filter the output by the file path that matches the module.

## Confirmed Violation Inventory (current build, refreshed)

### (a) defsWithUnderscore (13) — rename to lowerCamelCase

| File (Cslib/Logics/Propositional/...) | Line | Current name | Proposed name |
|---|---|---|---|
| Metalogic/GenericMCSBridge.lean | 140 (decl); linter 133 | `deriv_tree_to_list` | `derivTreeToList` |
| Metalogic/GenericMCSBridge.lean | 170 (decl); linter 165 | `unfold_listImp_in_tree` | `unfoldListImpInTree` |
| Metalogic/GenericMCSBridge.lean | 196 (decl); linter 192 | `list_deriv_to_tree` | `listDerivToTree` |
| SequentCalculus/LJ/CutElimination.lean | 120; linter 116 | `ljCutAdm_principal_andR` | `ljCutAdmPrincipalAndR` |
| SequentCalculus/LJ/CutElimination.lean | 230; linter 225 | `ljCutAdm_principal_orR` | `ljCutAdmPrincipalOrR` |
| SequentCalculus/LJ/CutElimination.lean | 353; linter 350 | `ljCutAdm_principal_impR` | `ljCutAdmPrincipalImpR` |
| SequentCalculus/LJ/CutElimination.lean | 465; linter 462 | `ljCutAdm_left` | `ljCutAdmLeft` |
| SequentCalculus/LJ/CutElimination.lean | 546; linter 543 | `ljCutAdm_right` | `ljCutAdmRight` |
| SequentCalculus/LK/CutElimination.lean | 147; linter 145 | `cutAdm_right_andR` | `cutAdmRightAndR` |
| SequentCalculus/LK/CutElimination.lean | 295; linter 293 | `cutAdm_right_orR` | `cutAdmRightOrR` |
| SequentCalculus/LK/CutElimination.lean | 439; linter 437 | `cutAdm_right_impR` | `cutAdmRightImpR` |
| SequentCalculus/LK/CutElimination.lean | 588; linter 586 | `cutAdm_right` | `cutAdmRight` |
| SequentCalculus/LK/CutElimination.lean | 712; linter 708 | `cutAdm_left` | `cutAdmLeft` |

Collision check: `grep` for all 13 proposed camelCase names across `Cslib/**.lean` returned
**no existing declarations** — safe to rename.

### (b) defLemma (1) — same decl as the first rename

- `Metalogic/GenericMCSBridge.lean:140` `deriv_tree_to_list` is
  `noncomputable def` returning `(propAlgDS Axioms).Deriv Γ φ` (a Prop). Linter:
  "is a def, should be lemma/theorem". Convert to `lemma derivTreeToList ...` and **drop the
  `noncomputable` keyword** (lemmas are always in Prop). The rename (a) and the def→lemma
  change are a single edit on the same declaration line.

### (c) docBlame (3) — add docstrings to nested helpers

| File | Linter line | Nested decl | Structure |
|---|---|---|---|
| Tableau/Classical/Expansion.lean | 125 | `classicalExpandBranches.processNext` | `let rec processNext` inside `classicalExpandBranches` |
| Tableau/Intuitionistic/Expansion.lean | 186 (spec said 169 — **drifted**) | `intExpandBranches.go` | `let rec go` inside `intExpandBranches` |
| Tableau/Intuitionistic/Rules.lean | 91 | `isAccessible.go` | `let rec go` inside `isAccessible` |

Fix: add a `/-- ... -/` docstring immediately above each `let rec` line. These are nested
`let rec` declarations; docBlame requires a docstring on them just like top-level defs.

### (d) unusedArguments (2 remaining — 1 already done)

| File | Linter line | Decl / arg | Action |
|---|---|---|---|
| Metalogic/DeductionTheorem.lean | 85 (decl at 91) | `deductionWithMem` arg 9 `_hA : A ∈ Γ'` | add `@[nolint unusedArguments]` + comment |
| Tableau/Intuitionistic/Soundness.lean | 1643 (decl `def intBotForces` at 1647) | `intBotForces` arg 1 `: ℕ` | add `@[nolint unusedArguments]` + comment |
| ~~Normalization/Termination.lean~~ | ~~41~~ | ~~`conclusionGrounded` arg `_d`~~ | **ALREADY FIXED** — `@[nolint unusedArguments]` present at line 42 (task 388) |

`_hA` and `intBotForces`'s argument are intentionally part of the API/semantics signature
(weakening witness; the `Nat` world parameter of the `botForces` predicate), so `@[nolint
unusedArguments]` with an explanatory comment is the correct fix rather than deletion.

### (e) simpNF (1)

- `Subformula.lean:175` (linter reports 173, the `@[simp]` attribute line) `vars_neg`.
  Linter detail (refreshed): LHS `a.neg.vars` simplifies to `a.vars ∪ Proposition.bot.vars`
  via the existing simp lemma `vars_imp` (since `¬a` is `a → ⊥`). The lemma is therefore not
  in simp-normal form — its LHS is already reducible by other `@[simp]` lemmas
  (`vars_imp` + `vars_bot` + `Finset.union_empty`).
  - **Recommended fix**: `@[nolint simpNF]` on `vars_neg` (the cleanest; the lemma is a
    convenience restatement and the underlying simp set already proves the RHS). Removing
    `@[simp]` entirely is an alternative but loses the named simp lemma; rewriting the LHS is
    not feasible because `neg` is definitionally `imp _ bot` and there is no distinct head to
    pin. Recommend `@[nolint simpNF]` plus a one-line comment.

## Call-Site / Cross-Module Impact Analysis

Verified via `grep -rn` across all of `Cslib/**.lean`.

### GenericMCSBridge renames (PL)

- `deriv_tree_to_list` → used only **within** `Propositional/Metalogic/GenericMCSBridge.lean`
  (line 224 `exact deriv_tree_to_list d`) plus docstring mentions (lines 23, 49 — comments).
- `unfold_listImp_in_tree` → used only within the same file (line 210 call; docstrings 25,
  49, 195).
- `list_deriv_to_tree` → used within the file (line 226) **and cross-file in the same PL
  namespace**: `Propositional/Metalogic/DeductionTheorem.lean:79` (`exact list_deriv_to_tree
  (...)`). **This call site MUST be updated** when renaming to `listDerivToTree`.

Also update the in-file docstring/comment references to keep docs accurate (GenericMCSBridge.lean
lines 23, 25, 27, 49, 195) — not lint-required but recommended.

### IMPORTANT — Modal/Temporal/Bimodal copies are OUT OF SCOPE and unaffected

Identical underscore names (`deriv_tree_to_list`, `unfold_listImp_in_tree`,
`list_deriv_to_tree`, plus `*_fc` variants) exist in:
- `Cslib/Logics/Modal/Metalogic/GenericMCSBridge.lean`
- `Cslib/Logics/Temporal/Metalogic/GenericMCSBridge.lean`
- `Cslib/Logics/Bimodal/Metalogic/Core/GenericMCSBridge.lean`

These are **separate declarations in separate namespaces**. Renaming the PL copy does not
touch them, and they are not in task 386's scope (task targets PL only). Each has its own
consumer (`Modal/Metalogic/DeductionTheorem.lean:73`, etc.). Their lint cleanup belongs to a
different task (see Coordination note).

### LK / LJ CutElimination renames — fully internal

`grep` across `Cslib/**.lean` confirms **none** of the 10 `cutAdm_*` / `ljCutAdm_*` helpers
are referenced outside their own files. All call sites are intra-file:
- LK helpers are called by each other and by the public wrapper `cutAdmissibility`
  (LK/CutElimination.lean:830). `cutAdm_right`/`cutAdm_left` live in a `mutual` block
  (lines 584–818); the three principal helpers are outside it.
- LJ helpers are called by each other and by the public wrapper `ljCutAdmissibility`
  (LJ/CutElimination.lean:660). LJ uses per-def `termination_by` (no mutual block).

Public wrappers `cutAdmissibility` / `ljCutAdmissibility` keep their names (no underscore).
When renaming, update every intra-file occurrence (use `replace_all` carefully — names like
`cutAdm_right` are substrings of `cutAdm_right_andR`/`cutAdm_right_orR`/`cutAdm_right_impR`,
so rename the longer names first or use word-boundary-aware edits).

## Coordination Note (task "403" is stale)

The description says "Coordinate GenericMCSBridge renames with the cross-cutting task (403)."
Current task 403 = "Rename specs 384 to 402" (COMPLETED, pure spec-directory bookkeeping). It
does **not** own GenericMCSBridge code renames. The actual cross-system MCS-bridge / derivation-
lifting refactor work appears under other tasks (e.g. 415 audit_propositional_lifting_structure_first,
419 generalize_derivation_lifting_intersystem). Because PL's GenericMCSBridge decls are
independent of the other-logic copies, **task 386 can proceed on the PL copies without blocking
on any coordination**. Recommendation: implement the PL renames as scoped here; if a future
cross-cutting refactor wants matching camelCase names in Modal/Temporal/Bimodal, that is a
separate task's responsibility.

## Recommended Fix Phasing (zero-debt, no sorry/axioms involved)

All fixes are mechanical (renames, docstrings, nolint attributes) — no proof obligations,
no sorry, no axioms. Suggested phase order (each a self-contained lint category):

1. **simpNF** — `@[nolint simpNF]` on `vars_neg` (Subformula.lean). Single edit; clears the
   error that leaks into every importing module's lint output.
2. **docBlame** — add docstrings to `processNext`, `intExpandBranches.go`, `isAccessible.go`.
3. **unusedArguments** — `@[nolint unusedArguments]` + comment on `deductionWithMem` and
   `intBotForces`. (Skip `conclusionGrounded`; already done.)
4. **defsWithUnderscore + defLemma (GenericMCSBridge)** — rename the 3 PL bridge decls;
   convert `deriv_tree_to_list`→`derivTreeToList` to `lemma` (drop `noncomputable`); update
   the DeductionTheorem.lean:79 consumer and in-file references/docstrings.
5. **defsWithUnderscore (LK)** — rename 5 `cutAdm_*`; longest-name-first to avoid substring
   clobbering; update intra-file call sites + `cutAdmissibility`.
6. **defsWithUnderscore (LJ)** — rename 5 `ljCutAdm_*`; same care; update `ljCutAdmissibility`.

### Verification (per phase and final)

- Per module: `lake exe runLinter Cslib.Logics.Propositional.<Module>` (filter to the module's
  own file path; ignore the leaked `vars_neg` line until phase 1 is done).
- Build: `lake build Cslib.Logics.Propositional.<Module>` after each rename phase.
- Final PL-clean check: run `lake exe runLinter` on each of the 9 touched modules; confirm
  zero errors whose file path is under `Cslib/Logics/Propositional/`. Then the full
  `lake lint` for the repo-wide gate.

## Tactic Survey

Not applicable — this is a lint-mechanical task (renames, docstrings, attributes). No proof
search, no tactic selection. No `lean_multi_attempt` needed.

## Reuse Check

Not applicable — no new definitions or abstractions are introduced. All changes are renames
of existing decls, docstrings, and lint-suppression attributes on existing decls.

## Open Items for Implementer

- Confirm `intBotForces` linter position: reports 1643 (docstring start); the `def` is at
  file line 1647. Place `@[nolint unusedArguments]` directly above the `def` line.
- When using `replace_all` for `cutAdm_right` / `ljCutAdm_right` etc., guard against substring
  matches (`cutAdm_right_andR`). Rename the longest variants first, or rename via
  unique-context edits.
