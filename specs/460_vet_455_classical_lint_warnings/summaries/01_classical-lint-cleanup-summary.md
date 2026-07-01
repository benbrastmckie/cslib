# Implementation Summary: Task #460

- **Task**: 460 - Fix lake-build lint warnings in Classical/Completeness.lean (task 455 vet)
- **Plan**: plans/01_classical-lint-cleanup.md
- **Status**: implemented (all 5 phases COMPLETED)

## What Was Done

Mechanical, sorry-free, axiom-free lint cleanup of
`Cslib/Logics/Propositional/Tableau/Classical/Completeness.lean`, following the plan's
five phases. Because task 458 had edited this file's imports just before this dispatch, all
plan-cited line numbers had shifted by +1; the live `lake build` output was used as the
authoritative work queue throughout, per the task brief.

- **Phase 1**: Wrapped 16 `linter.style.longLine` sites (branching-literal lists, binder lists,
  a docstring, an argument list, a `;`-chained tactic line, a `--` comment).
- **Phase 2**: Added `omit [Hashable Atom] in` / `omit [DecidableEq Atom] [Hashable Atom] in`
  clauses above the 12 declarations named in the plan. Rebuilding after each batch revealed a
  cascade: removing `[Hashable Atom]` from an upstream lemma made 8 further declarations'
  own `[Hashable Atom]` (or `[DecidableEq Atom]`) genuinely unused for the first time
  (`classicalBranchComplexity_drop`, `classicalBranchComplexity_extendMany`,
  `classicalBranchComplexity_child_le`, `classicalExpMeasure_step_lt`,
  `classicalExpandBranches_hintikka`, `classicalTableau_hintikka`,
  `classicalOpenBranch_countermodel`, `classicalTableau_complete`). Iteratively rebuilt and
  added `omit` clauses to each until the cascade stabilized at zero `unusedSectionVars`
  warnings. This also cleared both "unused hypothesis in type" warnings for
  `classicalApplyOne_output_complexity` and `classicalApplyOne_branching_length`.
- **Phase 3**: Deleted the exact unused simp arguments the linter named at 15 sites
  (`List.filter_cons` x8, `SignedFormula.formula`/`.sign`/`.label`, `complexity_atom/bot/imp/
  and/or`, `ite_false`, `List.length_map`), including removing one now-empty
  `simp only [SignedFormula.formula]` line entirely (a no-op after arg removal). Rebuilt to
  confirm every affected `simp` still closes.
- **Phase 4**: Replaced `simp at he; exact he` at line 1267 (original numbering) with
  `simp only [List.getElem?_cons_zero, Option.some.injEq] at he; exact he.symm`, verified via
  `lean_multi_attempt` before applying.
- **Phase 5**: Forced a clean rebuild; scoped `lake build
  Cslib.Logics.Propositional.Tableau.Classical.Completeness` emits **zero warnings** and exits
  0. Full `lake build`, `lake exe checkInitImports`, `lake exe lint-style`, `lake shake`
  (scoped to the two touched modules), and `lake test` all pass/exit 0.

## Plan Deviations

1. **Line numbers**: all plan-cited line numbers were off by the +1 shift from task 458's
   prior import edit; live linter output was used instead (explicitly permitted by the task
   brief).
2. **Cascade of `unusedSectionVars`**: Phase 2's 12 planned `omit` sites triggered a chain
   reaction — omitting `[Hashable Atom]` from one lemma made downstream callers' own
   `[Hashable Atom]` genuinely unused, one hop at a time. Fixed by iterating rebuild → find
   new site → add `omit` → rebuild, 8 additional times, until stable at zero warnings. This is
   the same mechanical fix pattern (`omit [...] in`), just discovered incrementally rather than
   up front.
3. **Out-of-scope file touched (1 line)**: the cascade's final link was
   `classicalTableau_complete` (the file's main public completeness theorem). Its sole external
   caller, `classicalTableau_decides` in the adjacent
   `Cslib/Logics/Propositional/Tableau/Classical/DecisionProcedure.lean`, picked up the same
   `unusedSectionVars` warning as a side effect once `classicalTableau_complete`'s signature
   narrowed. Rather than leave a newly introduced regression in a file outside the nominal
   single-file scope, one `omit [Hashable Atom] in` line was added there too (same mechanical
   pattern, no logic change, no import change). `Cslib/Foundations/Logic/Tableau/Measure.lean`
   and all Modal files were left untouched as instructed.
4. **Phase 5 scope**: added `lake exe checkInitImports`, scoped `lake shake`, and `lake test`
   runs beyond the plan's stated two checks, matching the CI pipeline required by the
   cslib-implementation-agent contract.

## Verification

- `awk 'length > 100'` on `Completeness.lean`: no output (zero long lines).
- Scoped `lake build Cslib.Logics.Propositional.Tableau.Classical.Completeness`: zero warnings,
  exit 0 (forced clean rebuild via `touch`).
- `grep -c '\bsorry\b'` / `grep -c '^axiom '` on `Completeness.lean`: 0 / 0.
- `DecisionProcedure.lean`: 0 actual `sorry` tactics (3 grep hits are doc-comment prose
  "sorry-free"), 0 axioms.
- Full `lake build`: exit 0. Only remaining warnings in the whole build are pre-existing and
  out of scope (`Cslib/Foundations/Logic/Tableau/Measure.lean:101` `simpa`→`simp`, and
  warnings/sorries in `Intuitionistic/Soundness.lean`, `Minimal/Soundness.lean`,
  `Intuitionistic/Scheme.lean`, `Intuitionistic/Completeness.lean`, `Minimal/Completeness.lean`
  — none of which were touched by this task).
- `lake exe checkInitImports`: no output, exit implied 0.
- `lake exe lint-style`: exit 0.
- `lake shake --add-public --keep-implied --keep-prefix` (scoped to the two touched modules):
  zero import suggestions for `Completeness.lean`; zero import suggestions for
  `DecisionProcedure.lean` (the one shake finding shown for `DecisionProcedure.lean` in a
  broader run — `Cslib.Init` vs `StrongCompleteness` — predates this task's edit, since the
  only change made there was the `omit` line, not an import).
- `lake test`: exit 0.

## AI Tools Used

This task was implemented with the assistance of Claude Code (Anthropic), acting as the
cslib-implementation-agent. The AI tool was used for:
- Running the live `lake build` linter and parsing warning output to drive every edit
- Writing all Lean edits (line wraps, `omit` clauses, simp-argument trims, the `simp only`
  replacement)
- Running the CSLib CI verification pipeline (`lake build`, `checkInitImports`, `lint-style`,
  `shake`, `test`)
