# Research Report: Task 460 — Classical Tableau Completeness Lint Cleanup

**Task**: Wrap long lines and clear lint warnings in
`Cslib/Logics/Propositional/Tableau/Classical/Completeness.lean` (repointed consumer from task 455).

**Status**: Researched. Non-blocking lint warnings only. `lake build` of the module is GREEN
(exit 0, 830 jobs). No `sorry`, no errors — the file compiles; every item below is a warning.

## Verification Method

The CSLib build-time linters (`linter.style.longLine`, `linter.unusedSectionVars`,
`linter.unusedSimpArgs`, `linter.flexible`, and the "unused hypothesis in type" linter) emit
directly during `lake build`. I forced a rebuild (`touch` + `lake build
Cslib.Logics.Propositional.Tableau.Classical.Completeness`) and captured every warning with its
current line number. Line lengths were independently confirmed with
`awk 'length > 100'`.

**Line numbers have NOT shifted** — the file is unchanged since task 455 commit `282a14bf`.
All 16 cited long-line numbers and all 5 cited non-long-line sites match the current file exactly.

## CRITICAL FINDING: Cited list is a SUBSET of actual warnings

Task 460 cites 16 long lines + 5 other sites (799/810/837/1102/1267). The build actually emits
**~46 warnings** in these same categories. Fixing only the cited subset will leave ~25 warnings,
so a re-vet would still flag the file. **Recommendation: fix ALL warnings in these categories**
(they are all mechanical, same-category, sorry-free edits). Full inventory below.

---

## Category 1 — Long lines (>100 chars) — `linter.style.longLine`

All 16 cited lines confirmed present and over 100 chars (measured length in parens):

| Line | Len | Content / wrap strategy |
|------|-----|-------------------------|
| 119 | 104 | `if b.any fun sf' => ...` findSome? lambda — break the boolean conjunction across lines |
| 140 | 108 | `cases hfind_bot : b.find? (fun sf => ...) with` — wrap the `find?` predicate onto its own line |
| 158 | 104 | `cases hf : b.find? (fun sf' => ...) with` — same wrap |
| 161 | 125 | `have hsome : (b.find? (fun sf' => ...)).isSome = true := by` — wrap predicate |
| 218 | 102 | `.branching [[SignedFormula.neg a sf.label], [SignedFormula.pos (.imp b1 b2) sf.label]] := by` — put each inner list on its own line |
| 237 | 102 | same shape with `.and b1 b2` |
| 256 | 101 | same shape with `.or b1 b2` |
| 360 | 114 | `have hca : classicalApplyOne sf = .linear [..., ...] := by` — break after `=` |
| 377 | 121 | `.branching [[...neg a...], [...neg c...]] := by` — break inner lists |
| 400 | 121 | `.branching [[...pos a...], [...pos c...]] := by` — break inner lists |
| 421 | 114 | `.linear [...neg a..., ...neg c...] := by` — break after `=` |
| 641 | 104 | Docstring `/-- classicalExpMeasure_split splits ... -/` — reflow to 2 lines |
| 912 | 107 | `(∀ (i : Nat) (b : Branch ...) (e : List (SignedFormula ...)),` — break the binder list |
| 961 | 105 | `key branches expandedSets [] [] hlength rfl hInv hfuel (by simpa [...] using h)` — wrap args |
| 979 | 109 | `· simp only [...] at hlength_p; exact hlength_p` — split at the `;` into two lines |
| 987 | 104 | Comment line — reflow the `--` comment |

Note lines 218/237/256/360/377/400/421 already have `:= by` continuation on the next line; the
fix is to also break the RHS list literal so the head fits under 100 chars.

## Category 2 — Unused section variables — `linter.unusedSectionVars`

The `variable {Atom : Type*} [DecidableEq Atom] [Hashable Atom]` block (line 49) leaks unused
instances into 12 declarations. Fix: add `omit [...] in` immediately before each declaration
(matching the existing pattern already used at lines 434 and 443:
`omit [DecidableEq Atom] [Hashable Atom] in`). The exact instances to omit are what the linter
lists per site:

| Decl line | Declaration | omit clause to add |
|-----------|-------------|--------------------|
| 85  | `classicalTruthLemma` | `omit [Hashable Atom] in` |
| 480 | `classicalBranchComplexity_append` | `omit [Hashable Atom] in` |
| 489 | `classicalBranchComplexity_mono_expanded` | `omit [Hashable Atom] in` |
| 569 | `classicalBranchComplexity_le_mapsum` | `omit [Hashable Atom] in` |
| 610 | `classicalApplyOne_output_complexity` | `omit [DecidableEq Atom] [Hashable Atom] in` |
| 642 | `classicalExpMeasure_split` | `omit [Hashable Atom] in` |
| 657 | `classicalExpMeasure_append` | `omit [Hashable Atom] in` |
| 667 | `classicalExpMeasure_const_exp` | `omit [Hashable Atom] in` |
| 676 | `classicalStepBranch_none_saturated` | `omit [Hashable Atom] in` |
| 704 | `classicalStepBranch_hintikka_inv` | `omit [Hashable Atom] in` |
| 800 | `classicalApplyOne_branching_length` | `omit [DecidableEq Atom] [Hashable Atom] in` |
| 1102| `classicalStepBranch_mem_preserved` | `omit [Hashable Atom] in` |

Task 460 explicitly cited only line 799/800 (`classicalApplyOne_branching_length`) and line 1102
(`classicalStepBranch_mem_preserved`). The other 10 sites are the same linter category and should
be fixed the same way. Place the `omit ... in` on its own line **above the docstring**, matching
lines 434/443.

## Category 3 — Unused hypothesis in type — "does not use hypothesis" linter

Distinct linter (fires at the docstring line). Two sites, both flag `[DecidableEq Atom]`:

| Line | Declaration | Fix |
|------|-------------|-----|
| 607 | `classicalApplyOne_output_complexity` | covered by the `omit [DecidableEq Atom] [Hashable Atom] in` added for line 610 |
| 799 | `classicalApplyOne_branching_length` | covered by the `omit [DecidableEq Atom] [Hashable Atom] in` added for line 800 |

The `omit` clause from Category 2 silences both linters at these two declarations — no separate
edit needed. (Alternative the linter suggests: remove the instance and use `classical` in the
proof; the `omit` approach is preferred here for consistency with the file's existing style and
because the proofs do not actually invoke decidability.)

## Category 4 — Unused simp arguments — `linter.unusedSimpArgs`

Each is a mechanical deletion of the struck-through argument the linter names. Full set (task
cited only 810 and 837):

| Line | Unused arg(s) to delete from the simp call |
|------|--------------------------------------------|
| 525 | `List.filter_cons` |
| 528 | `List.filter_cons` |
| 539 | `List.filter_cons` |
| 542 | `List.filter_cons` |
| 548 | `List.filter_cons` |
| 551 | `List.filter_cons` |
| 561 | `List.filter_cons` |
| 564 | `List.filter_cons` |
| 624 | `SignedFormula.formula` (the only arg — `simp only [SignedFormula.formula]` becomes empty; delete the whole tactic line, it is a no-op) |
| 629 | `SignedFormula.formula` |
| 630 | `complexity_atom`, `complexity_bot`, `complexity_imp`, `complexity_and`, `complexity_or` (all 5 unused) |
| 693 | `ite_false` |
| 809 | `SignedFormula.formula` |
| 810 | `SignedFormula.sign`, `SignedFormula.label` |
| 837 | `List.length_map` |

Recommended verification per site: after deleting the flagged args, re-run
`lake build <module>` (or `simp?` at the position) to confirm the simp still closes the goal.
The linter is authoritative that these args do not fire, so deletion is safe; re-build confirms.

## Category 5 — Flexible tactic — `linter.flexible`

| Line | Current | Fix |
|------|---------|-----|
| 1267 | `have heq : e = [] := by simp at he; exact he` | Replace `simp at he` with the `simp only [...]` set that `simp?` reports at that position (context: `he : [[]][0]? = some e`; expect lemmas like `List.getElem?_cons_zero`, `Option.some.injEq`). Run `simp?` in the editor to get the exact list, then `simp only [<that list>] at he`. |

## Out-of-scope note

The build also surfaces `Cslib/Foundations/Logic/Tableau/Measure.lean:102:4: try 'simp' instead
of 'simpa'`. This is the shared Measure module (task 452/455), NOT this file — leave it for its
owning task unless the plan explicitly widens scope.

## Recommended plan shape (single mechanical phase)

1. Category 1: wrap the 16 long lines.
2. Category 2+3: add 12 `omit ... in` clauses (silences both section-var and unused-hypothesis
   linters).
3. Category 4: delete the 15 unused simp args.
4. Category 5: replace the one `simp at he` with `simp only [...]`.
5. Verify: `lake build Cslib.Logics.Propositional.Tableau.Classical.Completeness` emits ZERO
   warnings and exits 0; then full `lake build` + `lake exe lint-style`.

All edits are sorry-free and mechanical. No new definitions, no axioms, no reuse concerns
(pure lint cleanup). Zero-debt policy fully satisfiable.
