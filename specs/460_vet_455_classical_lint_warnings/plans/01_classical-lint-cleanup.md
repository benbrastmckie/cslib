# Implementation Plan: Task #460

- **Task**: 460 - Fix lake-build lint warnings in Classical/Completeness.lean (task 455 vet)
- **Status**: [COMPLETED]
- **Effort**: 1.25 hours
- **Dependencies**: None
- **Research Inputs**: specs/460_vet_455_classical_lint_warnings/reports/01_classical-lint-warnings.md
- **Artifacts**: plans/01_classical-lint-cleanup.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: cslib
- **Lean Intent**: true

## Overview

Purely mechanical, sorry-free lint cleanup of a single file,
`Cslib/Logics/Propositional/Tableau/Classical/Completeness.lean`. The module already builds
green (exit 0, 0 sorry, 0 axioms); every item is a non-blocking build-time linter warning.
The plan clears ALL ~46 warnings the build emits across five categories, not just the ~21 the
task description originally cited, so a re-vet passes cleanly. Phases are grouped by warning
category and executed sequentially (they all touch one file), followed by a strict
zero-warning verification phase.

### Research Integration

The research report (`01_classical-lint-warnings.md`) forced a rebuild and captured every
warning with its current line number, confirming line numbers have NOT shifted since task 455
commit `282a14bf`. Its central finding drives this plan: the task's cited warning list is a
**subset** of the actual build output. The full per-category inventory (16 long lines, 12
`unusedSectionVars` sites, 2 "unused hypothesis in type" sites, 15 `unusedSimpArgs` sites, 1
`flexible` site) and the mechanical fix for each are transcribed directly into the phase task
lists below. The existing in-file `omit [DecidableEq Atom] [Hashable Atom] in` pattern at lines
434/443 (verified present) is the template for Phase 2.

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

No ROADMAP.md consulted (no roadmap_path provided, roadmap_flag not set).

## Goals & Non-Goals

**Goals**:
- Clear every long-line, `unusedSectionVars`, unused-hypothesis, `unusedSimpArgs`, and
  `flexible` warning the build emits for this one file.
- Keep the module sorry-free, axiom-free, and green throughout (each edit is mechanical and
  independently verifiable).
- Achieve a ZERO-warning scoped build so a re-vet of task 460 passes.

**Non-Goals**:
- No changes to proof strategy, definitions, notation, typeclasses, or any semantic content.
- No fixing of `Cslib/Foundations/Logic/Tableau/Measure.lean:102` (`simpa`->`simp`) — that is
  the shared Measure module owned by task 452/455 and is explicitly out of scope.
- No new lemmas, no refactors beyond what a linter fix requires.

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Deleting a simp arg that the linter flags but is actually load-bearing | M | L | Linter is authoritative that flagged args do not fire; re-run scoped `lake build` after each Phase-3 batch to confirm the simp still closes. Revert the single arg if a goal fails. |
| Line wrap changes indentation and breaks a tactic block | M | L | Wrap only list literals / binder lists / predicate lambdas; never reflow across a tactic boundary. Scoped build after Phase 1 confirms no breakage. |
| `omit` clause placed on wrong declaration or with wrong instances | L | L | Copy the exact instance list the linter names per site (report Category 2 table); place on its own line above the docstring, matching lines 434/443. |
| `simp only [...]` replacement at line 1267 misses a needed lemma | L | L | Obtain the exact lemma set from `simp?` at that position before substituting; scoped build confirms `he` still rewrites and `exact he` closes. |
| Fixing all ~46 sites (vs cited ~21) introduces a regression | L | L | All edits are same-category and mechanical; the final zero-warning scoped build plus full `lake build` gate the whole change. |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2 | 1 |
| 3 | 3 | 2 |
| 4 | 4 | 3 |
| 5 | 5 | 4 |

All phases edit the same file (`Completeness.lean`), so they run sequentially rather than in
parallel — a strict dependency chain avoids edit conflicts and lets each category be verified in
isolation before the next begins.

### Phase 1: Wrap 16 long lines (`linter.style.longLine`) [COMPLETED]

**Goal**: Bring all 16 flagged lines under 100 characters without altering semantics.

**Tasks**:
- [x] Line 119: break the boolean conjunction in the `b.any fun sf' => ...` findSome? lambda across lines.
- [x] Line 140: wrap the `b.find? (fun sf => ...)` predicate onto its own line.
- [x] Line 158: wrap the `b.find? (fun sf' => ...)` predicate onto its own line.
- [x] Line 161: wrap the `(b.find? (fun sf' => ...)).isSome = true` predicate.
- [x] Line 218: put each inner list of `.branching [[...], [...]]` (neg a / pos imp) on its own line.
- [x] Line 237: same wrap for the `.and b1 b2` branching literal.
- [x] Line 256: same wrap for the `.or b1 b2` branching literal.
- [x] Line 360: break the `classicalApplyOne sf = .linear [..., ...] := by` after `=`.
- [x] Line 377: break the inner lists of the `.branching [[...neg a...], [...neg c...]]` literal.
- [x] Line 400: break the inner lists of the `.branching [[...pos a...], [...pos c...]]` literal.
- [x] Line 421: break the `.linear [...neg a..., ...neg c...] := by` after `=`.
- [x] Line 641: reflow the `/-- classicalExpMeasure_split ... -/` docstring to two lines.
- [x] Line 912: break the binder list `(∀ (i : Nat) (b : Branch ...) (e : List (SignedFormula ...)),`.
- [x] Line 961: wrap the argument list `key branches expandedSets [] [] hlength rfl hInv hfuel (by simpa [...] using h)`.
- [x] Line 979: split the `· simp only [...] at hlength_p; exact hlength_p` at the `;` into two lines.
- [x] Line 987: reflow the `--` comment line.
- [x] *(deviation: altered)* All 16 line numbers had shifted by +1 (task 458 edited this file's
  imports before this dispatch); the live `awk`/build output was used as the authoritative
  target list rather than the plan's hardcoded numbers, per the task brief.

**Timing**: 20 minutes

**Depends on**: none

**Files to modify**:
- `Cslib/Logics/Propositional/Tableau/Classical/Completeness.lean` - wrap the 16 listed lines.

**Verification**:
- `awk 'length > 100 {print NR": "length}' Cslib/Logics/Propositional/Tableau/Classical/Completeness.lean` prints nothing.
- `lake build Cslib.Logics.Propositional.Tableau.Classical.Completeness` still exits 0.

---

### Phase 2: Add 12 `omit [...] in` clauses (silences `unusedSectionVars` + unused-hypothesis) [COMPLETED]

**Goal**: Add one `omit ... in` clause on its own line above each flagged declaration's docstring,
matching the existing pattern at lines 434/443. This silences BOTH the `unusedSectionVars`
warnings (12 sites) AND the two "unused hypothesis in type" warnings (607, 799), which share the
same two declarations (610, 800).

**Tasks**:
- [x] Line 85 `classicalTruthLemma`: add `omit [Hashable Atom] in`.
- [x] Line 480 `classicalBranchComplexity_append`: add `omit [Hashable Atom] in`.
- [x] Line 489 `classicalBranchComplexity_mono_expanded`: add `omit [Hashable Atom] in`.
- [x] Line 569 `classicalBranchComplexity_le_mapsum`: add `omit [Hashable Atom] in`.
- [x] Line 610 `classicalApplyOne_output_complexity`: add `omit [DecidableEq Atom] [Hashable Atom] in` (also clears the unused-hypothesis warning at 607).
- [x] Line 642 `classicalExpMeasure_split`: add `omit [Hashable Atom] in`.
- [x] Line 657 `classicalExpMeasure_append`: add `omit [Hashable Atom] in`.
- [x] Line 667 `classicalExpMeasure_const_exp`: add `omit [Hashable Atom] in`.
- [x] Line 676 `classicalStepBranch_none_saturated`: add `omit [Hashable Atom] in`.
- [x] Line 704 `classicalStepBranch_hintikka_inv`: add `omit [Hashable Atom] in`.
- [x] Line 800 `classicalApplyOne_branching_length`: add `omit [DecidableEq Atom] [Hashable Atom] in` (also clears the unused-hypothesis warning at 799).
- [x] Line 1102 `classicalStepBranch_mem_preserved`: add `omit [Hashable Atom] in`.
- [x] Place each `omit ... in` on its own line ABOVE the declaration's docstring (matching lines 434/443).
- [x] *(deviation: added)* Each `omit [Hashable Atom] in` removed a transitive dependency on
  `[Hashable Atom]`, which cascaded into 7 additional declarations whose own
  `[Hashable Atom]`/`[DecidableEq Atom]` use became vacuous only after the upstream omit was
  applied (only visible by rebuilding after each batch, since the live linter is authoritative
  per the task brief). Iteratively rebuilt and added `omit [Hashable Atom] in` (or
  `omit [DecidableEq Atom] [Hashable Atom] in`) to each newly-surfaced site until the cascade
  stabilized at zero `unusedSectionVars` warnings: `classicalBranchComplexity_drop`,
  `classicalBranchComplexity_extendMany`, `classicalBranchComplexity_child_le`,
  `classicalExpMeasure_step_lt`, `classicalExpandBranches_hintikka`, `classicalTableau_hintikka`,
  `classicalOpenBranch_countermodel`, `classicalTableau_complete` (8 additional sites, one of
  which — `classicalTableau_complete` — is the public completeness theorem; its cascade also
  reached its sole external caller `classicalTableau_decides` in the adjacent
  `DecisionProcedure.lean`, fixed in Phase 5 to avoid a regression).

**Timing**: 20 minutes

**Depends on**: 1

**Files to modify**:
- `Cslib/Logics/Propositional/Tableau/Classical/Completeness.lean` - insert 12 `omit ... in` lines.

**Verification**:
- `lake build Cslib.Logics.Propositional.Tableau.Classical.Completeness` exits 0 and emits no `unusedSectionVars` and no "does not use hypothesis" warnings.

---

### Phase 3: Delete 15 unused simp arguments (`linter.unusedSimpArgs`) [COMPLETED]

**Goal**: Delete exactly the simp arguments the linter names at each site; re-build to confirm
each simp still closes its goal.

**Tasks**:
- [x] Line 525: delete `List.filter_cons`.
- [x] Line 528: delete `List.filter_cons`.
- [x] Line 539: delete `List.filter_cons`.
- [x] Line 542: delete `List.filter_cons`.
- [x] Line 548: delete `List.filter_cons`.
- [x] Line 551: delete `List.filter_cons`.
- [x] Line 561: delete `List.filter_cons`.
- [x] Line 564: delete `List.filter_cons`.
- [x] Line 624: `SignedFormula.formula` is the sole arg — the `simp only [SignedFormula.formula]` is a no-op; delete the whole tactic line.
- [x] Line 629: delete `SignedFormula.formula`.
- [x] Line 630: delete all 5 unused args `complexity_atom, complexity_bot, complexity_imp, complexity_and, complexity_or`.
- [x] Line 693: delete `ite_false`.
- [x] Line 809: delete `SignedFormula.formula`.
- [x] Line 810: delete `SignedFormula.sign, SignedFormula.label`.
- [x] Line 837: delete `List.length_map`.
- [x] After deletions, run the scoped build and confirm every affected simp still closes (no new goals). *(deviation: altered — actual live line numbers had shifted further due to Phase 1/2 edits; the post-Phase-2 rebuild's live warning list was used as the authoritative target set, matching content 1:1 with the categories above.)*

**Timing**: 20 minutes

**Depends on**: 2

**Files to modify**:
- `Cslib/Logics/Propositional/Tableau/Classical/Completeness.lean` - trim simp arg lists at 15 sites.

**Verification**:
- `lake build Cslib.Logics.Propositional.Tableau.Classical.Completeness` exits 0 and emits no `unusedSimpArgs` warnings.

---

### Phase 4: Replace one flexible tactic (`linter.flexible`) [COMPLETED]

**Goal**: Replace `simp at he` at line 1267 with the explicit `simp only [...]` set that `simp?`
reports at that position.

**Tasks**:
- [x] At line 1267 (`have heq : e = [] := by simp at he; exact he`), run `simp?` (or the lean-lsp `lean_diagnostic_messages`/multi-attempt) at the `simp at he` position with context `he : [[]][0]? = some e`.
- [x] Substitute `simp only [<exact lemma list from simp?>] at he` (expected lemmas include `List.getElem?_cons_zero`, `Option.some.injEq`).
- [x] Confirm `exact he` still closes the goal. *(deviation: altered — used `simp only [List.getElem?_cons_zero, Option.some.injEq] at he; exact he.symm` via `lean_multi_attempt`, since the raw `simp` direction gives `e = []`'s mirror `[] = e`, requiring `.symm` rather than a bare `exact he`.)*

**Timing**: 10 minutes

**Depends on**: 3

**Files to modify**:
- `Cslib/Logics/Propositional/Tableau/Classical/Completeness.lean` - line 1267 tactic replacement.

**Verification**:
- `lake build Cslib.Logics.Propositional.Tableau.Classical.Completeness` exits 0 and emits no `flexible` warning.

---

### Phase 5: Zero-warning verification (scoped + full CI) [COMPLETED]

**Goal**: Prove the file is warning-clean and the whole library still builds and passes style CI.

**Tasks**:
- [x] Force a clean rebuild of the module (`touch` the file, then `lake build Cslib.Logics.Propositional.Tableau.Classical.Completeness`) and confirm the output contains ZERO warnings and exits 0.
- [x] Confirm 0 `sorry` and 0 `axiom` in the file (grep) — unchanged from baseline.
- [x] Run full `lake build` and confirm exit 0 (the only remaining known warning is the out-of-scope `Measure.lean:101`).
- [x] Run `lake exe lint-style` and confirm it passes.
- [x] *(deviation: added)* Ran `lake exe checkInitImports`, `lake shake` (scoped to the two touched modules), and `lake test`; all pass/exit 0.

**Timing**: 15 minutes

**Depends on**: 4

**Files to modify**:
- None planned. *(deviation: altered — one additional line touched in
  `Cslib/Logics/Propositional/Tableau/Classical/DecisionProcedure.lean`: adding
  `omit [Hashable Atom] in theorem classicalTableau_decides` was required because removing the
  unused `[Hashable Atom]` from `classicalTableau_complete` in Phase 2 caused the same
  unusedSectionVars warning to cascade one hop downstream into its sole caller. Fixed with the
  same mechanical `omit` pattern to avoid leaving a newly-introduced regression outside
  Completeness.lean.)*

**Verification**:
- Scoped `lake build <module>` output has zero warning lines.
- `lake build` exits 0; `lake exe lint-style` exits 0.

## Testing & Validation

- [x] `awk 'length > 100'` on the file returns no lines.
- [x] Scoped module rebuild emits ZERO warnings (all five categories cleared).
- [x] File still has 0 `sorry`, 0 `axiom`, 0 errors.
- [x] Full `lake build` exits 0.
- [x] `lake exe lint-style` passes.

## Artifacts & Outputs

- Modified `Cslib/Logics/Propositional/Tableau/Classical/Completeness.lean` (lint-clean).
- Implementation summary at `summaries/01_classical-lint-cleanup-summary.md` (on /implement).

## Rollback/Contingency

All edits are confined to one file with no semantic changes. If any scoped build fails after a
phase, `git checkout -- Cslib/Logics/Propositional/Tableau/Classical/Completeness.lean` reverts
the whole file to the green baseline (commit `282a14bf`). Because each phase is independently
verified by a scoped build, a failure isolates to the just-edited category and can be reverted
per-hunk (e.g. restore a single simp arg the linter mis-flagged, or drop a line-wrap that broke a
tactic) without discarding the earlier green phases.
