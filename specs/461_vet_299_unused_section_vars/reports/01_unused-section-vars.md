# Research Report: Task 461 — Fix `linter.unusedSectionVars` Warnings

**Task type:** cslib (lint-fix)
**Severity:** Low, non-blocking
**Session:** sess_1783922075_911857_461
**Date:** 2026-07-12

## Summary

The task asks to add `omit [...] in` before 6 lemmas flagged with
`linter.unusedSectionVars`. Ground truth from a fresh `lake build` of the three Modal
Tableau modules confirms the mechanical fix and the exact `omit` clauses, but surfaces two
material deviations from the task description:

1. **Item 6 is already fixed.** `classicalStepBranch_mem_preserved` in
   `Cslib/Logics/Propositional/Tableau/Classical/Completeness.lean` already carries
   `omit [Hashable Atom] in` (line 1093), added by task 460 (commit `10055ea5`,
   "fix all live lint warnings in Classical/Completeness.lean", 2026-07-01). No action
   needed for this item.
2. **`Cslib/Logics/Modal/Tableau/Completeness.lean` has ~11 additional
   `unusedSectionVars` warnings** not listed in the task, all identical in kind to the two
   named items. If the intent is a lint-clean file, these should be batched into the same
   fix.

All fixes are the same mechanical `omit ... in` pattern already used throughout these files
(e.g. `Branch.lean:142`, `Propositional Completeness.lean:81`), so risk is minimal and
zero-debt compliant (no `sorry`, no axioms, no new definitions).

## Reuse Check

Not applicable in the definitional sense — this task introduces no new abstractions,
lemmas, or notation. The "reuse" here is the pre-existing `omit [...] in` idiom already
established in every affected file. The fix is purely to reuse that idiom on additional
declarations. Confirmed present:
- `Branch.lean`: `omit [DecidableEq Atom] [Hashable Atom] in` at lines 142, 165
- `SoundnessStep.lean`: `omit [DecidableEq Atom] [Hashable Atom] in` at line 161
- `Modal Completeness.lean`: (none yet in the flagged region)
- `Propositional Completeness.lean`: 20+ existing `omit ... in` occurrences

## Ground-Truth Lint Results

Command run (fresh, forced rebuild of Completeness via `touch`):

```
lake build Cslib.Logics.Modal.Tableau.Branch \
           Cslib.Logics.Modal.Tableau.SoundnessStep \
           Cslib.Logics.Modal.Tableau.Completeness
```

Section variables in all three Modal files:
`variable {Atom : Type*} [DecidableEq Atom] [Hashable Atom]`
(namespace `Cslib.Logic.Modal.Tableau`).

### Task-listed items (confirmed) — the 5 that still need fixing

| # | File | Lemma | `lemma` line | Docstring start | Unused vars (from build) | Exact clause to insert |
|---|------|-------|--------------|-----------------|--------------------------|------------------------|
| 1 | `Modal/Tableau/Branch.lean` | `modalNextWorld_gt` | 105 | **102** | `[DecidableEq Atom]`, `[Hashable Atom]` | `omit [DecidableEq Atom] [Hashable Atom] in` |
| 2 | `Modal/Tableau/Branch.lean` | `label_le_modalMaxWorld` | 136 | **133** | `[DecidableEq Atom]` | `omit [DecidableEq Atom] in` |
| 3 | `Modal/Tableau/Completeness.lean` | `extractModel_atom_sat_iff` | 70 | **68** | `[Hashable Atom]` | `omit [Hashable Atom] in` |
| 4 | `Modal/Tableau/Completeness.lean` | `extractModel_bot_false` | 87 | **86** | `[Hashable Atom]` | `omit [Hashable Atom] in` |
| 5 | `Modal/Tableau/SoundnessStep.lean` | `modalClosed_unsat` | 92 | **88** | `[Hashable Atom]` (only) | `omit [Hashable Atom] in` |

Notes:
- **Item 5 omit clause resolved.** The task left the omit args unspecified; the build shows
  only `[Hashable Atom]` is unused (the proof uses `DecidableEq` via
  `Proposition.beqToEq`/`LawfulBEq.eq_of_beq`), so the correct clause is
  `omit [Hashable Atom] in` — NOT both.
- **Insertion point = above the docstring.** The `omit ... in` line must be inserted
  immediately above the lemma's `/-- ... -/` docstring block (the "Docstring start" column),
  matching the established pattern (`Branch.lean:142` omit → 143-146 docstring → 147 lemma).
  The warning line numbers point at the `lemma` keyword, but the omit does not go directly
  above the keyword.
- Items 1 and 2 also emit a secondary "does not use the following hypothesis in its type
  ... consider using `classical`" warning for `[DecidableEq Atom]`. Adding the `omit`
  clause clears both the primary and secondary warning for that variable.

### Item 6 — already fixed (no action)

| File | Lemma | Status |
|------|-------|--------|
| `Propositional/Tableau/Classical/Completeness.lean` | `classicalStepBranch_mem_preserved` (lemma line 1096) | `omit [Hashable Atom] in` **already present at line 1093** (task 460, commit `10055ea5`) |

The task's cited line 1102 falls inside the lemma signature; the omit sits above the
docstring at 1093 and matches the exact clause the task requested. This item is a no-op.

### Additional un-listed `unusedSectionVars` warnings in Modal Completeness.lean

The same build flagged these lemmas in `Cslib/Logics/Modal/Tableau/Completeness.lean`,
none of which appear in the task description:

| Lemma | `lemma`/`theorem` line | Unused vars | Clause |
|-------|------------------------|-------------|--------|
| `openBranch_noTBot` | 96 | `[Hashable Atom]` | `omit [Hashable Atom] in` |
| `openBranch_noContradiction` | 110 | `[Hashable Atom]` | `omit [Hashable Atom] in` |
| `hintikka_box_pos` | 142 | `[Hashable Atom]` | `omit [Hashable Atom] in` |
| `hintikka_box_neg` | 193 | `[Hashable Atom]` | `omit [Hashable Atom] in` |
| `modalAndOf?_eq` | 211 | `[DecidableEq Atom]`, `[Hashable Atom]` | `omit [DecidableEq Atom] [Hashable Atom] in` |
| `modalOrOf?_eq` | 216 | `[DecidableEq Atom]`, `[Hashable Atom]` | `omit [DecidableEq Atom] [Hashable Atom] in` |
| `modalImpOf?_eq` | 221 | `[DecidableEq Atom]`, `[Hashable Atom]` | `omit [DecidableEq Atom] [Hashable Atom] in` |
| `modalNegOf?_eq` | 235 | `[DecidableEq Atom]`, `[Hashable Atom]` | `omit [DecidableEq Atom] [Hashable Atom] in` |
| `modalApplyOne_eq_prop_of_applicable` | 287 | `[Hashable Atom]` | `omit [Hashable Atom] in` |
| `modalStepBranch_none_saturated` (private) | 691 | `[Hashable Atom]` | `omit [Hashable Atom] in` |

These are the same low-severity, mechanical class. The task likely undercounted (it named 2
of the ~13 warnings in this file). Each insertion goes above the respective declaration's
docstring, same pattern.

## Out-of-Scope Observations (do NOT fix under this task)

The build also emitted, in `SoundnessStep.lean`, warnings unrelated to `unusedSectionVars`:
- "This simp argument is unused" at lines 123, 363, 948 (and a `simp [...]` block at 214/263/278)
- `push_neg` deprecated at line 956 ("Prefer `push Not`")

These are separate lint categories and are outside this task's scope.

## Recommended Scope Decision (for planner/orchestrator)

Two viable scopings, both zero-debt-compliant:

- **Minimal (matches task literally):** Fix items 1–5 only (5 `omit` insertions across 3
  Modal files). Skip item 6 (already done). Fastest; leaves ~11 `unusedSectionVars` warnings
  in Modal Completeness.lean.
- **Comprehensive (recommended for lint-clean):** Fix items 1–5 **plus** the 10 additional
  Modal Completeness.lean lemmas listed above (15 insertions total). Same mechanical pattern,
  negligible added risk, achieves a `unusedSectionVars`-clean set of files. This aligns with
  CSLib's zero-debt posture and avoids a near-immediate follow-up vet.

Recommendation: **Comprehensive**, since every additional warning is the identical idiom and
the marginal cost is a handful of one-line insertions. If strict task-literal scope is
required, do Minimal and note the residual warnings.

## Implementation Notes

- No `lake exe cache get` needed beyond what's already built; the three Modal modules build
  clean (exit 0) — these are warnings only.
- After edits, verify with the same scoped build:
  `lake build Cslib.Logics.Modal.Tableau.Branch Cslib.Logics.Modal.Tableau.SoundnessStep Cslib.Logics.Modal.Tableau.Completeness`
  and confirm zero `unused in theorem` lines for the fixed lemmas.
- No new imports, definitions, notation, axioms, or `sorry`. Pure lint hygiene.
