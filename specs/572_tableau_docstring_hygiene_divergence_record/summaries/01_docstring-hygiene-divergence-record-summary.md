# Implementation Summary: Task #572

- **Task**: 572 - tableau_docstring_hygiene_divergence_record
- **Plan**: plans/01_docstring-hygiene-divergence-record.md
- **Status**: [COMPLETED]

## Overview

All six plan phases landed. Three stale docstring claims in
`Cslib/Logics/Propositional/Tableau/Intuitionistic/` were corrected, the expansion-loop
divergence witness and the fuel-0 saturation counter-instance were recorded as permanent
in-source notes, and the two missing BibTeX entries (`GargGenoveseNegri2012`, `Dyckhoff1992`)
were landed with their two citation sites repaired. Every change is confined to comments,
docstrings, module notes, or `references.bib`: no Lean definition, theorem statement, tactic,
or `sorry` was touched.

## Phases Completed

1. **Expansion.lean — divergence-witness note and termination-claim correction.** Added a new
   `/-! ### Divergence witness: no world bound exists for this calculus -/` module note
   immediately before `## Decision Procedures`, recording the witness formula, the measured
   max-label growth table (fuel 10-260), the period-2 structural-duplication fact, the three
   (a)/(b)/(c) consequences, and a directive against re-attempting the refuted world bound.
   Replaced the circular termination claim in `applyAllTImpRules`'s docstring with an accurate
   one pointing at the new note.
2. **Scheme.lean — annotated the refuted world-bound sites.** `intUniverse`'s docstring and
   `intApplyRuleFull_outputs_subset`'s docstring now state that the world bound / `hnw`
   hypothesis they assume is refuted by direct counterexample, cross-referencing the Divergence
   witness note. Neither declaration was altered.
3. **Scheme.lean — fuel-0 refutation record.** The `sorry` in
   `intExpandBranches_openBranch_sat`'s `| zero =>` case now has an in-proof comment recording
   the Lean-verified counter-instance (`branches = [[⟨.neg, p ∧ q, 0⟩]]`, ...) and why the goal
   is false as stated. The `sorry` token itself is unchanged.
4. **Scheme.lean — `sat_timp` hygiene.** Deleted the stale trailing "GAP 2 investigation ...
   determinacy remains BLOCKED" module note (contradicted the file's own earlier
   Gap-2-resolved account). Corrected both instances of the false "`sat_timp` is NOT added as an
   `IBranchSaturation` field" claim (the STOP-gate "Consequence" paragraph and the in-proof
   comment in `truthLemma`'s T-imp case) to state the field exists and is discharged by
   `intApplyRuleFull`'s `.pos, .imp` branching arm; the case stays `sorry` only because the
   copy-propagation invariant (Gap 1) is not established. Added a cross-reference to the
   Divergence witness note without claiming Gap 1 itself is refuted.
5. **references.bib — two dangling BibKeys.** Added `Dyckhoff1992` and `GargGenoveseNegri2012`,
   and repaired the two `Expansion.lean` citation sites that referenced them. Also removed a
   stray task-number citation from the pre-existing `Gore1999` entry's `note` field
   (zero-risk, in-scope cleanup).
6. **Full verification and invariant audit.** All checks below passed.

## Plan Deviations

- **Phase 1** transcribed the divergence data primarily from
  `specs/317_propositional_tableau_completeness/reports/13_blocker-root-cause-and-correct-approach.md`
  (the full derivation cited by report 14) rather than report 14 alone, because report 13 carries
  the complete ten-point fuel/max-label table (report 14 only summarizes the first four points
  and the endpoint). The two sources agree except at fuel 60, where report 13's authoritative
  table gives max label 21 (report 14's prose rounds/typos this as "20" in one place); the
  in-source note uses report 13's verified figure, 21.
- **Phase 5**: the BibTeX `pages`/`DOI` fields for `GargGenoveseNegri2012` (and `DOI` for
  `Dyckhoff1992`) could not be confirmed this session — no network access was available, and
  neither entry has a match in the local `~/Projects/Literature/index.json` or
  `zotero-library.json`. Both entries were landed with only the fields explicitly given in the
  plan (author/title/booktitle-or-journal/year/publisher as applicable), per the plan's own
  fallback instruction ("land the entry with the confirmed fields only ... rather than
  inventing values"). A future task with literature/web access should fill in `pages`/`doi` for
  both entries if desired; this is optional polish, not a correctness gap (the BibKeys resolve
  and the citations are no longer dangling).

No phase was skipped, blocked, or altered in substance from the plan's task sequence.

## Coordination Note (for task 456)

`GargGenoveseNegri2012` has now landed in `references.bib` (added by this task). Any other
in-flight work that also intends to add this BibKey (per the blocker-analysis report's
coordination flag) should verify field equivalence against the existing entry rather than adding
a duplicate. `DershowitzManna1979`, mentioned in that same coordination context, was NOT touched
by this task and remains open for whoever adds it.

## Verification Results

- `lake build` (full library, 3259 jobs): **green**.
- Scoped builds of all six modules in the directory (`Rules`, `Expansion`, `Scheme`,
  `Soundness`, `Completeness`, `DecisionProcedure`): **green**.
- `lake exe checkInitImports`: exit 0.
- `lake exe lint-style`: exit 0, no output (clean on touched files).
- `lake lint`: no new warnings attributable to the touched files (pre-existing warnings in
  `Scheme.lean`/`Expansion.lean`/`Soundness.lean`/`Minimal/Soundness.lean` unchanged).
- `lake test`: exit 0, full `CslibTests/` suite green.
- `lake exe mk_all --module`: "No update necessary".
- `lake shake --add-public --keep-implied --keep-prefix`: one pre-existing import-minimization
  suggestion on `Expansion.lean`, unrelated to this task (this task's diff contains zero
  `import` lines).
- **Sorry inventory (bare `sorry` tactic, `grep -cE '^[[:space:]]*sorry[[:space:]]*$'`) — before
  vs. after, per file**:

  | File | Before | After |
  |------|--------|-------|
  | `Scheme.lean` | 2 | 2 |
  | `Completeness.lean` | 1 | 1 |
  | `Expansion.lean` | 0 | 0 |
  | `Rules.lean` | 0 | 0 |
  | `Soundness.lean` | 0 | 0 |
  | `DecisionProcedure.lean` | 0 | 0 |

  Byte-identical to baseline. Both `Scheme.lean` occurrences remain at their original sites
  (`truthLemma`'s T-imp case; `intExpandBranches_openBranch_sat`'s fuel-0 case) — only their
  surrounding comments changed.
- No `#eval`, `#check`, or `dbg_trace` in any file under
  `Cslib/Logics/Propositional/Tableau/Intuitionistic/`.
- No line over 100 characters introduced in either edited `.lean` file.
- `git diff -U0` semantics audit: every added/removed line in both `.lean` files sits inside a
  `--` line comment, a `/-- ... -/` docstring, or a `/-! ... -/` module note. No code line
  (definition, theorem statement, hypothesis, or tactic) was touched.
- Rule audit: `git diff -- Cslib/ references.bib | grep -inE '^\+.*(task [0-9]|phase [0-9]|plan
  [0-9]{2}|report [0-9]{2})'` returns nothing — no task/phase/plan/report citations were
  introduced into any deliverable.
- `grep -c GargGenoveseNegri2012 references.bib` = 1; `grep -c Dyckhoff1992 references.bib` = 1;
  no duplicate BibTeX keys.
- `grep -n 'Divergence witness' Cslib/` returns 5 occurrences: the note itself, its
  self-reference in `applyAllTImpRules`'s docstring, and one cross-reference each from
  `intUniverse`, `intApplyRuleFull_outputs_subset`, and the Gap-1 discussion.

## Files Modified

- `Cslib/Logics/Propositional/Tableau/Intuitionistic/Expansion.lean`
- `Cslib/Logics/Propositional/Tableau/Intuitionistic/Scheme.lean`
- `references.bib`

## Artifacts

- `specs/572_tableau_docstring_hygiene_divergence_record/plans/01_docstring-hygiene-divergence-record.md`
  (all six phases marked `[COMPLETED]`)
- `specs/572_tableau_docstring_hygiene_divergence_record/summaries/01_docstring-hygiene-divergence-record-summary.md`
  (this file)
