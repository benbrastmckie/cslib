# Implementation Summary: Task #389 — Docstrings, Headers, Citations (Prop/Foundations Tier-2)

- **Task**: 389 - Fix docBlame, barrel headers, unusedSectionVars, broken citation
- **Status**: [COMPLETED]
- **Plan**: plans/01_docstrings-headers-citations.md
- **Report**: reports/01_docstrings-headers-citations.md
- **Session**: sess_1782924983_6bcecb_389

## What Was Done

Task 389 arrived with most of its originally-scoped work already completed by intervening
tasks 406 (docstrings) and 460 (Classical/Completeness `omit` cleanup). This implementation
executed the small residual identified by research report 01:

### Phase 1 (COMPLETED) — `references.bib`
Added the missing `NegriVonPlato2001` `@book` entry (Negri & von Plato, *Structural Proof
Theory*, CUP 2001), mirroring the adjacent `TroelstraSchwichtenberg2000` format. DOI
`10.1017/CBO9780511527340` was verified live via Cambridge University Press's product page
(WebFetch redirect from doi.org confirmed title/authors/publisher/year). This entry resolves
~21 broken `[NegriVonPlato2001]` doc-gen citation links across `OrImpConservative.lean` and the
LJ/LK `SequentCalculus` modules.

### Phase 2 (COMPLETED) — `omit` clauses for live, sorry-free `unusedSectionVars`
Drove edits from **live** `lake build ... | grep unusedSectionVars` output, not stale
report/description line numbers:
- `Cslib/Logics/Propositional/Tableau/Minimal/Soundness.lean` — added
  `omit [Hashable Atom] in` above `minimalTableau_sound` (confirmed sorry-free).
- `Cslib/Logics/Propositional/Tableau/Intuitionistic/Expansion.lean` — added
  `omit [Hashable Atom] in` above `intStepBranch_result_ne_notApplicable` (confirmed sorry-free,
  and the linter still fired live at implement time).
- `Cslib/Logics/Propositional/Tableau/Intuitionistic/Scheme.lean` — extended the existing
  `omit [Hashable Atom] in` above `ILabelBound_extendMany` to
  `omit [Hashable Atom] [DecidableEq Atom] in`, since the live linter also flagged
  `[DecidableEq Atom]` as unused there. This incidentally also silenced the companion
  `linter.unusedDecidableInType` warning on the same declaration.

**Deviation note**: the plan's draft edit placed `omit ... in` *between* the docstring and the
`theorem`/`lemma` keyword. This is a parse error (`unexpected token 'omit'; expected 'lemma'`) —
the correct placement, matching the existing idiom at `Soundness.lean:62`, is *before* the
docstring. All three sites were corrected to this placement and verified to build clean.

Did **not** touch any Completeness module (`Minimal/Completeness.lean`,
`Intuitionistic/Completeness.lean`, `Classical/Completeness.lean`) or any sorry-containing
theorem — that sweep remains deferred to post-task-317 per the plan's explicit non-goal.

### Phase 3 (ABANDONED, per plan option) — `fld` → `himpFold` rename
Marked abandoned per the delegation instruction ("optional... do only if cheap; droppable").
The rename has zero lint value (already lowerCamelCase-compliant) and is purely cosmetic
(task 395 naming reconciliation). `fld` occurs 26× in
`FreeMeetExtension.lean` only; `himpFold` is unused elsewhere in `Cslib/`, so the rename remains
available as a trivial future follow-up if task 395 still wants it.

### Phase 4 (COMPLETED) — Full CI verification
- `lake exe cache get` — cache already warm, no-op.
- `lake build` (full) — 3188 jobs, **succeeded**.
- `lake exe checkInitImports` — clean.
- `lake exe lint-style` — clean.
- `lake lint` (scoped to the 3 touched Lean files) — clean, zero warnings.
- Targeted `unusedSectionVars` grep on Minimal.Soundness / Minimal.Completeness /
  Intuitionistic.Completeness — **zero matches** (edited sites silenced; Completeness modules'
  sorry-containing theorems correctly still emit nothing, as expected pre-317).
- `lake test` — no failures.
- `lake exe mk_all --module` — "No update necessary" (no new files).
- `lake shake --add-public --keep-implied --keep-prefix` — pre-existing repo-wide import-hygiene
  debt observed across dozens of unrelated files (confirmed present in
  `Intuitionistic/Expansion.lean` both before and after this task's one-line `omit` edit via a
  stash comparison); out of scope for 389, tracked separately by tasks 457/458/460-style
  shake-cleanup work.
- Zero-debt check: `git diff` on the 4 touched files (`references.bib`,
  `Minimal/Soundness.lean`, `Intuitionistic/Expansion.lean`, `Intuitionistic/Scheme.lean`)
  introduces **zero** new `sorry` and **zero** new `axiom`.

## Plan Deviations

- Phase 2: `omit ... in` placement corrected to precede the docstring (plan implied it could go
  directly above the `theorem`/`lemma` line, which broke parsing when a docstring intervened).
- Phase 2: extended scope to `Intuitionistic/Scheme.lean`'s `ILabelBound_extendMany` by widening
  its *existing* `omit [Hashable Atom] in` to also omit `[DecidableEq Atom]`, rather than adding
  a second separate `omit` clause — this was necessary because Lean only permits one `omit ... in`
  modifier immediately before a declaration.
- Phase 3: abandoned per the delegation's explicit optional/droppable framing. No files touched.

## Files Modified

- `/home/benjamin/Projects/cslib/references.bib`
- `/home/benjamin/Projects/cslib/Cslib/Logics/Propositional/Tableau/Minimal/Soundness.lean`
- `/home/benjamin/Projects/cslib/Cslib/Logics/Propositional/Tableau/Intuitionistic/Expansion.lean`
- `/home/benjamin/Projects/cslib/Cslib/Logics/Propositional/Tableau/Intuitionistic/Scheme.lean`

## Out of Scope / Deferred (unchanged from plan)

- Post-317 Minimal/Intuitionistic Completeness `unusedSectionVars` `omit` sweep (gated on task
  317 landing).
- `Minimal/Soundness.lean:136:59` `unusedSimpArgs` warning (pre-existing, part (c) is
  `unusedSectionVars`-only scope).
- `fld` → `himpFold` rename (abandoned as optional/cosmetic).
- Repo-wide `lake shake` import-hygiene debt (pre-existing, unrelated to this task's edits).
- `Cslib/Logics/Propositional/Tableau/Classical/Completeness.lean` — explicitly not touched
  (owned by task 460, already landed).

## Verification Evidence

```
grep -n "NegriVonPlato2001" references.bib
869:@book{NegriVonPlato2001,

lake build  → Build completed successfully (3188 jobs).
lake exe checkInitImports → (clean)
lake exe lint-style → (clean)
lake build Cslib...Minimal.Soundness Cslib...Minimal.Completeness Cslib...Intuitionistic.Completeness \
  2>&1 | grep -i unusedSectionVars → (no matches)
lake test → (no failures)
lake exe mk_all --module → No update necessary
git diff <4 files> | grep sorry|axiom → (no matches)
```
