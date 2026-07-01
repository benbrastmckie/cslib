# Implementation Summary: Task #446 - Temporal Burgess Citation Hygiene

- **Task**: 446 - Burgess citation hygiene in the task-180 Temporal metalogic
- **Plan**: plans/01_burgess-citation-hygiene.md
- **Status**: [COMPLETED]
- **Type**: cslib (pure docstring/comment edit; no proofs, no `sorry`, no axioms)

## Overview

Converted all 12 plain-prose "Burgess 1982" / "Xu 1988" citation sites in
`Cslib/Logics/Temporal/Metalogic/` to the established bracket house style
`[Description][BibKey]`, disambiguating `Burgess1982I` (BX axiom system — "Since and
Until") from `Burgess1982II` (chronicle construction — "Time Periods"). No proof,
definition, tactic, signature, or `references.bib` changes were made. Every edit is
confined to a `/-! ... -/` doc-comment reference block or an inline doc sentence.

## Phases Completed

### Phase 1: Chronicle/ subtree conversions (Burgess1982II) — COMPLETED
Converted 8 sites across 7 files, normalizing `-` → `*` at the 5 flagged sites:
- `Chronicle/TruthLemma.lean:34` (bullet) and `:274` (inline prose)
- `Chronicle/RRelation.lean:21`
- `Chronicle/ChronicleToCountermodel.lean:33`
- `Chronicle/PointInsertion.lean:41`
- `Chronicle/ChronicleConstruction.lean:52`
- `Chronicle/ChronicleTypes.lean:21`
- `Chronicle/CounterexampleElimination.lean:40`

All 8 sites match the report's exact target strings verbatim.

### Phase 2: Metalogic top-level conversions (Burgess1982I, split, Xu1988) — COMPLETED
Converted 4 sites across 3 files:
- `Soundness.lean:28` (Burgess1982I, BX axiom system) — matches target string verbatim.
- `DenseSoundness.lean:28` (Burgess1982I, `-` → `*`) — **deviation**: report target string
  was 110 chars, exceeding the 100-char `lake exe lint-style` line limit; shortened
  trailing description to "— BX axioms (dense case)" (98 chars).
- `Completeness.lean:40-41` (SPLIT into three bullets: Burgess1982I, Burgess1982II, Xu1988)
  — the Burgess1982I and Xu1988 bullets match the report's target strings verbatim; the
  Burgess1982II bullet is a **deviation**: report target string was 110 chars, exceeding
  the line limit; shortened to "— completeness, Claim 2.11" (99 chars), preserving the
  `[Burgess1982II]` citation and the Claim 2.11 cross-reference.

### Phase 3: Build + grep-guard verification — COMPLETED
Full CSLib CI pipeline executed and passed:
- `lake exe cache get` — cache already warm (no-op).
- `lake build` (scoped, then full) — green; the two lint-style warnings surfaced by the
  scoped build (the 110-char lines above) were fixed and confirmed clean on rebuild.
- `lake exe checkInitImports` — no violations.
- `lake lint` — 2 pre-existing `defsWithUnderscore` errors in
  `Cslib/Logics/Temporal/Theorems.lean` (a file never touched by this task; confirmed via
  `git diff --stat`) — out of scope for task 446.
- `lake exe lint-style` — 2 pre-existing "space before semicolon" errors in
  `Cslib/Logics/Modal/Tableau/Completeness.lean` (untouched by this task) — out of scope.
- `lake shake --add-public --keep-implied --keep-prefix` — extensive pre-existing
  import-minimization suggestions across the codebase (tracked separately by task 447);
  none of the 10 files edited by task 446 appear anywhere in the shake report.
- `lake exe mk_all --module` — "No update necessary" (no new files created).
- `lake test` — exit code 0, full `CslibTests/` suite passes.

## Verification

- Grep guard `grep -rn "Burgess (19\|Burgess 1982:" Cslib/Logics/Temporal/Metalogic/`
  returns zero hits.
- `git diff -- Cslib/Logics/Temporal/Metalogic/` shows all 10 file diffs confined to
  `## References` doc-comment bullets or one inline doc-comment sentence
  (`TruthLemma.lean:274`) — zero behavioural change.
- `grep -n "\bsorry\b"` across all 10 edited files: zero hits.
- Vacuous-definition pattern check across all 10 edited files: zero hits.
- New-axiom check (`git diff` for `^+axiom`) across the edited subtree: zero hits.

## EXCLUSIONS Honored

- Lean identifiers (`BurgessR3Maximal`, `burgessR*`, etc.) — untouched.
- `PointInsertion.Burgess` module and its module-description bullet — untouched.
- Section-header shorthand (`## Burgess Lemma 2.3`, `Burgess C4a/C5a`, inline "Burgess 2.x"
  proof comments) — untouched.
- `Burgess-Xu (BX)` system naming in `ProofSystem/Axioms.lean` — untouched (not part of
  this task's file set; not referenced by the plan's 12 sites).
- `references.bib` — not edited (all keys already resolved).
- Reynolds1994/Tableau description mismatch — left alone, per plan (separate task).

## Plan Deviations

1. **DenseSoundness.lean:28** — report's exact target string
   (`* [J. Burgess, *Axioms for Tense Logic I: Since and Until*][Burgess1982I] — BX axiom
   system for temporal logic`, 110 chars) exceeded the CSLib 100-char `lint-style` line
   limit; this was only discoverable at Phase 3 build time (the plan's risk table had
   predicted "well under limits"). Shortened the trailing description to "— BX axioms
   (dense case)" (98 chars), preserving the `[Burgess1982I]` citation and the file's
   dense-case context.
2. **Completeness.lean:41 (Burgess1982II bullet)** — same 100-char overflow issue (110
   chars in the report's target). Shortened to "— completeness, Claim 2.11" (99 chars),
   preserving the `[Burgess1982II]` citation and the Claim 2.11 reference.

Both deviations are annotated inline in the plan file's Phase 2 checklist. No other
deviations from the plan occurred; all other 10 sites match the report's target strings
verbatim.

## Files Modified

- `Cslib/Logics/Temporal/Metalogic/Chronicle/TruthLemma.lean`
- `Cslib/Logics/Temporal/Metalogic/Chronicle/RRelation.lean`
- `Cslib/Logics/Temporal/Metalogic/Chronicle/ChronicleToCountermodel.lean`
- `Cslib/Logics/Temporal/Metalogic/Chronicle/PointInsertion.lean`
- `Cslib/Logics/Temporal/Metalogic/Chronicle/ChronicleConstruction.lean`
- `Cslib/Logics/Temporal/Metalogic/Chronicle/ChronicleTypes.lean`
- `Cslib/Logics/Temporal/Metalogic/Chronicle/CounterexampleElimination.lean`
- `Cslib/Logics/Temporal/Metalogic/Soundness.lean`
- `Cslib/Logics/Temporal/Metalogic/DenseSoundness.lean`
- `Cslib/Logics/Temporal/Metalogic/Completeness.lean`

## Out-of-Scope Findings (Not Fixed — Reported Only)

- `Cslib/Logics/Temporal/Theorems.lean:51,68` — 2 `defsWithUnderscore` lint errors
  (pre-existing, unrelated to task 446's citation scope).
- `Cslib/Logics/Modal/Tableau/Completeness.lean:432,491` — 2 `lint-style`
  "space before semicolon" errors (pre-existing, unrelated).
- Codebase-wide `lake shake` import-minimization suggestions (tracked by task 447;
  none touch the 10 files edited here).

These are pre-existing baseline issues, confirmed via `git diff --stat` to be outside the
set of files this task modified, and are out of scope per the plan's Non-Goals.
