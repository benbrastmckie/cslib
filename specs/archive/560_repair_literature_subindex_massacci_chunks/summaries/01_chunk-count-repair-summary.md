# Implementation Summary: Repair literature sub-index chunk counts (Massacci and 18 others)

- **Task**: 560 - repair_literature_subindex_massacci_chunks
- **Status**: [COMPLETED]
- **Started**: 2026-07-26T00:00:00Z
- **Completed**: 2026-07-26T00:00:00Z
- **Effort**: ~20 minutes (Phase 3 only)
- **Dependencies**: Phases 1-2 (Tier-2 parent `chunk_count` fallback; Tier-3 on-disk `chunk_*.md`
  glob fallback), both `[COMPLETED]` prior to this phase
- **Artifacts**: `plans/01_briefing-chunk-count-repair.md`,
  `reports/01_briefing-chunk-count-defect.md`, this summary

## Overview

`.claude/scripts/literature-briefing.sh` reported `1 chunk(s)` for 19 of the 34 documents in the
per-repo literature sub-index, even though most of those documents have dozens of on-disk chunk
files. The root cause was that the per-repo briefing path only ever counted *registered child
index entries* (`parent_doc == doc_id`); documents ingested before a later consolidation step
never received those child registrations, so the count silently defaulted to a hardcoded `1`.
Phases 1-2 added two fallback tiers — the parent's own `chunk_count` field, then a non-recursive
on-disk glob for `chunk_*.md` files — ordered deliberately *after* the child-entry count because
the `chunk_count` field can itself hold a stale pre-consolidation value (one corpus entry carries
`997` against 6 true registered children). This phase documents that four-tier precedence
directly in the script, records the final full-34 verification sweep, and captures two residuals
that are out of scope for this task.

## What Changed

- Added a ~25-line comment block in `.claude/scripts/literature-briefing.sh`, positioned
  immediately above the chunk-count derivation in per-repo mode (not the top-of-file usage
  header), documenting:
  - The four-tier precedence: registered child entries -> parent `chunk_count` field ->
    on-disk `chunk_*.md` glob -> literal `1`.
  - Why child count must be checked first: a stale pre-consolidation `chunk_count` field can
    be wildly wrong (the 997-vs-6 case), so preferring it over an available child count would
    silently over-report a consolidated document.
  - Why `chunks.json` length is never used as a signal at any tier: identical staleness risk
    to the `chunk_count` field.
  - The known residual: chunk files named with a different convention (`sec*.md` rather than
    `chunk_*.md`) are not matched by the Tier-3 glob and degrade cleanly to the Tier-4 literal
    `1`.
  - Removed two pre-existing inline comments in the script that cited an ephemeral task
    number (task-management metadata, not durable for a reader of the script) and replaced
    them with descriptions of the behavior itself, per
    `.claude/rules/no-task-references-in-deliverables.md`.
- Ran the definitive full-34 verification sweep (below) and recorded the result here.

## Verification Sweep (full 34 documents)

All 34 documents in `specs/literature-index.json` were checked against the expected
chunk-count/token-count table from the implementation plan.

```
ALL 34 DOCUMENTS MATCH EXPECTED: PASS
```

| Document | Before (this task) | After | Tier that resolved it |
|---|---|---|---|
| alechinamendlerdepaivaritter_2001_categorical_and_kripke_semantics_for_constructive_s4 | 1 | 52 | Tier 2 |
| arisakadasstrassburger_2015_onnestedsequentsforconstructivemodallogics | 1 | 40 | Tier 2 |
| bentzen_2023 | 1 | 33 | Tier 3 |
| biermandepaiva_2000_onanintuitionisticmodallogic | 1 | 53 | Tier 2 |
| blackburn_2002 | 35 | 35 | unchanged (Tier 1, already correct) |
| burgess_1982_i | 1 | 25 | Tier 3 |
| burgess_1982_ii | 1 | 24 | Tier 3 |
| caleiro_2013 | 7 | 7 | unchanged (Tier 1, already correct) |
| chagrovzakharyaschev_1997_modallogic (regression sentinel) | 6 | 6 | unchanged (Tier 1, already correct; never regressed to 997) |
| church_1956 | 7 | 7 | unchanged (Tier 1, already correct) |
| from_2022 | 1 | 34 | Tier 3 |
| gabbay_1993 | 5 | 5 | unchanged (Tier 1, already correct) |
| gabbay_1994_ch10 | 1 | 12 | Tier 3 |
| gentzen_1935 | 5 | 5 | unchanged (Tier 1, already correct) |
| goldblatt_2003 | 5 | 5 | unchanged (Tier 1, already correct) |
| henkin_1949 | 1 | 27 | Tier 3 |
| hodkinson_2006 | 1 | 8 | Tier 3 |
| hughes_1996 | 4 | 4 | unchanged (Tier 1, already correct) |
| johansson_1937 | 1 | 24 | Tier 3 |
| marinmoralesstrassburger_2021_fully_labelled_proof_system_intuitionistic_modal | 1 | 51 | Tier 2 |
| massacci_2000_single_step_tableaux_for_modal_logics (namesake case) | 1 | 77 | Tier 2 |
| mendelson_2016 | 6 | 6 | unchanged (Tier 1, already correct) |
| negri_von_plato_2001 | 7 | 7 | unchanged (Tier 1, already correct) |
| pacheco_2024_collapsingconstructiveandintuitionisticmodallogics | 1 | 19 | Tier 2 |
| post_1921 | 1 | 46 | Tier 3 |
| rabinovich_2014 | 1 | 30 | Tier 3 |
| reynolds_2001 | 10 | 10 | unchanged (Tier 1, already correct) |
| simpson_1994_intuitionisticmodallogic | 1 | 206 | Tier 2 |
| troelstra_schwichtenberg_2000 | 7 | 7 | unchanged (Tier 1, already correct) |
| trufas_2024 | 1 | 48 | Tier 3 |
| venema_1993 | 1 | 1 | residual (Tier 4, sec*.md naming) |
| venema_1993_since | 1 | 1 | residual (Tier 4, sec*.md naming) |
| wijesekera_1990_constructivemodallogicsi | 1 | 38 | Tier 2 |
| zakharyaschev_2001 | 4 | 4 | unchanged (Tier 1, already correct) |

**Totals**: 19 documents repaired (8 via Tier 2, 11 via Tier 3), 13 unchanged and already
correct, 2 residuals unchanged at the Tier-4 literal `1`. 8 + 11 + 13 + 2 = 34.

**Sentinel confirmations**:
- `massacci_2000_single_step_tableaux_for_modal_logics` (the namesake document): 77 chunks — PASS.
- `chagrovzakharyaschev_1997_modallogic` (regression sentinel guarding against re-trusting the
  stale `chunk_count` field): holds at 6, never regresses to 997 — PASS.
- `<!-- lit-coverage mode=repo seg_count=34 sparse=false threshold=3 -->` — unchanged from
  before this task (counts documents, not chunks) — PASS.
- `--global` mode: smoke-tested with `bash .claude/scripts/literature-briefing.sh --global
  "modal logic tableaux"`, returned 8 segments with a `<!-- lit-coverage mode=global
  seg_count=20 sparse=false threshold=3 -->` marker — unaffected by the per-repo-mode changes
  in this task, as expected (the global-corpus code path does not touch the chunk-count
  derivation edited here) — PASS.
- Global index untouched: `~/Projects/Literature/index.json` — no writes performed by this
  script at any point in this task (read-only corpus).
- Wall-clock timing: `time bash .claude/scripts/literature-briefing.sh` — `real 0m2.171s`,
  `user 0m1.794s`, `sys 0m0.872s`. No perceptible regression from the two added fallback tiers
  (both only run per-document when the child-entry count is zero, and even then are a single
  `jq` field lookup or a `find -maxdepth 1` glob).

## Decisions

- Consolidated the Tier 1-4 precedence rationale into one comment block placed at the point of
  use (immediately above the derivation) rather than in the top-of-file usage header, so a
  maintainer reading the derivation logic sees the "why" inline rather than needing to jump to
  a separate section.
- Cleaned up two pre-existing inline comments in the script that referenced an ephemeral task
  number, replacing them with behavior-based descriptions, to bring Phase 1-2's inline comments
  into compliance with the same durable-anchor rule this phase's own new comment follows.
- Left `venema_1993` / `venema_1993_since` as documented residuals rather than adding a fifth
  tier for the `sec*.md` naming convention — out of scope for this task, and a second on-disk
  glob adds a maintenance surface for what is currently a two-document edge case.

## Impacts

- `/research`, `/plan`, and `/implement --lit` invocations against this repository's per-repo
  sub-index now report accurate chunk counts for 19 previously-undercounted documents,
  including the namesake `massacci_2000_single_step_tableaux_for_modal_logics` (1 -> 77).
- No change to token counts, the `<!-- lit-coverage -->` marker's `seg_count` (it counts
  documents, not chunks), or `--global` mode behavior.
- **Known residual — git-tracking gap (important, user-decision required)**: `.claude/` is
  excluded from this repository's git tracking by `.git/info/exclude` line 18 (`/.claude`), a
  machine-local exclusion file that is not shared with the repository. This means
  `.claude/scripts/literature-briefing.sh` — the actual code deliverable of this task — is live
  and working on disk right now, but is **not under version control in this repository**. This
  contradicts the repository's own `.gitignore` line 18 comment (".claude tracked files are
  allowed; ignore only generated/local state"), which implies `.claude/` files should normally
  be tracked. Concretely: the fix documented in this summary will be **lost** on a fresh clone
  of this repository, or if a user restores `.claude/` from the tracked repository state. This
  was confirmed directly: `git ls-files .claude/scripts/literature-briefing.sh` returns nothing
  (untracked), and `git check-ignore -v .claude/scripts/literature-briefing.sh` reports
  `.git/info/exclude:18:/.claude`. Resolving this requires a user decision about git
  configuration (e.g. removing or narrowing the `.git/info/exclude` line 18 exclusion) — this
  task does not modify `.git/info/exclude`, `.gitignore`, or any git configuration, per its
  hard constraints.

## Follow-ups

- **`venema_1993` / `venema_1993_since` still report 1 chunk.** Their on-disk chunk files use a
  `sec*.md` naming convention, not `chunk_*.md`, so the Tier-3 glob correctly finds nothing and
  degrades cleanly rather than erroring. A future task could add a second on-disk glob pattern
  (or a configurable pattern list) if these two documents' accurate chunk counts become
  operationally important; not addressed here as out of scope.
- **17 orphaned `parent_doc` values in the global index** (see
  `reports/01_briefing-chunk-count-defect.md` Recommendation 4): global-index entries whose
  `parent_doc` points at a document ID with no corresponding parent entry. This is a corpus
  data-quality issue in the shared, read-only `~/Projects/Literature/` repository, out of scope
  for this per-repository-briefing-script task.
- **Git-tracking gap** (see Impacts above): a user decision is needed on whether/how to bring
  `.claude/scripts/literature-briefing.sh` (and the rest of `.claude/`) under version control in
  this repository, given the conflict between `.git/info/exclude` line 18 and the `.gitignore`
  line 18 comment's stated intent.

## References

- `specs/560_repair_literature_subindex_massacci_chunks/reports/01_briefing-chunk-count-defect.md`
- `specs/560_repair_literature_subindex_massacci_chunks/plans/01_briefing-chunk-count-repair.md`
- `.claude/scripts/literature-briefing.sh` (not git-tracked in this repository — see Impacts)
