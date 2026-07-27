# Implementation Summary: Task #555 Round 2 (Phases 6-7)

**Completed**: 2026-07-26
**Duration**: ~1.5 hours across Phases 6-7 (Phases 1-5 were completed and committed in round 1)

## Overview

This round executed the two phases left revised-but-not-yet-implemented by plan v2: Phase 6
closed out the former DJVU-install blocker (found to be moot) and re-adjudicated the remaining
quarantined document; Phase 7 produced a decision memo surfacing the Group B disposition, the
Group A regression, and residual findings to the user without stamping any value or editing any
policy constant.

## What Changed

- `.claude/scripts/literature-search.sh` — restored from `HEAD` (335c034a) via
  `git checkout HEAD --`, undoing an uncommitted revert that had removed the entire four-site
  `doc_id` fallback fix. No new logic added in this round.
- `.claude/scripts/literature-fidelity-audit.sh` — restored from `HEAD`, then repointed the
  `--legacy-schema` startup guard (no longer hard-fails on absent/empty `.sources-recovered/`)
  and `classify_legacy()`'s source resolution (prefers `sources/<doc_id>/source.{pdf,djvu}`,
  falls back to `.sources-recovered/<doc_id>.{pdf,djvu}` only if present) to match the Literature
  repo's migration of recovered sources into the canonical `sources/` layout. Header comments and
  `usage()` text updated to match.
- `specs/literature/SOURCES.md` — annotated the Part II note about recovered sources to record
  that they were migrated into `sources/<doc_id>/` and that `.sources-recovered/` is now empty.
  Documentation-only change; the file was not restructured.
- `specs/555_literature_search_fidelity_schema_quarantine/summaries/02_group-b-decision-memo.md` —
  new. The Phase 7 deliverable: restates options (b)/(c)/(d) with concrete costs, reports the
  Group A regression, states plainly that `no_source_pdf` is citable by default, and records
  residual findings (djvu gate closure, arisaka's quarantined outcome, gabbay_1994, the
  `.sources-recovered/` migration, the now-no-op Phase 1-5 code, and an incidental
  measurement side effect on 8 `burgess_1984` sub-entries).
- `specs/555_literature_search_fidelity_schema_quarantine/summaries/02_blocker-resolution-summary.md` —
  this file.
- `$LITERATURE_DIR/index.json` (data, not repo source): Phase 6.4's default-mode `--write` run
  re-stamped `arisakadasstrassburger_2015` with its already-current value (`unadjudicated`,
  `word_ratio` 0.539 — no change), and incidentally recomputed `word_ratio` for 8
  `burgess_1984_secNN` entries (drift `1.0041` → `1.0033`, no `provenance_fidelity` class change,
  a side effect of the script's full-corpus recompute — it has no single-document mode). A
  timestamped `index.json.bak.<ts>` backup was written by the script's existing safety mechanism
  before the write. Phase 7 caused no write to `index.json` at all (verified: byte-identical to
  the post-Phase-6 snapshot).

## Decisions

- Restored both scripts from `HEAD` rather than treating the uncommitted revert as a deliberate
  concurrent decision, per the plan's explicit rationale: `HEAD` is the committed record of
  already-verified work, the revert was unexplained by any commit, and a
  `git-snapshot.sh --no-revert` checkpoint (patch:
  `working-progress-1785112536.patch`) makes the revert recoverable if that assessment turns out
  to be wrong.
- Ran the `arisakadasstrassburger_2015` re-adjudication in default mode rather than
  `--legacy-schema`, per the plan's schema-driven decision table — the entry's `path`/`id` fields
  confirmed it had already migrated to the `sources/` schema.
- Did not adjust `RATIO_THRESHOLD`, `PROOF_ADEQUACY_THRESHOLD`, or `QUARANTINED_FIDELITY_VALUES`,
  and did not hand-stamp a different value for `arisakadasstrassburger_2015` to force it to
  surface. Its quarantined outcome is recorded as the honest, measured result.
- Phase 7 chose no option among (b)/(c)/(d) and took no action on the Group A regression or the
  Phase 1-5 code-retirement question. All three are surfaced in the decision memo for the user.

## Plan Deviations

- **Task 6.4** (diff assertion): the plan expected the `index.json` entry-by-entry diff to show
  no changed document other than `arisakadasstrassburger_2015`. In practice, `arisaka` itself
  showed no change (it was already stamped with the same value, so it is absent from the diff
  rather than present-and-identical), and 8 `burgess_1984_secNN` entries showed incidental
  `word_ratio` drift as a side effect of the script's full-corpus `--write` recompute (no
  single-document mode exists). No `provenance_fidelity` value changed for any document. Recorded
  in the plan's Phase 6.4 annotation and in the decision memo section 4; not actioned, per the
  same no-threshold/no-hand-stamp discipline governing arisaka.

(All other tasks in Phases 6-7 completed as planned.)

## Verification

- Both scripts pass `bash -n`.
- `grep -c 'doc_id = e.get("doc_id")' literature-search.sh` = 4;
  `grep -c 'fmap.get(doc_id) or "unverified_summary"' literature-search.sh` = 4.
- `--legacy-schema --dry-run` exits 0, reports 0 entries (expected post-migration result, not a
  failure).
- Default no-flag search returns `degraded: false` with non-quarantined values for
  `chagrovzakharyaschev_1997_modallogic`, `wijesekera_1990_constructivemodallogicsi`, and
  `simpson_1994_intuitionisticmodallogic`.
- `arisakadasstrassburger_2015` absent from default search, present under
  `--include-unverified` with `unadjudicated`.
- `RATIO_THRESHOLD` (0.75), `PROOF_ADEQUACY_THRESHOLD` (0.6), and `QUARANTINED_FIDELITY_VALUES`
  (`"unverified_summary unverified_no_baseline unadjudicated"`) all unchanged at task end.
- Decision memo exists (198 lines), covers `no_source_pdf`, options (b)/(c)/(d), Wijesekera,
  Simpson, and `QUARANTINED_FIDELITY_VALUES` (all verified present via grep).
- Phase 7 modified no script (`git status --short -- .claude/scripts/` empty) and caused no
  `index.json` write (byte-identical to the post-Phase-6 snapshot).
- No file under `Cslib/` and no `.lean` file modified at any point in either phase.

## Notes

The task's three open decisions (Group B disposition, Group A regression restoration, Phase 1-5
code retirement) are all recorded in
`summaries/02_group-b-decision-memo.md` for the user to resolve at their discretion. No further
automated work is expected on this task until that memo is reviewed.
