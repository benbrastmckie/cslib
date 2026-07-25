# Implementation Summary: Task #555

**Completed**: 2026-07-25
**Duration**: ~1 session

## Overview

Restored default (no-flag) literature search visibility for legacy-schema (`doc_id`/`chunks_dir`)
index entries by fixing the directory-name-only key derivation in `load_fidelity_map()`, then
extended `literature-fidelity-audit.sh` with a `--legacy-schema` classification and write mode
that computed and stamped honest `provenance_fidelity` values for the source-recoverable Group B
documents. Phases 1-5 (Stage A + Stage B) are complete and verified against the live corpus.
Phases 6-7 are explicit gates and were not resolved, per the plan's instruction.

## What Changed

- `.claude/scripts/literature-search.sh` — `load_fidelity_map()` at all four sites
  (`do_search` primary, the unscoped-retry fallback, `do_read`, `do_toc`) gained a `doc_id`-keyed
  fallback branch for entries whose `path` is not a `sources/`-prefixed string. The
  `sources/`-schema branch, `get_fidelity()`'s fail-open behavior, and `QUARANTINED_FIDELITY_VALUES`
  are all unchanged.
- `.claude/scripts/literature-fidelity-audit.sh` — added `--legacy-schema` mode:
  `enumerate_legacy_entries()`, `classify_legacy()`, `resolve_legacy_targets()`, and a
  `main_legacy()` write path routed separately from the existing `main_default()` (renamed from
  the original `main()`; both are dispatched from a new top-level `main()`). Default (sources/-
  schema) behavior is byte-identical to its pre-change baseline.
- `specs/555_literature_search_fidelity_schema_quarantine/plans/01_fidelity-key-derivation-and-legacy-audit.md`
  — phase statuses and per-task completion notes updated through Phase 5.
- Out-of-repo: `$LITERATURE_DIR/index.json` gained `provenance_fidelity`/`word_ratio` on 5 legacy
  entries (see "Fidelity Outcomes" below), backed up first to a timestamped
  `index.json.bak.<ts>` by the script's own safety mechanism.

## Decisions

- Patched `load_fidelity_map()` identically at all four sites rather than factoring into a shared
  module, per the research report's rationale (separate subprocess heredocs, no shared import
  path; the existing "full docstring at primary site, short comment at the other three" is the
  codebase's own established convention for this function).
- `--legacy-schema` mode reuses `disclosure_check()`/`proof_completeness_fraction()` unchanged
  against `chunk_*.md` text (no chunk-exclusion filter applied, since for this schema the chunks
  ARE the document).
- A `.djvu` (or any source producing 0 extracted words) is classified `unadjudicated` with an
  explicit `[blocked]` stderr note, never `unverified_no_baseline` — a baseline exists, only the
  extractor is missing. Tracked via a `djvu_blocked` flag distinct from the ordinary
  "no numbered statements to check" `unadjudicated` path, so the write loop can key its skip
  decision on it precisely.
- **Group A protection (SIX_VALUE_ENUM guard)**: the legacy write loop skips stamping any entry
  whose current `provenance_fidelity` is already set to a value outside this script's own
  six-value enum. This was added after Phase 4's first write attempt overwrote Group A's
  pre-existing, more specific `ocr_rescanned_reflowed_partial_symbol_loss` value with the generic
  detector's `verified_conversion` — see "Plan Deviations" below.
- `QUARANTINED_FIDELITY_VALUES` was never modified. The fail-open-to-unverified design is
  unweakened: a synthetic unknown `doc_id` and every Group-B document not covered by this task
  still resolve to `unverified_summary`.

## Plan Deviations

- **Real regression caught and fixed mid-Phase-4, not anticipated by the plan text verbatim**: the
  plan's Phase 4 verification anticipated "at most 6 changed entries." The first `--legacy-schema
  --write` run stamped 7 entries — it recomputed `verified_conversion` for Group A's two
  already-honestly-stamped documents (`wijesekera_1990`, `simpson_1994`) via the generic six-value
  detector, clobbering their more specific `ocr_rescanned_reflowed_partial_symbol_loss` value.
  This was caught by the plan's own verification harness (7 > "at most 6"), not silently missed.
  Fix: restored Group A from the pre-write scratchpad snapshot
  (`$SCRATCH/index.before.json`) and added the `SIX_VALUE_ENUM` guard described above. Re-ran
  `--write`; the corrected result is 5 changed entries, `NON-LEGACY TOUCHED: []`, Group A
  untouched, and idempotent on a second run (`changed: 0`). This is a within-scope bug fix to the
  Phase 4 implementation, not a plan-scope change — no plan task was skipped or altered.
- No other deviations. All Phase 1-5 tasks completed as specified.

## Fidelity Outcomes (for the user, ahead of Phase 6/7 decisions)

| doc_id | provenance_fidelity | word_ratio | Default-search visible? |
|---|---|---|---|
| `wijesekera_1990_constructivemodallogicsi` | `ocr_rescanned_reflowed_partial_symbol_loss` (unchanged, pre-existing) | — | Yes (Phase 1 fix) |
| `simpson_1994_intuitionisticmodallogic` | `ocr_rescanned_reflowed_partial_symbol_loss` (unchanged, pre-existing) | — | Yes (Phase 1 fix) |
| `biermandepaiva_2000_onanintuitionisticmodallogic` | `verified_conversion` | 1.0349 | Yes |
| `marinmoralesstrassburger_2021_fully_labelled_proof_system_intuitionistic_modal` | `verified_conversion` | 1.0158 | Yes |
| `pacheco_2024_collapsingconstructiveandintuitionisticmodallogics` | `verified_conversion` | 1.0298 | Yes |
| `alechinamendlerdepaivaritter_2001_categorical_and_kripke_semantics_for_constructive_s4` | `verified_conversion` | 1.0203 | Yes |
| `arisakadasstrassburger_2015_onnestedsequentsforconstructivemodallogics` | `unadjudicated` | 0.539 | **No** — quarantined (honest outcome; ratio below threshold, undisclosed, no numbered statements to adjudicate proof-completeness) |
| `chagrovzakharyaschev_1997_modallogic` | left as-is (no stamp) | — | No — **Phase 6 gate**, unresolved: no DJVU text extractor on this machine |
| 10 unrecoverable docs (incl. `massacci_2000_single_step_tableaux_for_modal_logics`) | left as-is (no stamp) | — | No — **Phase 7 gate**, unresolved: disposition is an explicit user decision |

## Verification

- Build: N/A (bash/Python scripts, no compile step)
- Tests: All phase-level verification commands from the plan were run against the live corpus and
  passed:
  - `bash -n` clean on both scripts.
  - Phase 1 map-diff harness: `old 95 / new 97`, added = exactly the two Group A `doc_id`s,
    removed/changed empty.
  - Phase 2: default search for Wijesekera and Simpson content returns `degraded: false`,
    `fallback_tier: "bm25"`, correct `provenance_fidelity`. `--include-unverified` superset
    confirmed; Group B still `unverified_summary` under the flag; `do_read`/`do_toc` exercised
    cleanly.
  - Phase 3: `--legacy-schema --dry-run` reproduces all five hand-computed ratios within the
    plan's tolerance; default-mode `--dry-run` output byte-identical to a reconstructed pre-change
    baseline.
  - Phase 4: `--legacy-schema --write` run twice; second run `changed: 0`. Post-write diff against
    the pre-Phase-4 snapshot: 5 changed entries, all `legacy=True`, `NON-LEGACY TOUCHED: []`.
  - Phase 5: default search for all 4 newly-`verified_conversion` documents returns
    `degraded: false`; `arisakadasstrassburger_2015` confirmed absent from default search and
    still visible (as `unadjudicated`) under `--include-unverified`; final map-diff harness
    confirms `old 95 / new 102`, zero removed/changed among pre-existing keys.
- Files verified: Yes (both scripts pass `bash -n`; `index.json` diffed entry-by-entry before and
  after each write; `QUARANTINED_FIDELITY_VALUES` confirmed unchanged).

## Notes

Two gates remain open and were deliberately NOT resolved, per the plan's explicit instruction:

- **Phase 6 (DJVU extractor)**: `chagrovzakharyaschev_1997_modallogic` cannot be classified on
  this machine — neither `djvutxt` nor `djvups` is installed, and this build of PyMuPDF (1.27.2)
  raises `FileDataError` on the recovered `.djvu`. No package was installed and no OCR workaround
  was attempted. Resolution requires either installing `djvulibre` (preferred; no code change
  needed afterward — re-run `--legacy-schema --write`) or a separate, explicitly-approved OCR-based
  approach.
- **Phase 7 (10 unrecoverable documents)**: their disposition is an explicit user decision between
  option (b) per-document adjudication to `unverified_no_baseline`, option (c) a new
  non-quarantined fidelity value, and option (d) leaving them at the current `unverified_summary`
  fail-open. No value was stamped and `QUARANTINED_FIDELITY_VALUES` was not modified. Only
  `massacci_2000_single_step_tableaux_for_modal_logics` is referenced by this repository's
  `specs/literature-index.json`; the other 9 are not referenced by cslib at all.
