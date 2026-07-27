# Implementation Summary: Task #519

**Completed**: 2026-07-25
**Duration**: single implementation session, 8 phases across both parts

## Overview

Part 1 re-ingested `wijesekera_1990_constructivemodallogicsi` (154 chunks, 468B mean, 62.3% under
300B, spurious mid-sentence headings on 150/154 chunks) by bypassing `literature-convert.sh`'s
font-heuristic entirely: a new durable reflow tool (`literature-reflow-ocr.sh`) rejoins a
`pdftotext -layout` extraction into real paragraphs and inserts only the paper's own 13 numbered
section headings, then the unmodified `literature-chunk.sh` produces the final 38-chunk set
(1669.5B mean, 5.3% under 300B). Part 2 hardened `literature-convert.sh`'s shared no-TOC heading
heuristic with an independent structural signal (numbered-heading pattern + mid-sentence
continuation post-check) alongside a broadened OCR-producer detector, plus added a non-blocking
pathological-mean-chunk-size guard to `literature-ingest.sh`. Both parts verified against the
actual retrieval path and a corpus regression sample; no regression found on any currently-
acceptable document.

## What Changed

- `.claude/scripts/literature-reflow-ocr.sh` — new, durable reflow tool: paragraph-reflow pass
  (indent-window + atomic-keyword cues + blank-line-suppression for atomic statements) and
  heading insertion by raw-line join key against a validated headings TSV.
- `.claude/scripts/literature-convert.sh` — `is_heading_candidate()`/`derive_heuristic_markdown()`
  hardened with two independent signals (font-based, unchanged; structural, new) plus a new
  `detect_ocr_producer()` helper and a mid-sentence continuation post-check applied to both
  signals. `derive_toc_markdown()`, `run_quality_gate()`, and everything else left untouched
  (confirmed via byte-identical re-read).
- `.claude/scripts/literature-ingest.sh` — new non-blocking pathological-mean-chunk-size guard
  (`LITERATURE_MIN_MEAN_CHUNK_BYTES`, default 600B) inserted after the existing chunk-count log
  line; warns via the existing `[...]` banner family without failing the ingest.
- `.claude/context/project/literature/domain/ocr-heading-hardening.md` — new sibling doc to
  `format-decision.md`: two-independent-signals rationale, observed OCR producer signatures, and
  the regression evidence supporting Part 2's non-regression claim.
- `~/Projects/Literature/wijesekera_1990_constructivemodallogicsi/` (separate repo, committed
  there) — 154 old chunks replaced with 38 new ones + reflowed markdown source preserved
  alongside; `metadata.json` and the `index.json` entry refreshed (`chunk_count`, `ingested_at`,
  `provenance_fidelity: "ocr_rescanned_reflowed_partial_symbol_loss"`, an honest summary note).
  `bib_key: Wijesekera1990` unchanged. Global FTS5 index (`.literature.db`) rebuilt.
- `~/Projects/Literature/wijesekera_1990_constructivemodallogicsi.bak-pre-reingest-154chunks/` —
  rollback copy of the old 154-chunk set (kept uncommitted on disk, matching the prior task's
  precedent for this kind of backup).
- `specs/519_fix_literature_ocr_chunking_and_wijesekera/baseline-audit.md`,
  `headings-wijesekera.txt` — Phase 1/2 working artifacts.

## Decisions

- Followed the plan's correction to the task description's premise: OCR-producer detection is
  two independent signals (a broadened substring family AND unconditional structural cues), not
  a Tesseract/OCRmyPDF-only allowlist — the allowlist would have missed this exact document
  (`Acrobat 3.0 Capture Plug-in`).
- Iterated on the reflow tool's paragraph-grouping rules after empirically finding Definition
  1.1.4 split mid-definition in the first working version (enumerated-list markers were flipped
  from "always start a new paragraph" to "never start one, stay glued to the preceding text," plus
  a one-line-lookahead blank-line suppression for atomic-keyword-opened paragraphs, plus an
  `ENUM_RE` regex fix for OCR-fused adjacent markers like `"(l)(i)"`) — the plan explicitly
  authorized this iteration rather than promoting a marginal result.
- Wijesekera's raw source_path in `metadata.json` (pointing at a dead prior-session scratchpad
  directory) was refreshed to the durable Zotero storage path while updating the file anyway.
- The `index.json` summary note deliberately omits a task-number citation, unlike the existing
  Simpson entry's precedent, in the spirit of the no-task-references convention even though
  `~/Projects/Literature/` sits outside that rule's literal repo scope.

## Plan Deviations

- **Task 4.2** (enumerated-list cues as paragraph triggers) altered: flipped to the opposite
  polarity after finding it split Definition 1.1.4 mid-definition — full rationale in the plan's
  Phase 4 deviation note and `progress/phase-4-progress.json`'s `approaches_tried`.
- **Task 8.2** (regression-convert `chagrovzakharyaschev_1997_modallogic`) skipped: its source is
  a DJVU file and this environment has neither `djvutxt` nor `djvups`/`ps2pdf` installed — a
  pre-existing environmental gap, not a Phase 7 issue. Noted rather than silently dropped.

## Findings Worth Flagging (not fixed — out of scope, recorded for future work)

- **`literature-search.sh` fidelity-map bug**: `load_fidelity_map()` only recognizes the older
  `index.json` `path: "sources/..."` schema; newer `doc_id`/`chunks_dir`-schema entries (including
  both Wijesekera's and the pre-existing Simpson entry from a prior task) are silently skipped,
  so their real `provenance_fidelity` is never found and `get_fidelity()`'s fail-open default
  (`unverified_summary`) wrongly quarantines them from default search results.
  `--include-unverified` is the workaround, used throughout Phase 6's validation. Reproduced
  identically on Simpson to confirm this predates this task.
- **`proofs_and_types`'s `auto`-mode conversion currently fails the quality gate** (`pymupdf4llm`
  tier) on a `sentence-boundary-glue: 3` boundary-threshold hit — unrelated to this task's changes
  (that code path was never touched), observed only because the Phase 8 regression run happened
  to exercise it.
- **The original 154-chunk Wijesekera corpus does not reproduce under the current environment's
  fallback heuristic** (pre- or post-hardening — both land around 59-62 chunks under
  `LITERATURE_CONVERTER=fallback`), suggesting the original ingestion ran under different
  library-version/environment conditions than exist today. Recorded in `ocr-heading-hardening.md`;
  did not change the Part 2 regression conclusion.

## Verification

- Build: N/A (no compiled artifacts)
- Tests: `bash -n` passes on all three modified/new scripts; the embedded Python in
  `literature-convert.sh` compiles; a 9-case standalone unit-test suite for
  `is_heading_candidate()`/`detect_ocr_producer()` passes, including the explicit Phase 7
  verification criterion (structural cues reject a synthetic mid-sentence bold/large span with no
  producer metadata present); the Phase 3 guard tested against synthetic healthy/breach/forced-
  breach fixtures, all preserving exit status.
- Files verified: production chunk count (38) matches `index.json` and the FTS5 index; backup
  directory intact (154 files + `chunks.json.bak-inactive`); `Cslib/` untouched; `literature-
  chunk.sh` untouched (mtime unchanged).
- Retrieval acceptance (Phase 6, via `literature-search.sh --include-unverified`): Definition
  1.1.4 complete (chunk `ecabd94d9eea5595`); box/diamond independence statement complete (chunk
  `dea76c3d5f47bab5`); Definitions 1.1.1-1.1.3 contiguous across a clean boundary (no definition
  cut); zero mid-sentence-fragment titles; zero `"X > X"` self-duplicating breadcrumbs across all
  38 chunks.
- Regression (Phase 8): all 5 convertible no-TOC/priority sample documents structurally unaffected
  by the Phase 7 heuristic change (4 resolve to the untouched primary `pymupdf4llm` tier, 1 to the
  untouched `derive_toc_markdown()` TOC path, confirmed byte-identical old-vs-new on that one via
  a reconstructed pre-Phase-7 copy of the script). `chagrovzakharyaschev_1997_modallogic` (djvu)
  untestable in this environment.

## Notes

Neither `.claude/scripts/*.sh` nor `.claude/context/**/*.md` changes are committed to the cslib
git repository — `.git/info/exclude` deliberately excludes `.claude/` from this repo's tracked
history. Those file edits are real and live on disk, but this repo's git log will not show them;
only the `specs/519_fix_literature_ocr_chunking_and_wijesekera/` task-tracking artifacts are
committed here, one commit per phase. The `~/Projects/Literature/` changes (production corpus,
`index.json`, `.literature.db`) are committed in that repository's own independent git history
(a single commit covering the promoted Wijesekera directory, `index.json`, and the rebuilt
`.literature.db`; the rollback backup directory kept intentionally uncommitted, matching the
established convention for this kind of backup).
