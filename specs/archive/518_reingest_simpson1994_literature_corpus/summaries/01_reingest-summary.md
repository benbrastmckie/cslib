# Task 518: Re-ingest Simpson 1994 into the Literature corpus

## Outcome: SUCCESS

Simpson 1994 (*The Proof Theory and Semantics of Intuitionistic Modal Logic*, BibKey
`Simpson1994`, doc_id `simpson_1994_intuitionisticmodallogic`) has been re-converted and
re-chunked in the global Literature corpus (`~/Projects/Literature/`). The corpus is now
usable for reading complete lemma/theorem statements.

## Diagnosis

- **Source**: `/home/benjamin/Downloads/Simpson_1994_IntuitionisticModalLogic.ocr.pdf`
  (OCRmyPDF 17.4.2 / Tesseract 5.5.2 over a 219-page scanned PDF, LFCS report
  ECS-LFCS-94-308). No embedded PDF outline/TOC (`fitz.Document.get_toc()` returns empty).
- **Old state**: 1091 chunks, ~312 byte mean, hundreds of 120-140 byte fragments.
- **Root cause**: `literature-convert.sh`'s PyMuPDF conversion path has two branches —
  one uses an embedded TOC for headings, the other (used here, since there is no TOC)
  falls back to font-size-heuristic heading detection. On this OCR'd scan, per-line font
  metrics from Tesseract's invisible text layer are noisy enough that the heuristic
  inserted spurious `## heading` markers mid-sentence and even mid-word (e.g. one false
  heading was literally "tuitionistic or clas..." — a mid-word truncation of
  "intuitionistic or classical"). `literature-chunk.sh` Pass 1 splits at every heading
  boundary, so each false heading became its own tiny chunk. Combined with `pdftotext`
  emitting extra blank lines at OCR line-break noise, the result was systematic
  over-fragmentation that sliced directly through lemma statements — e.g. Lemma 5.3.1's
  "there is a T-prime context (H," / "A) with (H,A) ≥ (G,Γ) ..." was split across two
  separate chunks (chunk_0417/chunk_0418 in the old numbering).

## Fix

Bypassed the font-heuristic path entirely (this was a targeted fix for Simpson only —
`literature-convert.sh`/`literature-chunk.sh` were not modified, so no other corpus
document is affected):

1. Extracted full text via plain `pdftotext -layout` (219 pages).
2. Custom Python paragraph-reflow pass: joins OCR line-break noise into real paragraphs
   using an indent window (2-4 leading spaces = real first-line paragraph indent; deeper
   indents are wrapped-math-expression alignment artifacts, not paragraph breaks) plus
   atomic-keyword (`Lemma|Theorem|Definition|Proof|...`) and enumerated-list start cues.
3. Inserted only 9 chapter-level `## Chapter N: Title` headings (derived from the
   stripped running header "Chapter N.  Title  NN"), instead of hundreds of false
   sub-headings.
4. Fed the resulting markdown through the existing (unmodified)
   `.claude/scripts/literature-chunk.sh` Pass-2 merge logic (target 512 tokens/chunk).

**Result**: 206 chunks, mean 1768 bytes (up from 312), max 2316 bytes, only 3 chunks
(1%) under 300 bytes (down from 764/70%).

## Validation (acceptance test)

All four target passages verified present and **structurally intact** (not truncated)
via `.claude/scripts/literature-search.sh` and direct `--read`:

| Query target | Chunk ID | Status |
|---|---|---|
| Lemma 5.3.1 (Prime lemma) | `b7b7543b80021f0d` | Full statement + proof intact |
| Lemma 5.3.2 (Canonical model lemma) | `e2c9da9458f24650` | Full statement intact (co-located with end of 5.3.1's proof) |
| Theorem 6.2.1 | `342383d3ad79a9af` | Full "following are equivalent" statement (items 1-2) intact |
| p.161 "other than IS5" passage | `89b8708e61d12778` | Verbatim: "Henceforth, we fix L as any logic in Dec_T, other than IS5." — confirms task 517's finding that Ch. 8 explicitly excludes IS5 |

Note: FTS5 queries containing periods (e.g. `"Lemma 5.3.1"`) or hyphenated terms (e.g.
`"T-prime"`) trigger a pre-existing `literature-search.sh` sanitizer bug ("syntax error
near '.'" / "no such column"), unrelated to this task's fix — word-based queries work
correctly and all four chunks were independently confirmed via `--read <chunk_id>`.

## Re-indexing

- `~/Projects/Literature/index.json`: updated the `simpson_1994_intuitionisticmodallogic`
  doc-level entry (`chunk_count`: 1091 -> 206, `ingested_at` refreshed, added
  `provenance_fidelity: "ocr_rescanned_reflowed_partial_symbol_loss"` and an honest note
  in `summary` about the OCR ceiling).
- `~/Projects/Literature/.literature.db` (global FTS5): rebuilt via
  `literature-build-index.sh --global` (8981 -> 7890 total chunks across the corpus,
  reflecting the 1091 -> 206 Simpson delta).
- `specs/literature-index.json` (cslib sub-index): no change needed — it references
  `simpson_1994_intuitionisticmodallogic` only by `doc_id`, which is unchanged.
- BibKey linkage (`Simpson1994`) preserved.

## Safety / working-state preservation

The old 1091-chunk set was **not deleted**. It was moved to
`~/Projects/Literature/simpson_1994_intuitionisticmodallogic.bak-pre518-1091chunks/` and
its `chunks.json` renamed to `.bak-inactive` so `literature-build-index.sh` does not
pick it up. This directory is kept on disk as a rollback safety net but was
**deliberately not committed to git** (would add 1091 files being actively replaced to
history for no ongoing benefit). The new chunks were validated in a scratch directory
before touching production, per the task's ordering constraint.

## OCR quality ceiling (honest assessment)

Tesseract's OCR of this scan is **good for prose** — full sentences, section structure,
and lemma/theorem/proof boundaries are reliably recoverable. It is **unreliable for
mathematical notation**: turnstiles (⊢), Gamma/Delta (Γ/Δ), set membership (∈), and
similar symbols are frequently misrecognized (e.g. "⊢" as "V/5" or "I/g", "Γ" as "7" or
"T", "∈" as "€"). Anyone citing exact symbolic notation from these chunks should
cross-check against the source PDF at
`/home/benjamin/Downloads/Simpson_1994_IntuitionisticModalLogic.ocr.pdf`. This is a
ceiling of the available scan/OCR quality, not an artifact of the chunking fix — no
attempt was made to "clean up" or guess at garbled symbols.

## Audit: other large corpus documents

Checked mean chunk size for all 20 doc-level entries in the global index (chunk_count
sorted descending):

| Chunks | Mean bytes | % under 300B | doc_id |
|---|---|---|---|
| 997 | 1434 | 7% | chagrovzakharyaschev_1997_modallogic — OK |
| 206 | 1768 | 1% | simpson_1994_intuitionisticmodallogic — fixed by this task |
| 176 | 1662 | 7% | proofs_and_types — OK |
| **154** | **468** | **62%** | **wijesekera_1990_constructivemodallogicsi — FRAGMENTED, needs the same fix** |
| 107 | 1368 | 12% | cariani future-directed thought — OK |
| (all others, <80 chunks each) | 1370-2014 | 0-20% | OK |

**`wijesekera_1990_constructivemodallogicsi` (Wijesekera 1990, cited as a BibKey in task
517's dependency chain) shows the identical over-fragmentation signature**: 154 chunks,
468-byte mean, 62% of chunks under 300 bytes, self-duplicating breadcrumb titles
(e.g. "accessibility, relat... > accessibility, relat..."), and mid-sentence chunk
boundaries (spot-checked chunk_0010-0012). This is very likely the same root cause
(scanned/OCR'd PDF, no embedded TOC, PyMuPDF font-heuristic misfire) and is a strong
candidate for a follow-up task using the same reflow approach. **Not fixed here** per
task scope — reported only.

## Impact on downstream tasks

- Task 517 can now cite Simpson Ch. 5-6 (Prime Lemma 5.3.1, Canonical Model Lemma
  5.3.2, Adequacy Theorem 6.2.1) and Ch. 7-8 material directly from the corpus via
  `literature-search.sh` / `Read`, rather than bypassing it to read the source PDF.
- The Ch. 8 "other than IS5" exclusion (p.161) is now directly verifiable in the corpus,
  correcting the citation error in task 516's report 02.
- A new follow-up task should be filed for `wijesekera_1990_constructivemodallogicsi`
  before it is relied on for precise lemma citation.

## Files changed (Literature repo, not cslib)

- `~/Projects/Literature/index.json` (Simpson entry updated)
- `~/Projects/Literature/.literature.db` (rebuilt)
- `~/Projects/Literature/simpson_1994_intuitionisticmodallogic/` (206 new chunk files +
  `chunks.json` manifest + `simpson_1994_intuitionisticmodallogic.reflowed.md` source)
- `~/Projects/Literature/simpson_1994_intuitionisticmodallogic.bak-pre518-1091chunks/`
  (old 1091 chunks, preserved uncommitted as rollback safety net)

Committed in the Literature repo: `task 518: re-chunk Simpson 1994 to fix mid-lemma
truncation` (session `sess_1784127828_1f2b2f`).

No `Cslib/` Lean source was touched.
