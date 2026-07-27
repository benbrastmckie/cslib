# Research Report: Task #519

**Task**: 519 - Fix literature OCR chunking and re-ingest Wijesekera 1990
**Started**: 2026-07-24
**Completed**: 2026-07-24
**Effort**: 3-5 hours (implementation)
**Dependencies**: Task 518 (Simpson 1994 re-ingest — proven procedure this task adapts)
**Sources/Inputs**: `specs/archive/518_reingest_simpson1994_literature_corpus/summaries/01_reingest-summary.md`, `.claude/scripts/literature-convert.sh`, `.claude/scripts/literature-chunk.sh`, `.claude/scripts/literature-ingest.sh`, on-disk Literature corpus (`~/Projects/Literature/wijesekera_1990_constructivemodallogicsi/`), source PDF, `Cslib/Logics/Modal/Metalogic/Constructive/CS4.lean` and `CS5.lean`
**Artifacts**: this report
**Standards**: report-format.md, subagent-return.md

## Executive Summary

- Confirmed on disk: `wijesekera_1990_constructivemodallogicsi` currently has 154 chunks, mean
  468 bytes, 96/154 (62.3%) under 300 bytes — matches task 518's audit exactly. 150 of 154
  chunks (97%) carry a spurious mid-sentence/mid-phrase heading title (e.g. `'and (0111).'`,
  `'C+I'`, `"'"`), confirming the identical font-heuristic over-fragmentation signature found in
  Simpson 1994.
- Root cause confirmed structurally identical to Simpson: no embedded PDF TOC
  (`doc.get_toc() == []`), so `literature-convert.sh` falls through to
  `derive_heuristic_markdown()`'s font-size/bold heading heuristic, which fires on noisy
  per-span font metrics from the OCR text layer, and `literature-chunk.sh` Pass 1 then splits at
  every false heading.
- **Important refinement vs. Simpson**: Wijesekera's OCR producer is **not** Tesseract/OCRmyPDF —
  `pdfinfo`/`fitz.metadata` report `Creator: Acrobat 3.0 Capture Plug-in`,
  `Producer: Acrobat 3.0 Import Plug-in` (Adobe Acrobat Capture, a 2001-era scan-to-searchable-PDF
  OCR tool, consistent with this being a 1990 APAL journal article scanned for archival). This
  means a producer-string allowlist limited to `Tesseract`/`OCRmyPDF` (as literally named in the
  task description) would **miss this exact document** — the hardening fix (Part 2) must either
  broaden the producer signature list or lean primarily on structural corroborating cues, not an
  OCR-tool allowlist. See Findings §3 for the concrete recommendation.
- The reingest procedure from task 518 transfers cleanly, with one adaptation: Wijesekera is a
  31-page single-column journal article (not a 219-page scanned book), and `pdftotext -layout`
  reliably surfaces its own numbered section/subsection headings (`1.`, `1.1.`, ..., `2.3.`, `3.`,
  etc. — 14 clean hits via a simple regex, see Findings §4) directly in the body text. This is a
  **better** heading source than Simpson's chapter-only running-header derivation and should be
  used instead (finer section granularity, still bypasses the font heuristic entirely).
- Target passages for validation: Definition 1.1.4 (the intuitionistic modal frame quintuple
  `(K, ≤, D, R, ⊩)`) is currently intact and un-split, sitting inside `chunk_0020.md` — the
  content itself is not truncated by the 512-token merge, only mis-titled. The core "diamond does
  not distribute over disjunction; independent, non-interdefinable box and diamond" motivational
  statement (task 517/CS4/CS5's citation target) is intact in `chunk_0002.md`. This means content
  loss is less severe than titles suggest, but citation/retrieval quality (breadcrumbs,
  section-path search) is still badly degraded and should still be fixed per the task's
  specification.
- Recommend implementing Part 2 (root-cause hardening) **before** re-running Part 1's ingest via
  the general pipeline, OR keep using the same bespoke-reflow escape hatch task 518 used (bypass
  `literature-convert.sh` entirely for this one document) if the general fix isn't ready yet —
  either path reaches a valid re-ingested Wijesekera corpus; recommend doing Part 2 first since it
  is lower-risk and unblocks future ingests too.

## Context & Scope

Task 519 has two parts, both scoped to `.claude/scripts/` and the Literature repo — no `Cslib/`
Lean source is touched:

1. Re-ingest `wijesekera_1990_constructivemodallogicsi` using the proven bespoke-reflow procedure
   from task 518 (Simpson 1994), validating that Definition 1.1.4 and the Section 2
   diamond/fallible-world material return complete via `literature-search.sh`.
2. Harden `literature-convert.sh`'s no-TOC heading heuristic so it does not fire pathologically on
   OCR'd scans in general, plus add a loud low-mean-chunk-size guard to the ingest pipeline.

This report investigates and inventories both parts; it does not perform the re-ingest or edit
the scripts (that is implementation work for `/plan` + `/implement`).

## Findings

### 1. Current on-disk state of Wijesekera (confirmed, not assumed)

- Global index entry (`~/Projects/Literature/index.json`): `doc_id:
  wijesekera_1990_constructivemodallogicsi`, `chunk_count: 154`, `bib_key: Wijesekera1990`,
  `ingested_at: 2026-07-13T23:15:07Z`.
- Chunk directory: `~/Projects/Literature/wijesekera_1990_constructivemodallogicsi/` — 154
  `chunk_NNNN.md` files + `chunks.json` manifest + `metadata.json` (no cached authors/year — those
  fields are empty in `metadata.json`, only populated in the top-level `index.json` entry).
- Recomputed directly from `chunks.json`'s `token_count` field (×4 bytes/token) and independently
  from actual chunk-file byte sizes on disk — **both agree**: mean 468 bytes, 96/154 (62.3%) under
  300 bytes. This is an exact match to task 518's audit table, confirming the audit is still
  accurate and nothing has changed since.
- `chunks.json`'s `title` field for 150 of 154 chunks (97%) is a mid-sentence/mid-phrase fragment,
  not a real section heading, e.g.: `'minimal set of axioms and semantics are general enough to
  cover the natural'`, `'of free and bound variables. (cont.)'`, `'Weakening'`, `'Exchange'`,
  `"'"` (a single closing-quote character), `'C+I'` (a garbled inline formula), `'r>>A,cp
  cp,n>>n'` (garbled sequent notation). Section-path breadcrumbs self-duplicate exactly as in
  Simpson (`"of free and bound va... > of free and bound va..."`), because the same title string
  becomes both the current heading and its own last ancestor in the breadcrumb stack.
- Source PDF located via the index's `source_path`:
  `/home/benjamin/Documents/Zotero/storage/HDH8YF7H/Wijesekera - 1990 - Constructive modal logics
  I.pdf` (2.2 MB, 31 pages, page size 533×749pt). `fitz.Document.get_toc()` returns `[]` (no
  embedded outline) — confirms the no-TOC fallback path is the one that ran.

### 2. Content-loss assessment: less catastrophic than the title corruption suggests

Spot-checking the two passages the task calls out by name:

- **Definition 1.1.4** (intuitionistic modal frame quintuple `(K, ≤, D, R, ⊩)`, cited in
  `CS4.lean:83` and `CS5.lean:131` as `"[D. Wijesekera, Constructive modal logics I][Wijesekera1990],
  §2 and Definition 1.1.4"`) is **not** split across chunks — it reads complete, start to finish,
  inside `chunk_0020.md`. (Note: the docstring citation says "§2" but the actual definition is in
  §1.1 per the source PDF's own section numbering — this is a pre-existing citation-precision
  question for a separate task, not something this task should silently "fix" by relocating the
  definition; flagging only.)
- The core diamond-independence motivational statement — *"both box and diamond are needed, but
  these two are not intuitionistically interdefinable and, worse, diamond does not distribute
  over 'or' ... We provide intuitionistic logics with independent box and diamond without
  assuming distribution of diamond over 'or'"* — is intact, unsplit, inside `chunk_0002.md`.
- What **is** damaged: (a) breadcrumb/title garbage makes `literature-search.sh`'s summary/title
  fields useless for browsing or relevance ranking, (b) some multi-part definitions **are** split
  mid-sequence — e.g. Definitions 1.1.1–1.1.3 straddle `chunk_0018`/`chunk_0019` with an OCR-noise
  artifact mid-definition (`"A@,, . . . , Xi, . , . , xi"` — garbled subscript/superscript
  notation, a `derive_heuristic_markdown` reading-order/OCR artifact, not a chunking-boundary
  artifact), and (c) OCR of math symbols is unreliable throughout (turnstile `⊩` renders as `It`
  or `Ik`, `≤` as `s` or `=z`, etc. — the same "honest ceiling" task 518 documented for Simpson).
- **Conclusion for the re-ingest**: the fix is still clearly warranted (breadcrumb quality,
  section-path search, and the several genuinely-split multi-part definitions all justify it), but
  the acceptance-test framing should be "produces clean, correctly-titled, non-duplicated-breadcrumb
  chunks with intact atomic blocks" rather than "recovers content that was previously
  inaccessible" — most content is technically present today, just badly indexed/titled.

### 3. Root cause — confirmed identical mechanism, DIFFERENT OCR producer

`literature-convert.sh`'s no-TOC path (`derive_heuristic_markdown()`, lines 459-497) is exactly
the code path that ran, confirmed by three independent signals:
1. `doc.get_toc()` is empty (line 503's branch: `if doc.get_toc(): ... else: return
   derive_heuristic_markdown(doc), "pymupdf-fallback-heuristic"`).
2. The `chunks.json` titles show the exact defect signature `is_heading_candidate()` (lines
   433-456) is supposed to prevent but doesn't fully: short (≤80 char), no-trailing-`.,;`,
   bold-and-1.15×-body-size spans firing on noisy OCR font metrics rather than genuine headings.
   This confirms the **already-tightened heuristic (per the in-file "BUG 3 fix" comment
   referencing prior work) is still insufficient** for this class of document — punctuation/
   length/bold/size checks alone do not reliably distinguish a real heading from a bold/large OCR
   artifact span.
3. No `literature-pyenv/venv` directory currently exists under `.claude/scripts/` (the
   `pymupdf4llm` primary-tier venv), consistent with the mandatory PyMuPDF fallback tier having
   run at ingest time — though this is not fully conclusive since the venv is gitignored/ephemeral
   and could have been provisioned-then-removed since. Either way, both engine tiers derive
   headings via a font-size-family heuristic, so the same class of bug threatens pymupdf4llm's
   own internal heading detection too if it ever becomes the tier that runs against this file.

**Producer mismatch — important for Part 2's design**: `pdfinfo` / `fitz.metadata` report
`Creator: Acrobat 3.0 Capture Plug-in`, `Producer: Acrobat 3.0 Import Plug-in`. This is **Adobe
Acrobat Capture**, a legacy (circa 2001) scan-to-searchable-PDF OCR product — not Tesseract or
OCRmyPDF, which is what the task description names explicitly ("detect the OCR producer
(Tesseract / OCRmyPDF metadata)"). A literal Tesseract/OCRmyPDF-only producer-string check would
**not catch this document** — it would correctly detect Simpson (`OCRmyPDF 17.4.2 / Tesseract
5.5.2` per the 518 summary) but silently miss Wijesekera, defeating the point of a general fix.

**Recommendation**: implement the OCR-detection gate as a **broadened producer/creator substring
match** (`Tesseract`, `OCRmyPDF`, `Acrobat.*Capture`, `ABBYY`, `ScanSoft`, `Adobe.*Capture` — the
common OCR-product families that stamp `Producer`/`Creator` metadata) **combined with** the
task's suggested corroborating structural cues (numbering pattern, line length, position,
blank-line context) as a second, independent signal that fires even when the producer string is
unrecognized (e.g. a future OCR tool not in the list, or metadata stripped/rewritten by an
intermediate tool). Relying on corroborating structural cues as the primary signal — with the
producer string as a fast-path/logging aid rather than the sole gate — is more robust than an
allowlist alone, precisely because this real corpus already contains two OCR'd documents from two
completely different OCR tool families with no shared metadata fingerprint.

### 4. A better heading source for Wijesekera than Simpson's chapter-derivation

Simpson (219-page scanned monograph) derived 9 chapter-level headings from stripped running
headers (`"Chapter N.  Title  NN"`, present on every page). Wijesekera has **no comparable
per-page running header carrying section info** — its running header is just `"Constructive modal
logics I   <page>"` (paper title + page number only, confirmed in `chunk_0012.md`'s raw content:
`"Constructive modal lo@   I    273"`, itself OCR-garbled).

However, `pdftotext -layout` on the source PDF cleanly surfaces the paper's own numbered
section/subsection headings as body-text lines matching `^\d+(\.\d+)*\.?\s+[A-Z]`:

```
1. Syntax, semantics and completeness
1.1. Introduction
1.2. Sequent calculus
1.3. Soundness of the sequent calculus
1.4. Completeness of the sequent calculus
1.5. Hilbert style axioms
2. Cut elimination, algebraic and topological semantics
2.1. Freedom of cut and its consequences
2.2. Heyting modal algebras
2.3. Topological models of constructive modal logic.
2.4. A homomorphism
3.2. Algebraic and topological semantics
3.3. Ewald's axioms
```

(Two false positives from the same naive regex, both filterable: one OCR-garbled/scrambled line
mid-document that is not a heading at all, and two reference-list entries like `"1141 D.M.
Gabbay, Investigations..."` — OCR-mangled `[14] D.M. Gabbay...` citation-list lines that happen to
start with digits. Both are easily excluded by requiring the matched line to be short (comparable
to the ≤80-char check already in `is_heading_candidate`) and not immediately followed by
lowercase run-on prose characteristic of a citation entry, or by simply restricting extraction to
pages before the bibliography.)

This gives **finer heading granularity than Simpson's 9-chapter scheme** (13-14 usable
section/subsection headings across 31 pages) while still fully bypassing the font-size heuristic,
matching task 518's proven recipe: `pdftotext -layout` extraction → paragraph-reflow pass (rejoin
OCR line-break noise; the same indent-window + atomic-keyword cues from 518 should transfer,
though Wijesekera's indentation profile should be spot-checked, not assumed identical) → insert
only the ~13 numbered-section headings above → feed through the existing, unmodified
`literature-chunk.sh` Pass-2 merge (`TARGET_TOKENS=512`).

### 5. `literature-chunk.sh` requires no changes for Part 1

Confirmed by direct reading: `literature-chunk.sh`'s Pass 1 (`split_at_headings`, lines 168-224)
and Pass 2 (`subdivide_chunk`/`merge_small_pieces`, lines 232-308) are pure functions of the input
markdown's heading structure — they contain no OCR-specific logic and were correctly left
untouched for Simpson. The same holds here: feeding it a reflowed markdown with ~13 clean headings
will merge well below the 512-token target into a healthy chunk count (Simpson: 1091→206 chunks,
mean 312B→1768B; Wijesekera, being a much shorter single-article source, should land well under
50 chunks with a comparable multi-KB mean).

### 6. Concrete insertion point for the Part 2 "loud warning" chunk-size guard

`literature-ingest.sh` (the orchestrator invoked by `/literature --convert`) calls
`literature-convert.sh` then `literature-chunk.sh` sequentially per file
(`literature-ingest.sh:210`, `:259`). Immediately after line 268
(`log "Created $CHUNK_COUNT chunks in $DOC_DIR"`) is exactly where a mean-chunk-size check belongs
— `$DOC_DIR/chunks.json` already exists at that point with all `token_count` fields populated, so
computing `mean_bytes = mean(token_count) * 4` and comparing against a ~600-byte threshold
(env-overridable, mirroring the `LITERATURE_SPARSE_THRESHOLD` pattern already established
elsewhere in this extension) is a same-process, no-extra-I/O check. The banner should follow the
existing loud-but-non-blocking family already established in this codebase (`[SPARSE COVERAGE
...]`, `[UNVERIFIED ...]`, `[DEGRADED RETRIEVAL ...]`) — e.g. `[PATHOLOGICAL CHUNK SIZE - N
chunks, mean MB, threshold TB]` — logged via the existing `log()` helper, **not** a hard failure
(unlike the `run_quality_gate()` exit-3 contract in `literature-convert.sh`, which is intentionally
a hard block): a low mean chunk size is a strong *signal* worth a human's attention, not a
provably-always-wrong condition the way column-interleaving or unresolved ligatures are, so it
should warn and continue ingesting, matching the task's own wording ("warns loudly rather than
silently landing a shredded corpus").

## Decisions

- Treat the OCR-producer detection as "broadened substring family + corroborating structural cues
  as the primary robustness layer," not a Tesseract/OCRmyPDF-only allowlist — justified directly
  by Wijesekera's Acrobat Capture producer string, a real counterexample in this exact corpus.
- Use the source PDF's own numbered section/subsection headings (via `pdftotext -layout` +
  regex `^\d+(\.\d+)*\.?\s+[A-Z]`, filtered to short lines outside the bibliography) as
  Wijesekera's heading source, rather than attempting to force Simpson's running-header-derived
  "Chapter N" scheme onto a document that has no comparable running header.
- Recommend implementing Part 2 (general hardening) before Part 1's re-ingest so the re-ingest can
  optionally go through the hardened general pipeline rather than requiring a second bespoke
  one-off script — though the bespoke-reflow escape hatch (task 518's approach, entirely bypassing
  `literature-convert.sh`) remains available as a fallback if Part 2 slips or proves riskier than
  expected within this task's scope, exactly as task 518 did for Simpson.
- Re-affirm the "honest ceiling" from task 518: math notation garbling (turnstile, set-membership,
  quantifiers, subscripts) is a property of the 1990s-era OCR scan itself and out of scope — only
  the chunking/heading pathology is this task's target.

## Risks & Mitigations

- **Risk**: A broadened OCR-producer substring list still misses some future OCR tool.
  **Mitigation**: per Findings §3, do not rely on the producer string alone — require
  corroborating structural cues (or a mid-sentence post-check rejecting headings whose surrounding
  context indicates a sentence continuation) as an independent signal that fires regardless of
  producer metadata.
- **Risk**: The numbered-heading regex over-fires on bibliography entries or under-fires if a
  section is un-numbered (e.g. an abstract or unnumbered intro paragraph before "1.").
  **Mitigation**: bound extraction to pages before the references section (`pdftotext -layout`
  page markers `\x0c` make this easy to detect), and manually spot-check the derived heading list
  against the source PDF before feeding it to `literature-chunk.sh` (matches task 518's own
  "validated in a scratch directory before touching production" discipline).
- **Risk**: Implementing Part 2 first and having it change `literature-convert.sh`'s no-TOC
  heuristic in a way that *also* changes behavior for documents that currently convert acceptably
  (this corpus has other no-TOC documents that were audited as "OK" in task 518 — e.g.
  `chagrovzakharyaschev_1997_modallogic` at 7% under 300B). **Mitigation**: any Part 2 change
  should be validated by re-running the mean-chunk-size/under-300B check across all no-TOC corpus
  documents (the same audit table task 518 already produced) before and after, to confirm no
  regression on documents that are currently fine.
- **Risk**: mean-chunk-size guard threshold (~600B) is somewhat arbitrary and could false-positive
  on genuinely short atomic documents (e.g. a short note or errata with naturally small chunks).
  **Mitigation**: make the threshold env-overridable (as recommended in Findings §6) so a
  known-legitimate short document can suppress the warning without editing the script.

## Context Extension Recommendations

- **Topic**: OCR-producer detection heuristics for PDF ingestion.
- **Gap**: No existing context file documents the known OCR-producer metadata signatures observed
  in this corpus (Tesseract/OCRmyPDF for Simpson, Adobe Acrobat Capture for Wijesekera). A future
  ingest hitting a third OCR family would benefit from a running list.
- **Recommendation**: once Part 2 lands, add a short note to
  `.claude/context/project/literature/domain/format-decision.md` (or a new sibling file) listing
  observed OCR producer signatures and the corroborating-cues design rationale, so future
  maintainers extending the detection list have a documented precedent rather than re-deriving it.

## Appendix

### Search queries / commands used

```
jq -r '.entries[] | select(.doc_id=="wijesekera_1990_constructivemodallogicsi")' ~/Projects/Literature/index.json
python3 -c "... statistics.mean(sizes) ... chunks.json token_count*4 ..."
grep -il "fallible\|diamond\|distribut" ~/Projects/Literature/wijesekera_.../chunk_*.md
pdfinfo "Wijesekera - 1990 - Constructive modal logics I.pdf"
python3 -c "import fitz; doc=fitz.open(...); print(doc.get_toc(), doc.metadata)"
pdftotext -layout "Wijesekera ... .pdf" - | grep -nE '^[0-9]+(\.[0-9]+)*\.?\s+[A-Z]'
grep -rn "Wijesekera\|1\.1\.4\|fallible" Cslib/Logics/Modal/Metalogic/Constructive/CS4.lean CS5.lean
```

### References

- `specs/archive/518_reingest_simpson1994_literature_corpus/summaries/01_reingest-summary.md` —
  the proven procedure this task adapts.
- `.claude/scripts/literature-convert.sh` (lines 379-508: TOC vs. heuristic path;
  433-456: `is_heading_candidate`; 568-603: `run_quality_gate`).
- `.claude/scripts/literature-chunk.sh` (lines 168-224: Pass 1 heading split; 264-308: Pass 2
  size-based subdivision).
- `.claude/scripts/literature-ingest.sh` (lines 200-268: convert→chunk orchestration; insertion
  point for the Part 2 chunk-size guard is immediately after line 268).
- `Cslib/Logics/Modal/Metalogic/Constructive/CS4.lean:83`, `CS5.lean:131` — the two Lean docstring
  citations of `Wijesekera1990`, §2 and Definition 1.1.4.
