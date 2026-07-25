# Implementation Plan: Fix literature OCR chunking and re-ingest Wijesekera 1990

- **Task**: 519 - Fix literature OCR chunking and re-ingest Wijesekera 1990
- **Status**: [IMPLEMENTING]
- **Effort**: 7.5 hours
- **Dependencies**: 518 (Simpson 1994 re-ingest — the procedure this task adapts; archived)
- **Research Inputs**: `specs/519_fix_literature_ocr_chunking_and_wijesekera/reports/01_wijesekera-ocr-chunking-fix.md`
- **Artifacts**: plans/01_wijesekera-reingest-ocr-hardening.md (this file)
- **Standards**: plan-format.md; status-markers.md; artifact-management.md; tasks.md
- **Type**: general
- **Lean Intent**: false

## Overview

Two independent workstreams. **Part 1** re-ingests `wijesekera_1990_constructivemodallogicsi`
(154 chunks, 468B mean, 62.3% under 300B, 150/154 spurious mid-sentence titles) by bypassing
`literature-convert.sh`'s font-size heading heuristic entirely: `pdftotext -layout` extraction,
a paragraph-reflow pass, insertion of only the paper's own ~13 numbered section headings, then
the existing unmodified `literature-chunk.sh` Pass-2 merge. **Part 2** hardens the shared root
cause in `literature-convert.sh` (no-TOC heading heuristic misfiring on OCR'd scans) and adds a
loud non-blocking pathological-mean-chunk-size guard to `literature-ingest.sh`. Done when
Wijesekera's corpus returns complete, correctly-titled statements via `literature-search.sh`,
the two script changes are in place, and a before/after corpus audit confirms no regression on
documents that currently convert acceptably.

### Correction to the Task Description's Premise

The task description instructs the fix to "detect the OCR producer (Tesseract / OCRmyPDF
metadata)". **That allowlist would silently miss this exact document.** Wijesekera's actual
metadata is `Creator: Acrobat 3.0 Capture Plug-in`, `Producer: Acrobat 3.0 Import Plug-in`
(Adobe Acrobat Capture) — confirmed via `pdfinfo`/`fitz.metadata` in the research report §3.
The corpus therefore already contains two OCR'd documents from two OCR tool families sharing no
metadata fingerprint (Simpson: OCRmyPDF/Tesseract; Wijesekera: Acrobat Capture).

Phase 7 accordingly implements detection as **two independent signals**:
1. A **broadened producer/creator substring family** (`Tesseract`, `OCRmyPDF`, `Acrobat.*Capture`,
   `Adobe.*Capture`, `ABBYY`, `ScanSoft`, `FineReader`) — a fast-path hint and logging aid.
2. **Structural corroborating cues** (numbering pattern, line length, position, blank-line
   context, mid-sentence continuation post-check) treated as an **independent primary signal**
   that fires regardless of producer metadata — including when the string is unrecognized,
   absent, or rewritten by an intermediate tool.

Signal 2 is not gated on signal 1. This is the substantive design deviation from the task's
literal wording, and it is deliberate.

### Research Integration

- Root cause confirmed structurally identical to the Simpson case: `doc.get_toc() == []` routes
  conversion to `derive_heuristic_markdown()` (`literature-convert.sh:459-497`), whose
  `is_heading_candidate()` (`:433-456`) fires on noisy OCR font metrics; `literature-chunk.sh`
  Pass 1 then splits at every false heading.
- `literature-chunk.sh` requires **no changes** — confirmed a pure function of heading structure
  with no OCR-specific logic (research §5). It is explicitly out of scope.
- Heading source for Part 1 is Wijesekera's own numbered sections via `pdftotext -layout` +
  `^\d+(\.\d+)*\.?\s+[A-Z]` (13-14 clean hits, 2 filterable bibliography false positives) —
  **not** a Simpson-style running-header chapter scheme, which Wijesekera does not support (its
  running header carries only title + page number).
- Content loss is less severe than the title corruption suggests: Definition 1.1.4 and the
  Section 2 diamond-independence passage are currently **intact but badly titled**, while
  Definitions 1.1.1-1.1.3 **are** genuinely split across `chunk_0018`/`chunk_0019`. Phase 6's
  acceptance framing reflects this distinction.
- Part 2 guard insertion point identified: `literature-ingest.sh` immediately after line 268
  (`log "Created $CHUNK_COUNT chunks in $DOC_DIR"`), where `chunks.json` already exists with
  `token_count` populated.

### Prior Plan Reference

No prior plan for this task. Task 518's execution summary
(`specs/archive/518_reingest_simpson1994_literature_corpus/summaries/01_reingest-summary.md`)
supplies effort calibration and the proven Part-1 recipe.

**Verified gap not noted in the research report**: task 518's reflow tooling was **not
preserved**. There is no reflow script under `.claude/scripts/`, and the archived 518 task
directory contains only `.orchestrator-handoff.json` and the summary — no scratch script. The
procedure survives as prose only and must be rebuilt from scratch in Phase 4. This is the
main reason this plan's 7.5h estimate exceeds the task's original 3-5h. Phase 4 therefore
writes the reflow pass as a **durable, reusable script** rather than a third throwaway, so a
future third OCR document does not repeat this loss.

### Roadmap Alignment

No `roadmap_path` was provided in the delegation context and no ROADMAP.md was loaded. No
roadmap phases included.

## Goals & Non-Goals

**Goals**:
- Wijesekera corpus re-chunked to a healthy profile (target: well under 50 chunks, multi-KB
  mean, near-zero chunks under 300B) with real section headings and non-duplicating breadcrumbs.
- Definition 1.1.4 and the Section 2 diamond / fallible-world material return **complete**
  statements via `literature-search.sh`; Definitions 1.1.1-1.1.3 no longer split mid-sequence.
- Old 154-chunk set preserved on disk as a rollback safety net, as task 518 did.
- `literature-convert.sh`'s no-TOC heading heuristic no longer fires pathologically on OCR'd
  scans, using broadened producer detection **plus** independent structural cues.
- `literature-ingest.sh` warns loudly (non-blocking) on pathological mean chunk size.
- Before/after corpus audit confirms no regression on currently-acceptable no-TOC documents.
- The reflow tool is preserved as reusable tooling, not a third throwaway script.

**Non-Goals**:
- Fixing OCR quality itself. Math notation (turnstile `⊩` as `It`/`Ik`, `≤` as `s`/`=z`,
  subscripts, quantifiers) is garbled by the 1990s-era scan. This is an accepted ceiling; no
  guessing at or "cleaning up" garbled symbols.
- Any change to `literature-chunk.sh` (confirmed unnecessary).
- Any change to `Cslib/` Lean source.
- Resolving the §2-vs-§1.1 citation-precision question in `CS4.lean:83` / `CS5.lean:131`
  (research §2 flags it; it is a separate task, not to be silently "fixed" here).
- Re-ingesting any corpus document other than Wijesekera.
- Fixing the pre-existing `literature-search.sh` FTS5 sanitizer bug on queries containing
  periods or hyphens (documented in the 518 summary; work around it with word-based queries
  plus `--read <chunk_id>`).

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Part 2 heuristic change regresses documents that currently convert acceptably (e.g. `chagrovzakharyaschev_1997_modallogic`, 7% under 300B) | H | M | Phase 1 captures a before-table across all no-TOC corpus docs; Phase 8 re-runs the same audit after the change and diffs. No promotion of Part 2 without a clean diff. |
| Reflow tooling must be rebuilt from prose (518's script was not preserved) | M | H (confirmed) | Phase 4 budgets 1.5h and writes it as a durable script under `.claude/scripts/`; Wijesekera's indentation profile is spot-checked, not assumed identical to Simpson's. |
| Numbered-heading regex over-fires on bibliography entries (`1141 D.M. Gabbay, ...`) or under-fires on unnumbered front matter | M | M | Phase 2 filters by line length and excludes pages at/after the bibliography (`\x0c` page markers), then manually spot-checks the derived list against the source PDF before it is used. |
| Promoting new chunks corrupts the production corpus / global FTS5 index | H | L | Phase 1 backs up the old chunk set with `chunks.json` renamed to `.bak-inactive` (so `literature-build-index.sh` ignores it); Phase 4 validates in a scratch dir before Phase 5 touches production. |
| 600B mean-chunk threshold false-positives on genuinely short documents | L | M | Make it env-overridable (`LITERATURE_MIN_MEAN_CHUNK_BYTES`, default 600), mirroring the `LITERATURE_SPARSE_THRESHOLD` pattern; warn-only, never blocking. |
| Hardening suppresses false headings but leaves Wijesekera with *no* headings, yielding one blob | M | M | Expected and acceptable — Pass 2 subdivides by size, which is still far better than 154 shreds. This is precisely why Part 1's bespoke heading insertion remains necessary and is **not** made redundant by Part 2. Phase 8 records the outcome rather than treating no-headings as a failure. |
| Guard added to `literature-ingest.sh` accidentally hard-fails the ingest loop under `set -e` | M | L | Guard is a pure `log` call with arithmetic in a subshell; Phase 3 verifies exit status is unchanged on both the warn and no-warn paths. |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1, 2, 3, 7 | -- |
| 2 | 4, 8 | 2 (for 4); 1, 3, 7 (for 8) |
| 3 | 5 | 1, 4 |
| 4 | 6 | 5 |

Phases within the same wave can execute in parallel. Phases 1/2/3/7 touch disjoint targets
(backup dir, a scratch heading list, `literature-ingest.sh`, `literature-convert.sh`).

---

### Phase 1: Baseline capture and rollback preservation [COMPLETED]

**Goal**: Freeze a verifiable before-state for both parts — the Wijesekera rollback copy and
the corpus-wide audit table that Phase 8's regression check diffs against.

**Tasks**:
- [x] Record current Wijesekera stats from `~/Projects/Literature/wijesekera_1990_constructivemodallogicsi/chunks.json`: chunk count, mean bytes, count/% under 300B, and the count of titles that are mid-sentence fragments. Expect 154 / ~468B / 96 (62.3%) / ~150 — confirm, do not assume. *(completed: confirmed exactly 154 / 468.5B / 96 (62.3%) / 150)*
- [x] Copy (not move) `~/Projects/Literature/wijesekera_1990_constructivemodallogicsi/` to `~/Projects/Literature/wijesekera_1990_constructivemodallogicsi.bak-pre-reingest-154chunks/`. *(completed)*
- [x] In the backup dir only, rename `chunks.json` to `chunks.json.bak-inactive` so `literature-build-index.sh` does not index it. *(completed)*
- [x] Verify the backup is complete (154 `chunk_NNNN.md` files present) and that the production dir is untouched. *(completed)*
- [x] Build the corpus-wide baseline audit table: for every doc-level entry in `~/Projects/Literature/index.json`, record `doc_id`, `chunk_count`, mean bytes, % under 300B. Note which documents have no embedded TOC (`fitz.Document.get_toc() == []`) — these are the ones Part 2 can affect. *(completed: 291 entries; TOC status determined via `fitz` where the source PDF is still local — 5 confirmed absent, 4 confirmed present, 282 unknown/source-not-local, documented honestly rather than guessed)*
- [x] Write the baseline table to `specs/519_fix_literature_ocr_chunking_and_wijesekera/baseline-audit.md` so Phase 8 can diff against a committed artifact rather than a recomputed number. *(completed)*

**Timing**: 0.75 hours

**Depends on**: none

**Files to modify**:
- `~/Projects/Literature/wijesekera_1990_constructivemodallogicsi.bak-pre-reingest-154chunks/` - new backup directory (Literature repo, not cslib)
- `specs/519_fix_literature_ocr_chunking_and_wijesekera/baseline-audit.md` - new baseline table

**Verification**:
- Backup directory contains 154 chunk files and `chunks.json.bak-inactive`; no `chunks.json`.
- Production `wijesekera_1990_constructivemodallogicsi/` still has its original 154 chunks and `chunks.json`.
- `baseline-audit.md` lists every doc-level index entry with a TOC-present/absent marker.

---

### Phase 2: Derive and validate the Wijesekera heading list [COMPLETED]

**Goal**: Produce a manually verified list of the ~13 numbered section/subsection headings that
Phase 4 will insert, with bibliography false positives excluded.

**Tasks**:
- [x] Run `pdftotext -layout` on `/home/benjamin/Documents/Zotero/storage/HDH8YF7H/Wijesekera - 1990 - Constructive modal logics I.pdf` into a scratch file. *(completed)*
- [x] Extract candidate headings with `^\d+(\.\d+)*\.?\s+[A-Z]`. *(completed)*
- [x] Filter false positives: require short lines (comparable to the existing 80-char bound in `is_heading_candidate`), and exclude pages at or after the bibliography (detect via `\x0c` page markers plus the references heading). *(completed: filtered by column-0 match, leading-integer-in-{1,2,3}, and line-precedes-References — see headings-wijesekera.txt header comment for the full rule derivation and each excluded false-positive example)*
- [x] Manually compare the surviving list against the source PDF's own section numbering; confirm the expected set (`1.`, `1.1.`-`1.5.`, `2.`, `2.1.`-`2.4.`, `3.2.`, `3.3.`) and investigate any gap (notably whether a `3.` / `3.1.` exists and was missed). *(completed: exact 13-heading set confirmed; 3./3.1. do exist in the paper's own numbering (Definition 3.1.1, Lemma 3.1.2-3.1.6, Theorem 3.1.3/3.1.7, and an explicit "Section 3.1" back-reference) but their heading lines fall on a severely OCR-corrupted, mirrored/reversed page region that pdftotext -layout could not recover — documented as a genuine gap, not fabricated)*
- [x] Record each heading with the page and character offset where it occurs, so Phase 4 can insert at the right position rather than by fuzzy re-matching. *(completed)*
- [x] Save the validated list to a scratch file under the task directory. *(completed)*

**Timing**: 0.5 hours

**Depends on**: none

**Files to modify**:
- `specs/519_fix_literature_ocr_chunking_and_wijesekera/headings-wijesekera.txt` - validated heading list with offsets

**Verification**:
- Every entry in the final list corresponds to a real section heading in the source PDF (visually confirmed).
- The two known false positives (a garbled mid-document line and the OCR-mangled `[14] D.M. Gabbay` citation line) are absent.
- Any missing expected section number is explicitly noted with a reason.

---

### Phase 3: Pathological mean-chunk-size guard in literature-ingest.sh [COMPLETED]

**Goal**: Any future ingest producing a shredded corpus warns loudly instead of landing silently.

**Tasks**:
- [x] Insert the guard in `.claude/scripts/literature-ingest.sh` immediately after line 268 (`log "Created $CHUNK_COUNT chunks in $DOC_DIR"`), where `$DOC_DIR/chunks.json` exists with `token_count` populated. *(completed)*
- [x] Compute `mean_bytes` as `mean(token_count) * 4` across the chunk manifest. *(completed)*
- [x] Compare against `LITERATURE_MIN_MEAN_CHUNK_BYTES` (env-overridable, default `600`), mirroring the `LITERATURE_SPARSE_THRESHOLD` convention already used in this extension. *(completed)*
- [x] On breach, emit via the existing `log()` helper a banner in the established loud-but-non-blocking family (`[SPARSE COVERAGE ...]`, `[UNVERIFIED ...]`, `[DEGRADED RETRIEVAL ...]`): `[PATHOLOGICAL CHUNK SIZE - N chunks, mean MB, threshold TB]`. *(completed)*
- [x] **Warn and continue** — do not exit, do not increment `FAILED`, do not `continue` the loop. This is deliberately unlike `run_quality_gate()`'s exit-3 hard block: a low mean is a strong signal, not a provably-wrong condition. *(completed)*
- [x] Verify the guard is safe under `set -e` (no bare non-zero arithmetic or command substitution that could abort the ingest loop). *(completed: tested guard logic in isolation against synthetic chunks.json fixtures for healthy/breach/forced-breach-via-env-override — all three preserve exit status 0)*

**Timing**: 0.5 hours

**Depends on**: none

**Files to modify**:
- `.claude/scripts/literature-ingest.sh` - guard inserted after line 268

**Verification**:
- Ingesting a document with a healthy mean produces no banner and unchanged exit status.
- Forcing a breach (e.g. `LITERATURE_MIN_MEAN_CHUNK_BYTES=99999`) produces the banner and the ingest still completes successfully with the same exit status.
- `bash -n .claude/scripts/literature-ingest.sh` passes.

---

### Phase 4: Build the reflow tool and produce scratch chunks [COMPLETED]

**Goal**: A reflowed, correctly-headed Wijesekera markdown chunked in a **scratch** directory
with a healthy size profile, production untouched.

**Tasks**:
- [x] Write a durable reflow script (`.claude/scripts/literature-reflow-ocr.sh`, or a Python helper it invokes) rather than a throwaway — 518's tooling was lost and is being rebuilt here for the second time. *(completed: `.claude/scripts/literature-reflow-ocr.sh`, generalized via a `raw_line`-keyed headings TSV contract rather than hardcoded to this one document)*
- [x] Implement the paragraph-reflow pass: rejoin OCR line-break noise into real paragraphs using an indent window (518 used 2-4 leading spaces = real first-line indent; deeper indents = wrapped-math alignment artifacts) plus atomic-keyword cues (`Lemma|Theorem|Definition|Proof|Corollary|Proposition`) and enumerated-list start cues. *(completed — see deviation note below on how enumerated-list cues ended up being used)*
- [x] **Spot-check Wijesekera's indentation profile against the source before trusting 518's window** — this is a 31-page single-column journal article, not a 219-page monograph, and the profile may differ. Adjust the window if it does; record what was used. *(completed: spot-checked directly against raw `pdftotext -layout` output — confirmed real paragraph starts at indent 2-4 (body text) and 2 (footnote), continuation at indent 0, and deep indents 7-23 as centered math-display/abstract-block artifacts. The 2-4/7+ window transferred from 518 unchanged; used as documented in the script's own header comment)*
- [x] Insert only the Phase 2 headings as `## {heading}` markers at their recorded offsets. Insert nothing else. *(completed: all 13 headings matched and inserted by raw-line join key, verified by the script's own missing-heading hard-fail check)*
- [x] Run the existing **unmodified** `.claude/scripts/literature-chunk.sh` against the reflowed markdown, writing to a scratch directory (not `~/Projects/Literature/wijesekera_1990_constructivemodallogicsi/`). *(completed)*
- [x] Compute scratch stats: chunk count, mean bytes, max bytes, count/% under 300B. Compare against Phase 1's baseline. *(completed: 38 chunks / 1669.5B mean / 2226B max / 2 chunks (5.3%) under 300B, vs. baseline 154 / 468.5B / 62.3%)*
- [x] Inspect the resulting `chunks.json` titles: confirm they are real section headings and that breadcrumbs no longer self-duplicate (the `"X > X"` pattern). *(completed: all 38 titles are real headings or `{heading} (cont.)`; programmatic self-dup check found zero `"X > X"` breadcrumbs)*
- [x] If the profile is not clearly healthy (expect well under 50 chunks, multi-KB mean, near-zero under 300B), iterate on the reflow pass before proceeding — do **not** promote a marginal result. *(completed: iterated twice on real defects found empirically, not assumed — see deviation note)*

**Deviation note (recorded per plan-format-enforcement.md, not a silent fix)**: the first working reflow (font/indent rules only, per the literal task list above) produced a healthy aggregate profile (37 chunks, 1716B mean) but **Definition 1.1.4 was split mid-definition** across two chunks — caught by directly grepping the scratch chunks for the definition's opening ("quintuple") and closing ((viii) clause) text, not assumed from the aggregate stats. Root cause: `literature-chunk.sh`'s Pass-2 size-based merge has no atomic-block awareness *below* the top-level heading-chunk boundary (confirmed by reading `subdivide_chunk()`/`is_atomic_start()` — atomicity is checked only against a heading-chunk's own first line/title, never per-paragraph within a large section), so a Definition's own nested `(1)/(2)/(3)` and `(i)-(viii)` enumerated sub-items, if split into separate paragraphs, are exposed to a mid-definition chunk cut. Two additive fixes, both re-verified against the actual scratch chunks after each change (not assumed fixed): (1) enumerated-list-start cues were changed from "always start a new paragraph" to "never start a new paragraph, stay glued to the preceding paragraph" — the literal task wording anticipated enum cues as heading-adjacent triggers, but empirically they needed the opposite polarity to keep an atomic statement's own sub-items together; (2) a one-line-lookahead blank-line-suppression rule was added for paragraphs that opened with an atomic keyword, since a single blank line surrounds this document's centered math-display insert (`k IFA(&) implies...`) as pure typesetting, not a paragraph break, and was still splitting the definition even after fix (1). A regex bug in the enumerated-marker pattern (missing support for fused adjacent markers like the OCR-mangled `"(l)(i)"`) was also found and fixed during this iteration, not before. Post-fix, Definition 1.1.4 is verified complete (single chunk, opening "quintuple" phrase through closing "(viii)" clause) with no regression to the aggregate profile (38 chunks / 1669.5B mean / 5.3% under 300B — still comfortably healthy).

**Timing**: 1.5 hours

**Depends on**: 2

**Files to modify**:
- `.claude/scripts/literature-reflow-ocr.sh` - new reusable reflow tool
- scratch chunk directory (temporary, not committed)

**Verification**:
- Scratch chunk count, mean bytes, and % under 300B are all substantially better than the 154 / 468B / 62.3% baseline.
- `chunks.json` titles are real section headings; no mid-sentence fragments; no self-duplicating breadcrumbs.
- Definitions 1.1.1-1.1.3 are readable as a contiguous sequence within the scratch chunks.
- Production `~/Projects/Literature/wijesekera_1990_constructivemodallogicsi/` is byte-identical to its Phase 1 state.

---

### Phase 5: Promote to production and reindex [COMPLETED]

**Goal**: The validated scratch chunk set becomes the live Wijesekera corpus with consistent
metadata and a rebuilt search index.

**Tasks**:
- [x] Replace the contents of `~/Projects/Literature/wijesekera_1990_constructivemodallogicsi/` with the Phase 4 scratch chunks + `chunks.json`, preserving the reflowed markdown source alongside them (as 518 did for Simpson). *(completed: old 154 chunk_*.md + chunks.json removed, 38 new ones copied in, reflowed markdown saved as wijesekera-reflowed-source.md)*
- [x] Update `metadata.json` in that directory: new `chunk_count`, refreshed `ingested_at`. *(completed: chunk_count 38, ingested_at 2026-07-25T07:40:22Z; also refreshed the stale source_path, which pointed at a dead prior-session scratchpad directory, to the durable Zotero storage path)*
- [x] Update the `wijesekera_1990_constructivemodallogicsi` entry in `~/Projects/Literature/index.json`: new `chunk_count`, refreshed `ingested_at`, add `provenance_fidelity: "ocr_rescanned_reflowed_partial_symbol_loss"` (matching the Simpson entry's convention), and an honest `summary` note about the OCR math-notation ceiling. *(completed — the summary note deliberately omits a task-number citation, unlike the Simpson entry's precedent, in the spirit of the no-task-references convention even though `~/Projects/Literature/` is a separate repository outside that rule's literal scope)*
- [x] Confirm `bib_key: Wijesekera1990` is preserved unchanged. *(completed, verified)*
- [x] Rebuild the global FTS5 index: `bash .claude/scripts/literature-build-index.sh --global`. Record the total-chunk delta. *(completed: 7774 chunks reported by the build script across 126 manifests; `chunks_data` query confirms exactly 38 rows for `doc_id = 'wijesekera_1990_constructivemodallogicsi'` post-rebuild. A precise corpus-wide before/after total delta could not be computed — Phase 1's baseline table was built from `index.json`'s entries array, a smaller/different inventory than `literature-build-index.sh`'s own `find`-based manifest discovery (126 manifests vs. 257 resolvable baseline rows), so the two totals are not directly comparable. The verifiable, apples-to-apples fact is reported instead: Wijesekera's own indexed chunk count is 38 (down from 154), and no other document's `chunks.json` was touched by this task.)*
- [x] Confirm `specs/literature-index.json` needs no change (it references documents by `doc_id`, which is unchanged) — verify rather than assume. *(completed: verified — the sub-index entry only stores `doc_id`/`relevance`, no cached chunk metadata, `doc_id` unchanged)*

**Timing**: 0.75 hours

**Depends on**: 1, 4

**Files to modify**:
- `~/Projects/Literature/wijesekera_1990_constructivemodallogicsi/` - new chunks, `chunks.json`, `metadata.json`, reflowed markdown
- `~/Projects/Literature/index.json` - doc entry updated
- `~/Projects/Literature/.literature.db` - rebuilt

**Verification**:
- `index.json` `chunk_count` matches the actual on-disk chunk file count.
- `bib_key` is still `Wijesekera1990`.
- The FTS5 rebuild reports a total-chunk delta consistent with the 154 → new-count change.
- The Phase 1 backup directory is still intact and still has `chunks.json.bak-inactive`.

---

### Phase 6: Wijesekera retrieval acceptance validation [NOT STARTED]

**Goal**: Confirm via the actual retrieval path that the target passages return complete,
correctly-titled statements.

**Tasks**:
- [ ] Query Definition 1.1.4 (the intuitionistic modal frame quintuple `(K, ≤, D, R, ⊩)`) via `literature-search.sh`; confirm the returned chunk carries the **complete** definition and a real section title.
- [ ] Query the Section 2 diamond / fallible-world material (diamond does not distribute over disjunction; independent, non-interdefinable box and diamond); confirm complete return.
- [ ] Confirm Definitions 1.1.1-1.1.3 — genuinely split across `chunk_0018`/`chunk_0019` in the old set — are now contiguous within a single chunk or across a clean boundary that does not cut a definition.
- [ ] Spot-check that breadcrumb/section-path fields are real headings and do not self-duplicate.
- [ ] Use word-based queries plus `--read <chunk_id>` to work around the known pre-existing `literature-search.sh` FTS5 sanitizer bug on queries containing periods (`"Definition 1.1.4"`) or hyphens; note the workaround, do not fix the sanitizer.
- [ ] Record the acceptance results in a table (query target, chunk id, status), following 518's summary format.
- [ ] Frame acceptance as "clean, correctly-titled, non-duplicated-breadcrumb chunks with intact atomic blocks" — **not** "recovers previously inaccessible content", since research §2 established that Definition 1.1.4 and the diamond passage were already intact, just badly titled.

**Timing**: 0.75 hours

**Depends on**: 5

**Files to modify**:
- (none — validation only; results feed the implementation summary)

**Verification**:
- Every target passage returns complete and untruncated.
- No returned chunk carries a mid-sentence fragment as its title.
- No breadcrumb exhibits the `"X > X"` self-duplication pattern.

---

### Phase 7: Harden the no-TOC heading heuristic in literature-convert.sh [COMPLETED]

**Goal**: `derive_heuristic_markdown()` stops emitting spurious mid-sentence headings on OCR'd
scans, using broadened producer detection **plus** independent structural cues.

**Tasks**:
- [x] Add an OCR-producer detector reading `doc.metadata`'s `creator` and `producer`, matching a broadened substring family: `Tesseract`, `OCRmyPDF`, `Acrobat.*Capture`, `Adobe.*Capture`, `ABBYY`, `ScanSoft`, `FineReader`. Case-insensitive. Log which signature matched (or that none did). *(completed: new `detect_ocr_producer()` helper + `_OCR_PRODUCER_FAMILY_RE`)*
- [x] Add structural corroborating cues to `is_heading_candidate()` (`literature-convert.sh:433-456`), evaluated **independently of** the producer result — they must fire even when producer metadata is unrecognized, absent, or rewritten: *(completed)*
  - Numbering pattern: a leading `^\d+(\.\d+)*\.?\s` markedly raises heading confidence. *(completed: `_NUMBERED_HEADING_RE`)*
  - Line length and position within the block. *(completed: length bound preserved from the original check; position/blank-line context satisfied by construction — documented in the docstring — since candidates are always the first line of an already block-isolated PyMuPDF text unit)*
  - Blank-line context around the candidate. *(completed, same construction argument as above)*
  - **Mid-sentence post-check**: reject a candidate whose preceding context ends without terminal punctuation and whose own text begins lowercase, or which otherwise reads as a sentence continuation. This is the check that would have caught 518's literal `"tuitionistic or clas..."` mid-word false heading. *(completed: `_reads_as_sentence_continuation()`, applied to BOTH signals, not just the structural one)*
- [x] When the producer signature matches a known OCR family, raise the corroboration bar (require structural cues, not font metrics alone) rather than disabling heading detection outright. *(completed: `ocr_hint=True` branch returns `structural_ok` only, ignoring `font_ok`)*
- [x] Preserve the existing conservative failure mode documented in the function's own docstring: a document with no surviving candidates gets **no** heading markers rather than a low-confidence guess. Do not weaken this. *(completed, unchanged)*
- [x] Keep the change confined to `is_heading_candidate` / `derive_heuristic_markdown` and their new helper(s). Do **not** touch `derive_toc_markdown` (`:379-430`), `run_quality_gate` (`:568-603`), or `literature-chunk.sh`. *(completed: confirmed byte-identical re-read of both untouched functions; `literature-chunk.sh` not opened)*
- [x] Update the function docstrings to reflect the new two-signal design and record the observed producer strings. *(completed)*

**Timing**: 1.5 hours

**Depends on**: none

**Files to modify**:
- `.claude/scripts/literature-convert.sh` - `is_heading_candidate` (~:433-456), `derive_heuristic_markdown` (~:459-497), new producer-detection and structural-cue helpers

**Verification**:
- `bash -n .claude/scripts/literature-convert.sh` passes and the embedded Python compiles.
- Detection correctly identifies both `Acrobat 3.0 Capture Plug-in` (Wijesekera) and an OCRmyPDF/Tesseract string (Simpson's source, if still available) as OCR producers.
- Structural cues alone reject a synthetic mid-sentence bold/large span with no producer metadata present — proving the cue path is not producer-gated.
- The TOC path and quality gate are unchanged (diff confirms).

---

### Phase 8: Part 2 regression validation and OCR signature documentation [COMPLETED]

**Goal**: Prove the hardened heuristic improves OCR'd documents without regressing ones that
currently convert acceptably, and record the design rationale for future maintainers.

**Tasks**:
- [x] Select the regression sample from Phase 1's baseline table: all no-TOC documents, prioritizing `chagrovzakharyaschev_1997_modallogic` (997 chunks, 1434B mean, 7% under 300B — currently OK, the primary regression risk) and `proofs_and_types` (176 chunks, 1662B mean, 7%). *(completed: full sample = the 4 confirmed-absent-TOC docs (`alechinamendlerdepaivaritter_2001`, `biermandepaiva_2000`, `marinmoralesstrassburger_2021`, `simpson_1994`) + both named priority docs)*
- [x] Re-convert each sample document through the hardened `literature-convert.sh` into a **scratch** directory; chunk with the unmodified `literature-chunk.sh`. *(completed for 5/6 — see deviation note)*
- [x] Compute the after-table (chunk count, mean bytes, % under 300B) and diff against `baseline-audit.md`. Any material degradation on a currently-OK document blocks Part 2 — fix or revert before proceeding. *(completed: zero degradation found — see deviation note for why the mechanism is structural, not just empirically observed)*
- [x] Re-convert the raw Wijesekera PDF through the hardened path into scratch and record the outcome. Expect improvement over 154 shreds; **a result with few or no headings is an acceptable pass**, not a failure — Pass 2 subdivides by size, and this is exactly why Part 1's bespoke heading insertion remains necessary. Do not promote this output; production comes from Phase 5. *(completed: forced-fallback conversion produced 62 chunks / no 154-shred signature; not promoted — see deviation note on `auto`-mode now resolving to the primary tier for this document)*
- [x] Confirm the Phase 3 guard fires as expected on any scratch conversion that lands below the 600B threshold. *(completed: none of the fresh regression conversions landed below 600B in this environment, so the guard's exact formula (`mean(token_count) * 4`) was applied directly to the real historical 154-chunk Wijesekera set — 461B, confirmed below threshold, confirming the guard would have fired loudly had it existed at that ingest)*
- [x] Document the observed OCR producer signatures (`OCRmyPDF 17.4.2 / Tesseract 5.5.2` for Simpson; `Acrobat 3.0 Capture Plug-in` / `Acrobat 3.0 Import Plug-in` for Wijesekera) and the two-independent-signals rationale in `.claude/context/project/literature/domain/format-decision.md` (or a new sibling file), so a future third OCR family is an append rather than a re-derivation. *(completed: new sibling file `.claude/context/project/literature/domain/ocr-heading-hardening.md` — kept separate from `format-decision.md` since that file's own scope is the unrelated markdown-vs-typst decision)*
- [x] Per `.claude/rules/no-task-references-in-deliverables.md`, the documentation must cite durable anchors (script/function names, producer strings) and **must not** reference task numbers. *(completed, grep-verified clean)*

**Deviation note**: `chagrovzakharyaschev_1997_modallogic`'s source is a DJVU file, and this
environment has neither `djvutxt` nor `djvups`/`ps2pdf` installed — `literature-convert.sh`'s
`try_djvu()` fails both methods (exit 2), a pre-existing environmental gap unrelated to this
hardening pass. It could not be re-converted here; noted rather than silently dropped from the
sample.

A more important finding, discovered empirically rather than assumed: re-running the 5
convertible sample documents under `auto` mode showed **all 5 resolve to the PRIMARY engine tier**
(`pymupdf4llm.to_markdown()`) or, for `proofs_and_types`, to `derive_toc_markdown()` (embedded
TOC) — neither code path calls the hardened `is_heading_candidate()` / `derive_heuristic_markdown()`
functions at all. This means the regression risk these 5 documents represent is not merely
"empirically zero this run" but **structurally zero** — the modified functions are provably
unreachable for them under real `auto`-mode operation, confirmed by the log line `[convert]
Engine used: pymupdf4llm` (or `pymupdf-fallback-toc` for `proofs_and_types`) on every run. Forcing
the fallback tier (`LITERATURE_CONVERTER=fallback`) to directly exercise the modified code against
`biermandepaiva_2000` and the raw Wijesekera PDF confirmed: (a) the OCR-producer detector
correctly identifies `Acrobat 3.0 Capture Plug-in` on Wijesekera and logs the raised corroboration
bar; (b) `proofs_and_types` forced through the fallback path produces **byte-identical** output
before and after the Phase 7 change (it takes the TOC path even when the primary tier is skipped);
(c) neither the pre- nor post-hardening fallback heuristic reproduces anything resembling the
154-shred pathology on Wijesekera under forced-fallback (59 vs. 62 chunks, ~1300B mean either
way) — the original 154-chunk corpus was evidently produced under different conditions (a prior
environment/library-version state) than either heuristic version reproduces today, an observation
recorded in `ocr-heading-hardening.md` rather than chased further, since it does not change the
Part 2 regression conclusion.

**Timing**: 1.25 hours

**Depends on**: 1, 3, 7

**Files to modify**:
- `.claude/context/project/literature/domain/format-decision.md` (or new sibling) - OCR producer signatures and detection rationale
- scratch conversion directories (temporary, not committed)

**Verification**:
- After-table shows no material degradation versus `baseline-audit.md` on any currently-acceptable no-TOC document.
- Wijesekera's raw-PDF scratch conversion no longer produces the 154-shred signature.
- The documentation lists both observed producer families and explains why structural cues are an independent primary signal rather than producer-gated.
- No task-number references appear in the documentation.

---

## Testing & Validation

- [ ] `bash -n` passes on `literature-convert.sh`, `literature-ingest.sh`, and the new reflow script.
- [ ] Wijesekera production chunk profile: well under 50 chunks, multi-KB mean, near-zero chunks under 300B.
- [ ] `chunks.json` titles are real section headings; zero mid-sentence fragments; zero self-duplicating breadcrumbs.
- [ ] Definition 1.1.4 returns complete via `literature-search.sh`.
- [ ] Section 2 diamond / fallible-world material returns complete via `literature-search.sh`.
- [ ] Definitions 1.1.1-1.1.3 are no longer split mid-sequence.
- [ ] `index.json` `chunk_count` matches on-disk reality; `bib_key: Wijesekera1990` preserved.
- [ ] Global FTS5 index rebuilt with a chunk delta consistent with the re-chunk.
- [ ] Chunk-size guard warns without failing; ingest exit status unchanged on both paths.
- [ ] Corpus regression diff clean on all currently-acceptable no-TOC documents.
- [ ] Backup directory `wijesekera_1990_constructivemodallogicsi.bak-pre-reingest-154chunks/` intact with `chunks.json.bak-inactive`.
- [ ] No `Cslib/` file modified (`git status` confirms).
- [ ] No change to `literature-chunk.sh` (`git status` confirms).

## Artifacts & Outputs

- `specs/519_fix_literature_ocr_chunking_and_wijesekera/plans/01_wijesekera-reingest-ocr-hardening.md` (this file)
- `specs/519_fix_literature_ocr_chunking_and_wijesekera/baseline-audit.md` (Phase 1)
- `specs/519_fix_literature_ocr_chunking_and_wijesekera/headings-wijesekera.txt` (Phase 2)
- `specs/519_fix_literature_ocr_chunking_and_wijesekera/summaries/01_wijesekera-reingest-summary.md` (on completion)
- `.claude/scripts/literature-reflow-ocr.sh` (new, Phase 4)
- `.claude/scripts/literature-convert.sh` (modified, Phase 7)
- `.claude/scripts/literature-ingest.sh` (modified, Phase 3)
- `.claude/context/project/literature/domain/format-decision.md` or sibling (modified/new, Phase 8)
- Literature repo (not cslib, committed separately there):
  `~/Projects/Literature/wijesekera_1990_constructivemodallogicsi/`,
  `~/Projects/Literature/wijesekera_1990_constructivemodallogicsi.bak-pre-reingest-154chunks/`,
  `~/Projects/Literature/index.json`, `~/Projects/Literature/.literature.db`

## Rollback/Contingency

- **Part 1 (corpus)**: the Phase 1 backup is the rollback path. Restore by moving
  `wijesekera_1990_constructivemodallogicsi.bak-pre-reingest-154chunks/` back over the production
  directory, renaming `chunks.json.bak-inactive` to `chunks.json`, reverting the `index.json`
  entry (`chunk_count` 154, prior `ingested_at`, drop `provenance_fidelity`), and re-running
  `literature-build-index.sh --global`. Following 518's precedent, the backup stays on disk
  uncommitted — committing 154 files being actively replaced adds nothing.
- **Part 2 (scripts)**: `literature-convert.sh` and `literature-ingest.sh` are tracked in git;
  revert with a targeted checkout of those two paths. Both changes are additive and confined to
  the no-TOC heuristic and a post-chunk log line, so reverting either does not affect the other,
  and neither affects the Part 1 corpus result (Part 1 bypasses `literature-convert.sh`
  entirely).
- **If Phase 4's reflow cannot reach a healthy profile**: do not promote. Leave production at
  the 154-chunk state, mark Phase 5 `[BLOCKED]`, and deliver Part 2 alone — the two parts are
  independent and Part 2 is the higher-leverage, lower-risk half.
- **If Phase 8 finds a regression**: revert the Phase 7 change only. Parts 1 and 3 stand on
  their own.
