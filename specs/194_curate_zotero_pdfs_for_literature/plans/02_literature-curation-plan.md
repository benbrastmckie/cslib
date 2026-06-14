# Implementation Plan: Curate Zotero PDFs for Literature

- **Task**: 194 - Curate Zotero PDFs for literature
- **Status**: [IMPLEMENTING]
- **Effort**: 5 hours
- **Dependencies**: None (user will fix literature-retrieve.sh separately)
- **Research Inputs**: reports/01_team-research.md, reports/02_literature-organization-practices.md
- **Artifacts**: plans/02_literature-curation-plan.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: general
- **Lean Intent**: false

## Overview

The `specs/literature/` directory contains 5.3 MB of monolithic markdown files (333x over the 4,000-token budget for `--lit` injection), making the entire literature system non-functional. This plan restructures the directory into an indexed, chapter-split collection with a master `index.json` for keyword-based retrieval. The work covers: creating the index schema, splitting book-length files into chapter subdirectories, curating high-priority temporal/bimodal papers from Zotero, and adding corresponding BibTeX entries. Done when: `index.json` exists with entries for all literature, book-length files are split into chapter-level chunks (2,000-4,000 tokens each), and at least 5 priority temporal papers are curated as scoped markdown excerpts.

### Research Integration

Two research reports inform this plan:
- **Report 01** (team research): Identified Zotero infrastructure readiness (322 PDFs accessible locally), 9 critical temporal/bimodal papers with priority order, BibTeX key mismatch between `references.bib` and Zotero, and the 333:1 token budget crisis.
- **Report 02** (organization practices): Recommended header-based chapter splitting with JSON index, proposed directory structure (`specs/literature/{bibkey}/ch01_title.md`), defined index.json schema mirroring `.claude/context/index.json`, and confirmed paper-length files need no splitting.

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

This plan supports the remaining Roadmap items for temporal and bimodal completeness. Tasks 36, 39, 40, 180, 181 (temporal/bimodal metalogic) depend on literature from Burgess 1982/1984 and GHR94 -- curating these papers enables `--lit` for those implementations.

## Goals & Non-Goals

**Goals**:
- Create `specs/literature/index.json` master registry with per-entry metadata (keywords, token_count, summary, bib_key)
- Split the 6 book-length markdown files into chapter subdirectories preserving full content
- Curate 5 highest-priority temporal/bimodal papers from Zotero as scoped markdown excerpts
- Add corresponding BibTeX entries to `references.bib` for newly curated papers
- Index all existing paper-length files (already appropriately sized)

**Non-Goals**:
- Creating or modifying `literature-retrieve.sh` (user handles this)
- Summarizing or paraphrasing content (full text preservation required)
- Adding copyright-problematic full-text book dumps from Zotero
- Building an automated Zotero-to-markdown pipeline script
- Splitting all 6 books in one pass (start with blackburn_2001 as template, others follow pattern)

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Manual chapter splitting is time-intensive for large books | H | H | Start with blackburn_2001 (smallest, best ToC); establish pattern for later books |
| OCR quality in chagrov_1997 makes boundaries ambiguous | M | M | Use page numbers from PDF as reference; defer this book to last |
| Token count estimates inaccurate | L | M | Measure with `wc -w * 1.3` ratio; store in index for validation |
| Zotero PDFs may be scanned images without extractable text | M | L | PyMuPDF and pdftotext are both available; fall back to manual excerpt |
| BibTeX key naming inconsistency causes confusion | L | H | Use `references.bib` naming convention (AuthorYear) for all new entries |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2, 3 | 1 |
| 3 | 4 | 2, 3 |

Phases within the same wave can execute in parallel.

---

### Phase 1: Create Master Index Schema and Index Paper-Length Files [IN PROGRESS]

**Goal**: Establish the `specs/literature/index.json` with the correct schema and populate it with entries for all existing paper-length files that already fit within the token budget.

**Tasks**:
- [ ] Design the index.json schema (fields: id, bib_key, book_title, authors, year, section, path, page_range, token_count, keywords, summary)
- [ ] Measure token counts for all paper-length files (bentzen_2023.md, from_2022.md, henkin_1949.md, johansson_1937.md, post_1921.md, trufas_2024.md)
- [ ] Create `specs/literature/index.json` with version=1, token_budget=4000, max_chunks=10
- [ ] Add entries for each paper-length file with curated keywords (6-10 per entry) and one-sentence summaries
- [ ] Verify the index is valid JSON with `jq . specs/literature/index.json`

**Timing**: 1 hour

**Depends on**: none

**Files to modify**:
- `specs/literature/index.json` - Create new master index file

**Verification**:
- `jq . specs/literature/index.json` succeeds without parse errors
- All 6 paper-length files have entries with non-empty keywords arrays
- Each entry has a plausible token_count (measured, not estimated)

---

### Phase 2: Split Book-Length Files into Chapter Subdirectories [NOT STARTED]

**Goal**: Convert the 6 oversized book-length markdown files into chapter-level subdirectories, starting with blackburn_2001 as the template pattern, then applying to remaining books.

**Tasks**:
- [ ] Read blackburn_2001.md table of contents and identify chapter boundaries (pages/line numbers)
- [ ] Create `specs/literature/blackburn_2001/` directory with chapter files (ch01_basic-concepts.md through ch07 or similar)
- [ ] Strip `<!-- Page N -->` comments during extraction (noise reduction)
- [ ] Add source metadata comment at top of each chapter file (`<!-- Source: ... -->`)
- [ ] Measure token count for each resulting chapter file
- [ ] Create per-book `specs/literature/blackburn_2001/index.json` with chapter metadata
- [ ] Repeat pattern for hughes_1996 (split by Parts: 3 files)
- [ ] Repeat for mendelson_2016 (split by chapters using `## Page N` boundaries)
- [ ] Repeat for chagrov_1997 (use PDF ToC for boundaries)
- [ ] Repeat for church_1956 and gentzen_1935
- [ ] Add all chapter entries to the master `specs/literature/index.json`
- [ ] Verify no content is lost: compare line counts of original vs sum of chapter files

**Timing**: 2 hours

**Depends on**: 1

**Files to modify**:
- `specs/literature/blackburn_2001/` - New directory with chapter files + index.json
- `specs/literature/hughes_1996/` - New directory with part files + index.json
- `specs/literature/mendelson_2016/` - New directory with chapter files + index.json
- `specs/literature/chagrov_1997/` - New directory with chapter files + index.json
- `specs/literature/church_1956/` - New directory with chapter files + index.json
- `specs/literature/gentzen_1935/` - New directory with chapter files + index.json
- `specs/literature/index.json` - Add all chapter entries

**Verification**:
- Each chapter file is under 4,000 tokens
- Line count of all chapter files per book equals or exceeds original (no content lost)
- Each per-book index.json is valid JSON
- Master index.json contains entries for all chapters across all books

---

### Phase 3: Curate Temporal/Bimodal Papers from Zotero [NOT STARTED]

**Goal**: Extract and curate the 5 highest-priority temporal/bimodal papers from Zotero as scoped markdown excerpts, targeting sections cited in existing Lean files.

**Tasks**:
- [ ] Locate GHR94 PDF via Zotero storage path and extract Chapter 10 content (temporal logic completeness)
- [ ] Create `specs/literature/gabbay_1994_ch10.md` (~2,000-4,000 tokens, scoped to completeness proof architecture)
- [ ] Locate Burgess 1982 Part II PDF and extract core axiom system + completeness section
- [ ] Create `specs/literature/burgess_1982_ii.md` (~2,000-4,000 tokens)
- [ ] Locate Burgess 1984 PDF and extract relevance-filtered sections
- [ ] Create `specs/literature/burgess_1984.md` (~2,000-4,000 tokens)
- [ ] Locate Burgess 1982 Part I PDF and extract axiom definitions
- [ ] Create `specs/literature/burgess_1982_i.md` (~1,500-3,000 tokens)
- [ ] Locate Reynolds 1992 PDF and extract temporal completeness methodology
- [ ] Create `specs/literature/reynolds_1992.md` (~1,500-3,000 tokens)
- [ ] Add curated keyword arrays for each new file (theorems, named systems, key concepts)
- [ ] Add entries for all 5 new files to `specs/literature/index.json`

**Timing**: 1.5 hours

**Depends on**: 1

**Files to modify**:
- `specs/literature/gabbay_1994_ch10.md` - New curated excerpt
- `specs/literature/burgess_1982_ii.md` - New curated excerpt
- `specs/literature/burgess_1984.md` - New curated excerpt
- `specs/literature/burgess_1982_i.md` - New curated excerpt
- `specs/literature/reynolds_1992.md` - New curated excerpt
- `specs/literature/index.json` - Add entries for new papers

**Verification**:
- Each new file is between 1,000-4,000 tokens
- Content is verbatim extraction (not summarized)
- Each file has a source metadata comment at top
- Keywords include theorem names and named logical systems referenced in Lean files

---

### Phase 4: Add BibTeX Entries and Final Index Validation [NOT STARTED]

**Goal**: Add BibTeX entries for all newly curated papers to `references.bib` and perform final validation of the complete index.

**Tasks**:
- [ ] Add BibTeX entry for GHR94 (Gabbay, Hodkinson, Reynolds 1994) using `references.bib` key convention
- [ ] Add BibTeX entry for Burgess 1982 Part I
- [ ] Add BibTeX entry for Burgess 1982 Part II
- [ ] Add BibTeX entry for Burgess 1984
- [ ] Add BibTeX entry for Reynolds 1992
- [ ] Cross-reference: verify all `bib_key` values in index.json have matching entries in `references.bib`
- [ ] Final validation: run `jq . specs/literature/index.json` and verify all paths resolve to existing files
- [ ] Update `specs/literature/README.md` to document the new directory structure and index.json schema
- [ ] Consider adding original monolithic .md files to `.gitignore` (copyright concern for full-text dumps)

**Timing**: 0.5 hours

**Depends on**: 2, 3

**Files to modify**:
- `references.bib` - Add 5 new BibTeX entries
- `specs/literature/index.json` - Final validation pass
- `specs/literature/README.md` - Update documentation

**Verification**:
- All bib_key values in index.json have corresponding entries in references.bib
- All paths in index.json resolve to existing files on disk
- README.md documents the index schema and directory conventions
- `jq '.entries | length' specs/literature/index.json` returns expected total entry count

---

## Testing & Validation

- [ ] `jq . specs/literature/index.json` parses without error
- [ ] All file paths referenced in index.json exist on disk
- [ ] No chapter file exceeds 4,000 tokens
- [ ] Sum of chapter file line counts matches or exceeds original book file line counts (no content loss)
- [ ] All 5 new temporal/bimodal papers have index entries with keywords
- [ ] All new papers have corresponding BibTeX entries in references.bib
- [ ] Paper-length files (bentzen_2023, from_2022, henkin_1949, johansson_1937, post_1921, trufas_2024) have index entries

## Artifacts & Outputs

- `specs/literature/index.json` - Master registry for literature retrieval
- `specs/literature/blackburn_2001/` - Chapter directory (7+ files + per-book index.json)
- `specs/literature/hughes_1996/` - Part directory (3 files + per-book index.json)
- `specs/literature/mendelson_2016/` - Chapter directory (5+ files + per-book index.json)
- `specs/literature/chagrov_1997/` - Chapter directory (files + per-book index.json)
- `specs/literature/church_1956/` - Chapter directory (files + per-book index.json)
- `specs/literature/gentzen_1935/` - Chapter directory (files + per-book index.json)
- `specs/literature/gabbay_1994_ch10.md` - Curated GHR94 Ch. 10 excerpt
- `specs/literature/burgess_1982_ii.md` - Curated Burgess 1982 Part II excerpt
- `specs/literature/burgess_1984.md` - Curated Burgess 1984 excerpt
- `specs/literature/burgess_1982_i.md` - Curated Burgess 1982 Part I excerpt
- `specs/literature/reynolds_1992.md` - Curated Reynolds 1992 excerpt
- `references.bib` - Updated with 5 new entries

## Rollback/Contingency

- Original monolithic .md files remain in place (splitting creates new directories alongside them)
- If chapter splitting produces unusable chunks, delete the subdirectory and retry with different granularity
- index.json is additive; removing entries does not affect existing files
- If Zotero PDFs prove unextractable (scanned images), manually type key theorem statements from the source
- Git history preserves all original file states for full rollback
