# Implementation Plan: Task #253 — Gather Automata Theory Literature

- **Task**: 253 - Gather PDFs for all 25 literature references cited across tasks 241-252
- **Status**: [COMPLETED]
- **Effort**: 3 hours
- **Dependencies**: None
- **Research Inputs**: reports/01_reference-inventory.md, reports/02_source-availability.md
- **Artifacts**: plans/02_literature-gathering.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: general
- **Lean Intent**: false

## Overview

Download all freely available PDFs for 25 automata theory references cited across tasks 241-252, convert them to markdown via the literature pipeline, update the centralized Literature index at ~/Projects/Literature/, and produce a final acquisition report documenting what was obtained and what remains behind paywalls. Research identified 11 confirmed open-access PDFs (Tier 1) plus 2 likely free sources (Tier 2), leaving 12 behind paywalls.

### Research Integration

Two research reports inform this plan:
- **01_reference-inventory.md**: Deduplicated inventory of all 25 references with categorization (books, journals, conference proceedings) and high-value author homepages (Vardi at Rice, Thomas at RWTH, Piterman, Esparza, Schewe).
- **02_source-availability.md**: Per-reference URL verification with access classification. Identified 11 confirmed free PDFs from arXiv (refs 9, 11, 13), ORBi (refs 6, 24), author homepages at Rice (refs 18, 25), Hebrew U (ref 7), Cornell (ref 5), and institutional mirrors (refs 12, 14). Two additional sources (refs 1, 8) are likely free via mirrors or Elsevier open archive.

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

No ROADMAP.md found.

## Goals & Non-Goals

**Goals**:
- Download all freely available PDFs for the 25 automata theory references
- Create properly named source directories under ~/Projects/Literature/sources/
- Convert all acquired PDFs to markdown with content-aware chunking
- Add enriched index.json entries for all converted documents
- Produce a clear acquisition report listing found vs. unfound references

**Non-Goals**:
- Acquiring paywall-restricted PDFs (refs 2, 3, 4, 10, 15, 16, 17, 19, 20, 21, 22, 23) -- these are documented for manual library acquisition
- Full-text quality review of converted markdown
- Creating BibTeX entries (handled by downstream tasks)
- Reading or analyzing the paper contents

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Download URLs return 403/404 (stale mirrors) | M | M | Try alternate URLs from research report; skip and document in report |
| Large PDFs (e.g., Baier-Katoen 975pp) produce huge markdown | M | M | Content-aware chunking handles this; verify chunk count is reasonable |
| Elsevier open-archive check for ref 8 (McNaughton 1966) fails | L | M | Document as paywall in final report; ref is non-critical |
| PDF conversion produces low-quality output (scanned images) | M | L | Flag in report; older papers (1960s-70s) may have OCR issues |
| Literature index conflicts with existing entries | L | L | Check index.json before adding; no automata entries exist currently |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2 | 1 |
| 3 | 3 | 2 |
| 4 | 4 | 3 |

Phases within the same wave can execute in parallel.

---

### Phase 1: Download Tier 1 Open-Access PDFs [COMPLETED]

**Goal**: Download all 11 confirmed freely available PDFs into properly named source directories under ~/Projects/Literature/sources/.

**Tasks**:
- [ ] Create source directories for each reference using `{author}_{year}` naming convention
- [ ] Download ref 9 (Piterman 2007) from https://arxiv.org/pdf/0705.2205 to `sources/piterman_2007/`
- [ ] Download ref 13 (Yan 2008) from https://arxiv.org/pdf/0802.1226 to `sources/yan_2008/`
- [ ] Download ref 11 (Schewe 2009) from https://arxiv.org/pdf/0902.2152 to `sources/schewe_2009/`
- [ ] Download ref 24 (Vardi & Wolper 1986) from https://orbi.uliege.be/bitstream/2268/116609/1/lics86.pdf to `sources/vardi_wolper_1986/`
- [ ] Download ref 25 (Vardi 1996) from https://www.cs.rice.edu/~vardi/papers/banff94rj.pdf to `sources/vardi_1996/`
- [ ] Download ref 18 (Gerth et al. 1995) from https://www.cs.rice.edu/~vardi/papers/pstv95rj.pdf to `sources/gerth_1995/`
- [ ] Download ref 6 (Courcoubetis et al. 1992) from https://orbi.uliege.be/bitstream/2268/164300/1/CVWY%20FMSD%2092.pdf to `sources/courcoubetis_1992/`
- [ ] Download ref 5 (Thomas 1997) from https://www.cs.cornell.edu/courses/cs6860/2019sp/Handouts/thomas.pdf to `sources/thomas_1997_languages/`
- [ ] Download ref 14 (Zielonka 1998) from https://people.na.infn.it/~murano/COMP1314/1.pdf to `sources/zielonka_1998/`
- [ ] Download ref 12 (Tarjan 1972) from https://sites.cs.ucsb.edu/~gilbert/cs240a/old/cs240aSpr2011/slides/TarjanDFS.pdf to `sources/tarjan_1972/`
- [ ] Download ref 7 (Kupferman & Vardi 2001, conf. version) from https://www.cs.huji.ac.il/~ornak/publications/istcs97.pdf to `sources/kupferman_vardi_2001/`
- [ ] Verify each downloaded file is a valid PDF (check file size > 10KB, file type)
- [ ] Record download results (success/failure, file size) for each reference

**Timing**: 1 hour

**Depends on**: none

**Files to modify**:
- `~/Projects/Literature/sources/piterman_2007/` - New directory with PDF
- `~/Projects/Literature/sources/yan_2008/` - New directory with PDF
- `~/Projects/Literature/sources/schewe_2009/` - New directory with PDF
- `~/Projects/Literature/sources/vardi_wolper_1986/` - New directory with PDF
- `~/Projects/Literature/sources/vardi_1996/` - New directory with PDF
- `~/Projects/Literature/sources/gerth_1995/` - New directory with PDF
- `~/Projects/Literature/sources/courcoubetis_1992/` - New directory with PDF
- `~/Projects/Literature/sources/thomas_1997_languages/` - New directory with PDF (note: `thomas_1997` already exists for a different Thomas paper)
- `~/Projects/Literature/sources/zielonka_1998/` - New directory with PDF
- `~/Projects/Literature/sources/tarjan_1972/` - New directory with PDF
- `~/Projects/Literature/sources/kupferman_vardi_2001/` - New directory with PDF

**Verification**:
- All 11 source directories created
- Each directory contains exactly one PDF file
- Each PDF is a valid file (not an HTML error page)
- `file` command confirms PDF type for each download

---

### Phase 2: Attempt Tier 2 Downloads and Verify [COMPLETED]

**Goal**: Attempt to download the 2 "likely free" references (refs 1 and 8) and verify. Check author homepages for Tier 3 references (refs 19, 20, 23, 16) that may have preprints.

**Tasks**:
- [ ] Attempt ref 8 (McNaughton 1966) from ScienceDirect open archive URL; check if Elsevier serves the PDF without paywall
- [ ] Attempt ref 1 (Baier & Katoen 2008) from the IFMO mirror URL; verify file integrity (975-page book, expect large file ~10-50MB)
- [ ] Check Wilke homepage (https://www.ti.informatik.uni-kiel.de/~wilke/) for ref 19 preprint
- [ ] Check Loeding RWTH page for ref 20 preprint
- [ ] Check Esparza TU Munich page (https://www7.in.tum.de/~esparza/) for ref 23 preprint
- [ ] Check Semantic Scholar PDF links for ref 16 (Emerson & Jutla)
- [ ] Save any successfully downloaded PDFs to appropriate `sources/` directories
- [ ] Document all download attempts and results (success, 403, paywall redirect, etc.)

**Timing**: 30 minutes

**Depends on**: 1

**Files to modify**:
- `~/Projects/Literature/sources/mcnaughton_1966/` - New directory if download succeeds
- `~/Projects/Literature/sources/baier_katoen_2008/` - New directory if download succeeds
- `~/Projects/Literature/sources/kahler_wilke_2008/` - New directory if download succeeds
- `~/Projects/Literature/sources/loding_1999/` - New directory if download succeeds
- `~/Projects/Literature/sources/schwoon_esparza_2005/` - New directory if download succeeds
- `~/Projects/Literature/sources/emerson_jutla_1991/` - New directory if download succeeds

**Verification**:
- Each attempted download documented with outcome (success/failure/paywall)
- All successfully downloaded PDFs verified as valid
- Running tally of total acquired PDFs updated

---

### Phase 3: Convert All Acquired PDFs to Markdown [COMPLETED]

**Goal**: Convert every successfully downloaded PDF to markdown using the literature pipeline with content-aware chunking.

**Tasks**:
- [ ] For each acquired PDF, run the literature conversion pipeline (`/literature --convert`)
- [ ] Convert Piterman 2007 PDF to markdown
- [ ] Convert Yan 2008 PDF to markdown
- [ ] Convert Schewe 2009 PDF to markdown
- [ ] Convert Vardi & Wolper 1986 PDF to markdown
- [ ] Convert Vardi 1996 PDF to markdown
- [ ] Convert Gerth et al. 1995 PDF to markdown
- [ ] Convert Courcoubetis et al. 1992 PDF to markdown
- [ ] Convert Thomas 1997 (Languages) PDF to markdown
- [ ] Convert Zielonka 1998 PDF to markdown
- [ ] Convert Tarjan 1972 PDF to markdown
- [ ] Convert Kupferman & Vardi 2001 PDF to markdown
- [ ] Convert any Tier 2/3 PDFs that were successfully downloaded in Phase 2
- [ ] Spot-check markdown output quality for each conversion (headings preserved, math notation readable, no garbled text)
- [ ] Flag any conversions with quality issues for the final report

**Timing**: 1 hour

**Depends on**: 2

**Files to modify**:
- `~/Projects/Literature/sources/*/` - Markdown files created alongside PDFs in each source directory

**Verification**:
- Every acquired PDF has at least one corresponding `.md` file
- Large documents (e.g., Baier-Katoen if acquired) are properly chunked
- No empty or near-empty markdown files (indicating failed conversion)
- Markdown files contain recognizable content (not OCR garbage)

---

### Phase 4: Update Literature Index and Produce Acquisition Report [COMPLETED]

**Goal**: Add all converted documents to the Literature index.json and write a final acquisition report listing what was obtained and what remains unavailable.

**Tasks**:
- [ ] For each converted document, add an enriched index.json entry with: id, path, token_count, keywords, summary, authors, title, year, doc_type, source_format, bib_key, project_tags (include "cslib", "automata-theory")
- [ ] Index ref 9 (Piterman): keywords=[Buchi, Streett, deterministic, parity, automata], doc_type=paper
- [ ] Index ref 13 (Yan): keywords=[complementation, omega-automata, lower-bounds], doc_type=paper
- [ ] Index ref 11 (Schewe): keywords=[Buchi, complementation, tight-bound], doc_type=paper
- [ ] Index ref 24 (Vardi & Wolper 1986): keywords=[automata-theoretic, verification, program-verification, LTL], doc_type=paper
- [ ] Index ref 25 (Vardi 1996): keywords=[automata-theoretic, LTL, linear-temporal-logic, tutorial], doc_type=paper
- [ ] Index ref 18 (Gerth et al.): keywords=[on-the-fly, verification, LTL, model-checking], doc_type=paper
- [ ] Index ref 6 (Courcoubetis et al.): keywords=[memory-efficient, verification, temporal, nested-DFS], doc_type=paper
- [ ] Index ref 5 (Thomas 1997): keywords=[languages, automata, logic, omega-regular, MSO], doc_type=chapter
- [ ] Index ref 14 (Zielonka): keywords=[infinite-games, coloured-graphs, parity-games, infinite-trees], doc_type=paper
- [ ] Index ref 12 (Tarjan): keywords=[depth-first-search, strongly-connected-components, graph-algorithms], doc_type=paper
- [ ] Index ref 7 (Kupferman & Vardi): keywords=[weak-alternating-automata, alternation, complementation], doc_type=paper
- [ ] Index any additional PDFs acquired in Phase 2
- [ ] Run `/literature --validate` to confirm index consistency
- [ ] Write final acquisition report to `specs/253_gather_automata_literature/reports/03_acquisition-report.md` containing:
  - Summary table: ref number, authors, year, title, status (acquired/paywall/unavailable)
  - Count of successfully acquired vs. total references
  - List of paywall references with recommended acquisition methods (library ILL, IEEE Xplore subscription, book purchase)
  - Notes on any conversion quality issues

**Timing**: 30 minutes

**Depends on**: 3

**Files to modify**:
- `~/Projects/Literature/index.json` - Add 11+ new entries for automata theory sources
- `specs/253_gather_automata_literature/reports/03_acquisition-report.md` - Final acquisition report

**Verification**:
- `/literature --validate` passes with no errors
- All acquired documents have index entries
- index.json entries have complete metadata (authors, year, keywords, doc_type, project_tags)
- Acquisition report covers all 25 references with clear status for each
- Report includes actionable recommendations for paywall references

## Testing & Validation

- [ ] All Tier 1 PDFs (11) downloaded and verified as valid PDFs
- [ ] All acquired PDFs converted to markdown with readable content
- [ ] Literature index.json updated with correct entries for all new documents
- [ ] `/literature --validate` passes without errors
- [ ] Final acquisition report lists status for all 25 references
- [ ] No existing Literature index entries were corrupted or overwritten
- [ ] Source directory naming follows `{author}_{year}` convention consistently

## Artifacts & Outputs

- `~/Projects/Literature/sources/{author}_{year}/` - 11-17 new source directories with PDFs and markdown
- `~/Projects/Literature/index.json` - Updated with new entries
- `specs/253_gather_automata_literature/plans/02_literature-gathering.md` - This plan
- `specs/253_gather_automata_literature/reports/03_acquisition-report.md` - Final acquisition report

## Rollback/Contingency

- Each phase is independently committable; partial progress is preserved
- If Literature index becomes corrupted, restore from git (`git checkout -- ~/Projects/Literature/index.json`)
- New source directories can be removed individually without affecting existing Literature content
- If PDF conversion fails for a specific document, skip it and document in the acquisition report
- Failed downloads do not block other downloads or subsequent pipeline steps
