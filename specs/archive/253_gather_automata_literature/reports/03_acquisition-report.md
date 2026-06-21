# Literature Acquisition Report — Automata Theory References

**Task**: 253 — Gather automata literature (PDF acquisition)  
**Completed**: 2026-06-19  
**Session**: sess_1781901617_19c4bf

---

## Summary

| Metric | Count |
|--------|-------|
| Total references targeted | 25 |
| Successfully acquired | 13 |
| Behind paywall | 12 |
| Converted to markdown | 13 |
| Index.json entries added | 24 |

---

## Acquisition Status Table

| # | Authors | Year | Title (short) | Status | Notes |
|---|---------|------|---------------|--------|-------|
| 1 | Baier & Katoen | 2008 | Principles of Model Checking | **Acquired** (Tier 2) | IFMO mirror; 994 pages; 12 chunks |
| 2 | Clarke, Grumberg & Peled | 1999 | Model Checking | Paywall/Library | MIT Press, no free PDF |
| 3 | Perrin & Pin | 2004 | Infinite Words | Paywall/Library | Elsevier; HAL bot-blocked |
| 4 | Thomas | 1990 | Automata on Infinite Objects | Paywall/Library | Elsevier handbook chapter |
| 5 | Thomas | 1997 | Languages, Automata, Logic | **Acquired** (Tier 1) | Cornell course mirror |
| 6 | Courcoubetis et al. | 1992 | Memory-Efficient Algorithms | **Acquired** (Tier 1) | ORBi author preprint |
| 7 | Kupferman & Vardi | 2001 | Weak Alternating Automata | **Acquired** (Tier 1) | Hebrew U author preprint (ISTCS 1997 version) |
| 8 | McNaughton | 1966 | Testing/Generating Infinite Sequences | Paywall | ScienceDirect returned 403 |
| 9 | Piterman | 2007 | Büchi/Streett → Deterministic Parity | **Acquired** (Tier 1) | arXiv:0705.2205 |
| 10 | Rabin | 1969 | Decidability 2nd-order Arithmetic | Paywall | AMS subscription required |
| 11 | Schewe | 2009 | Büchi Complementation Made Tight | **Acquired** (Tier 1) | arXiv:0902.2152 |
| 12 | Tarjan | 1972 | Depth-First Search & Linear Graphs | **Acquired** (Tier 1) | UCSB course mirror |
| 13 | Yan | 2008 | Lower Bounds for Complementation | **Acquired** (Tier 1) | arXiv:0802.1226 |
| 14 | Zielonka | 1998 | Infinite Games on Coloured Graphs | **Acquired** (Tier 1) | INFN Naples mirror |
| 15 | Büchi | 1962 | Decision Method 2nd-Order Arithmetic | Paywall/Library | Springer Collected Works reprint |
| 16 | Emerson & Jutla | 1991 | Tree Automata, Mu-Calculus, Determinacy | Paywall | IEEE Xplore; no open access |
| 17 | Emerson & Lei | 1986 | Efficient Model Checking Mu-Calculus | Paywall | IEEE Xplore; predates arXiv |
| 18 | Gerth et al. | 1995 | Simple On-the-Fly Verification LTL | **Acquired** (Tier 1) | Vardi homepage (Rice) |
| 19 | Kähler & Wilke | 2008 | Complementation/Disambiguation NBA | Paywall | Springer LNCS; no preprint found |
| 20 | Löding | 1999 | Optimal Bounds ω-Automata Transforms | Paywall | Springer LNCS; RWTH page empty |
| 21 | Muller | 1963 | Infinite Sequences and Finite Machines | Paywall/Library | IEEE 1963; hardest to obtain |
| 22 | Safra | 1988 | On Complexity of ω-Automata | Paywall | IEEE Xplore FOCS 1988 |
| 23 | Schwoon & Esparza | 2005 | Note on On-the-Fly Verification | **Acquired** (Tier 3) | CiteSeerX mirror |
| 24 | Vardi & Wolper | 1986 | Automata-Theoretic Approach to Verif. | **Acquired** (Tier 1)* | ORBi preprint (scanned PDF) |
| 25 | Vardi | 1996 | Automata-Theoretic Approach to LTL | **Acquired** (Tier 1) | Vardi homepage (Rice) |

*Ref 24: Scanned image PDF — text extraction not possible without OCR (tesseract not installed). Placeholder markdown created.

---

## Successfully Acquired PDFs

All files in `/home/benjamin/Projects/Literature/sources/`:

| Directory | Filename | Size | Lines (md) | Quality |
|-----------|----------|------|------------|---------|
| `piterman_2007/` | Piterman_2007_Buchi_Streett_Parity.pdf | 289 KB | 1,056 | Good text extraction |
| `yan_2008/` | Yan_2008_Lower_Bounds_Complementation.pdf | 375 KB | 1,333 | Good text extraction |
| `schewe_2009/` | Schewe_2009_Buchi_Complementation.pdf | 247 KB | 655 | Good text extraction |
| `vardi_wolper_1986/` | Vardi_Wolper_1986_Automata_Theoretic_Verification.pdf | 837 KB | — | Scanned image PDF; placeholder only |
| `vardi_1996/` | Vardi_1996_Automata_Theoretic_LTL.pdf | 240 KB | 1,295 | Good text extraction |
| `gerth_1995/` | Gerth_1995_OnTheFly_LTL_Verification.pdf | 132 KB | 771 | Good text extraction |
| `courcoubetis_1992/` | Courcoubetis_1992_Memory_Efficient_Verification.pdf | 280 KB | 713 | Good text extraction |
| `thomas_1997_languages/` | Thomas_1997_Languages_Automata_Logic.pdf | 468 KB | 3,001 | Good text extraction |
| `zielonka_1998/` | Zielonka_1998_Infinite_Games_Coloured_Graphs.pdf | 3.8 MB | 2,303 | Good text extraction |
| `tarjan_1972/` | Tarjan_1972_Depth_First_Search_Linear_Graphs.pdf | 4.2 MB | 739 | Good text extraction |
| `kupferman_vardi_2001/` | Kupferman_Vardi_2001_Weak_Alternating_Automata.pdf | 325 KB | 985 | Good text extraction |
| `schwoon_esparza_2005/` | Schwoon_Esparza_2005_Note_OnTheFly_Verification.pdf | 180 KB | 800 | Good text extraction |
| `baier_katoen_2008/` | Baier_Katoen_2008_Principles_Model_Checking.pdf | 5.6 MB | 46,734 (12 parts) | Good text extraction; chunked |

---

## Conversion Quality Notes

- **All 13 acquired PDFs** extracted readable text except Vardi-Wolper 1986 (scanned image).
- **Scanned PDF (ref 24)**: Vardi-Wolper 1986 is a 1986-era scanned document (PDF 1.2, no embedded text). A placeholder markdown with abstract and keywords was created. OCR via `tesseract` would be required for full text extraction.
- **Baier-Katoen 2008**: 994-page book (46,734 lines) split into 12 parts of ~4,000 lines each. No content-aware chapter splitting was possible (chapter headings not at line starts); mechanical 4,000-line chunking was used.
- **Large papers**: Zielonka 1998 (2,303 lines, 3.8MB) and Thomas 1997 (3,001 lines, 468KB) are within single-file limits. No chunking needed.

---

## Paywall References — Recommended Acquisition Methods

### IEEE Xplore Access Needed

| Ref | Authors | Year | DOI/URL |
|-----|---------|------|---------|
| 16 | Emerson & Jutla | 1991 | doi:10.1109/SFCS.1991.185392 |
| 17 | Emerson & Lei | 1986 | LICS 1986 proceedings |
| 21 | Muller | 1963 | doi:10.1109/SWCT.1963.8 |
| 22 | Safra | 1988 | doi:10.1109/SFCS.1988.21948 |

**Recommendation**: Use IEEE Xplore via institutional subscription, or request via ILL (Interlibrary Loan).

### Springer LNCS Access Needed

| Ref | Authors | Year | DOI/URL |
|-----|---------|------|---------|
| 19 | Kähler & Wilke | 2008 | doi:10.1007/978-3-540-70575-8_59 |
| 20 | Löding | 1999 | doi:10.1007/3-540-46691-6_8 |
| 23 (alt) | Schwoon & Esparza | 2005 | doi:10.1007/978-3-540-31980-1_12 |

**Recommendation**: SpringerLink via institutional access, or request via ResearchGate/author contact.

### Elsevier/AMS Access Needed

| Ref | Authors | Year | Notes |
|-----|---------|------|-------|
| 8 | McNaughton | 1966 | ScienceDirect (returned 403); may be Elsevier open archive but access failed |
| 10 | Rabin | 1969 | AMS Transactions; 403 without subscription |

**Recommendation**: Check institutional AMS/Elsevier subscriptions or request via ILL.

### Books (Purchase or Physical Library)

| Ref | Authors | Year | ISBN/Publisher |
|-----|---------|------|----------------|
| 2 | Clarke, Grumberg & Peled | 1999 | MIT Press, ISBN 978-0-262-03262-4 |
| 3 | Perrin & Pin | 2004 | Elsevier, ISBN 978-0-12-532111-2 |

### Very Rare Materials

| Ref | Authors | Year | Notes |
|-----|---------|------|-------|
| 4 | Thomas | 1990 | Handbook of TCS Chapter 7; Elsevier; ILL or library |
| 15 | Büchi | 1962 | Springer Collected Works reprint (1990); rare |

---

## Literature Index Updates

24 new entries added to `/home/benjamin/Projects/Literature/index.json`:

- 11 Tier 1 papers (refs 5, 6, 7, 9, 11, 12, 13, 14, 18, 24, 25)
- 1 Tier 2 book (ref 1, Baier-Katoen, 12 parts)
- 1 Tier 3 paper (ref 23, Schwoon-Esparza)
- All tagged with `project_tags: ["cslib", "automata-theory"]`
- All indexed paths validated (24/24 OK, 0 missing)

---

## Phase 2/3 Search Summary (Tier 2/3 Attempts)

| Ref | Source Checked | Result |
|-----|---------------|--------|
| Ref 8 (McNaughton 1966) | ScienceDirect | 403 Forbidden |
| Ref 1 (Baier & Katoen) | IFMO mirror | **Success** (5.6MB, 994 pages) |
| Ref 19 (Kähler & Wilke) | Wilke homepage (Kiel) | Empty/no papers listed |
| Ref 20 (Löding 1999) | RWTH Aachen moves.rwth-aachen.de | No accessible preprint |
| Ref 23 (Schwoon & Esparza) | CiteSeerX (insecure mode) | **Success** (180KB, 18 pages) |
| Ref 16 (Emerson & Jutla) | Semantic Scholar API | No open access PDF |
