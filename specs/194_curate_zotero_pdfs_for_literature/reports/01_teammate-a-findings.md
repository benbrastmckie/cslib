# Teammate A Findings: Zotero PDF Curation — Implementation Approaches

**Task**: 194 — Curate Zotero PDFs for Literature  
**Angle**: Primary — Implementation approaches and patterns  
**Date**: 2026-06-14

---

## Key Findings

### 1. Current State of specs/literature/

The directory already exists and is populated with 13 markdown files plus a README.md. Files follow the naming convention `{author_last_lower}_{year}.md` with paired PDFs (and one `.djvu`). The README documents each source with `[MD]` / `[NO FILE]` availability markers and BibTeX keys.

Current contents:
- `bentzen_2023.md` (~8K tokens), `blackburn_2001.md` (~39K tokens), `chagrov_1997.md` (~345K tokens), `church_1956.md` (~268K tokens), `from_2022.md` (~13K tokens), `gentzen_1935.md` (~30K tokens), `henkin_1949.md` (~7K tokens), `hughes_1996.md` (~209K tokens), `johansson_1937.md` (~7K tokens), `mendelson_2016.md` (~271K tokens), `post_1921.md` (~14K tokens), `trufas_2024.md` (~11K tokens), `zakharyaschev_2001.md` (~108K tokens)

**Critical observation**: The `--lit` flag TOKEN_BUDGET is 4000 tokens (MAX_FILES=10). The existing files total ~1.33M tokens. The current md files are full OCR transcriptions — unusable as-is with the token budget. The pipeline clips them to the first ~300 chars each, effectively discarding all content past the title/abstract.

**Note**: `literature-retrieve.sh` (the script that actually performs the retrieval for `--lit`) does **not yet exist** at `.claude/scripts/literature-retrieve.sh`. The skills reference it but it is absent from the scripts directory. This means `--lit` currently produces empty context.

### 2. Zotero Infrastructure — Already Available

Zotero 9.0.4 is running with the **local API enabled** (`extensions.zotero.httpServer.localAPI.enabled = true`). The API is accessible at `http://localhost:23119/api/users/2622830/`.

**Better BibTeX** is installed and active with the `auth + year` key format (e.g., `Gabbay2023a`, `Blackburn2002`). The citation key is exposed as `citationKey` in every API response for non-attachment items.

**Zotero storage**: PDFs are at `/home/benjamin/Documents/Zotero/storage/{ATTACHMENT_KEY}/{filename}`. The attachment key in the API response maps directly to the storage folder name.

**Scale**: 322 PDF attachments exist across the library (confirmed by API). The exported `~/texmf/bibtex/bib/Zotero.bib` has 746 entries with attached PDFs (878 total items). Collections include logic/philosophy topics relevant to CSLib (e.g., "TM Completeness" with 6 items).

### 3. PDF-to-Markdown Conversion

**PyMuPDF (fitz)** is installed and produces clean text output equivalent to what the existing `.md` files contain. Quality comparison confirms the existing files were generated with pdftotext or equivalent OCR-free extraction — they look identical to PyMuPDF output.

**pdftotext** is also available at `/home/benjamin/.nix-profile/bin/pdftotext`.

**pandoc 3.7.0.2** is installed and can handle PDF-to-markdown conversion for well-structured files.

For mathematical content, neither tool produces LaTeX-formatted formulas from PDF — they extract Unicode approximations. This is acceptable for agent context (agents understand the mathematical content from prose).

**DjVu**: `djvutxt` is not available. The existing `chagrov_1997.djvu` was converted separately (the `.md` exists). Future DjVu files would need a different approach.

### 4. Metadata Preservation

The Zotero Local API provides all needed metadata per item:
- `citationKey` (Better BibTeX format: `AuthorYear` or `AuthorYear_a` for disambiguated)
- `title`, `authors` (array of firstName/lastName/creatorType)
- `abstractNote`, `date`, `publisher`, `journal`, `volume`, `pages`, `doi`, `url`
- `collections` (which Zotero collections contain the item)

The `references.bib` file uses a different key format from Zotero (e.g., `ChagrovZakharyaschev1997` in references.bib vs `Chagrov1997` in Zotero). The cslib convention for file names (`{author_last_lower}_{year}.md`) is also distinct from the Better BibTeX key (`AuthorYear`).

### 5. Workflow Options

**Option A: Semi-automated collection-based curation**  
User selects a Zotero collection → script converts all PDFs in collection to curated markdown summaries → copies to `specs/literature/`. This is the most practical approach. The user already organizes papers by topic in Zotero collections.

**Option B: Full-library automated sync**  
Too broad. 322+ PDFs is far too many to inject as context. The token budget (4000 tokens, 10 files) is the primary constraint.

**Option C: Single-paper curation on demand**  
User specifies a BibTeX key or Zotero item key → script fetches PDF, converts, produces curated summary. Most targeted but requires knowing item keys.

**Option D: BibTeX key lookup from references.bib**  
Match entries in `references.bib` against Zotero library to find and convert papers already cited in CSLib. Most relevant to the `--hard` H3 reference grounding use case.

---

## Recommended Approach

**Semi-automated, curated-summary workflow** (Option A + D hybrid):

The core problem is the mismatch between full PDF transcriptions (~100K tokens each) and the 4000-token budget. The solution is not to put full transcriptions in `specs/literature/` but to put **curated summaries**: short markdown documents with:
- Metadata header (title, authors, year, BibTeX key, DOI)
- Abstract (verbatim)
- Key theorems/lemmas relevant to CSLib (manually curated or agent-extracted)
- Section index

This matches what the README already models in `specs/literature/README.md` — each entry there is a curated ~10-line summary, not the full text.

**Proposed workflow** (implemented as a shell script `.claude/scripts/zotero-curate.sh`):

```
1. Query Zotero Local API for items matching a collection or BibTeX key pattern
2. For each matching item with a PDF attachment:
   a. Extract metadata (citationKey, title, authors, abstract, year, doi)
   b. Locate PDF at /home/benjamin/Documents/Zotero/storage/{key}/{filename}
   c. Extract full text using PyMuPDF (fitz)
   d. Generate curated summary (.md) with:
      - YAML-style metadata header
      - Abstract (first 500 words)
      - Table of contents (section headings extracted from text)
      - Full text truncated to ~3000 tokens
   e. Write to specs/literature/{author_lower}_{year}.md
   f. Copy PDF to specs/literature/{author_lower}_{year}.pdf (optional)
3. Update README.md with new entries
```

**Alternative for already-cited papers**: Match `references.bib` keys against Zotero `citationKey` field, convert those PDFs automatically. This ensures only papers already in CSLib's bibliography get converted.

**Also needed**: Create `literature-retrieve.sh` in `.claude/scripts/`. This script is referenced by skills but does not exist, meaning `--lit` currently silently produces empty context.

---

## Evidence/Examples

### Zotero Local API (working)
```bash
curl -s "http://localhost:23119/api/users/2622830/collections"
# Returns 14 collections including: Formal Tools (7 items), TM Completeness (6 items)

curl -s "http://localhost:23119/api/users/2622830/items?limit=1"
# Returns items with citationKey: "Gabbay2023a"
# PDF attachment at: /home/benjamin/Documents/Zotero/storage/3TUIG2ZY/Gabbay et al. - 2023 - ....pdf
```

### Conversion Quality (PyMuPDF)
Existing `bentzen_2023.md` is byte-identical in content to what `fitz` produces from `bentzen_2023.pdf`. The conversion is lossless for text-based PDFs.

### Token Budget Problem
- `chagrov_1997.md`: 1,381,134 bytes ≈ 345K tokens (86x over the 4K budget)
- `henkin_1949.md`: 27,003 bytes ≈ 6.75K tokens (1.7x over budget — smallest full conversion)
- Budget per file if 10 files: 400 tokens ≈ 1600 characters ≈ abstract only

### BibTeX Key Mapping
- `references.bib` key: `ChagrovZakharyaschev1997` → file: `chagrov_1997.md`
- Zotero Better BibTeX key: `Chagrov1997` (first author only + year)
- Mapping needed: Zotero `citationKey` → cslib `references.bib` `@key` → file `author_year.md`

### Missing Infrastructure
```
.claude/scripts/literature-retrieve.sh  ← DOES NOT EXIST
```
Referenced in: `skill-researcher/SKILL.md`, `skill-planner/SKILL.md`, `skill-implementer/SKILL.md`

---

## Confidence Level

**High confidence** on:
- Zotero Local API structure and availability (confirmed by live queries)
- PyMuPDF conversion quality (confirmed by file comparison)
- Token budget mismatch problem (confirmed by measurement)
- Missing `literature-retrieve.sh` (confirmed by filesystem search)
- Naming conventions in `specs/literature/` (observed from existing files)

**Medium confidence** on:
- Whether curated summaries are preferable to full transcriptions (depends on how `--lit` is intended to be used)
- The right mapping between Zotero `citationKey` and `references.bib` keys (they use different formats)

**Low confidence** on:
- Whether the user intends `--lit` to inject the full PDF text or curated summaries
- Workflow for DjVu files (no tools available; existing `chagrov_1997.md` was created previously by unknown means)
