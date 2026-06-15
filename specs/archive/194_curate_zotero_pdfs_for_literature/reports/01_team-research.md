# Research Report: Task #194

**Task**: Curate Zotero PDFs for literature
**Date**: 2026-06-14
**Mode**: Team Research (4 teammates)

## Summary

The `--lit` flag is currently non-functional because `literature-retrieve.sh` does not exist. Existing `specs/literature/` files are full-text book dumps (5.3 MB total, 333x over the 4,000-token budget), making them useless for injection. The project needs: (1) the missing retrieval script, (2) curated excerpt files (~400-4,000 tokens each) replacing/supplementing the oversized dumps, and (3) a Zotero-to-curated-summary pipeline for adding temporal/bimodal literature that current tasks urgently need. Nine critical Zotero PDFs have been verified as available with local file paths for the highest-priority curation targets.

## Key Findings

### 1. Infrastructure Gap: `literature-retrieve.sh` Does Not Exist

All teammates confirmed this independently. The script is referenced in `skill-researcher/SKILL.md`, `skill-planner/SKILL.md`, and `skill-implementer/SKILL.md` but is absent from `.claude/scripts/` (38 scripts present, this one missing). The `--lit` flag silently produces empty context on every invocation.

**Impact**: The entire `--lit` system is non-functional. This is a blocking prerequisite for any literature injection to work.

### 2. Token Budget Crisis: 333:1 Mismatch

The `--lit` system specifies `TOKEN_BUDGET=4000` tokens (~16 KB), `MAX_FILES=10`. Current files:

| File | Size | Over Budget |
|------|------|-------------|
| `chagrov_1997.md` | 1.38 MB | 86x |
| `mendelson_2016.md` | 1.08 MB | 68x |
| `church_1956.md` | 1.07 MB | 67x |
| `hughes_1996.md` | 837 KB | 52x |
| All 13 .md files | 5.3 MB | 333x total |

Only `README.md` (1,810 tokens) fits within budget. The current files are raw `pdftotext` dumps — they cannot be meaningfully injected.

### 3. Copyright Concern in Public Repository

Full-text dumps of copyrighted commercial textbooks (Chagrov/Oxford UP, Mendelson/CRC Press, Church/Princeton UP, Hughes & Cresswell/Routledge) are tracked in `origin/main` of a public GitHub fork. The `.gitignore` excludes `*.pdf` but not the `.md` text dumps. This predates task 194 but constrains the solution: any workflow must not add more copyrighted full-text dumps.

### 4. Zotero Infrastructure Is Ready

- Zotero 9.0.4 running with local API at `http://localhost:23119/api/users/2622830/`
- Better BibTeX active with `citationKey` in every API response
- 322 PDF attachments accessible via `/home/benjamin/Documents/Zotero/storage/{KEY}/`
- PyMuPDF (`fitz`) and `pdftotext` installed for extraction
- Zotero.bib auto-export at `~/texmf/bibtex/bib/Zotero.bib` (878 entries)

### 5. Two Missing Literature Tiers

**Tier A — Temporal/Bimodal (PDFs in Zotero, not in specs/literature/)**:
- Burgess 1982 I/II, Burgess 1984, GHR94, Reynolds 1992, Xu 1988, Thomason 1984, Bellissima 1995, Goldblatt 2006
- Cited in 20+ Lean files, needed by tasks 36, 39, 40, 180, 181

**Tier B — Intuitionistic Modal/Temporal (not in Zotero)**:
- Fischer Servi 1984, Simpson 1994, Boudou et al. 2017
- Needed by tasks 179, 180; must be sourced externally

### 6. Prior Art: Ideal Curated Format Exists

`specs/archive/095_modal_k_t_soundness_completeness/references/literature-proof-structure.md` demonstrates the ideal format: ~800 tokens, structured as proof architecture steps from three papers, directly useful for Lean formalization. This is the template for curated literature files.

### 7. Task Scope Ambiguity

The task has no description field in state.json. "Curate" could mean: (A) build the missing retrieval script, (B) convert PDFs to summaries, (C) create a Zotero workflow, or (D) all of the above. Research suggests all three components are needed.

### 8. BibTeX Key Mismatch

Zero overlap between `references.bib` keys (e.g., `ChagrovZakharyaschev1997`) and Zotero Better BibTeX keys (e.g., `Chagrov1997`). Also, `references.bib` is missing entries for all temporal/bimodal papers (Burgess, GHR94, Goldblatt, Reynolds, Xu, Thomason). Any curation workflow must reconcile these naming schemes.

### 9. Tasks 192 and 194 Are Complementary

- Task 192: Uses existing literature (propositional scope) to verify PR 188
- Task 194: Should expand literature into temporal/bimodal/modal domains for upcoming Wave 2/3 tasks

## Synthesis

### Conflicts Resolved

1. **Full text vs. curated summaries**: All teammates agree curated excerpts (400-4,000 tokens) are the right format. No conflict.
2. **Zotero API vs. BibTeX-first workflow**: Teammate A recommends Zotero API, Teammate B suggests BibTeX-first as simpler. **Resolution**: Use Zotero API for PDF location (it provides file paths), but BibTeX export for metadata (already auto-exported). Hybrid approach.
3. **Flat directory vs. subdirectories**: Teammate D proposes topic subdirectories. **Resolution**: Defer subdirectory restructuring — focus on getting content created first; `literature-retrieve.sh` can be designed to handle either structure.

### Gaps Identified

1. **Whether user has PDF annotations**: If PDFs are annotated in Zotero, `/scrape` could extract highlighted passages. Not verified (Zotero DB was locked during research).
2. **DjVu handling**: `djvutxt` is not available. The existing `chagrov_1997.djvu` was converted by unknown means. Low priority — all high-value papers are PDFs.
3. **Exact token budget behavior**: Whether `literature-retrieve.sh` should use smallest-first selection, keyword relevance scoring, or task-type matching is a design decision for planning phase.

### Recommendations

**Three-component implementation** (ordered by priority):

1. **Create `literature-retrieve.sh`** (infrastructure prerequisite)
   - Greedy selection algorithm within 4,000-token budget
   - Smallest-first ordering (ensures curated files are preferred over raw dumps)
   - Wrap output in `<literature-context>` tags
   - Model on existing `memory-retrieve.sh` patterns

2. **Curate high-priority temporal/bimodal literature** (content)
   - Convert 5 highest-priority Zotero PDFs to scoped markdown excerpts
   - Priority order: GHR94 Ch. 10, Burgess 1982 II, Burgess 1984, Burgess 1982 I, Reynolds 1992
   - Target 2,000-4,000 tokens per file, scoped to sections cited in Lean files
   - Add corresponding BibTeX entries to `references.bib`

3. **Address existing file oversizing** (remediation)
   - Create companion `{author}_{year}_key.md` curated summary files (~400-800 tokens)
   - Configure `literature-retrieve.sh` to prefer `_key.md` files
   - Consider `.gitignore` addition for full-text dumps (copyright concern)

**Stretch goal**: Semi-automated curation script (`.claude/scripts/zotero-curate.sh`) that queries Zotero API, locates PDFs, extracts metadata + abstract, and generates curated summary skeletons.

## Teammate Contributions

| Teammate | Angle | Status | Confidence |
|----------|-------|--------|------------|
| A | Primary (Zotero tools, workflows) | completed | high |
| B | Alternatives (token budgets, prior art) | completed | high |
| C | Critic (gaps, copyright, scope) | completed | high |
| D | Horizons (strategic alignment, priorities) | completed | high |

## References

- specs/literature/README.md — Existing bibliography index
- specs/archive/095_modal_k_t_soundness_completeness/references/literature-proof-structure.md — Ideal curated format example
- .claude/scripts/memory-retrieve.sh — Model for greedy selection algorithm
- references.bib — CSLib citation database (48 entries, missing temporal/bimodal)
- ~/texmf/bibtex/bib/Zotero.bib — Zotero auto-export (878 entries)
- Zotero Local API: http://localhost:23119/api/users/2622830/
