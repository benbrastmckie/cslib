# Research Report: Task #194

**Task**: 194 - Curate Zotero PDFs for literature
**Started**: 2026-06-14T00:00:00Z
**Completed**: 2026-06-14T01:00:00Z
**Effort**: 1.5 hours
**Dependencies**: None
**Sources/Inputs**:
- Codebase: `.claude/context/index.json`, `.claude/scripts/memory-retrieve.sh`
- Codebase: `specs/literature/*.md` (all 14 files, surveyed structure)
- WebSearch: RAG chunking strategies, markdown organization best practices (2025-2026)
- WebFetch: firecrawl.dev (chunking strategies), langcopilot.com (practical RAG guide), fern (LLM-friendly docs), llmstxt.org (index standard), glama.ai (markdown splitting for RAG)
**Artifacts**:
- `specs/194_curate_zotero_pdfs_for_literature/reports/02_literature-organization-practices.md`
**Standards**: report-format.md, artifact-formats.md

---

## Executive Summary

- The 14 literature markdown files total ~5.3 MB with wildly inconsistent internal structure: some use `<!-- Page N -->` comments, some use `## Page N` headings, one has real headings, most have none — no file currently has semantic section headers compatible with header-based splitting.
- The `literature-retrieve.sh` script does not exist yet; when built, it should mirror `memory-retrieve.sh`'s architecture: keyword scoring against an `index.json`, then greedy selection within a 4000-token budget.
- Best practice (2025-2026) for lightweight, shell-script-compatible retrieval is **header-based splitting into chapter/section files with a JSON index** per book — no embeddings, no vector database, just structured files and keyword overlap scoring.
- The recommended design splits each book into a subdirectory `specs/literature/{bibkey}/` containing `ch01_title.md`, `ch02_title.md`, ... plus an `index.json` with per-chapter metadata (keywords, token count, page range, section title).
- A top-level `specs/literature/index.json` acts as the master registry — analogous to `.claude/context/index.json` — enabling the retrieval script to score and select chapters across all books without reading any file content.
- The paper-length files (bentzen_2023.md, from_2022.md, post_1921.md, johansson_1937.md, henkin_1949.md) are already small enough to use as single-chunk entries in the index; only the six book-length files need splitting.

---

## Context & Scope

### What Was Researched

The goal is to restructure `specs/literature/` from a flat directory of monolithic markdown files (5.3 MB total, 333x over the 4000-token budget enforced by `literature-retrieve.sh`) into an indexed, chunked collection that a shell retrieval script can efficiently query.

The research addressed:
1. What internal structure currently exists in each file (can we split by headers?)
2. What current best practices (2025-2026) recommend for markdown chunking and indexing
3. How the existing `memory-retrieve.sh` and `.claude/context/index.json` work as patterns
4. What index format and retrieval algorithm would work for this use case

### Constraints

- Must preserve full content — no lossy summarization
- Must be queryable by a shell script (no Python, no embeddings, no external services)
- Must fit the `--lit` injection pattern: token budget of 4000, max ~10 files
- Must remain maintainable: adding a new book should require only adding a subdirectory and updating the index

---

## Findings

### Codebase Patterns

**memory-retrieve.sh pattern (the model to follow)**:

The existing `memory-retrieve.sh` implements a two-phase retrieval pipeline:
1. **Phase 1**: Extract keywords from `description + focus_prompt`. Score each `memory-index.json` entry by keyword overlap (1 point per matching keyword) plus topic match bonus (+2). Filter entries scoring below MIN_SCORE=1.
2. **Phase 2**: Greedy selection — pick highest-scoring entries until TOKEN_BUDGET=2000 or MAX_ENTRIES=5 is reached. Read the selected files and emit a `<memory-context>` block.

The key insight: the script never reads any content file during scoring. All scoring is done against the JSON index. File reads only happen for the selected entries. This is the correct architecture for `literature-retrieve.sh`.

**`.claude/context/index.json` schema (the index format to adapt)**:

Each entry has:
```json
{
  "path": "relative/path/to/file.md",
  "keywords": ["keyword1", "keyword2", "keyword3"],
  "summary": "One-sentence description of the content",
  "line_count": 143,
  "subdomain": "standards",
  "domain": "core",
  "load_when": { "task_types": [...], "agents": [...], "commands": [...] },
  "topics": ["documentation", "references"]
}
```

For literature, `load_when` is not needed (every task is a candidate). What IS needed: `token_count`, `bib_key`, `page_range`, and `section_title` to distinguish chapters within a book.

### Current Literature File Structure

Survey of all markdown files in `specs/literature/`:

| File | Size | Lines | Effective Structure |
|------|------|-------|---------------------|
| `bentzen_2023.md` | 33 KB | 822 | No headers; paper body (~400 tokens) |
| `blackburn_2001.md` | 156 KB | 4,205 | `<!-- Page N -->` comments (66 markers), no headings |
| `chagrov_1997.md` | 1.3 MB | 24,810 | `# ...` lines are OCR artifacts (not real headings), no structure |
| `church_1956.md` | 1.1 MB | ~n/a | Not surveyed (large) |
| `from_2022.md` | 53 KB | 918 | `## Page N` headers (18 pages); paper-length |
| `gentzen_1935.md` | 119 KB | ~n/a | Not surveyed |
| `henkin_1949.md` | 27 KB | ~n/a | Small, paper-length |
| `hughes_1996.md` | 837 KB | 19,269 | "Part One/Two/Three" appears in text; no real markdown headers |
| `johansson_1937.md` | 27 KB | ~n/a | Small, paper-length |
| `mendelson_2016.md` | 1.1 MB | 59,759 | `## Page N` headers (492 pages); page-per-section only |
| `post_1921.md` | 56 KB | ~n/a | Journal paper-length |
| `trufas_2024.md` | 45 KB | ~n/a | Not surveyed |
| `zakharyaschev_2001.md` | 431 KB | ~n/a | Not surveyed |

**Key finding**: No file uses semantic section headers (e.g., `## 1. Introduction`, `## Chapter 3: Kripke Completeness`). The headers that exist are either page numbers or OCR artifacts. Splitting by existing headers would produce page-granular chunks with no semantic meaning.

**Implication**: The splitting must be done **manually or semi-manually** by reading the table of contents (which is present in the rendered content) and creating chapter files that correspond to logical sections of each book.

### External Best Practices (2025-2026)

**Header-based splitting is the consensus best practice for structured markdown**:

The 2025-2026 consensus (Firecrawl, Pinecone, LangCopilot, Weaviate) is that for structured documents, header-based splitting is the "single biggest and easiest improvement." The recommended approach:
- Split on H1/H2/H3 headers as natural boundaries
- Each chunk should be 1000-2000 characters (roughly 250-500 tokens)
- Preserve the heading hierarchy in chunk metadata

**But our files lack semantic headers** — the implication is that creating them during splitting is the correct approach, not trying to split existing files automatically.

**JSON index metadata per chunk (consensus pattern)**:

```json
{
  "id": "blackburn_2001_ch01",
  "bib_key": "Blackburn2001",
  "book": "Modal Logic",
  "authors": "Blackburn, de Rijke, Venema",
  "year": 2001,
  "section": "Chapter 1: Basic Concepts",
  "section_short": "ch01",
  "path": "literature/blackburn_2001/ch01_basic-concepts.md",
  "page_range": "1-49",
  "token_count": 3200,
  "keywords": ["relational structures", "modal language", "Kripke models", "frames", "bisimulation", "normal modal logic"],
  "summary": "Introduces relational structures, modal languages, Kripke models and frames, modal consequence relations, and normal modal logics"
}
```

**The llms.txt standard (2024-2026, now widely adopted)**:

The llms.txt standard (llmstxt.org) proposes a lightweight markdown index file at the root of a documentation collection. Its core format:

```markdown
# Book Title

> Brief description of the collection

## Core Content

- [Chapter 1: Basic Concepts](ch01_basic-concepts.md): Relational structures, modal languages, Kripke models
- [Chapter 2: Models](ch02_models.md): Bisimulations, finite models, standard translation

## Optional

- [Notes and Bibliography](notes.md): Historical notes and references
```

This pattern is relevant: a `README.md` (or `llms.txt`) per book directory that lists chapters with brief descriptions serves as a human-readable complement to the JSON index.

**Token budget awareness**:

Production RAG systems (2025) enforce token budgets by storing `token_count` per chunk in the index and doing greedy selection without reading file content. The `memory-retrieve.sh` already implements this correctly. For literature retrieval with a 4000-token budget, chapter-level chunks of 2000-3500 tokens allow selecting 1-2 chapters per task invocation — sufficient for targeted citation support.

**Keyword enrichment per chunk**:

The 2025-2026 best practice for non-embedding retrieval is to enrich each chunk's metadata with manually curated keywords covering:
- Technical terminology introduced in the section
- Theorems/lemmas proven (e.g., "compactness theorem", "Sahlqvist correspondence")
- Mathematical objects (e.g., "canonical model", "frame definability")
- Named logics/systems (e.g., "S4", "K4", "GL")

This enables keyword-overlap scoring (same algorithm as `memory-retrieve.sh`) to surface the right chapter when the task mentions "Sahlqvist" or "bisimulation".

### Proposed Directory Structure

```
specs/literature/
├── index.json                    # Master registry of all chunks across all books
├── README.md                     # Human-readable guide (existing, keep)
├── blackburn_2001/
│   ├── index.json               # Per-book chapter registry
│   ├── ch00_front-matter.md     # Title, ToC, preface (~200 tokens, optional)
│   ├── ch01_basic-concepts.md   # Chapter 1 (~3000 tokens)
│   ├── ch02_models.md           # Chapter 2 (~3500 tokens)
│   ├── ch03_frames.md           # Chapter 3
│   └── ...
├── hughes_1996/
│   ├── index.json
│   ├── part1_basic-modal-propositional-logic.md
│   ├── part2_normal-modal-systems.md
│   └── part3_modal-predicate-logic.md
├── mendelson_2016/
│   ├── index.json
│   ├── ch01_propositional-calculus.md
│   ├── ch02_first-order-logic.md
│   └── ...
├── chagrov_1997/
│   ├── index.json
│   └── ...
├── bentzen_2023.md              # Paper-length: keep as single file
├── from_2022.md                 # Paper-length: keep as single file
├── henkin_1949.md               # Paper-length: keep as single file
├── johansson_1937.md            # Paper-length: keep as single file
└── post_1921.md                 # Paper-length: keep as single file
```

### Master index.json Schema

Modeled on `.claude/context/index.json` and `memory-retrieve.sh`'s scoring logic:

```json
{
  "version": 1,
  "token_budget": 4000,
  "max_chunks": 10,
  "entries": [
    {
      "id": "blackburn_2001_ch01",
      "bib_key": "Blackburn2001",
      "book_title": "Modal Logic",
      "authors": "Blackburn, de Rijke, Venema",
      "year": 2001,
      "section": "Chapter 1: Basic Concepts",
      "path": "literature/blackburn_2001/ch01_basic-concepts.md",
      "page_range": "1-49",
      "token_count": 3200,
      "keywords": [
        "relational structures", "modal language", "Kripke model",
        "frame", "general frame", "normal modal logic", "bisimulation",
        "modal consequence"
      ],
      "summary": "Introduces relational structures, modal languages, Kripke models and frames, general frames, modal consequence relations, and normal modal logics with historical overview"
    }
  ]
}
```

The `literature-retrieve.sh` script will:
1. Read `specs/literature/index.json`
2. Score entries by keyword overlap with `description + focus_prompt`
3. Greedily select entries within `token_budget` (4000 tokens)
4. Read the selected `.md` files and emit them as `<literature-context>`

### Chunk Size Recommendations

Based on the 4000-token budget and the goal of including 1-3 relevant chapters per task:

| Book type | Recommended chunk granularity | Target token count |
|-----------|-------------------------------|-------------------|
| Long textbook (400+ pages) | Chapter-level | 2000-4000 tokens |
| Medium book (200-400 pages) | Part/section-level | 1500-3000 tokens |
| Short book/monograph (100-200 pages) | Half-chapter or chapter | 1000-2000 tokens |
| Journal paper (<50 pages) | Whole paper | 500-1500 tokens |

For blackburn_2001 (7 chapters, ~560 pages): chapter-level splitting is correct.
For hughes_1996 (3 parts, ~400 pages): part-level splitting may be sufficient to start.
For mendelson_2016 (5 chapters, ~600 pages): chapter-level splitting.
For chagrov_1997 (~700 pages): chapter-level splitting.

### What Makes a Good Chapter File

A well-structured chapter chunk should:
1. Begin with a metadata comment block (optional, for human readers):
   ```markdown
   <!-- Source: Blackburn et al., Modal Logic (2001), Chapter 1, pp. 1-49 -->
   <!-- BibKey: Blackburn2001 -->
   ```
2. Contain the original content verbatim — no summarization, no paraphrasing
3. Exclude page-number comments (`<!-- Page N -->`) that add noise without value
4. Include section headings manually added where the book's ToC indicates sections

---

## Decisions

1. **Split strategy**: Manual chapter extraction guided by each book's table of contents, not automated header-based splitting (which would produce meaningless page-granular chunks).
2. **Index format**: JSON master index at `specs/literature/index.json`, mirroring `.claude/context/index.json` schema, with fields: `id`, `bib_key`, `section`, `path`, `token_count`, `keywords`, `summary`, `page_range`.
3. **Paper-length files**: bentzen_2023.md, from_2022.md, post_1921.md, johansson_1937.md, henkin_1949.md, trufas_2024.md stay as single files but get entries in the master index.
4. **Book-length files to split**: blackburn_2001, hughes_1996, mendelson_2016, chagrov_1997, church_1956, zakharyaschev_2001, gentzen_1935.
5. **Retrieval script**: `literature-retrieve.sh` should follow `memory-retrieve.sh` architecture exactly, reading `index.json` for scoring, then reading selected files for content.
6. **No embeddings**: Pure keyword overlap scoring is sufficient for this use case and avoids all external dependencies.

---

## Recommendations

**Priority 1 (required for --lit to work at all)**:
1. Create `specs/literature/index.json` with entries for the existing paper-length files immediately — these are already the right size and can be indexed as-is.
2. Write `literature-retrieve.sh` mirroring `memory-retrieve.sh`: keyword scoring + greedy token-budget selection + `<literature-context>` output block.
3. Place the script at `.claude/scripts/literature-retrieve.sh` and hook it into the preflight of `/research`, `/plan`, `/implement` when `--lit` is passed.

**Priority 2 (splitting the book-length files)**:
4. Split blackburn_2001.md into `specs/literature/blackburn_2001/ch01_basic-concepts.md` ... `ch07_...md` using the ToC on pages 6-7 of the source (visible in the markdown). Token count each chapter and record in `index.json`.
5. Split hughes_1996.md by its three named Parts (visible in the text: "Part One: Basic Modal Propositional Logic", etc.).
6. Split mendelson_2016.md by chapter (the ToC is in the first few pages; the `## Page N` structure makes extraction straightforward with a line-number-based split).
7. Split chagrov_1997.md — requires manual ToC lookup since the file has no usable markdown structure (the `# ` markers are OCR artifacts, not real headings).
8. Handle church_1956.md, gentzen_1935.md, zakharyaschev_2001.md similarly.

**Priority 3 (enrichment)**:
9. Add curated `keywords` arrays to each index entry — do not rely solely on the section title. Include key theorems, named systems, and technical terms introduced in each chapter.
10. Write per-book `index.json` files as a secondary index (for human navigation and potential future use), but the master `specs/literature/index.json` is what the retrieval script reads.

---

## Risks & Mitigations

| Risk | Mitigation |
|------|-----------|
| Manual splitting is laborious for 700-page books | Start with blackburn_2001 (smallest book, best-structured ToC) as a template; use the same line-number-based extraction pattern for others |
| OCR quality in chagrov_1997 makes boundaries ambiguous | Use page numbers from the PDF as reference; the `## Page N` pattern in mendelson_2016 shows that page-level extraction is feasible even without chapter headings |
| Keywords too sparse → poor retrieval precision | Start with 6-10 keywords per chapter covering theorem names, named systems (K, T, S4, S5), and key concepts; iterate based on retrieval misses |
| Token count estimates wrong → budget overflow | Measure actual token count with `wc -w` × 1.3 (word-to-token ratio) or python tiktoken; store in index |
| literature-retrieve.sh missing until user fixes nvim config | This is acknowledged — the user will fix the script; this research informs the design so implementation can proceed correctly once that's done |

---

## Context Extension Recommendations

- **Topic**: Literature retrieval indexing pattern
- **Gap**: The `.claude/context/` system documents memory-retrieve.sh but not the analogous literature-retrieve.sh pattern. Once implemented, a brief context file `context/patterns/literature-retrieval.md` should document the index schema and retrieval algorithm for future agents.
- **Recommendation**: After implementation, add an entry to `.claude/context/index.json` pointing to this new context file, loaded when `--lit` flag is active.

---

## Appendix

### Search Queries Used

1. "best practices organizing large markdown files LLM context injection chunking 2025 2026"
2. "RAG chunking strategies markdown header-based splitting document collections JSON index metadata 2025"
3. "splitting book PDF markdown chapters subdirectories structured documentation LLM context 2025 shell script retrieval"
4. "llms.txt standard document index markdown AI agents 2025 2026"
5. "token budget aware document retrieval shell script grep keyword matching markdown sections academic papers"

### References

- [Best Chunking Strategies for RAG (and LLMs) in 2026 - Firecrawl](https://www.firecrawl.dev/blog/best-chunking-strategies-rag)
- [Document Chunking for RAG: 9 Strategies - LangCopilot](https://langcopilot.com/posts/2025-10-11-document-chunking-for-rag-practical-guide)
- [Write LLM-friendly docs - Fern](https://buildwithfern.com/post/how-to-write-llm-friendly-documentation)
- [The /llms.txt file standard - llmstxt.org](https://llmstxt.org/)
- [Splitting Markdown Documents for RAG - Glama](https://glama.ai/blog/2024-11-17-splitting-markdown-documents-for-rag)
- [Chunking Strategies for RAG - Weaviate](https://weaviate.io/blog/chunking-strategies-for-rag)
- [mdsplit - Python CLI for splitting markdown at headings](https://pypi.org/project/mdsplit/0.3.1/)
- [grep vs. RAG - LlamaIndex](https://www.llamaindex.ai/blog/is-grep-all-you-need-lexical-vs-sematic-search-for-agents)

### Existing Pattern: memory-index.json Entry Schema

The memory system uses:
- `id`: unique identifier
- `path`: relative path to `.md` file
- `title`: display title
- `summary`: one-sentence description
- `token_count`: for budget calculation
- `keywords`: for overlap scoring
- `topics`: for bonus scoring
- `retrieval_count` / `last_retrieved`: usage tracking

The literature index should use the same fields, adding `bib_key`, `authors`, `year`, `section`, and `page_range`.
