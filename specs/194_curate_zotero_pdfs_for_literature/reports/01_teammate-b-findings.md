# Teammate B Findings: Alternative Patterns and Prior Art for Literature Curation

**Task 194**: Curate Zotero PDFs for literature
**Role**: Alternative Approaches - Alternative patterns, prior art, token budgets, summarization strategies, formal verification community practices
**Date**: 2026-06-14

---

## Key Findings

### Finding 1: `literature-retrieve.sh` Does Not Exist Yet

The `specs/literature/` directory exists and contains 14 `.md` files (plus the README), but the
`literature-retrieve.sh` script referenced in three skills is **not implemented**. All three
skill files reference it via:

```bash
lit_context=$(bash .claude/scripts/literature-retrieve.sh "$description" "$task_type" 2>/dev/null) || lit_context=""
```

Files referencing the missing script:
- `.claude/skills/skill-researcher/SKILL.md` (line 149)
- `.claude/skills/skill-implementer/SKILL.md`
- `.claude/skills/skill-planner/SKILL.md`

The CLAUDE.md documents that `literature-retrieve.sh` reads all `.md` and `.txt` files from
`specs/literature/` up to `TOKEN_BUDGET=4000` tokens and `MAX_FILES=10`. This script must be
created as part of any complete implementation of the `--lit` workflow.

---

### Finding 2: Existing Literature Files Are Massively Over Budget

The current `.md` files in `specs/literature/` were produced by raw PDF-to-markdown conversion
and are far too large for the stated 4,000-token budget:

| File | Approx. Tokens | Over Budget by |
|------|---------------|----------------|
| `chagrov_1997.md` | ~329,838 | 82x |
| `mendelson_2016.md` | ~292,193 | 73x |
| `church_1956.md` | ~267,560 | 67x |
| `hughes_1996.md` | ~208,429 | 52x |
| `zakharyaschev_2001.md` | ~110,455 | 28x |
| `blackburn_2001.md` | ~33,884 | 8x |
| `gentzen_1935.md` | ~28,345 | 7x |
| `post_1921.md` | ~13,230 | 3x |
| `from_2022.md` | ~11,549 | 2.9x |
| `trufas_2024.md` | ~9,699 | 2.4x |
| `bentzen_2023.md` | ~7,334 | 1.8x |
| `johansson_1937.md` | ~5,653 | 1.4x |
| `henkin_1949.md` | ~5,872 | 1.5x |
| `README.md` | ~1,810 | Under budget |

**Critical implication**: The literature-retrieve.sh script, when implemented, will only ever
be able to inject the `README.md` (1,810 tokens) within the 4,000-token budget if it loads
files in sorted order, since all other files alone exceed budget. The MAX_FILES=10 cap is
irrelevant because even a single large file exhausts the budget.

The parallel with `memory-retrieve.sh` is instructive: that script has `TOKEN_BUDGET=2000`
and `MAX_ENTRIES=5` with a greedy selection algorithm (takes entries that fit within budget).

---

### Finding 3: The System Already Has Full PDF-to-Markdown Infrastructure

The project has robust, working tooling for PDF-to-markdown conversion:

**Available tools** (confirmed installed):
- `pymupdf` / `fitz` (Python): Primary PDF extractor
- `pdftotext` (at `/home/benjamin/.nix-profile/bin/pdftotext`): Text-layer extraction
- `pdfannots` (at `/run/current-system/sw/bin/pdfannots`): Annotation extraction
- `pandoc` (at `/run/current-system/sw/bin/pandoc`): Universal document converter

**Existing agent infrastructure**:
- `document-agent`: Full PDF-to-Markdown pipeline using `pymupdf4llm` (LLM-optimized output)
- `scrape-agent`: PDF annotation extraction to Markdown/JSON
- `skill-filetypes` + `filetypes-router-agent`: Routing layer for format conversions
- `/convert` command: User-facing interface for document conversion

The `document-agent` already handles PDF-to-Markdown with the best-available tools:
- Primary: `pymupdf4llm` (LLM-optimized markdown from PDF)
- Fallback: `pymupdf` with text extraction and table detection
- Fallback: `pandoc`

This means the project does NOT need new tooling for raw PDF-to-markdown conversion. The gap
is in **curation** (curated summaries vs. raw conversions) and **the missing `literature-retrieve.sh` script**.

---

### Finding 4: Prior Art in the Archive - Curated Proof Structure Documents

The archive contains a high-quality example of what a curated literature document should look
like: `specs/archive/095_modal_k_t_soundness_completeness/references/literature-proof-structure.md`

This file demonstrates the ideal format:
- 80 lines, approximately 800 tokens (well under the 4,000-token budget)
- Structured as: Sources -> Common Proof Architecture -> Step-by-step formal steps
- References three source papers, cross-referencing specific theorems
- Distills proof structure without including raw paper text
- Uses formal notation directly applicable to Lean 4 formalization

This is the model for what curated literature files should look like -- not full-text conversions.

---

### Finding 5: The README.md in specs/literature/ Is the Right Approach (Partially)

The existing `specs/literature/README.md` (1,810 tokens) serves as a bibliography index with:
- Paper BibKey identifiers (e.g., `[ChagrovZakharyaschev1997]`)
- Availability markers: `[MD]` = markdown in directory, `[NO FILE]` = unavailable
- Short descriptions of each paper's relevance to CSLib

This is an excellent starting point for the `--lit` injection context. It's the only file
currently within the 4,000-token budget. However, it lacks the detailed proof structure
information that makes literature injection valuable (like the archive example above).

---

### Finding 6: BibTeX Integration Points Are Already Established

The project has a mature BibTeX workflow:
- `references.bib` at project root with BibKey format (e.g., `Blackburn2001`, `ChagrovZakharyaschev1997`)
- `~/texmf/bibtex/bib/Zotero.bib` with 11,788 lines (full Zotero library auto-export via Better BibTeX)
- Zotero running at `/run/current-system/sw/bin/zotero` with Better BibTeX plugin
- Storage directory at `/home/benjamin/Documents/Zotero/storage/` with 923 items

The CSLib H3 hard-mode contract requires "BibKey verification against `references.bib`", meaning
any new literature files must use citation keys that match `references.bib` entries. The naming
convention `{author}_{year}.md` (e.g., `bentzen_2023.md`) is established in the README.

---

### Finding 7: Summarization Strategy - Abstract+Key Sections vs. Full Text

Given the token budget constraint, full-text conversion is inappropriate. Three strategies exist
for academic papers in AI context:

**Strategy A: Abstract + Key Sections (recommended for long books/papers)**
Extract: abstract, theorem statements, proof sketches, key definitions
Token target: 500-1,500 tokens per paper
Suitable for: Chagrov/Mendelson/Church (huge books; only specific sections matter)

**Strategy B: Structured Proof Summary (recommended for formal verification)**
Format: Sources -> Architecture -> Step-by-step formal steps (like the archive example)
Token target: 400-800 tokens per paper
Suitable for: All papers, especially when implementing specific theorems

**Strategy C: Key Theorem Catalog (recommended for reference lookup)**
Format: Theorem name -> Statement -> CSLib location -> BibKey
Token target: 200-400 tokens per paper
Suitable for: Cross-reference catalog during implementation

The existing README.md is closest to Strategy C but without theorem statements.

---

### Finding 8: The Memory System's Segmentation Algorithm Is Directly Applicable

The `skill-memory` SKILL.md defines a segmentation algorithm for content extraction that
mirrors what is needed for literature curation:

```
- Files >800 tokens: split at section boundaries
- Files 200-500 tokens: ideal size, no action
- Files <100 tokens: merge with adjacent same-topic segment
```

This same logic should govern curated literature files: each file should be
200-500 tokens (ideal) with a hard cap of 800 tokens. The `literature-retrieve.sh` budget
of 4,000 tokens can then fit 5-20 curated files.

The memory system's greedy selection (take entries that fit within budget) is also the
right model for `literature-retrieve.sh`, but since all current files exceed budget, the
selector effectively reduces to "only load README.md."

---

### Finding 9: Alternative Source Management Approaches

Beyond Zotero integration, alternative approaches include:

**BibTeX-first workflow** (recommended for this project):
1. All papers already in `~/texmf/bibtex/bib/Zotero.bib` with BibKeys
2. Use BibKey as the primary identifier; create curated `.md` per BibKey
3. No direct Zotero API needed -- BibTeX export already auto-syncs

**Manual PDF + pymupdf pipeline**:
1. User runs `/convert paper.pdf` to get raw markdown
2. User (or agent) manually curates to key sections
3. Result stored as `{author}_{year}_curated.md` in `specs/literature/`

**Annotation-driven curation** (using existing scrape-agent):
1. User annotates PDFs with highlights in Zotero/Okular
2. `/scrape paper.pdf` extracts annotations to markdown
3. Annotations + key theorems = curated file
4. This is optimal for user-curated content since annotations reflect what the user finds important

**Task-scoped literature files** (alternative to global `specs/literature/`):
1. Create `specs/{NNN}_{SLUG}/literature/` per task (not shared global directory)
2. Only load literature relevant to the current task
3. No token budget pressure from cross-task literature accumulation
4. Tradeoff: cannot reuse across tasks

---

### Finding 10: Mathlib and Lean Community Literature Practices

Mathlib handles reference material via:
- `references.bib` at the Mathlib root (identical to CSLib's approach -- CSLib inherited this)
- No mechanism to inject paper text into proofs; references are metadata only
- Docstring citations using `@[...] (See [BibKey])` format

The FormalizedFormalLogic project (referenced in the CSLib README) uses a similar approach:
GitHub repository + accompanying book at https://formalizedformallogic.github.io/Book/

**Industry practice for AI-assisted formal verification**:
There is no established standard. The closest comparable pattern is Lean's "blueprint" approach
(used in Liquid Tensor Experiment, Carleson project) where a human-readable LaTeX blueprint
documents proof structure, and AI agents implement from the blueprint. The CSLib `--lit` system
is implementing a lightweight version of this: curated summaries as the "blueprint."

---

## Recommended Approach

Based on these findings, the recommended approach has three components:

### Component 1: Create `literature-retrieve.sh` (blocking dependency)

The script must be created before `--lit` can work at all. It should follow the same
greedy selection algorithm as `memory-retrieve.sh`:

```bash
TOKEN_BUDGET=4000
MAX_FILES=10

# Load all .md and .txt files from specs/literature/
# Sort by file size (smallest first -- most budget-efficient)
# Greedily include files that fit within TOKEN_BUDGET
# Wrap in <literature-context> tags
```

Smallest-first sorting ensures smaller, already-curated files are injected before large ones.

### Component 2: Curate Existing Large Files into Summary Files

For each large `.md` in `specs/literature/`, create a companion `{name}_curated.md` file
targeting 400-800 tokens. Use the archive example
(`specs/archive/095_modal_k_t_soundness_completeness/references/literature-proof-structure.md`)
as the template. The raw full-text `.md` files can remain for reference but should be excluded
from injection (e.g., by a filename convention or explicit exclusion list).

Suggested naming: `{author}_{year}_key.md` (key = key theorems/sections)

### Component 3: Establish a Zotero-to-Curated Pipeline

For new papers being added from Zotero:
1. Use `/convert {pdf_path}` to get raw markdown (document-agent already handles this)
2. Store raw output as `{author}_{year}.md` (already done for existing files)
3. Manually or agent-generate curated `{author}_{year}_key.md` from raw
4. The `literature-retrieve.sh` script should prefer `_key.md` files over plain `.md` files
   (or use a separate subdirectory structure like `specs/literature/curated/` vs. `specs/literature/raw/`)

---

## Evidence/Examples

**Direct evidence from codebase**:
- Missing script: `grep -r "literature-retrieve" .claude/skills/` (3 matches, no corresponding `.sh` file)
- Archive example of ideal curated document: `specs/archive/095_modal_k_t_soundness_completeness/references/literature-proof-structure.md`
- Token budget mismatch: `wc -w specs/literature/*.md` (smallest non-README file = 4,349 words = ~5,654 tokens, over 4,000 budget)
- Memory system segmentation algorithm in `.claude/skills/skill-memory/SKILL.md` (200-800 token per segment guideline)
- Greedy selection algorithm in `.claude/scripts/memory-retrieve.sh` (TOKEN_BUDGET=2000, MAX_ENTRIES=5)

**Tools available for pipeline**:
- `pymupdf` installed: `python3 -c "import fitz; print('ok')"` returns `ok`
- `pdftotext` at `/home/benjamin/.nix-profile/bin/pdftotext`
- `pdfannots` at `/run/current-system/sw/bin/pdfannots`
- `pandoc` at `/run/current-system/sw/bin/pandoc`

---

## Confidence Level

**High confidence** on:
- `literature-retrieve.sh` does not exist (directly verifiable)
- Existing files are over token budget (directly measurable)
- Archive example is the right template (directly readable)
- Available tools (confirmed with `which` commands)
- Memory system algorithm as applicable pattern (directly readable)

**Medium confidence** on:
- Token budget figure of 4,000 (from CLAUDE.md documentation, not yet-implemented script)
- Optimal curated file size (200-800 tokens from memory system heuristic, may need tuning)
- Smallest-first vs. relevance-based sorting for literature-retrieve.sh (design choice)

**Low confidence** on:
- Whether the project intends curated summaries vs. task-scoped literature (design decision for user)
- Whether raw `.md` files should be replaced or kept alongside curated versions
