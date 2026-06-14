# Teammate C Findings: Gaps, Shortcomings, and Blind Spots
## Task 194: Curate Zotero PDFs for Literature

**Role**: Critic — research quality and completeness  
**Date**: 2026-06-14  
**Confidence Level**: High (based on direct filesystem and database inspection)

---

## Key Findings

### 1. The Task Is Critically Underspecified

The task record contains only a name (`curate_zotero_pdfs_for_literature`) with no description field in `state.json`. The TODO.md entry has no "Description" block. "Curate" is genuinely ambiguous:

- **Interpretation A**: Extract Zotero annotations (highlights, notes) from PDFs into `.md` files — this is what `/scrape` does.
- **Interpretation B**: Convert Zotero PDFs to text for use as `--lit` context — full text extraction.
- **Interpretation C**: Build a script/workflow that selects relevant PDFs from Zotero and produces curated *summaries* for `specs/literature/`.
- **Interpretation D**: Create `literature-retrieve.sh` (the missing script that `--lit` depends on).

These interpretations have wildly different implementation scopes. The research phase must clarify intent before proposing any solution.

**Critical gap**: No prior work (reports, plans) exists in `specs/194_curate_zotero_pdfs_for_literature/` before this research phase, and the task was created today (2026-06-14T18:15:52Z). The task is at the very beginning of its lifecycle with no documented user intent.

---

### 2. The `literature-retrieve.sh` Script Does Not Exist

**This is a blocking infrastructure gap.** The `--lit` flag is documented in CLAUDE.md and referenced in `skill-researcher/SKILL.md`, `skill-planner/SKILL.md`, and `skill-implementer/SKILL.md` as calling `.claude/scripts/literature-retrieve.sh`. However, that script does not exist at `/home/benjamin/Projects/cslib/.claude/scripts/literature-retrieve.sh`.

The scripts directory contains 38 scripts. `literature-retrieve.sh` is absent.

**Implication**: The `--lit` flag silently fails with an empty context on every invocation. The infrastructure is documented but not implemented. Task 194 may be about creating this script, but that is not stated.

---

### 3. Token Budget vs. Actual File Sizes: A 333:1 Mismatch

The `--lit` system specifies `TOKEN_BUDGET=4000 tokens, MAX_FILES=10` in CLAUDE.md. At approximately 4 characters per token, that is roughly 16,000 characters of usable literature context.

Current `specs/literature/` contains:

| File | Size | Relative to Budget |
|------|------|-------------------|
| `chagrov_1997.md` | 1.4 MB (24,810 lines) | 86x over budget |
| `mendelson_2016.md` | 1.1 MB (59,759 lines) | 68x over budget |
| `church_1956.md` | 1.1 MB (21,798 lines) | 68x over budget |
| `hughes_1996.md` | 837 KB (19,269 lines) | 52x over budget |
| `bentzen_2023.md` | 33 KB (822 lines) | ~2x over budget |
| **Total all .md files** | **5.3 MB** | **333x over budget** |

The existing `specs/literature/*.md` files are verbatim full-text dumps of entire books and papers via `pdftotext`. They vastly exceed what the `--lit` injection system can actually use. Any `literature-retrieve.sh` implementation would either: (a) truncate everything to near-uselessness, or (b) need a fundamentally different approach (curated summaries, per-section extraction, relevance scoring).

**This means the current `specs/literature/` directory is not fit for purpose with the documented token budget.**

---

### 4. Copyright/Licensing: Full Copyrighted Books Are Tracked in Public Git

The repository is a public fork of `leanprover/cslib` pushed to `git@github.com:benbrastmckie/cslib.git`. The following copyrighted full books have been committed as `.md` text dumps and are tracked in `origin/main`:

| File | Copyright Holder | Status |
|------|-----------------|--------|
| `chagrov_1997.md` | Oxford University Press, 1997 ("All rights reserved") | Full book, public repo |
| `mendelson_2016.md` | CRC Press (textbook, 6th ed.) | Full book, public repo |
| `church_1956.md` | Princeton University Press | Full book, public repo |
| `hughes_1996.md` | M.J. Cresswell and G.E. Hughes estate, 1996 ("All rights reserved") | Full book, public repo |
| `chagrov_1997.djvu` | Oxford University Press, 1997 | 7MB binary file, public repo |

These are verbatim full-text dumps of commercial academic books, committed to a public GitHub repository. This is a clear copyright violation. The `.gitignore` excludes `*.pdf` (correct) but does not exclude `*.md` files generated from those PDFs.

The arXiv papers (`bentzen_2023.md`, `trufas_2024.md`, `from_2022.md`) are Creative Commons licensed and present no copyright concern.

**This is the most urgent finding.** Any "curate Zotero PDFs" workflow must not add more copyrighted full-text dumps. The existing violations should be addressed (either removing from git history or making the repository private).

---

### 5. `specs/literature/` Already Has Established Conventions That Constrain the Solution

Direct inspection of `specs/literature/README.md` reveals a well-developed naming and organization convention already in place:

- Naming: `{author}_{year}.md` (lowercase, first author)
- Availability key: `[MD]` = conversion exists, `[NO FILE]` = no local file
- BibKey cross-referencing: uses CSLib's `references.bib` BibKey format (e.g., `[ChagrovZakharyaschev1997]`)
- Organized by topic: Propositional Logic, Intuitionistic and Minimal Logic, Modal Logic, Natural Deduction, Completeness, Algebraic Logic, Prior Art

Any new files added must conform to these conventions. The README documents 27 specific references, of which 15 have `.md` files and 12 are marked `[NO FILE]`.

**Key constraint**: The `references.bib` uses keys like `ChagrovZakharyaschev1997`, `Blackburn2001` — but the Zotero Better BibTeX export uses keys like `Blackburn2002` (different year). There is zero overlap between `references.bib` (48 entries) and the Zotero library export at `/home/benjamin/texmf/bibtex/bib/Zotero.bib` (878 entries). A workflow must reconcile these naming schemes.

---

### 6. Math Notation Quality in Existing Conversions Is Poor for Formal Verification

The existing `.md` files are raw `pdftotext` outputs. Inspection reveals:

- Greek letters become garbled (`<p` for `φ`, `^p` for `ψ`, `xp` for `χ`)
- Math tables become misaligned ASCII (truth tables appear as raw character grids)
- Proof rule boxes become `□` (end-of-proof marker) mixed with modal `□` (necessity operator) — indistinguishable
- Logical connectives: some appear as `—>` (arrow), `A` (and), `V` (or) — ASCII art
- Subscripts/superscripts: `qi+i` for `φᵢ₊₁`, `9Jt` for `𝔐` (model notation)
- Sequent calculus rules: not extractable — they appear as lines of text without inference bar structure

**Example from `chagrov_1997.md`**:
```
p<->q 
p A r <-> q A r 
```
(This is a congruence rule — the `A` is conjunction, not the letter A, and `<->` is biconditional.)

For a formal verification project like CSLib, where agents must accurately transcribe axioms, definitions, and theorems into Lean 4, garbled math notation is not just inconvenient — it can cause proof errors. The `/scrape` command (annotation extraction) would capture highlighted passages with context, but only if the user has annotated the PDFs in Zotero.

---

### 7. Does `references.bib` Already Provide Sufficient Context Without Full Text?

Yes, for citation purposes. The `references.bib` already provides:
- Full bibliographic metadata for all cited works
- BibKey cross-references in docstrings
- Coverage of all 48 CSLib references

The `specs/literature/README.md` already provides:
- Summaries of each reference's relevance to CSLib
- Which chapters/sections are relevant (e.g., "CZ Chapter 1, Section 5.1")
- Notes on design decisions informed by each source (e.g., the McKinsey independence result justifying five primitives)

What `references.bib` + `README.md` do NOT provide:
- Actual theorem statements agents need to transcribe
- Algorithm pseudocode
- Proof sketches that agents need to follow

**Conclusion**: For most `/research` tasks, `references.bib` + `README.md` + web search is sufficient. The `--lit` flag adds value only when an agent needs the exact statement of a theorem or proof technique that cannot be found via `lean_leansearch` or web search.

---

### 8. Zotero Library Scope vs. CSLib Needs

The Zotero library has 891 research items, 873 with PDFs. Only a small fraction is relevant to CSLib:

- Zotero.bib keyword analysis: ~351 entries match "logic" broadly; ~18 match highly specific CSLib topics (modal completeness + Lean4)
- The `references.bib` keys have **zero overlap** with Zotero BibTeX keys (different key naming schemes)
- Key CSLib references (Chagrov & Zakharyaschev, Church, Mendelson, Hughes & Cresswell) are present in Zotero storage but under different keys

The Zotero collection structure (from backup DB) shows collections for: TM Completeness, Papers, Formal Tools, Bilattice Theory, Category Theory, Type Theory, Counterpossibles, etc. These are organized around the user's broader research interests, not CSLib specifically. There is no dedicated "CSLib" or "Lean4 Formalization" Zotero collection.

**This means any automation would require relevance-filtering logic**, which cannot be fully automated without significant false positives or missing relevant papers.

---

### 9. Maintenance Burden Is Not Addressed

"Curating" implies ongoing maintenance. Questions not addressed:

- What happens when a cited paper is updated (e.g., Trufas 2024 gets a new version)?
- What is the workflow for adding new references to `references.bib` vs. `specs/literature/`?
- How does the selection of "relevant" Zotero papers evolve as CSLib grows into new topics?
- The `specs/literature/README.md` is already manually maintained — does automation add value or complexity?
- If `literature-retrieve.sh` implements relevance scoring against task descriptions, how is that score tuned?

No answers exist because the task has no documented scope beyond its name.

---

## Recommended Approach

Based on the above, the research should clarify scope by investigating two distinct work items:

**Item A (Infrastructure)**: Create `literature-retrieve.sh` that reads `specs/literature/*.md` and `.txt` files, applies a token budget, and returns a `<literature-context>` block. This is a prerequisite for `--lit` to function at all.

**Item B (Content)**: Define a selection and summarization protocol for adding new papers from Zotero. This should:
1. Use `/scrape` (annotation extraction) for PDFs the user has read and annotated, rather than full-text conversion.
2. Use curated summaries (200-500 words) rather than full-text dumps for books — to fit within the 4000-token budget.
3. Restrict to open-access papers (arXiv, Creative Commons) or brief excerpts (fair use) for git tracking, to avoid the copyright issue.
4. Map Zotero BibTeX keys to CSLib `references.bib` BibKey format.

**Item C (Remediation)**: Remove or substantially redact the full-text dumps of copyrighted books from git history. At minimum, add `*.md` for files in `specs/literature/` to `.gitignore` except for curated summaries.

---

## Evidence/Examples

- `literature-retrieve.sh` absence confirmed: `ls /home/benjamin/Projects/cslib/.claude/scripts/` — script not present.
- Copyright text in `chagrov_1997.md` line 79: "All rights reserved. No part of this publication may be reproduced..."
- Copyright text in `hughes_1996.md` line 26: "©1996 M.J. Cresswell and the estate of G.E. Hughes. All rights reserved."
- File sizes: `mendelson_2016.md` = 1.08 MB, `chagrov_1997.md` = 1.38 MB vs. ~16 KB token budget.
- Public remote confirmed: `origin git@github.com:benbrastmckie/cslib.git`.
- Files in `origin/main` confirmed: `git ls-tree origin/main specs/literature/` shows all 15 files tracked.
- Zero BibKey overlap: Python comparison of `references.bib` vs. `Zotero.bib` found 0 matching keys.
- Task has no description field in `state.json`.

---

## Confidence Level

**High** for all findings based on direct file system inspection, git history analysis, and database queries. The copyright concern, missing script, and token budget mismatch are confirmed facts, not estimates.

**Medium** for the "Zotero annotation" approach being preferable to full-text extraction — this depends on whether the user has actually annotated the relevant PDFs in Zotero (not verified, as Zotero was running with locked database during inspection; backup DB shows 873 PDF attachments but annotation count not queried).
