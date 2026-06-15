# Research Report: Task #200

**Task**: 200 - Fix Literature Directory Quality
**Started**: 2026-06-14T00:00:00Z
**Completed**: 2026-06-14T00:30:00Z
**Effort**: 1.5 hours
**Dependencies**: None
**Sources/Inputs**: Codebase (specs/literature/), index.json, per-book index.json files, README.md
**Artifacts**: specs/200_fix_literature_directory_quality/reports/01_literature-quality-audit.md
**Standards**: report-format.md, subagent-return.md

---

## Executive Summary

- The `specs/literature/` directory is largely well-organized, with 7 books correctly split into chapter/section subdirectories and all 45 index.json entries pointing to existing files
- Critical gap: `literature-retrieve.sh` is referenced in 3 skill files (skill-researcher, skill-planner, skill-implementer) but **does not exist** — the `--lit` flag is completely non-functional
- All split chapter files greatly exceed the 4000-token budget; the budget only applies to how many files get injected (MAX_FILES=10), not per-file size — but without the script, nothing gets injected at all
- blackburn_2001 split is genuinely incomplete: only 3 of 8+ chapters available (source limitation acknowledged in book index.json)
- The 3 scholarly reconstruction files (burgess_1984.md, gabbay_1994_ch10.md, reynolds_1992.md) have substantive content despite low token counts — adequate for research use
- 7 monolithic .md files are redundant duplicates of their chapter splits; 1 (blackburn_2001.md) covers only what's split
- README.md references a non-existent file: `blackburn_2001_ch4_summary.md`
- zakharyaschev_2001/sec00_introduction.md exists on disk but is absent from index.json

---

## Context & Scope

This audit covers all files in `/home/benjamin/Projects/cslib/specs/literature/` — a directory providing reference material for the `--lit` flag during `/research`, `/plan`, and `/implement` phases. The goal is to assess completeness, accuracy, and functionality for lit injection.

The `--lit` mechanism works as follows per CLAUDE.md:
> `literature-retrieve.sh` reads all `.md` and `.txt` files from `specs/literature/`. Files are included up to TOKEN_BUDGET=4000 tokens (MAX_FILES=10).

The critical implementation note: the TOKEN_BUDGET/MAX_FILES parameters are apparently for **selecting which files** to inject (keyword-matching, selecting up to 10 files that together fit the budget), not for enforcing per-file token limits.

---

## Findings

### 1. Complete File Inventory

**Top-level monolithic .md files** (words → actual tokens at 1.3x):

| File | Words | Tokens | Status |
|------|-------|--------|--------|
| bentzen_2023.md | 5,642 | 7,334 | Stand-alone paper — must keep |
| blackburn_2001.md | 26,065 | 33,884 | Redundant — only covers pp. 1-69 (same as 3 split files) |
| burgess_1982_i.md | 3,842 | 4,994 | Stand-alone paper — must keep |
| burgess_1982_ii.md | 4,027 | 5,235 | Stand-alone paper — must keep |
| burgess_1984.md | 1,655 | 2,151 | Scholarly reconstruction — keep |
| chagrov_1997.md | 253,722 | 329,838 | Redundant — fully covered by 6 split files |
| church_1956.md | 205,816 | 267,560 | Redundant — fully covered by 7 split files |
| from_2022.md | 8,884 | 11,549 | Stand-alone paper — must keep |
| gabbay_1994_ch10.md | 1,753 | 2,278 | Scholarly reconstruction — keep |
| gentzen_1935.md | 21,804 | 28,345 | Redundant — fully covered by 5 split files |
| henkin_1949.md | 4,517 | 5,872 | Stand-alone paper — must keep |
| hughes_1996.md | 160,330 | 208,429 | Redundant — fully covered by 4 split files |
| johansson_1937.md | 4,349 | 5,653 | Stand-alone paper — must keep |
| mendelson_2016.md | 224,764 | 292,193 | Redundant — fully covered by 6 split files |
| post_1921.md | 10,177 | 13,230 | Stand-alone paper — must keep |
| reynolds_1992.md | 1,594 | 2,072 | Scholarly reconstruction — keep |
| trufas_2024.md | 7,461 | 9,699 | Stand-alone paper — must keep |
| zakharyaschev_2001.md | 84,966 | 110,455 | Redundant — fully covered by 4 split files |

**Chapter/section split files and their token counts:**

| Directory | Files | Tokens (actual) |
|-----------|-------|-----------------|
| blackburn_2001/ | ch00_preface.md | 6,942 |
| blackburn_2001/ | ch01_basic-concepts.md | 14,527 |
| blackburn_2001/ | ch02_models-partial.md | 12,168 |
| chagrov_1997/ | p00_front-matter.md | 4,508 |
| chagrov_1997/ | p01_introduction.md | 70,402 |
| chagrov_1997/ | p02_kripke-semantics.md | 33,360 |
| chagrov_1997/ | p03_adequate-semantics.md | 80,462 |
| chagrov_1997/ | p04_properties-of-logics.md | 85,901 |
| chagrov_1997/ | p05_algorithmic-problems.md | 55,408 |
| church_1956/ | ch00_front-matter.md | 2,987 |
| church_1956/ | ch00b_introduction.md | 55,560 |
| church_1956/ | ch01_propositional-calculus.md | 35,656 |
| church_1956/ | ch02_propositional-calculus-continued.md | 31,625 |
| church_1956/ | ch03_functional-calculi-first-order.md | 32,390 |
| church_1956/ | ch04_pure-functional-calculus.md | 54,813 |
| church_1956/ | ch05_functional-calculi-second-order.md | 52,702 |
| gentzen_1935/ | sec00_synopsis-and-notation.md | 3,105 |
| gentzen_1935/ | sec02_natural-deduction.md | 3,651 |
| gentzen_1935/ | sec03_lj-lk-hauptsatz.md | 10,033 |
| gentzen_1935/ | sec04_applications.md | 6,063 |
| gentzen_1935/ | sec05_equivalence.md | 5,658 |
| hughes_1996/ | p00_front-matter.md | 2,628 |
| hughes_1996/ | p01_basic-modal-propositional-logic.md | 62,344 |
| hughes_1996/ | p02_normal-modal-systems.md | 54,706 |
| hughes_1996/ | p03_modal-predicate-logic.md | 88,869 |
| mendelson_2016/ | ch00_front-matter.md | 9,370 |
| mendelson_2016/ | ch01_propositional-calculus.md | 22,270 |
| mendelson_2016/ | ch02_first-order-logic.md | 70,398 |
| mendelson_2016/ | ch03_formal-number-theory.md | 48,399 |
| mendelson_2016/ | ch04_axiomatic-set-theory.md | 46,325 |
| mendelson_2016/ | ch05_computability.md | 93,697 |
| zakharyaschev_2001/ | sec00_introduction.md | 2,294 (not in index.json!) |
| zakharyaschev_2001/ | sec01_unimodal-logics.md | 46,126 |
| zakharyaschev_2001/ | sec02_polymodal-logics.md | 19,610 |
| zakharyaschev_2001/ | sec03_superintuitionistic-logics.md | 42,539 |

**Files within 4000-token budget (usable for single-file injection):**
- church_1956/ch00_front-matter.md: 2,987 tokens
- zakharyaschev_2001/sec00_introduction.md: 2,294 tokens
- gentzen_1935/sec00_synopsis-and-notation.md: 3,105 tokens
- gentzen_1935/sec02_natural-deduction.md: 3,651 tokens
- hughes_1996/p00_front-matter.md: 2,628 tokens
- burgess_1984.md: 2,151 tokens
- gabbay_1994_ch10.md: 2,278 tokens
- reynolds_1992.md: 2,072 tokens
- chagrov_1997/p00_front-matter.md: 4,508 tokens (slightly over)

**Note**: The `literature-retrieve.sh` script is described as reading "all .md and .txt files from specs/literature/" and injecting up to 10 files within TOKEN_BUDGET=4000 tokens total. This means all chapter-level files are too large for injection individually, and the monolithic files are vastly too large. The practical implication is that only the front-matter files, brief section files, and scholarly reconstructions fall within range. However, since the script doesn't exist yet, the actual selection logic is unknown — it may be keyword-based with selective inclusion.

---

### 2. Per-Book Split Completeness Analysis

#### blackburn_2001 — INCOMPLETE (source limitation)
- **Expected**: 8 chapters (Ch 0: Preface, Ch 1: Basic Concepts, Ch 2: Models, Ch 3: Frames, Ch 4: Correspondence Theory, Ch 5: Completeness, Ch 6: Decidability, Ch 7: Extended Modal Logic)
- **Available**: 3 files (ch00_preface, ch01_basic-concepts, ch02_models-partial — only pages 1-69)
- **Status**: The book index.json explicitly states: "Source file covers pages 1-69 only (Chapters 1-2 partial). Chapters 3-7 not available in this markdown source."
- **Assessment**: This is a genuine source limitation, not a splitting error. The monolithic blackburn_2001.md also ends at page 69. Missing chapters 3-7 are unavailable.

#### mendelson_2016 — COMPLETE
- **Expected**: ch00 (front matter) + ch01-ch05 = 6 files
- **Available**: 6 files covering pages i-xxiv and 1-443+
- **Word count parity**: Monolithic 224,764 words vs chapters_total 223,432 words (99.4%)
- **Terminus issue**: ch05 ends with publisher blurb rather than clean chapter end — likely PDF scan artifact. Content is complete through the book.
- **Assessment**: Split is complete and content matches. Minor artifact at the end of ch05 (publisher advertisement on back cover).

#### church_1956 — COMPLETE
- **Expected**: ch00 (front matter) + ch00b (Introduction pp. 1-68) + ch01-ch05 = 7 files
- **Available**: 7 files covering pages 1-388 (through index at back)
- **Word count parity**: Monolithic 205,816 words vs chapters_total 204,412 words (99.3%)
- **ch05 terminus**: Ends with an author index — expected content for book end.
- **Assessment**: Split is complete. The naming of `ch00b` for the Introduction (pages 1-68) is unusual but correctly documented in the book index.json.

#### chagrov_1997 — COMPLETE
- **Expected**: p00 (front matter) + p01-p05 = 6 files
- **Available**: 6 files (Parts I-V, pages i-xv and 3-592)
- **Assessment**: Split is complete and accurate. This is the primary CSLib reference (CZ).

#### gentzen_1935 — COMPLETE (section numbering gap)
- **Expected**: sec00 (synopsis/sect I) + sec02-sec05 = 5 files
- **Available**: 5 files
- **Note**: There is no sec01 file — the numbering jumps from sec00 to sec02. This is intentional: sec00 covers both the Synopsis and Section I (Terminology). Section I is brief notation material incorporated into sec00.
- **Assessment**: Split is complete. The sec01 "gap" is correct.

#### hughes_1996 — COMPLETE
- **Expected**: p00 (preface) + p01-p03 = 4 files
- **Available**: 4 files
- **Assessment**: Split is complete.

#### zakharyaschev_2001 — MOSTLY COMPLETE (missing sec00 from index)
- **Expected**: sec00 (introduction) + sec01-sec03 = 4 files
- **Available**: 4 files (sec00 through sec03)
- **Problem**: `zakharyaschev_2001/sec00_introduction.md` exists on disk (1,765 words, 2,294 tokens) but is NOT in index.json — neither as a standalone entry nor referenced in any book-level index.json for zakharyaschev
- **Assessment**: Split is physically complete but sec00 is orphaned from the index.

---

### 3. index.json Accuracy Audit

**Summary**: All 45 entries in `specs/literature/index.json` point to files that exist on disk. No broken paths.

**Token count discrepancies**: The index.json token counts are consistently **slightly lower** than actual (words × 1.3) by 20-250 tokens. This is a systematic rounding artifact — likely the index was generated with a slightly different formula or from a slightly different word count tool. All discrepancies are small (< 0.5% error) and not materially misleading.

| Entry | Index tokens | Actual tokens | Error |
|-------|-------------|---------------|-------|
| gentzen_1935_sec00 | 3,074 | 3,105 | +31 |
| chagrov_1997_p01 | 70,202 | 70,402 | +200 |
| chagrov_1997_p04 | 85,664 | 85,901 | +237 |
| mendelson_2016_ch05 | 93,601 | 93,697 | +96 |
| zakharyaschev_2001_sec03 | 42,573 | 42,539 | -34 |

All other entries are within ±50 tokens of actual.

**Missing entries in index.json:**
1. `zakharyaschev_2001/sec00_introduction.md` — file exists, not indexed
2. `blackburn_2001.md` — monolithic file, not indexed (expected — it's a redundant duplicate)
3. `chagrov_1997.md`, `church_1956.md`, `gentzen_1935.md`, `hughes_1996.md`, `mendelson_2016.md`, `zakharyaschev_2001.md` — monolithic files, not indexed (expected — all redundant duplicates)

**README.md inaccuracy:**
- Line 169 references `blackburn_2001_ch4_summary.md` — this file does not exist
- The README also references `concepts.md` (from a relative link `concepts.md` in markdown) — does not exist

**Keyword accuracy**: Keywords in index.json entries are generally well-chosen and accurate for their files. No significant keyword mismatches found.

---

### 4. Scholarly Reconstruction Files Assessment

These 3 files are described as "scholarly reconstructions from standard references" — i.e., they were created by summarizing/reconstructing content from paywalled sources rather than direct OCR/conversion.

#### burgess_1984.md (1,655 words, 2,151 tokens)
**Content assessment**: HIGH QUALITY. Contains:
- Definitions of F/P/G/H/U/S operators with precise semantic clauses
- Kt axioms and extensions (transitivity, linearity, density, discreteness)
- Until/Since axiom sets (U1-U3, U_expand, S1-S3, S_expand) matching Burgess 1982
- Canonical model construction (MCS definitions, Truth Lemma statement)
- Frame class table (linear, dense, discrete, ω, ℤ, ℚ, ℝ orders with axioms)
- Temporal logic over integers (circle-F/P operators, completeness reference)
- Kamp's theorem statement and corollary

**Verdict**: Substantive content. All key definitions and theorems present in a usable form. Below 4000-token budget. Safe for --lit injection.

#### gabbay_1994_ch10.md (1,753 words, 2,278 tokens)
**Content assessment**: HIGH QUALITY. Contains:
- Separation Theorem (Theorem 10.2.9) with precise statement
- Pure future/past formula definitions (Def 10.2.1)
- Key lemmas: distributivity, negation equivalences, duality, rank definition
- Elimination lemmas (10.2.5, 10.2.6) and TemporalClosure (10.2.7)
- Corollary 10.2.10 (reduction to one-directional logic)
- Full TLZ axiom system (Definition 10.3.1)
- Completeness proof sketch (Steps 1-4)
- Integer Assembly Lemma (10.4.2)
- BX bimodal extension (10.5)
- Key technical lemmas for Lean formalization (10.6)

**Verdict**: Highly substantive. Well-suited for use as reference during Lean formalization. Below 4000-token budget. The content is richer than the word count suggests because of mathematical notation density.

#### reynolds_1992.md (1,594 words, 2,072 tokens)
**Content assessment**: HIGH QUALITY. Contains:
- FOTL syntax and semantics (temporal structures, varying domains)
- Full axiom system FOTL-U-S (propositional + first-order + interaction axioms)
- Canonical model method with FOTL-MCS definition and Henkin witnesses
- Truth Lemma statement for FOTL
- Linearity handling (Lindenbaum adaptation, Lin axiom)
- Comparison with Burgess 1982 (propositional restriction connection)
- Soundness, Completeness, Decidability theorems (7.1-7.3)
- Discrete case remarks connecting to GHR94 Chapter 10

**Verdict**: Substantive content covering the key theoretical contributions. The note "Scholarly reconstruction" reflects that this paper is paywalled; the content is accurate and research-usable. Below 4000-token budget.

**Overall**: All 3 scholarly reconstruction files are adequate for research use. They are well-organized and contain the key definitions, theorems, and proof structures needed for CSLib formalization reference.

---

### 5. Monolithic Files: Safe to Remove vs Must Keep

**SAFE TO REMOVE** (fully redundant with complete chapter splits):
1. `chagrov_1997.md` — 329,838 tokens; 6 split files in chagrov_1997/ cover 99%+ content
2. `church_1956.md` — 267,560 tokens; 7 split files in church_1956/ cover 99%+ content
3. `mendelson_2016.md` — 292,193 tokens; 6 split files in mendelson_2016/ cover 99%+ content
4. `hughes_1996.md` — 208,429 tokens; 4 split files in hughes_1996/ cover the book
5. `gentzen_1935.md` — 28,345 tokens; 5 split files in gentzen_1935/ cover 99%+ content
6. `zakharyaschev_2001.md` — 110,455 tokens; 4 split files in zakharyaschev_2001/ cover the handbook chapter

**Borderline/conditional:**
7. `blackburn_2001.md` — 33,884 tokens; ONLY pages 1-69 exist (source limitation). The split files cover this exact content. The monolithic file adds no content the split files don't have. Safe to remove — BUT note that blackburn chapters 3-7 are simply unavailable (not a removal issue).

**MUST KEEP** (no chapter splits, stand-alone papers):
- `bentzen_2023.md` — Lean 4 formalization paper
- `burgess_1982_i.md` — Journal paper Part I
- `burgess_1982_ii.md` — Journal paper Part II
- `burgess_1984.md` — Scholarly reconstruction (under budget)
- `from_2022.md` — Isabelle/HOL paper
- `gabbay_1994_ch10.md` — Scholarly reconstruction (under budget)
- `henkin_1949.md` — Journal paper
- `johansson_1937.md` — Journal paper
- `post_1921.md` — Journal paper
- `reynolds_1992.md` — Scholarly reconstruction (under budget)
- `trufas_2024.md` — Lean 4 formalization paper

---

### 6. Critical Issue: literature-retrieve.sh Missing

The `--lit` flag is implemented in three skills (skill-researcher, skill-planner, skill-implementer) and references:
```bash
lit_context=$(bash .claude/scripts/literature-retrieve.sh "$description" "$task_type" 2>/dev/null) || lit_context=""
```

**The script `.claude/scripts/literature-retrieve.sh` does not exist.** The command is called with `2>/dev/null` and `|| lit_context=""`, so failure is silent — agents using `--lit` simply receive no literature context without any error. The `--lit` flag is currently a no-op.

This is the highest-priority fix needed: the entire `--lit` mechanism is broken.

The script needs to:
1. Accept `$description` and `$task_type` as arguments
2. Read `specs/literature/index.json` for keyword matching
3. Select relevant entries (keyword match against description/task_type)
4. Read and inject up to MAX_FILES=10 files, within TOKEN_BUDGET=4000 tokens
5. Wrap output in `<literature-context>` tags
6. Handle missing directory gracefully (exit 0, no output)

---

## Decisions

- The blackburn_2001 "only 3 chapters" issue is a source limitation, not a split deficiency. No action possible on missing chapters 3-7.
- All monolithic .md files for books with complete splits (chagrov, church, mendelson, hughes, gentzen, zakharyaschev, blackburn) are safe to remove — they add no content and waste significant disk space (1.2M+ words total across 7 redundant files).
- The scholarly reconstruction files are adequate quality and need no improvement.
- zakharyaschev_2001/sec00_introduction.md needs an index.json entry added.
- README.md reference to `blackburn_2001_ch4_summary.md` should be corrected.

---

## Risks & Mitigations

- **Removing monolithic files**: Risk is low since chapters cover 99%+ content. Before removal, verify the word count parity (done: 99.3-99.4% coverage). Keep a record of what was removed.
- **literature-retrieve.sh creation**: Must implement keyword matching correctly. If no keywords match, should fall back to injecting the most relevant front-matter files rather than nothing.
- **Token budget misunderstanding**: The 4000-token budget in CLAUDE.md refers to cumulative injection budget across selected files, not per-file limits. Chapter files (10k-94k tokens each) are all too large for single-file injection within a 4000-token total budget. Only the small files (reconstructions, front-matter sections) are individually small enough.

---

## Recommendations (Prioritized by Impact)

### Priority 1 — Create literature-retrieve.sh (BLOCKING)
The `--lit` flag is completely non-functional. Create `.claude/scripts/literature-retrieve.sh` that:
- Reads `specs/literature/index.json`
- Matches entries against the provided description/task_type by keyword overlap
- Selects up to 10 matching entries that together fit within TOKEN_BUDGET
- Reads each file and outputs `<literature-context>` block
- Exits cleanly if directory missing or no matches

### Priority 2 — Remove Redundant Monolithic Files
Remove 7 large monolithic files (verified to be fully covered by chapter splits):
- `chagrov_1997.md` (~329k tokens wasted)
- `mendelson_2016.md` (~292k tokens wasted)
- `church_1956.md` (~268k tokens wasted)
- `hughes_1996.md` (~208k tokens wasted)
- `zakharyaschev_2001.md` (~110k tokens wasted)
- `blackburn_2001.md` (~34k tokens wasted)
- `gentzen_1935.md` (~28k tokens wasted)
Total savings: ~1.25M tokens worth of files eliminated.

### Priority 3 — Add Missing index.json Entry
Add entry for `zakharyaschev_2001/sec00_introduction.md` to `specs/literature/index.json`:
- id: "zakharyaschev_2001_sec00"
- path: "zakharyaschev_2001/sec00_introduction.md"
- token_count: 2294
- keywords: ["advanced modal logic", "survey", "historical overview", "unimodal", "polymodal", "superintuitionistic"]

### Priority 4 — Fix README.md Reference
Remove the broken reference to `blackburn_2001_ch4_summary.md` at line 169 of README.md. Update the Blackburn entry to reflect the actual split files structure.

### Priority 5 — Correct Token Counts in index.json
The systematic ~30-250 token undercount in index.json is minor but should be corrected when regenerating the index after Priority 3. The discrepancies are within 0.5% and not material for keyword-based selection.

### Priority 6 — Document Budget Semantics
The README.md does not explain how the 4000-token budget applies to multi-file injection. Add a note clarifying that the budget is cumulative across selected files (not per-file), and that chapter-level files are generally too large for the current budget — meaning only small files (scholarly reconstructions, front-matter sections under ~3000 tokens) are practically injectable within budget.

---

## Context Extension Recommendations

- **Topic**: literature-retrieve.sh implementation contract
- **Gap**: No documentation of what the script should do, expected interface, or selection algorithm
- **Recommendation**: Create `.claude/context/guides/literature-retrieval.md` documenting the script's expected behavior, token budget semantics, and keyword matching approach

---

## Appendix

### Files Confirmed Below 4000-Token Budget
Only these files are individually small enough for injection:
| File | Tokens |
|------|--------|
| burgess_1984.md | 2,151 |
| gabbay_1994_ch10.md | 2,278 |
| reynolds_1992.md | 2,072 |
| zakharyaschev_2001/sec00_introduction.md | 2,294 |
| gentzen_1935/sec00_synopsis-and-notation.md | 3,105 |
| gentzen_1935/sec02_natural-deduction.md | 3,651 |
| hughes_1996/p00_front-matter.md | 2,628 |
| church_1956/ch00_front-matter.md | 2,987 |

### Token Count Verification Method
Actual tokens calculated as `wc -w <file> * 1.3` (per index.json schema).

### Word Count Parity (Split vs Monolithic)
| Book | Monolithic words | Chapters_total words | Coverage |
|------|-----------------|---------------------|----------|
| mendelson_2016 | 224,764 | 223,432 | 99.4% |
| church_1956 | 205,816 | 204,412 | 99.3% |
| blackburn_2001 | 26,065 | 25,875 | 99.3% |

### zakharyaschev_2001/sec00_introduction.md Content
Exists, 1,765 words (2,294 tokens). Contains the handbook chapter opening: historical overview of modal logic from the 1970s to 2001, framing the survey relative to "Basic Modal Logic" chapter. Substantive introduction but not critical — available in per-book index.json for the zakharyaschev_2001 directory.
