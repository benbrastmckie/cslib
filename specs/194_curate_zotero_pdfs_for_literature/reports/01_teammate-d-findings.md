# Teammate D — Horizons Research Findings
# Task 194: Curate Zotero PDFs for Literature

**Date**: 2026-06-14
**Angle**: Long-term alignment and strategic direction
**Teammate**: D (Horizons)

---

## Key Findings

### 1. The literature/ Directory Has a Token Budget Problem

The current `specs/literature/` directory contains 13 `.md` files totaling **5.3 MB** of content. The `--lit` injection system is capped at `TOKEN_BUDGET=4000 tokens` and `MAX_FILES=10` (from `CLAUDE.md` and referenced in all three skill definitions: skill-researcher, skill-planner, skill-implementer).

4,000 tokens ≈ 16,000 characters. The smallest file (`README.md`, 11 KB) already exceeds this budget. **The existing literature files are full-book markdown conversions**, not curated excerpts. Under the current budget, only a fragment of one or two files can be injected per `--lit` invocation.

**Implication**: The curation task should not simply dump more PDFs as large markdown conversions. The highest strategic value comes from creating **topic-scoped excerpt files** (2,000–4,000 tokens each) that fit within the injection budget for specific tasks.

### 2. The Project Has a Two-Tier Literature Problem

Two distinct literatures are currently underrepresented:

**Tier A — Temporal/Bimodal logic (active tasks 36, 37, 39, 40, 180, 181):**
The Lean source files cite `Burgess 1982`, `Burgess 1984`, `GHR94` (Gabbay/Hodkinson/Reynolds 1994), and `Goldblatt 1992` in **dozens of theorem docstrings**, but none of these are in `specs/literature/`. These references are foundational to the completeness proofs in Wave 2/3 tasks. The Zotero library has all three Burgess papers and the GHR94 volume as local PDFs.

**Tier B — Intuitionistic modal/temporal logic (active tasks 179, 180, 181):**
Tasks 179 (modal primitive diamond) and 180 (temporal primitive allFuture/allPast) cite `Fischer Servi 1984`, `Simpson 1994`, and `Boudou et al. 2017` as motivating references for making operators primitive (enabling intuitionistic semantics). These papers are **not in Zotero** — they would need to be downloaded separately. The Zotero library does have Thomason 1984, Reynolds 1992, Xu 1988, and Bellissima 1995 which are relevant to the bimodal axiomatic framework.

### 3. Task 192 Already Consumes the Existing Literature

Task 192 ("Research verify literature refs pr 188") is `[PLANNED]` and its description explicitly states it "draws on sources in `specs/literature/`." The current literature is scoped to **propositional logic** (Johansson, Church, Gentzen, Henkin, etc.) and task 192 is consuming exactly that. Task 194 should be understood as **expanding** the literature coverage into temporal, bimodal, and modal domains — not re-doing what's already there.

The two tasks are **complementary, not overlapping**:
- Task 192: Use existing literature to verify PR 188 (propositional scope, literature already present)
- Task 194: Add literature for upcoming Wave 2/3 tasks (temporal/bimodal/modal scope, literature missing)

### 4. Zotero Has the Critical Temporal/Bimodal Papers with Local PDFs

The Zotero library (`~/texmf/bibtex/bib/Zotero.bib`, 878 entries) contains verified local PDFs for all the Tier A papers:

| BibKey | Title | File Status |
|--------|-------|-------------|
| `Burgess1982` | Axioms for Tense Logic I (Since/Until) | **PDF exists** at `/home/benjamin/Documents/Zotero/storage/5HK4WV9T/` |
| `Burgess1982a` | Axioms for Tense Logic II (Time Periods) | **PDF exists** at `/home/benjamin/Documents/Zotero/storage/C9CHHCD2/` |
| `Burgess1984` | Basic Tense Logic (Handbook Ch.) | **PDF exists** at `/home/benjamin/Documents/Zotero/storage/6VFNSSIE/` |
| `Gabbay1994` | Temporal Logic Vol. 1 (GHR94) | **PDF exists** at `/home/benjamin/Documents/Zotero/storage/PKDIAG7M/` |
| `Gabbay2023a` | Temporal Logic Vol. 2 (GHR2) | **PDF exists** at `/home/benjamin/Documents/Zotero/storage/3TUIG2ZY/` |
| `Reynolds1992` | Axiomatization for Until/Since over Reals | **PDF exists** at `/home/benjamin/Documents/Zotero/storage/2EFF2PBK/` |
| `Xu1988` | On some U,S-tense logics | **PDF exists** at `/home/benjamin/Documents/Zotero/storage/27MQRXIX/` |
| `Thomason1984` | Combinations of Tense and Modality | **PDF exists** at `/home/benjamin/Documents/Zotero/storage/978ZVM9R/` |
| `Bellissima1995` | Distinguishable Model Theorem for US-Tense | **PDF exists** at `/home/benjamin/Documents/Zotero/storage/UFHYB75M/` |

Additionally, `Goldblatt2006` (Mathematical Modal Logic: A View of Its Evolution) has a PDF and is cited in `LinearityDerivedFacts.lean` and `ConservativeExtension/` files.

### 5. The Curation Should Produce Task-Scoped Summary Files, Not Full Conversions

The existing pattern (full-book markdown conversion) is appropriate only for short papers. For books like GHR94 (700+ pages), **chapter-level summaries** are the right artifact. The `--lit` budget of 4,000 tokens can accommodate a focused 3–4 page summary of a single chapter.

Proposed file naming pattern: `{author}_{year}_{scope}.md` where scope indicates the relevant extract, e.g.:
- `burgess_1982_chronicle-construction.md` — Section 2 definitions (chronicle, r-relation, C4/C5 conditions)
- `gabbay_1994_ch10-separation.md` — Chapter 10 separation theorem (GHR94 10.2)
- `burgess_1984_dense-completeness.md` — The quasimodel construction for dense linear orders

### 6. A Prioritized Curation Order Based on Dependency Waves

The task dependency structure from `TODO.md` reveals which literature is most urgent:

**Wave 1 (unblocked now)**:
- Task 179 (modal primitive diamond) is in `[PLANNING]` — needs Fischer Servi 1984, Simpson 1994
- Task 180 (temporal primitive G/H) is `[NOT STARTED]` — needs Boudou 2017
- These require papers not in Zotero; PDFs need to be sourced

**Wave 2 (blocked on upstream)**:
- Tasks 36, 39 (discrete completeness) — need GHR94 Ch. 10, Burgess 1982 II
- These are blocked upstream but literature prep would unblock agent dispatches once unblocked

**Wave 3 (future)**:
- Task 41 (abstract completeness) — needs Burgess 1982 I+II, Reynolds 1992

**Immediate priority**: GHR94 Chapter 10 (Section 10.2 for separation, Section 10.3 for integer model) and Burgess 1982 II are the highest-value curation targets because tasks 36/39 are blocked only on upstream sorry elimination — once upstream is fixed, these tasks will become immediately active.

### 7. Integration with references.bib is the Highest-Leverage Action

Currently `references.bib` does **not** contain entries for Burgess 1982 I/II, Burgess 1984, GHR94, Goldblatt 1992, Reynolds 1992, Xu 1988, or Thomason 1984. The Lean source files cite these as bare prose labels ("Burgess 1982", "GHR94") rather than proper `[BibKey]` format. The `CONTRIBUTING.md` convention requires BibKey format for doc-gen cross-linking.

A well-curated literature task should:
1. Convert key PDFs to markdown summaries (for `--lit` injection)
2. Add corresponding BibTeX entries to `references.bib` (for doc-gen)
3. Update Lean file docstrings from bare labels to `[BibKey]` format

This is the same three-step pattern that task 192 is executing for the propositional layer, just applied to the temporal/bimodal layer.

### 8. Topic-Scoped literature/ Subdirectories Could Prevent Budget Exhaustion

As the literature grows (propositional, modal, temporal, bimodal), a flat `specs/literature/` directory will exhaust the MAX_FILES=10 budget rapidly. A forward-looking convention would use topic subdirectories:

```
specs/literature/
├── propositional/     (existing files, scoped)
├── modal/             (Fischer Servi, Simpson, Chagrov Ch. 2)
├── temporal/          (Burgess 1982 I/II, GHR94 Ch. 10, Reynolds)
└── bimodal/           (Burgess 1984, GHR94 Ch. 10, Xu 1988)
```

This would require a `literature-retrieve.sh` change to select by subdirectory (or the script already selects files matching task keywords). Whether the current script does keyword-based selection is worth verifying before restructuring.

---

## Recommended Approach

### Phase 1: Curate Temporal/Bimodal Literature (High Priority, PDFs Available)

Convert the following Zotero PDFs to focused markdown summaries scoped to sections directly cited in the Lean source:

1. **Burgess 1982 II** (`burgess_1982_chronicle-construction.md`) — Section 2: chronicle definitions, r-relation, C4/C5 conditions, Claim 2.11 (truth lemma). ~3,000 tokens. Cited in 8+ Lean files.

2. **Burgess 1984** (`burgess_1984_dense-completeness.md`) — Sections on quasimodel construction for BX. ~2,500 tokens. Cited in dense completeness pipeline.

3. **GHR94 Chapter 10** (`gabbay_1994_ch10-separation.md`) — Sections 10.2 (separation theorem, Lemmas 10.2.1–10.2.9) and 10.3 (Q-lemma for Z). ~4,000 tokens. Cited in 12+ Lean files including entire `Separation/` directory.

4. **Burgess 1982 I** (`burgess_1982_since-until.md`) — The US axiom system definition for reference. ~1,500 tokens.

5. **Reynolds 1992** (`reynolds_1992_reals-axioms.md`) — The axiomatization for Until/Since over reals. ~2,000 tokens.

### Phase 2: Add BibTeX Entries to references.bib

For each curated paper, add a properly formatted BibTeX entry to `references.bib` using the Zotero BibTeX data. This allows Lean docstrings to be updated from bare prose labels to proper `[BibKey]` format.

Entries needed: `Burgess1982`, `Burgess1982a`, `Burgess1984`, `Gabbay1994`, `Reynolds1992`, `Xu1988`, `Thomason1984`.

### Phase 3: Source Intuitionistic Modal/Temporal Papers (Medium Priority)

For tasks 179/180 (Wave 1), the key papers are not in Zotero:
- Fischer Servi 1984: Available via ResearchGate or journal archive (Rendiconti del Seminario Matematico)
- Simpson 1994: Available from University of Edinburgh thesis repository
- Boudou et al. 2017: Available on arXiv (CSL 2017 proceedings)

These should be downloaded, converted to markdown summaries, and added to `specs/literature/modal/` and `specs/literature/temporal/` respectively.

### Scope Boundary: Do Not Replace Existing Files

The existing `specs/literature/*.md` files (propositional layer, book-length conversions) serve task 192 and should remain. The curation task adds **new** scoped summary files for temporal/bimodal coverage. The design question of subdirectories vs. flat files is secondary to getting the content in place.

---

## Evidence/Examples

### Example: Burgess 1982 II Cited in 8+ Lean Files

```lean
-- From Cslib/Logics/Bimodal/Metalogic/BXCanonical/Chronicle/ChronicleTypes.lean:
# Chronicle Types for Burgess 1982 Construction
# Burgess 1982: "Axioms for tense logic II: Time periods"

-- From Cslib/Logics/Temporal/Metalogic/Chronicle/TruthLemma.lean:
-- Burgess 1982: Section 2, Claim 2.11
-- This is Claim 2.11 of Burgess 1982, adapted to the temporal logic setting.
```

If `--lit` is used with `/implement 39` (discrete temporal completeness), a curated `burgess_1982_chronicle-construction.md` file would inject exactly the section definitions the agent needs to verify truth-lemma cases.

### Example: GHR94 Cited in 12+ Lean Files

```lean
-- From Cslib/Logics/Bimodal/Metalogic/Separation/Defs.lean:
-- Core definitions for the separation theorem over integer time (GHR94 Chapter 10.2).
-- GHR94, Chapter 10, Section 10.2 (pp. 569-592)

-- From Cslib/Logics/Bimodal/Metalogic/Separation/SeparationThm.lean:
-- GHR94, Lemmas 10.2.4-10.2.8, Theorem 10.2.9
```

A `gabbay_1994_ch10-separation.md` excerpt covering these specific lemmas and theorem statements would let agents implementing task 36 (discrete bimodal completeness) verify their proof structure against the source.

### Example: Token Budget Mismatch

The `chagrov_1997.md` file is 1.38 MB. The `--lit` budget is 4,000 tokens ≈ 16,000 characters. The file cannot be injected. If `literature-retrieve.sh` truncates to fit, only the first ~16KB of the 1.38MB file is used — likely just the book's front matter and table of contents, not the relevant chapter content.

This confirms that **curated excerpt files** (scoped to specific sections) are the right artifact format for `--lit` injection to actually work.

### Task Dependency Alignment

```
Task 192 [PLANNED] → draws on literature/ (propositional) → ✓ already populated
Task 179 [PLANNING] → needs modal lit (Fischer Servi, Simpson) → missing
Task 180 [NOT STARTED] → needs temporal lit (Boudou 2017) → missing
Task 36 [BLOCKED] → unblocks to need (Burgess 1982 II, GHR94 Ch.10) → missing
Task 39 [NOT STARTED] → needs (GHR94 Ch.10, Burgess 1982 II) → missing
Task 40 [BLOCKED] → needs (Reynolds 1992, dense/continuous analysis) → missing
```

---

## Confidence Level

**High** on findings 1–7 (directly verified from codebase, Zotero library, and file system).

**Medium** on finding 8 (subdirectory recommendation) — depends on how `literature-retrieve.sh` actually selects files; the script body was not found locally (may be generated from skill SKILL.md templates), so keyword-matching behavior is inferred from CLAUDE.md documentation.

**High** on recommended approach — the Zotero PDFs exist, the citation mapping to Lean files is verified, and the token budget constraint is measured directly.
