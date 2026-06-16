# Research Report: Task #737

**Task**: 737 - Refactor cslib specs/literature/ to sources/ structure and remove blackburn_2001
**Started**: 2026-06-16T00:00:00Z
**Completed**: 2026-06-16T00:00:00Z
**Effort**: 1 hour
**Dependencies**: None
**Sources/Inputs**: Codebase exploration (cslib specs/literature/)
**Artifacts**: specs/737_refactor_cslib_literature_sources/reports/01_cslib-refactor-research.md
**Standards**: report-format.md, subagent-return.md

## Executive Summary

- The cslib `specs/literature/` directory has 76 index.json entries: 33 from blackburn_2001 (to be deleted), 43 to retain
- 11 loose markdown files need individual `sources/{id}/` directories; 6 subdirectories move to `sources/`; chagrov_1997.djvu co-locates with its content directory
- No Lean source files reference `specs/literature/` paths; no symlinks exist; the .gitignore has no literature-specific rules
- README.md has 2 blackburn_2001 references (lines 155 and 169) that need removal

## Context & Scope

This research covers the exact inventory required to execute the refactoring of `~/Projects/cslib/specs/literature/` to match a centralized Literature/ repository structure. The operation involves: adding a `sources/` subdirectory, relocating content into it, removing blackburn_2001 entirely, and updating index.json and README.md.

## Findings

### Codebase Patterns

#### Current Directory Structure

```
specs/literature/
├── index.json                  (76 entries)
├── README.md                   (273 lines)
├── chagrov_1997.djvu           (loose DJVU)
├── 11 loose markdown files     (paper-length sources)
│   ├── bentzen_2023.md
│   ├── burgess_1982_i.md
│   ├── burgess_1982_ii.md
│   ├── burgess_1984.md
│   ├── from_2022.md
│   ├── gabbay_1994_ch10.md
│   ├── henkin_1949.md
│   ├── johansson_1937.md
│   ├── post_1921.md
│   ├── reynolds_1992.md
│   └── trufas_2024.md
└── 7 subdirectories            (book-length sources)
    ├── blackburn_2001/         (TO BE DELETED — 33 files)
    ├── chagrov_1997/           (6 files + index.json)
    ├── church_1956/            (7 files + index.json)
    ├── gentzen_1935/           (5 files + index.json)
    ├── hughes_1996/            (4 files + index.json)
    ├── mendelson_2016/         (6 files + index.json)
    └── zakharyaschev_2001/     (4 files + index.json)
```

#### index.json Entry Counts

| Source | Entries | Action |
|--------|---------|--------|
| blackburn_2001 | 33 | Delete all |
| chagrov_1997 | 6 | Update paths to `sources/chagrov_1997/...` |
| church_1956 | 7 | Update paths to `sources/church_1956/...` |
| gentzen_1935 | 5 | Update paths to `sources/gentzen_1935/...` |
| hughes_1996 | 4 | Update paths to `sources/hughes_1996/...` |
| mendelson_2016 | 6 | Update paths to `sources/mendelson_2016/...` |
| zakharyaschev_2001 | 4 | Update paths to `sources/zakharyaschev_2001/...` |
| loose files (11) | 11 | Update paths to `sources/{id}/{id}.md` |
| **Total retained** | **43** | |

#### blackburn_2001 — All 33 index.json Entries

```
blackburn_2001/ch00_preface.md
blackburn_2001/ch01_relational-structures.md
blackburn_2001/ch01_models-and-frames.md
blackburn_2001/ch01_general-frames.md
blackburn_2001/ch02_invariance-results.md
blackburn_2001/ch02_bisimulations.md
blackburn_2001/ch02_standard-translation.md
blackburn_2001/ch02_characterization.md
blackburn_2001/ch02_simulation-safety.md
blackburn_2001/ch03_frame-definability.md
blackburn_2001/ch03_definable-properties.md
blackburn_2001/ch03_sahlqvist-formulas.md
blackburn_2001/ch03_more-sahlqvist.md
blackburn_2001/ch03_advanced-frame-theory.md
blackburn_2001/ch04_preliminaries-canonical.md
blackburn_2001/ch04_applications.md
blackburn_2001/ch04_transforming-canonical.md
blackburn_2001/ch04_rules-finitary-i.md
blackburn_2001/ch04_finitary-ii-summary.md
blackburn_2001/ch05_logic-as-algebra.md
blackburn_2001/ch05_jonsson-tarski.md
blackburn_2001/ch05_duality-theory.md
blackburn_2001/ch05_general-frames.md
blackburn_2001/ch05_persistence-summary.md
blackburn_2001/ch06_satisfiability-decidability.md
blackburn_2001/ch06_quasi-models-tiling.md
blackburn_2001/ch06_np-pspace.md
blackburn_2001/ch06_exptime-summary.md
blackburn_2001/ch07_logical-modalities.md
blackburn_2001/ch07_since-until-hybrid.md
blackburn_2001/ch07_guarded-fragment.md
blackburn_2001/ch07_multi-dimensional.md
blackburn_2001/ch07_lindstrom-summary.md
```

#### README.md blackburn_2001 References

Two lines in `/home/benjamin/Projects/cslib/specs/literature/README.md` reference blackburn_2001:

- **Line 155**: `Book-length files are split into chapter subdirectories (e.g., \`blackburn_2001/ch01_basic-concepts.md\`).`
  — Example in a general convention note; can update example to another book (e.g., `church_1956/ch01_propositional-calculus.md`) or remove the example.

- **Line 169**: Full entry for Blackburn, de Rijke & Venema 2001 under "Modal Logic (Foundations shared with Propositional)" section (lines 168-171).
  — Entire bullet block should be removed.

#### Symlinks

No symlinks exist within `specs/literature/`.

#### References from Outside specs/literature/

No Lean source files (`.lean`) reference paths inside `specs/literature/`. References found in `specs/` task reports and README files are historical documentation only — they describe old paths but are not functional dependencies that need updating.

The `.gitignore` at the cslib root excludes `.lake`, `docs/doc-data`, `.DS_Store`, and `.claude` — no special rules for literature files.

### Recommendations

#### Target Structure After Refactor

```
specs/literature/
├── index.json                  (43 entries, paths prefixed with sources/)
├── README.md                   (updated: remove blackburn refs, update examples)
└── sources/
    ├── chagrov_1997/
    │   ├── chagrov_1997.djvu   (moved from parent)
    │   ├── index.json
    │   ├── p00_front-matter.md
    │   ├── p01_introduction.md
    │   ├── p02_kripke-semantics.md
    │   ├── p03_adequate-semantics.md
    │   ├── p04_properties-of-logics.md
    │   └── p05_algorithmic-problems.md
    ├── church_1956/
    │   ├── index.json
    │   ├── ch00_front-matter.md
    │   ├── ch00b_introduction.md
    │   ├── ch01_propositional-calculus.md
    │   ├── ch02_propositional-calculus-continued.md
    │   ├── ch03_functional-calculi-first-order.md
    │   ├── ch04_pure-functional-calculus.md
    │   └── ch05_functional-calculi-second-order.md
    ├── gentzen_1935/
    │   ├── index.json
    │   ├── sec00_synopsis-and-notation.md
    │   ├── sec02_natural-deduction.md
    │   ├── sec03_lj-lk-hauptsatz.md
    │   ├── sec04_applications.md
    │   └── sec05_equivalence.md
    ├── hughes_1996/
    │   ├── index.json
    │   ├── p00_front-matter.md
    │   ├── p01_basic-modal-propositional-logic.md
    │   ├── p02_normal-modal-systems.md
    │   └── p03_modal-predicate-logic.md
    ├── mendelson_2016/
    │   ├── ch00_front-matter.md
    │   ├── ch01_propositional-calculus.md
    │   ├── ch02_first-order-logic.md
    │   ├── ch03_formal-number-theory.md
    │   ├── ch04_axiomatic-set-theory.md
    │   ├── ch05_computability.md
    │   └── index.json
    ├── zakharyaschev_2001/
    │   ├── index.json
    │   ├── sec00_introduction.md
    │   ├── sec01_unimodal-logics.md
    │   ├── sec02_polymodal-logics.md
    │   └── sec03_superintuitionistic-logics.md
    ├── bentzen_2023/
    │   └── bentzen_2023.md
    ├── burgess_1982_i/
    │   └── burgess_1982_i.md
    ├── burgess_1982_ii/
    │   └── burgess_1982_ii.md
    ├── burgess_1984/
    │   └── burgess_1984.md
    ├── from_2022/
    │   └── from_2022.md
    ├── gabbay_1994_ch10/
    │   └── gabbay_1994_ch10.md
    ├── henkin_1949/
    │   └── henkin_1949.md
    ├── johansson_1937/
    │   └── johansson_1937.md
    ├── post_1921/
    │   └── post_1921.md
    ├── reynolds_1992/
    │   └── reynolds_1992.md
    └── trufas_2024/
        └── trufas_2024.md
```

#### index.json Path Update Strategy

All 43 retained entries need the `path` field updated:
- Subdirectory entries: `chagrov_1997/p01_introduction.md` → `sources/chagrov_1997/p01_introduction.md`
- Loose file entries: `johansson_1937.md` → `sources/johansson_1937/johansson_1937.md`

This can be done with a Python script or `jq` transformation — a Python script is safer to avoid jq escaping issues.

## Decisions

- chagrov_1997.djvu should move into `sources/chagrov_1997/` alongside the text content (not left at top level)
- blackburn_2001's own `index.json` file (inside the directory) is deleted along with the directory
- No path updates needed in Lean source files (no references exist)
- Historical task report files referencing old paths do not need updating (they are archival documentation)

## Risks & Mitigations

| Risk | Mitigation |
|------|-----------|
| index.json becomes invalid after move | Use Python to rebuild entries, validate JSON after update |
| chagrov_1997.djvu co-location missed | Explicitly include in move plan |
| README.md line 155 example creates confusion after blackburn removal | Update example to reference church_1956 instead |
| blackburn_2001's internal index.json left behind | `rm -rf blackburn_2001/` removes it along with everything else |

## Appendix

### Commands Used

```bash
ls ~/Projects/cslib/specs/literature/
ls ~/Projects/cslib/specs/literature/blackburn_2001/
# (and all other subdirs)
python3 -c "..." ~/Projects/cslib/specs/literature/index.json  # entry counting/grouping
grep -n "blackburn" ~/Projects/cslib/specs/literature/README.md
grep -r "specs/literature" ~/Projects/cslib --include="*.lean"
find ~/Projects/cslib/specs/literature -type l
cat ~/Projects/cslib/.gitignore
```
