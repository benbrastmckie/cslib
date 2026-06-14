# Implementation Plan: Task #200

- **Task**: 200 - Fix Literature Directory Quality
- **Status**: [IMPLEMENTING]
- **Effort**: 1.5 hours
- **Dependencies**: None
- **Research Inputs**: specs/200_fix_literature_directory_quality/reports/01_literature-quality-audit.md
- **Artifacts**: plans/01_literature-quality-fix.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: general
- **Lean Intent**: false

## Overview

The `specs/literature/` directory contains 7 redundant monolithic .md files (1.25M+ tokens combined), a missing index.json entry, and a broken README.md reference. The critical blocker from the original plan -- the missing `literature-retrieve.sh` script -- has been resolved: the script now exists at `.claude/scripts/literature-retrieve.sh`, is executable, and produces correct `<literature-context>` output. This revised plan focuses on the remaining cleanup: fixing metadata inaccuracies, removing redundant files, and verifying the directory is fully consistent after changes.

### Research Integration

Key findings from the research report (01_literature-quality-audit.md):
- All 7 book splits are complete (blackburn_2001 has only 3/8 chapters due to source PDF limitation, not a split error)
- 7 monolithic .md files are confirmed redundant and safe to remove after split verification
- `zakharyaschev_2001/sec00_introduction.md` exists on disk but is missing from index.json
- README.md references non-existent `blackburn_2001_ch4_summary.md`
- All 3 scholarly reconstruction files are adequate -- no changes needed

Reports integrated: 01_literature-quality-audit.md

### Revision Notes

Revised from original plan due to external resolution of the `literature-retrieve.sh` blocker. Phase 3 (Create literature-retrieve.sh) is now marked [COMPLETED]. Effort estimate reduced from 3 hours to 1.5 hours. Phase 5 (end-to-end test) simplified to focus on post-cleanup verification only, since the script is already confirmed functional.

### Prior Plan Reference

Original plan created during /orchestrate 200 session.

### Roadmap Alignment

No ROADMAP.md consultation needed for this task.

## Goals & Non-Goals

**Goals**:
- Remove 7 redundant monolithic .md files to reduce disk waste by ~1.25M tokens
- Add missing `zakharyaschev_2001/sec00_introduction.md` entry to index.json
- Fix broken README.md reference to non-existent `blackburn_2001_ch4_summary.md`
- Verify end-to-end consistency after cleanup

**Non-Goals**:
- Acquiring missing blackburn_2001 chapters 3-7 (source limitation, not actionable)
- Rewriting or improving scholarly reconstruction file content (already adequate per research)
- Changing the TOKEN_BUDGET or MAX_FILES constants (design decision outside this task's scope)
- Updating per-book index.json files within subdirectories (only the master index.json matters for retrieval)
- Correcting minor token count discrepancies in index.json (<0.5% error, immaterial)
- Creating or modifying literature-retrieve.sh (already functional)

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Removing monolithic files loses content not in splits | H | L | Research confirmed 99.3-99.4% word count parity; verify before deletion |
| README.md changes break existing documentation links | L | L | Only fixing one broken reference; no structural changes |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1, 2 | -- |
| 2 | 4 | 2 |
| 3 | 5 | 1, 4 |

Phases within the same wave can execute in parallel. Phase 3 is already [COMPLETED] and does not appear in the wave table.

---

### Phase 1: Fix index.json and README.md [COMPLETED]

**Goal**: Correct metadata inaccuracies in index.json and README.md before any file operations.

**Tasks**:
- [x] Add missing entry for `zakharyaschev_2001/sec00_introduction.md` to `specs/literature/index.json` with id `zakharyaschev_2001_sec00`, path `zakharyaschev_2001/sec00_introduction.md`, token_count 2294, and keywords `["advanced modal logic", "survey", "historical overview", "unimodal", "polymodal", "superintuitionistic"]` *(completed)*
- [x] Fix README.md line 169: replace `blackburn_2001_ch4_summary.md` reference with accurate description of the actual split files (`blackburn_2001/ch00_preface.md`, `ch01_basic-concepts.md`, `ch02_models-partial.md`) *(completed)*
- [x] Update README.md book entries to reference split directories instead of monolithic files (chagrov_1997, church_1956, gentzen_1935, hughes_1996, mendelson_2016, zakharyaschev_2001) *(completed)*
- [x] Verify the updated index.json is valid JSON with `jq . specs/literature/index.json` *(completed)*

**Timing**: 30 minutes

**Depends on**: none

**Files to modify**:
- `specs/literature/index.json` - Add missing zakharyaschev sec00 entry
- `specs/literature/README.md` - Fix broken blackburn reference, update book entries

**Verification**:
- `jq '.entries | length' specs/literature/index.json` returns 46 (was 45)
- `jq '.entries[] | select(.id == "zakharyaschev_2001_sec00") | .path' specs/literature/index.json` returns the correct path
- `grep -c "blackburn_2001_ch4_summary" specs/literature/README.md` returns 0

---

### Phase 2: Remove redundant monolithic files [NOT STARTED]

**Goal**: Delete 7 verified-redundant monolithic .md files to eliminate ~1.25M tokens of duplicate content.

**Tasks**:
- [ ] Final verification: for each book with splits (chagrov_1997, church_1956, mendelson_2016, hughes_1996, gentzen_1935, zakharyaschev_2001, blackburn_2001), confirm the split directory exists and contains the expected number of files
- [ ] Remove `specs/literature/chagrov_1997.md` (329k tokens, 6 split files cover content)
- [ ] Remove `specs/literature/church_1956.md` (268k tokens, 7 split files cover content)
- [ ] Remove `specs/literature/mendelson_2016.md` (292k tokens, 6 split files cover content)
- [ ] Remove `specs/literature/hughes_1996.md` (208k tokens, 4 split files cover content)
- [ ] Remove `specs/literature/zakharyaschev_2001.md` (110k tokens, 4 split files cover content)
- [ ] Remove `specs/literature/blackburn_2001.md` (34k tokens, 3 split files cover same pages 1-69)
- [ ] Remove `specs/literature/gentzen_1935.md` (28k tokens, 5 split files cover content)
- [ ] Verify no index.json entries reference the removed files (they should not -- monolithic files were not indexed)

**Timing**: 20 minutes

**Depends on**: none

**Files to modify**:
- `specs/literature/chagrov_1997.md` - Delete
- `specs/literature/church_1956.md` - Delete
- `specs/literature/mendelson_2016.md` - Delete
- `specs/literature/hughes_1996.md` - Delete
- `specs/literature/zakharyaschev_2001.md` - Delete
- `specs/literature/blackburn_2001.md` - Delete
- `specs/literature/gentzen_1935.md` - Delete

**Verification**:
- `ls specs/literature/*.md | wc -l` returns 11 (down from 18; 11 standalone papers/reconstructions remain)
- Each split directory still contains expected file count: `ls specs/literature/chagrov_1997/ | wc -l` etc.
- `jq '.entries[].path' specs/literature/index.json | grep -v "/" | sort` shows no references to removed files

---

### Phase 3: Create literature-retrieve.sh [COMPLETED]

**Goal**: Implement the missing retrieval script that makes `--lit` functional.

**Tasks**:
- [x] Create `.claude/scripts/literature-retrieve.sh`
- [x] Make the script executable
- [x] Verify script produces `<literature-context>` output for relevant queries

**Timing**: 1 hour

**Depends on**: none

**Completed**: 2026-06-14

**Notes**: Script was created and verified externally. Tested with `"modal logic Kripke completeness" "cslib"` and confirmed proper `<literature-context>` output. No changes needed.

---

### Phase 4: Verify monolithic removal completeness [NOT STARTED]

**Goal**: Confirm that removing monolithic files did not break any references or lose content, and that all split directories are intact.

**Tasks**:
- [ ] Run `grep -rn "chagrov_1997\.md\|church_1956\.md\|mendelson_2016\.md\|hughes_1996\.md\|zakharyaschev_2001\.md\|blackburn_2001\.md\|gentzen_1935\.md" specs/literature/` to confirm no internal references to removed files remain
- [ ] Verify each per-book index.json within subdirectories (e.g., `specs/literature/blackburn_2001/index.json`) still has valid file references
- [ ] Confirm no `index.json` entries in the master index reference removed monolithic files
- [ ] Verify README.md no longer references any monolithic book files by their original filenames

**Timing**: 15 minutes

**Depends on**: 2

**Files to modify**:
- None (verification only)

**Verification**:
- All grep searches return 0 results for removed filenames in specs/literature/
- `jq -e . specs/literature/index.json` succeeds (valid JSON)
- No broken file references in README.md

---

### Phase 5: Post-cleanup integration test [NOT STARTED]

**Goal**: Verify that the `literature-retrieve.sh` script continues to work correctly after index.json updates and monolithic file removal, and that the `--lit` pipeline is fully functional.

**Tasks**:
- [ ] Test with CSLib-relevant description: `bash .claude/scripts/literature-retrieve.sh "Kripke semantics canonical model completeness proof modal logic" "cslib"` and verify output contains relevant entries (should match chagrov, blackburn, hughes entries)
- [ ] Test with temporal logic description: `bash .claude/scripts/literature-retrieve.sh "temporal logic Until Since tense logic linear orders" "cslib"` and verify burgess/gabbay/reynolds entries are selected
- [ ] Verify that the newly indexed `zakharyaschev_2001_sec00` entry appears in results for relevant queries: `bash .claude/scripts/literature-retrieve.sh "advanced modal logic survey unimodal polymodal" "cslib"`
- [ ] Verify the output wraps content in `<literature-context>...</literature-context>` tags
- [ ] Verify that no removed monolithic files appear in any output paths

**Timing**: 15 minutes

**Depends on**: 1, 4

**Files to modify**:
- None (testing only)

**Verification**:
- All test invocations produce non-empty `<literature-context>` output for relevant queries
- The zakharyaschev_2001_sec00 entry is reachable via keyword matching
- No references to removed monolithic files in output
- Token budget is respected (output file count stays within MAX_FILES=10)

---

## Testing & Validation

- [ ] `jq -e . specs/literature/index.json` validates JSON structure
- [ ] `jq '.entries | length' specs/literature/index.json` returns 46
- [ ] All 7 monolithic .md files are removed (ls shows 11 top-level .md files)
- [ ] All 7 split directories remain intact with correct file counts
- [ ] `literature-retrieve.sh` is executable and at correct path (pre-existing)
- [ ] Script produces `<literature-context>` output for relevant modal logic queries
- [ ] Script produces empty output for completely unrelated queries
- [ ] README.md contains no broken file references
- [ ] No references to removed monolithic files exist in specs/literature/

## Artifacts & Outputs

- `specs/200_fix_literature_directory_quality/plans/01_literature-quality-fix.md` (this plan)
- `specs/literature/index.json` (updated with new entry)
- `specs/literature/README.md` (fixed references)
- 7 deleted monolithic files (chagrov_1997.md, church_1956.md, mendelson_2016.md, hughes_1996.md, zakharyaschev_2001.md, blackburn_2001.md, gentzen_1935.md)

## Rollback/Contingency

- Monolithic files can be recovered from git history if splits are found incomplete after removal
- index.json changes are additive (only adding one entry) and reversible via git
- README.md changes are documentation-only and do not affect functionality
