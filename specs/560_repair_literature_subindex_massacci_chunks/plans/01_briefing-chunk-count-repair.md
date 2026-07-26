# Implementation Plan: Repair per-document chunk-count under-reporting in literature-briefing.sh

- **Task**: 560 - Repair the per-repo literature sub-index (Massacci corpus reported as 1 chunk, holds 77)
- **Status**: [IMPLEMENTING]
- **Effort**: 1.5 hours
- **Dependencies**: None
- **Research Inputs**: `specs/560_repair_literature_subindex_massacci_chunks/reports/01_briefing-chunk-count-defect.md`
- **Artifacts**: `plans/01_briefing-chunk-count-repair.md`
- **Standards**:
  - `.claude/rules/artifact-formats.md`
  - `.claude/rules/state-management.md`
  - `.claude/rules/plan-format-enforcement.md`
  - `.claude/context/formats/plan-format.md`
- **Type**: meta

## Overview

`.claude/scripts/literature-briefing.sh` per-repo mode derives each document's displayed chunk
count by counting global-index child entries (`parent_doc == doc_id`) at lines 203-206, falling
back to a hardcoded `chunk_count=1` at line 224 when there are no children. 21 of the 34
sub-index documents have zero registered children and therefore display `1 chunk(s)` regardless
of how much material they actually hold — Massacci displays `1` while holding 77 chunks. This
plan adds two further fallback tiers, in strict precedence order, behind the existing
child-count path: the parent entry's own `chunk_count` field (Tier 2), then an on-disk
`chunk_*.md` glob (Tier 3). Definition of done: all 34 sub-index documents display their true
chunk count except the two documents whose chunk files use a non-`chunk_*` naming scheme, with
zero change to any currently-correct count and zero change to any token total.

The scope figures in this plan supersede the task description's. The description's "19 of 34
documents" conflates two classes with different remedies, and its proposed fix precedence
(prefer `chunk_count` field over child count) is inverted and would cause a regression. Both
corrections come from the research report, which passed adversarial verification; where the
description and the report disagree, the report governs.

### Research Integration

| Report | Integrated in plan version | Date |
|---|---|---|
| `reports/01_briefing-chunk-count-defect.md` | 1 | 2026-07-26 |

Report findings carried into this plan: mechanism and line numbers (Finding A), Massacci data
shape (Finding B), the 4-class 34-document taxonomy (Finding C), the `chagrovzakharyaschev`
regression counterexample (Finding E), the `chunks.json` prohibition (Recommendation 2), and
the correction that the `<!-- lit-coverage -->` marker is not part of this defect (Finding D).

### Source-to-Implementation Mapping

| Source | Location | Implementation consequence |
|---|---|---|
| Report Finding A | report lines 32-56 | Edit target is `literature-briefing.sh:203-225`, the per-repo chunk-count block, and nothing else |
| Report Finding C, class (1) | report line 96 | Phase 1 repairs exactly 8 documents via the parent `chunk_count` field |
| Report Finding C, class (4) | report line 99 | Phase 2 repairs 11 of 13 documents via an on-disk `chunk_*.md` glob |
| Report Finding E / Risk 1 | report lines 160-173, 238-245 | Precedence MUST be child-count-first; `chagrovzakharyaschev_1997_modallogic` is the regression sentinel |
| Report Recommendation 2 | report lines 215-229 | `chunks.json` array length is forbidden as a count source anywhere in this change |
| Report Finding D / Recommendation 3 | report lines 129-151, 230-231 | The `<!-- lit-coverage -->` marker is already correct; it is a no-change assertion, not a fix target |
| Report Recommendation 4 | report lines 232-234 | 17 orphaned `parent_doc` values are out of scope; note only |

### Preserved Assets

The following behavior is already correct and MUST NOT regress. There is no prior implementation
work on this task; the preserved assets are the script's existing correct outputs.

| Component | File | Status | Verified |
|---|---|---|---|
| Child-count path for 12 documents with real children (class 3) | `.claude/scripts/literature-briefing.sh:203-218` | [CORRECT TODAY] | 2026-07-26 |
| `chagrovzakharyaschev_1997_modallogic` reporting 6 chunks despite a stale `chunk_count: 997` field (class 2) | same | [CORRECT TODAY — REGRESSION SENTINEL] | 2026-07-26 |
| Token totals for all 34 documents (`~N tokens`) | `.claude/scripts/literature-briefing.sh:208-225` | [CORRECT TODAY] | 2026-07-26 |
| `<!-- lit-coverage mode=repo seg_count=34 sparse=false threshold=3 -->` marker | `.claude/scripts/literature-briefing.sh:290-292` | [CORRECT TODAY] | 2026-07-26 |
| Global-corpus mode (`--global`) | `.claude/scripts/literature-briefing.sh:294-393` | [UNAFFECTED] | 2026-07-26 |

Every phase's verification includes the `chagrovzakharyaschev_1997_modallogic == 6` sentinel
check and a full-34 token-column no-change check.

## Postmortem Constraints

Binding rules for all implementation dispatches on this task.

**Do NOT**:
- Do NOT write to `~/Projects/Literature/index.json`, `~/Projects/Literature/.literature.db`, or
  any file under `~/Projects/Literature/`. That tree is the user's SHARED global corpus, lives
  outside this repository, and is consumed by every project on this machine. It is READ-ONLY for
  the entire duration of this task. A phase that writes there is a failed phase, not a shortcut.
- Do NOT implement the precedence the task description literally proposes ("prefer `chunk_count`
  field over the derived child count"). It is inverted. It regresses
  `chagrovzakharyaschev_1997_modallogic` from a correct 6 to a wrong 997, because that entry
  carries a stale pre-consolidation `chunk_count: 997` alongside 6 real registered children.
  Child count wins whenever children exist; `chunk_count` is consulted only at zero children.
- Do NOT use `chunks.json` array length as a chunk-count source at any tier. For consolidated
  documents it holds the raw pre-consolidation count (`chagrovzakharyaschev` → 997 vs. a true 6;
  `church_1956` → 1025 vs. 7; `hughes_1996` → 581 vs. 4). It is not a safe universal source.
- Do NOT "fix" the `<!-- lit-coverage ... -->` marker. In repo mode its `seg_count` counts
  resolved DOCUMENTS (34), not chunks. It is already correct. The task description's claim that
  it "must reflect the corrected count" is wrong and was retracted by the research report.
- Do NOT touch the global-corpus (`--global`) code path, lines 294-393. It never reads
  `parent_doc` or `chunk_count` and is not affected by this defect.
- Do NOT expand `file_scope`. The only file this task modifies is
  `.claude/scripts/literature-briefing.sh`. No sibling script reproduces the defect
  (report Finding F).
- Do NOT attempt Report Recommendation 4 (the 17 orphaned `parent_doc` values in the global
  index). It is a corpus-data issue outside this repository and out of scope.

**MUST preserve**:
- The existing child-count path and its token-summing branch for the 12 class-3 documents.
- `chagrovzakharyaschev_1997_modallogic` at exactly 6 chunks after every phase.
- All 34 token totals, byte-identical before and after.
- The `<!-- lit-coverage mode=repo seg_count=34 sparse=false threshold=3 -->` marker line.
- Silent-exit behavior when the sub-index or global index is missing (script lines 8-13 contract).

**Design decisions are SETTLED** (do not re-open without a concrete counterexample):
- **Precedence is Tier 1 child count → Tier 2 parent `chunk_count` field → Tier 3 on-disk
  `chunk_*.md` glob → literal 1.** Rejected alternative: `chunk_count`-field-first, which
  regresses the class-2 document.
- **Tier 3 is in scope and is a separate phase.** Rejected alternative: shipping Tier 2 alone.
  The task's own verification bar names documents from both classes, and Tier 3 has been
  verified to recover exact, correct counts for 11 documents.
- **Tier 3 globs `chunk_*.md` only, not `sec*.md` or `p0*.md`.** Rejected alternative: a broader
  glob. This leaves 2 documents at `1`, documented as a known residual in Phase 3, rather than
  widening the glob on unverified evidence.
- **Tier 3 reuses the script's existing `doc_dir` resolution logic** (currently lines 227-246),
  hoisted above the chunk-count block. Rejected alternative: a second, duplicate path-resolution
  block, which would drift from the displayed `dir:` value.

## Goals & Non-Goals

**Goals**:
- Massacci displays 77 chunks in per-repo briefing output.
- All 8 class-1 documents display their parent `chunk_count` value.
- All 11 recoverable class-4 documents display their on-disk `chunk_*.md` count.
- Zero regression on the 13 documents that are already correct.
- The three-tier precedence and the 2 known residuals are documented in the script itself.

**Non-Goals**:
- Repairing `~/Projects/Literature/index.json` metadata (out of scope, read-only tree).
- The 17 orphaned `parent_doc` values (Report Recommendation 4).
- Any change to global-corpus mode or to the sparse-coverage marker.
- Recovering the 2 `venema_1993*` documents whose chunk files use `sec*.md` naming.

## Risks & Mitigations

- **Risk**: Implementing the description's literal precedence regresses `chagrovzakharyaschev`
  6 → 997. This is the single highest-value catch from research.
  **Mitigation**: Precedence is fixed in the Postmortem Constraints as SETTLED; every phase's
  verification asserts the sentinel value 6 explicitly, and the full-34 diff would surface it.
- **Risk**: Tier 3 runs `find` on a directory that does not exist (a sub-index doc whose
  `path` is stale), producing a shell error or a non-numeric count.
  **Mitigation**: Phase 2 requires `2>/dev/null`, a `[[ =~ ^[0-9]+$ ]]` numeric guard, and a
  default of 0 → falls through to the literal-1 tier. Same defensive shape the script already
  uses at lines 217 and 223.
- **Risk**: Hoisting the `doc_dir` resolution block changes the displayed `dir:` value.
  **Mitigation**: The hoist is a pure move of lines 227-246 with no edits to their content;
  the full-34 verification compares the `dir:` basename column, so any drift fails the diff.
- **Risk**: Tier 3 adds up to 34 filesystem `find` calls per briefing, slowing preflight.
  **Mitigation**: Tier 3 only executes when both prior tiers yield zero — at most 15 of 34
  documents today, and each is a single non-recursive `-maxdepth 1` glob. Phase 3 records the
  measured wall-clock before/after; if it exceeds 2x, note it rather than optimizing in-task.

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2 | 1 |
| 3 | 3 | 2 |

Fully sequential. Phase 2 edits the same code block Phase 1 edits, and Phase 3 verifies the
combined result, so there is no parallel opportunity in this plan. All three phases own the
same single file, `.claude/scripts/literature-briefing.sh` — no concurrent dispatch.

**Shared setup — capture the baseline before Phase 1 (run once, keep for all phases)**:

```bash
cd /home/benjamin/Projects/cslib
mkdir -p /tmp/lit560
bash .claude/scripts/literature-briefing.sh 2>/dev/null \
 | sed -n 's#^ *\([0-9]*\) chunk(s), ~\([0-9]*\) tokens . dir: .*/sources/\(.*\)$#\3\t\1\t\2#p' \
 | sort > /tmp/lit560/before.tsv
wc -l < /tmp/lit560/before.tsv    # expect exactly: 34
```

This emits one `docdir<TAB>chunk_count<TAB>token_count` row per document and is the extraction
used by every verification command below. It has been run against the current script and
produces 34 rows.

---

### Phase 1: Tier-2 fallback — use the parent entry's `chunk_count` field when child count is 0 [COMPLETED]

**Goal**: In `.claude/scripts/literature-briefing.sh`, insert a second fallback tier into the
`else` branch at lines 219-225 so that a document with zero registered children uses its parent
entry's own `chunk_count` field, when that field is present and greater than 0, instead of
falling straight to the hardcoded `1`. The child-count branch at lines 209-218 is not touched.

**Tasks**:
- Read `.claude/scripts/literature-briefing.sh` lines 195-250 to confirm the block is unchanged
  from the report's quotation (chunk-count derivation at 203-206, `chunk_count=1` at 224).
- In the `else` branch (the `chunk_count -eq 0` case), after the existing `total_tokens`
  resolution and its numeric guard, replace the bare `chunk_count=1` with a lookup of the parent
  entry's `chunk_count` field:
  - `jq -r --arg id "$doc_id" '.entries[] | select(.id == $id) | .chunk_count // 0' "$GLOBAL_INDEX" 2>/dev/null | head -1`
  - Apply the same `[[ "$x" =~ ^[0-9]+$ ]] || x=0` numeric guard the surrounding code uses —
    the field is `null` for 25 of 34 documents and `jq` renders that as the string `null`.
  - If the guarded value is greater than 0, use it as `chunk_count`; otherwise set `chunk_count=1`
    exactly as today.
- Leave `total_tokens` in this branch entirely alone. It already reads the parent `token_count`
  and is correct (Massacci's `~30656` is right today).
- Add a brief inline comment naming this as the Tier-2 fallback and stating why the field is not
  preferred over the child count (stale pre-consolidation values, e.g. 997 vs. a true 6).

**Timing**: ~30 minutes.

**Depends on**: none.

**Estimated output**: ~15 lines changed in one file.

**Done when**: exactly the 8 class-1 documents change from `1` to their parent `chunk_count`
value, no other row's chunk count changes, and no token value changes anywhere.

**Verification** (runnable; expects the shared-setup `before.tsv` to exist):

```bash
cd /home/benjamin/Projects/cslib

# 1. Primary target: Massacci must report 77.
bash .claude/scripts/literature-briefing.sh 2>/dev/null | grep -B1 'sources/massacci_2000'
# expect the chunk line to read: 77 chunk(s), ~30656 tokens | dir: .../sources/massacci_2000_single_step_tableaux_for_modal_logics

# 2. Regression sentinel: chagrovzakharyaschev MUST stay 6, not become 997.
bash .claude/scripts/literature-briefing.sh 2>/dev/null | grep 'sources/chagrovzakharyaschev_1997_modallogic'
# expect: 6 chunk(s), ~329042 tokens | dir: .../sources/chagrovzakharyaschev_1997_modallogic

# 3. Full-34 diff: exactly 8 rows may change, and only in the chunk-count column.
bash .claude/scripts/literature-briefing.sh 2>/dev/null \
 | sed -n 's#^ *\([0-9]*\) chunk(s), ~\([0-9]*\) tokens . dir: .*/sources/\(.*\)$#\3\t\1\t\2#p' \
 | sort > /tmp/lit560/after-p1.tsv
wc -l < /tmp/lit560/after-p1.tsv                      # expect: 34
diff <(cut -f1,3 /tmp/lit560/before.tsv) <(cut -f1,3 /tmp/lit560/after-p1.tsv) && echo "TOKENS UNCHANGED: OK"
diff /tmp/lit560/before.tsv /tmp/lit560/after-p1.tsv | grep -c '^>'   # expect: 8

# 4. The 8 changed rows must be exactly these, with exactly these values.
grep -E '^(alechinamendlerdepaivaritter_2001|arisakadasstrassburger_2015|biermandepaiva_2000|marinmoralesstrassburger_2021|massacci_2000|pacheco_2024|simpson_1994|wijesekera_1990)' /tmp/lit560/after-p1.tsv | cut -f1,2
# expect (order as sorted):
#   alechinamendlerdepaivaritter_2001_..._constructive_s4                     52
#   arisakadasstrassburger_2015_onnestedsequentsforconstructivemodallogics    40
#   biermandepaiva_2000_onanintuitionisticmodallogic                          53
#   marinmoralesstrassburger_2021_..._intuitionistic_modal                    51
#   massacci_2000_single_step_tableaux_for_modal_logics                       77
#   pacheco_2024_collapsingconstructiveandintuitionisticmodallogics           19
#   simpson_1994_intuitionisticmodallogic                                    206
#   wijesekera_1990_constructivemodallogicsi                                  38

# 5. Coverage marker unchanged.
bash .claude/scripts/literature-briefing.sh 2>/dev/null | grep 'lit-coverage'
# expect: <!-- lit-coverage mode=repo seg_count=34 sparse=false threshold=3 -->

# 6. Global mode still functions (smoke check, must not error).
bash .claude/scripts/literature-briefing.sh --global "modal tableaux" >/dev/null 2>&1 && echo "GLOBAL MODE OK"
```

Note on `pacheco_2024`: the correct expected value is **19**, the parent `chunk_count` field
value. The task description said 20 and the research report's verification section repeated 20
while itself recording the field as 19; 19 is the value this tier reads and is correct. The
off-by-one against the on-disk glob is pre-existing corpus metadata, not introduced here.

**Observed verification output (Phase 1, executed)**:
```
1. Massacci: 77 chunk(s), ~30656 tokens | dir: .../sources/massacci_2000_single_step_tableaux_for_modal_logics
2. Regression sentinel: 6 chunk(s), ~329042 tokens | dir: .../sources/chagrovzakharyaschev_1997_modallogic  (unchanged, PASS)
3. Full-34 diff: 34 rows; TOKENS UNCHANGED: OK; 8 rows changed
4. Exact 8 changed rows (all match expected):
   alechinamendlerdepaivaritter_2001_categorical_and_kripke_semantics_for_constructive_s4  52
   arisakadasstrassburger_2015_onnestedsequentsforconstructivemodallogics                  40
   biermandepaiva_2000_onanintuitionisticmodallogic                                        53
   marinmoralesstrassburger_2021_fully_labelled_proof_system_intuitionistic_modal           51
   massacci_2000_single_step_tableaux_for_modal_logics                                     77
   pacheco_2024_collapsingconstructiveandintuitionisticmodallogics                         19
   simpson_1994_intuitionisticmodallogic                                                  206
   wijesekera_1990_constructivemodallogicsi                                                38
5. Coverage marker: <!-- lit-coverage mode=repo seg_count=34 sparse=false threshold=3 --> (unchanged, PASS)
6. Global mode smoke check: GLOBAL MODE OK
```
All six verification steps PASS.

**Rollback/Contingency**: The change is confined to the `else` branch of one `if` block. Revert
with `git checkout HEAD -- .claude/scripts/literature-briefing.sh` (safe: the working tree
change is this phase's only edit to that file; if other uncommitted edits exist, snapshot first
via `bash .claude/scripts/git-snapshot.sh`). If the sentinel check at step 2 shows 997, the
precedence was implemented inverted — restore child-count-first before proceeding.

---

### Phase 2: Tier-3 fallback — count on-disk `chunk_*.md` files when both child count and `chunk_count` field are absent [NOT STARTED]

**Goal**: Add a third fallback tier that counts `chunk_*.md` files in the document's resolved
source directory when Tier 1 (child count) and Tier 2 (parent `chunk_count` field) both yield 0.
This requires hoisting the existing `doc_dir` resolution block (currently lines 227-246) to run
before the chunk-count block, so Tier 3 can reuse the exact directory the briefing displays.

**Tasks**:
- Move the `parent_path` / `doc_dir` resolution block (currently lines 227-246, from the
  `# Resolve directory path` comment through the closing `fi`) to sit immediately before the
  `# Find all chunk entries` comment at line 203. Move it verbatim — no edits to its contents.
  It depends only on `$doc_id`, `$GLOBAL_INDEX`, and `$LIT_DIR`, all of which are already bound
  at that point, so the hoist is safe.
- In the Tier-2 branch added by Phase 1, extend the `else` case (Tier-2 value is 0) with the
  disk glob before falling back to the literal 1:
  - `disk_chunks=$(find "$doc_dir" -maxdepth 1 -name 'chunk_*.md' 2>/dev/null | wc -l)`
  - Guard with `[[ "$disk_chunks" =~ ^[0-9]+$ ]] || disk_chunks=0` (defensive; matches the
    script's existing style at lines 217, 223).
  - If `disk_chunks` is greater than 0, use it; otherwise `chunk_count=1` unchanged.
- Use `-maxdepth 1` (non-recursive) and the literal `chunk_*.md` glob only. Do NOT broaden to
  `sec*.md`, `p0*.md`, or `*.md`.
- Do NOT read `chunks.json` at this or any tier.
- Add an inline comment naming this as the Tier-3 fallback and recording that `chunks.json` is
  deliberately not used because it holds raw pre-consolidation counts.

**Timing**: ~30 minutes.

**Depends on**: 1.

**Estimated output**: ~25 lines changed in one file (a ~20-line verbatim hoist plus ~8 new lines).

**Done when**: exactly 11 further documents change from `1` to their on-disk count, the 8
Phase-1 documents are unchanged from their Phase-1 values, no already-correct row changes, and
no token value changes.

**Verification** (runnable):

```bash
cd /home/benjamin/Projects/cslib

# 1. Regression sentinel, again — Tier 3 must not reach this document at all.
bash .claude/scripts/literature-briefing.sh 2>/dev/null | grep 'sources/chagrovzakharyaschev_1997_modallogic'
# expect: 6 chunk(s), ~329042 tokens | dir: .../sources/chagrovzakharyaschev_1997_modallogic

# 2. Massacci still 77 (Tier 2 must still win over Tier 3 here; its disk count is also 77,
#    so also confirm Tier 2 fired by checking pacheco stays at the field value 19, not the disk glob).
bash .claude/scripts/literature-briefing.sh 2>/dev/null | grep -E 'sources/(massacci_2000|pacheco_2024)'
# expect: 77 chunk(s) ... massacci ... ; 19 chunk(s) ... pacheco ...

# 3. Full-34 diff vs. Phase 1: exactly 11 rows change, tokens unchanged.
bash .claude/scripts/literature-briefing.sh 2>/dev/null \
 | sed -n 's#^ *\([0-9]*\) chunk(s), ~\([0-9]*\) tokens . dir: .*/sources/\(.*\)$#\3\t\1\t\2#p' \
 | sort > /tmp/lit560/after-p2.tsv
wc -l < /tmp/lit560/after-p2.tsv                       # expect: 34
diff <(cut -f1,3 /tmp/lit560/before.tsv) <(cut -f1,3 /tmp/lit560/after-p2.tsv) && echo "TOKENS UNCHANGED: OK"
diff /tmp/lit560/after-p1.tsv /tmp/lit560/after-p2.tsv | grep -c '^>'   # expect: 11

# 4. The 11 changed rows must be exactly these values.
grep -E '^(bentzen_2023|burgess_1982_i|burgess_1982_ii|from_2022|gabbay_1994_ch10|henkin_1949|hodkinson_2006|johansson_1937|post_1921|rabinovich_2014|trufas_2024)\b' /tmp/lit560/after-p2.tsv | cut -f1,2
# expect:
#   bentzen_2023        33
#   burgess_1982_i      25
#   burgess_1982_ii     24
#   from_2022           34
#   gabbay_1994_ch10    12
#   henkin_1949         27
#   hodkinson_2006       8
#   johansson_1937      24
#   post_1921           46
#   rabinovich_2014     30
#   trufas_2024         48

# 5. Known residual: the two venema documents stay at 1 (their chunk files are sec*.md).
grep -E '^venema_1993' /tmp/lit560/after-p2.tsv | cut -f1,2
# expect: venema_1993  1  /  venema_1993_since  1

# 6. Global index untouched — this MUST print nothing.
git -C ~/Projects/Literature status --porcelain 2>/dev/null | head
# (if ~/Projects/Literature is not a git repo, instead confirm mtime is unchanged:)
stat -c '%y %n' ~/Projects/Literature/index.json
```

**Rollback/Contingency**: If the hoist breaks path resolution, the `dir:` column in step 3's
diff changes and the diff count exceeds 11 — revert with
`git checkout HEAD -- .claude/scripts/literature-briefing.sh` (snapshot first via
`bash .claude/scripts/git-snapshot.sh` if other uncommitted edits to that file exist) and
re-apply Phase 1 only. Phase 1 is independently valuable and shippable: if Tier 3 cannot be made
to work, stopping after Phase 1 leaves 8 documents repaired (including Massacci) and 13 still
under-reporting, which is a defensible partial outcome — record it as `[PARTIAL]` rather than
reverting Phase 1.

---

### Phase 3: Document the three-tier precedence and known residuals in the script header, and record the full-34 verification sweep [NOT STARTED]

**Goal**: Make the precedence decision and its two residuals legible to the next maintainer, so
the inverted-precedence trap is not re-introduced, and record the final verified state of all 34
documents.

**Tasks**:
- Add a comment block to `.claude/scripts/literature-briefing.sh` — immediately above the
  chunk-count derivation in per-repo mode, not in the file's top-of-file usage header —
  documenting:
  - The four-tier precedence: registered child entries → parent `chunk_count` field → on-disk
    `chunk_*.md` glob → literal 1.
  - Why child count wins over the `chunk_count` field: the field can hold a stale
    pre-consolidation count (an entry in the corpus carries 997 against a true 6), so preferring
    it would over-report consolidated documents.
  - Why `chunks.json` length is never used: same pre-consolidation staleness.
  - The known residual: documents whose chunk files use a `sec*.md` naming scheme are not matched
    by the Tier-3 glob and still display 1. Two sub-index documents are in this state today.
  - Do NOT cite task numbers in this comment — it lives outside `specs/**`
    (`.claude/rules/no-task-references-in-deliverables.md`). Reference the behavior, not the ticket.
- Run the full-34 sweep one final time and record the result in the phase notes / execution
  summary: 21 documents repaired (8 via Tier 2, 11 via Tier 3), 13 unchanged and correct,
  2 known residuals at 1.
- Measure and record briefing wall-clock time before/after (`time` on the script) as a note.
- Note for the user, in the summary only, that the 17 orphaned `parent_doc` values in the global
  index remain as a separate corpus-data issue outside this repository (Report Recommendation 4).

**Timing**: ~20 minutes.

**Depends on**: 2.

**Estimated output**: ~20 lines of comment plus recorded verification output.

**Done when**: the comment block exists in the script, the full-34 sweep matches the expected
final table below exactly, and the residual/orphan notes are recorded.

**Verification** (runnable — this is the definitive acceptance check for the whole task):

```bash
cd /home/benjamin/Projects/cslib

cat > /tmp/lit560/expected-final.tsv <<'EOF'
alechinamendlerdepaivaritter_2001_categorical_and_kripke_semantics_for_constructive_s4	52	19198
arisakadasstrassburger_2015_onnestedsequentsforconstructivemodallogics	40	18070
bentzen_2023	33	7334
biermandepaiva_2000_onanintuitionisticmodallogic	53	19607
blackburn_2002	35	365065
burgess_1982_i	25	5437
burgess_1982_ii	24	5589
caleiro_2013	7	42173
chagrovzakharyaschev_1997_modallogic	6	329042
church_1956	7	265545
from_2022	34	11549
gabbay_1993	5	39634
gabbay_1994_ch10	12	2279
gentzen_1935	5	28343
goldblatt_2003	5	30689
henkin_1949	27	5872
hodkinson_2006	8	2094
hughes_1996	4	208427
johansson_1937	24	5653
marinmoralesstrassburger_2021_fully_labelled_proof_system_intuitionistic_modal	51	20379
massacci_2000_single_step_tableaux_for_modal_logics	77	30656
mendelson_2016	6	290077
negri_von_plato_2001	7	156369
pacheco_2024_collapsingconstructiveandintuitionisticmodallogics	19	7179
post_1921	46	13230
rabinovich_2014	30	7312
reynolds_2001	10	66084
simpson_1994_intuitionisticmodallogic	206	90383
troelstra_schwichtenberg_2000	7	243938
trufas_2024	48	9699
venema_1993	1	22333
venema_1993_since	1	3927
wijesekera_1990_constructivemodallogicsi	38	15626
zakharyaschev_2001	4	110561
EOF

bash .claude/scripts/literature-briefing.sh 2>/dev/null \
 | sed -n 's#^ *\([0-9]*\) chunk(s), ~\([0-9]*\) tokens . dir: .*/sources/\(.*\)$#\3\t\1\t\2#p' \
 | sort > /tmp/lit560/after-final.tsv

diff /tmp/lit560/expected-final.tsv /tmp/lit560/after-final.tsv && echo "ALL 34 DOCUMENTS MATCH EXPECTED: PASS"

# Coverage marker unchanged from the very start.
bash .claude/scripts/literature-briefing.sh 2>/dev/null | grep 'lit-coverage'
# expect: <!-- lit-coverage mode=repo seg_count=34 sparse=false threshold=3 -->

# Global corpus untouched.
stat -c '%y %n' ~/Projects/Literature/index.json

# Timing note.
time bash .claude/scripts/literature-briefing.sh >/dev/null 2>&1
```

The `expected-final.tsv` table above was generated from a live run of the current script plus
the verified per-document Tier-2 field values and Tier-3 disk counts. The token column is
identical to the pre-change baseline for all 34 rows.

**Rollback/Contingency**: This phase adds only comments and records verification. If the final
diff fails, the fault lies in Phase 1 or Phase 2, not here — do not paper over a mismatch by
editing `expected-final.tsv`. Identify which tier produced the wrong value and fix the tier.

## Testing & Validation

- The per-phase verification commands above are the test suite; there is no unit-test harness for
  `literature-briefing.sh` (`test-lit-pipeline.sh` covers the convert/chunk/index pipeline, not
  the briefing renderer).
- Three invariants are asserted after every phase: the `chagrovzakharyaschev == 6` sentinel, the
  34-row token column unchanged, and the `lit-coverage` marker unchanged.
- Global mode is smoke-checked in Phase 1 to confirm the shared code path was not disturbed.
- A read-only assertion on `~/Projects/Literature/index.json` runs in Phases 2 and 3.

## Artifacts & Outputs

| Path | Type | Note |
|---|---|---|
| `.claude/scripts/literature-briefing.sh` | modified | The only file this task changes |
| `specs/560_repair_literature_subindex_massacci_chunks/summaries/01_briefing-chunk-count-repair-summary.md` | new | Execution summary, including the final 34-document sweep and the residual/orphan notes |

## Rollback/Contingency

Whole-task rollback is a single-file revert:

```bash
cd /home/benjamin/Projects/cslib
bash .claude/scripts/git-snapshot.sh          # required if the tree is dirty
git checkout HEAD -- .claude/scripts/literature-briefing.sh
```

Partial-outcome ladder, in order of preference:
1. All three phases land — 21 documents repaired, 2 known residuals.
2. Phases 1 and 3 only (Tier 3 abandoned) — 8 documents repaired including Massacci; the plan
   must then state plainly that 13 documents continue to under-report. Mark `[PARTIAL]`.
3. Full revert — no change; the defect stands. Only if Phase 1 cannot be made to pass its
   sentinel check.

Nothing in this task writes outside the repository, so no rollback of external state is ever
required.
