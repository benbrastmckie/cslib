# Research Report: Literature briefing per-document chunk-count under-report defect

- **Task**: 560 - Repair the per-repo literature sub-index (Massacci corpus reported as 1 chunk, holds 77)
- **Started**: 2026-07-26T00:00:00Z
- **Completed**: 2026-07-26T00:00:00Z
- **Effort**: ~1 hour (verification-only; no implementation)
- **Dependencies**: None
- **Sources/Inputs**: `.claude/scripts/literature-briefing.sh`, `~/Projects/Literature/index.json` (read-only), `specs/literature-index.json`, on-disk `~/Projects/Literature/sources/*/chunks.json` and `chunk_*.md` files, `.claude/scripts/literature-search.sh`, `.claude/scripts/literature-discover.sh`, `.claude/scripts/literature-fidelity-audit.sh`
- **Artifacts**: this report
- **Standards**: status-markers.md, artifact-management.md, tasks.md, report-format.md

## Executive Summary

- The task description's mechanism diagnosis (A, B) is **CONFIRMED exactly**, including the specific line numbers.
- The task description's scope claim ("19 of 34 documents, 848 chunk files") is **PARTIALLY WRONG**. Only **8 of the 34** sub-index documents are actually repairable by the description's proposed fix ("prefer parent `chunk_count`"), because only 8 of the 34 carry a non-null `chunk_count` field on their parent entry with zero registered children. The other 11 documents named in the description's list (`rabinovich_2014`, `henkin_1949`, `burgess_1982_i`, `burgess_1982_ii`, `johansson_1937`, `post_1921`, `from_2022`, `bentzen_2023`, `trufas_2024`, `gabbay_1994_ch10`, `hodkinson_2006`) have **no `chunk_count` field at all** on their global-index parent entry — the proposed fix cannot recover their true chunk counts from `index.json` alone.
- The task description's proposed fix ordering — "prefer chunk_count field, fall back to child count only when chunk_count is absent" — is **UNSAFE as literally stated**: it would introduce a regression on `chagrovzakharyaschev_1997_modallogic` (in the sub-index), which currently reports correctly (6 chunks, via the existing child-count path) but carries a stale/mismatched `chunk_count: 997` field (a raw pre-consolidation page-chunk count, not the final 6-section chunk count). The correct precedence is the reverse: prefer child count when children exist, only fall back to `chunk_count` field when there are zero children.
- Both defect confirmations reproduced live: Massacci currently prints `1 chunk(s)` in the actual repo-mode briefing output; `chagrovzakharyaschev_1997_modallogic` currently prints the correct `6 chunk(s)`.
- Only per-repo mode is affected. Global-corpus mode (`--global`) never touches `chunk_count`/`parent_doc` derivation and is unaffected (D). The `<!-- lit-coverage ... -->` sparse marker in repo mode counts **resolved documents** (34), not chunks, so it is also unaffected by this defect — the task description's verification claim that the marker "must reflect the corrected count" does not apply to chunk counts.
- No other script in `.claude/scripts/` duplicates this child-entry-counting-with-fallback-to-1 pattern (F) — `file_scope: [".claude/scripts/literature-briefing.sh"]` remains correctly scoped, no expansion needed.

## Context & Scope

Task 560 (P0, no dependency) asks for verification of a diagnosed defect in
`.claude/scripts/literature-briefing.sh`'s per-repo mode: it under-reports chunk counts for
documents whose global-index parent entry has no registered child entries, falling back to a
hardcoded `chunk_count=1`. This is the research dispatch only; no implementation was performed.
`~/Projects/Literature/index.json` was read-only for this investigation, per the task's explicit
constraint — it was never written.

## Findings

### A. Mechanism verification — CONFIRMED, line numbers match

`.claude/scripts/literature-briefing.sh:203-206` (current file, 467 lines total):

```bash
    # Find all chunk entries (children: parent_doc == doc_id)
    chunk_count=$(jq --arg id "$doc_id" '
      [.entries[] | select(.parent_doc == $id)] | length
    ' "$GLOBAL_INDEX" 2>/dev/null || echo 0)
```

`.claude/scripts/literature-briefing.sh:208-225` — the `if chunk_count -gt 0 / else` branch; the
fallback is at line 224:

```bash
    else
      total_tokens=$(jq -r --arg id "$doc_id" '
        .entries[] | select(.id == $id) | .token_count // 0
      ' "$GLOBAL_INDEX" 2>/dev/null | head -1) || { echo "..."; total_tokens=0; }
      [[ "$total_tokens" =~ ^[0-9]+$ ]] || total_tokens=0
      chunk_count=1
    fi
```

Task description's claimed line numbers (~203-206, ~224) are exact — no drift.

### B. Data-shape verification — CONFIRMED

```
jq '.entries[] | select(.id == "massacci_2000_single_step_tableaux_for_modal_logics")' ~/Projects/Literature/index.json
```
returns a single entry with `"chunk_count": 77`, `"parent_doc": null`.

```
jq '[.entries[] | select(.parent_doc == "massacci_2000_single_step_tableaux_for_modal_logics")] | length' ~/Projects/Literature/index.json
```
returns `0`.

Massacci has 77 `chunk_*.md` files on disk in
`~/Projects/Literature/sources/massacci_2000_single_step_tableaux_for_modal_logics/` (verified via
`find ... -maxdepth 1 -name "chunk_*.md" | wc -l` → `77`), matching its parent `chunk_count` field
exactly and confirming that field is the ground truth for this document.

### C. True scope of the 34-document sub-index — CORRECTED from the task description

Reproducible command (per sub-index doc_id, against the global index):

```bash
SUB_INDEX=specs/literature-index.json
GLOBAL_INDEX=~/Projects/Literature/index.json
jq -r '.entries[].doc_id' "$SUB_INDEX" | while read -r id; do
  jq -r --arg id "$id" '
    .entries as $all
    | ($all[] | select(.id == $id)) as $p
    | ($all | map(select(.parent_doc == $id)) | length) as $child_count
    | "\($id)\t\($p.chunk_count // "null")\t\($child_count)"
  ' "$GLOBAL_INDEX"
done
```

Classifying all 34 sub-index documents by `(chunk_count field, child_count)`:

| Class | Count | Members | Behavior today | Behavior after description's literal fix |
|---|---|---|---|---|
| (1) `chunk_count` present, `child_count=0` | **8** | `massacci_2000_single_step_tableaux_for_modal_logics`(77), `simpson_1994_intuitionisticmodallogic`(206), `biermandepaiva_2000_onanintuitionisticmodallogic`(53), `wijesekera_1990_constructivemodallogicsi`(38), `arisakadasstrassburger_2015_onnestedsequentsforconstructivemodallogics`(40), `alechinamendlerdepaivaritter_2001_categorical_and_kripke_semantics_for_constructive_s4`(52), `marinmoralesstrassburger_2021_fully_labelled_proof_system_intuitionistic_modal`(51), `pacheco_2024_collapsingconstructiveandintuitionisticmodallogics`(19) | reports `1 chunk(s)` (BUG) | **fixed** — reports true count |
| (2) `chunk_count` present, `child_count>0` (mismatched) | **1** | `chagrovzakharyaschev_1997_modallogic` (`chunk_count`=997, real children=6) | reports `6 chunk(s)` (CORRECT, via child-count path) | **REGRESSES** to `997 chunk(s)` if `chunk_count` is preferred unconditionally |
| (3) `chunk_count` null, `child_count>0` | **12** | `reynolds_2001`, `gabbay_1993`, `goldblatt_2003`, `caleiro_2013`, `blackburn_2002_book`, `church_1956`, `gentzen_1935`, `hughes_1996`, `mendelson_2016`, `negri_von_plato_2001`, `troelstra_schwichtenberg_2000`, `zakharyaschev_2001` | reports correct child-derived count | unaffected either way (chunk_count absent ⇒ fallback path unchanged for these) |
| (4) `chunk_count` null, `child_count=0` | **13** | `burgess_1982_i`, `burgess_1982_ii`, `venema_1993_since_until`, `venema_1993_anti_axioms`, `rabinovich_2014`, `hodkinson_2006`, `bentzen_2023`, `from_2022`, `gabbay_1994_ch10`, `henkin_1949`, `johansson_1937`, `post_1921`, `trufas_2024` | reports `1 chunk(s)` (BUG) | **STILL BROKEN** — no `chunk_count` field exists to prefer, so the fix cannot recover these from `index.json` alone |

8 + 1 + 12 + 13 = 34. ✓

The task description's "19 documents, 848 chunk files" list conflates classes (1) and (4): it
lists 8 truly-fixable documents alongside 11 (of the 13) class-(4) documents whose true counts
were evidently obtained by counting `chunk_*.md` files on disk or `chunks.json` array length, NOT
from any field the proposed `index.json`-only fix can read. This was spot-checked directly:

```
find ~/Projects/Literature/sources/rabinovich_2014 -maxdepth 1 -name "chunk_*.md" | wc -l   # → 30
find ~/Projects/Literature/sources/henkin_1949 -maxdepth 1 -name "chunk_*.md" | wc -l        # → 27
```
Both match the task description's claimed figures for these documents (`rabinovich_2014:30`,
`henkin_1949:27`) exactly — confirming the description's numbers are real and disk-sourced, but
also confirming that **the preferred fix as literally stated cannot produce them**, since
`index.json` carries no `chunk_count` for these entries. `chunks.json` (present for 31 of 34
sub-index docs, absent for `venema_1993_since_until`, `venema_1993_anti_axioms`,
`blackburn_2002_book`) also carries the correct length for class-(4) docs (e.g. `rabinovich_2014`
→ 30, `henkin_1949` → 27) and could be used as a third-tier, on-disk fallback if the planner
wants to close class (4) too — but note `chunks.json` is **not reliable for class (2)/(3)**
documents that underwent post-ingest consolidation: `chagrovzakharyaschev_1997_modallogic`'s
`chunks.json` has 997 entries (the same raw pre-consolidation count as its `chunk_count` field),
even though only 6 final, consolidated `p0X_*.md` chunks are registered as children and are the
ones the briefing's "Read a chunk" instructions actually point at.

Sum of `chunk_count` field across the 8 truly-fixable (class 1) documents: **536**, not the
description's claimed 848 (848 was evidently computed over the full 19-document list, most of
whose true counts do not come from `chunk_count`).

### D. Both briefing modes — only per-repo mode affected; sparse marker unaffected

Repo mode (`literature-briefing.sh:170-292`) is the only path that reads `chunk_count`/
`parent_doc`. Global mode (`--global "<query>"`, lines 294-393) sources results entirely from
`literature-search.sh`'s FTS5 hits (`chunk_id`, `doc_id`, `section_path`, `token_count` per
matched segment) and never touches the parent `chunk_count` field or does child-entry counting —
confirmed by grep: no `parent_doc` or `chunk_count` reference appears in lines 294-393.

The `<!-- lit-coverage ... -->` marker's `seg_count`/`coverage_count` value is set per-mode:
- Repo mode (`literature-briefing.sh:290-292`): `coverage_count="${#briefing_lines[@]}"` — the
  **number of resolved documents** (34 in this repo), not a chunk total.
- Global mode (`literature-briefing.sh:369-371`): `coverage_count="$seg_count"` — the number of
  matched search segments, independent of any document's `chunk_count` field.

Live reproduction confirms the marker is unaffected by the defect:
```
$ bash .claude/scripts/literature-briefing.sh 2>&1 | grep "lit-coverage"
<!-- lit-coverage mode=repo seg_count=34 sparse=false threshold=3 -->
```
This is document count (34), already correct and far above the sparse threshold (3), both before
and after any chunk-count fix. **The task description's verification instruction — "the
sparse-coverage marker ... must reflect the corrected count" — does not apply**: fixing the
per-document chunk-count bug will not (and should not) change this marker's value.

### E. Parent/child schema invariant

Confirmed both populations genuinely exist in the global index (321 entries total: 124 parents +
197 children):
- 12 sub-index documents (class 3 above) have real, correctly-linked children (`parent_doc`
  matches the parent's `id`) — the existing child-counting path is correct and necessary for
  these, so it must not be removed or fully replaced.
- 1 sub-index document (`chagrovzakharyaschev_1997_modallogic`, class 2) has both real children
  AND a stale, larger `chunk_count` field — this is the regression case that rules out "always
  prefer `chunk_count`" as a safe fix.
- Separately (not in the cslib sub-index, noted for completeness): 17 child `parent_doc` values
  in the global index (`burgess_1982`, `venema_1993`, `reynolds_1992`, etc.) do not match any
  current parent `.id` — these are orphaned children from a prior ID-splitting rename (e.g.
  `burgess_1982` → `burgess_1982_i`/`burgess_1982_ii`). They do not affect this task's fix (the
  now-split parents `burgess_1982_i`/`burgess_1982_ii` are in class 4, `chunk_count` null,
  0 matching children under their current IDs) but are worth flagging to the planner as a
  separate, lower-priority data-quality issue in the global index, out of this task's scope.

**Conclusion for E**: the fix must be "child count wins when present, `chunk_count` field is a
fallback only for the zero-children case" — the inverse precedence from the task description's
literal wording ("prefer chunk_count, fall back to child count only when chunk_count absent").

### F. Other consumers of the same pattern — none found

```
grep -rln "parent_doc" .claude/scripts/
```
→ `literature-briefing.sh`, `test-lit-pipeline.sh` (test fixture, literal `"parent_doc": null`
in a JSON blob, not logic), `literature-discover.sh` (iterates root entries for search matching,
no chunk-count derivation), `literature-fidelity-audit.sh` (uses `parent_doc` absence to identify
"true roots" for provenance stamping, not for a displayed chunk count), `literature-search.sh`
(references `id`/`parent_doc` only in comments about directory-naming ambiguity, not for a
chunk-count derivation with a `=1` fallback).

No sibling script reproduces the specific "count children, fallback to 1" pattern. **`file_scope`
should remain `[".claude/scripts/literature-briefing.sh"]`** — no expansion needed for this
specific defect (though see Recommendations for the separate class-4 gap).

## Decisions

- Confirmed: implement the fix only in `literature-briefing.sh`, only in the per-repo mode block
  (lines ~203-225).
- Rejected (per task constraint, independently re-confirmed necessary): any fix that writes to
  `~/Projects/Literature/index.json`. This investigation only read that file.
- Corrected: the fix precedence must be child-count-first, `chunk_count`-field-second — not
  `chunk_count`-field-first as the task description proposed — to avoid regressing
  `chagrovzakharyaschev_1997_modallogic`.

## Recommendations

1. **Primary fix** (in `literature-briefing.sh`, lines ~203-225): change the branch so that when
   the derived `child_count` is `0`, check the parent entry's own `chunk_count` field before
   falling back to the hardcoded `1`:
   - `child_count > 0` → keep existing behavior (sum children's tokens + parent tokens, as today).
   - `child_count == 0` AND parent `chunk_count` field is present and `> 0` → use that field's
     value as `chunk_count`; tokens continue to come from the parent `token_count` field (already
     correct today for this branch — e.g. Massacci's `token_count: 30656` already reported
     correctly).
   - `child_count == 0` AND parent `chunk_count` field is absent/`0` → fall back to `chunk_count=1`
     (unchanged; this is class (4), 13 documents, not resolvable from `index.json` alone).
   This fixes exactly the 8 class-(1) documents and leaves class (2)'s `chagrovzakharyaschev`
   correctly on its existing child-count path (no regression).
2. **Scope caveat to record explicitly in the plan**: this fix resolves 8 of the 34 sub-index
   documents, not 19. The other 11 documents from the task description's list remain reporting
   `1 chunk(s)` after this fix, because their global-index parent entries carry no `chunk_count`
   metadata at all. If the planner wants full coverage of all 34 (or the originally-claimed 19),
   a second, clearly-separated remediation is needed — e.g. a third fallback tier in
   `literature-briefing.sh` that counts `chunk_*.md` files on disk under the parent's `chunks_dir`
   when both `child_count` and `chunk_count` are absent/zero. This is still within the same file
   and file_scope, but is a distinct, larger change (adds a filesystem read) that the planner
   should size as a separate phase rather than bundling into the "prefer chunk_count field"
   one-line fix. **Do not use `chunks.json` array length as a third-tier source** — for
   consolidated documents (`chagrovzakharyaschev_1997_modallogic` confirmed; likely
   `church_1956`, `hughes_1996`, `mendelson_2016`, `negri_von_plato_2001`,
   `troelstra_schwichtenberg_2000`, `zakharyaschev_2001`, `gentzen_1935` given their similarly
   large `chunks.json` lengths vs. small registered child counts) it reflects the raw
   pre-consolidation chunking, not the final indexed/readable chunk count.
3. Do not attempt to "fix" the `<!-- lit-coverage ... -->` sparse marker as part of this task —
   it is already correct (counts documents in repo mode) and is not driven by the defect.
4. File the 17 orphaned `parent_doc` values (Finding E) as a separate, lower-priority global-index
   data-quality note for the user — out of scope for this task, and out of scope for any
   `.claude/scripts/` fix since it lives in the corpus data itself.

## Risks & Mitigations

- **Risk**: implementing the fix exactly as the task description literally proposes ("prefer
  chunk_count field") without the child-count-first inversion silently regresses
  `chagrovzakharyaschev_1997_modallogic` from 6 (correct) to 997 (wrong) chunks reported. **This
  is the single highest-value catch of this research pass.**
  **Mitigation**: implement with child-count-first precedence per Recommendation 1; add
  `chagrovzakharyaschev_1997_modallogic` as an explicit fourth spot-check in the plan's
  verification step (in addition to the three the task description asked for), since it is the
  only sub-index document that can regress.
- **Risk**: the plan may be written assuming "19 documents fixed" and later judged incomplete
  when spot-checks on `rabinovich_2014` or similar class-(4) documents still show `1 chunk(s)`.
  **Mitigation**: Recommendation 2's scope caveat should be copied verbatim into the plan's
  acceptance criteria so "8 of 34 fixed, 13 documented as a follow-on" is the explicit, agreed
  success bar — not a surprise discovered during verification.

## Verification (for the planner/implementer)

Before/after command, Massacci (task description's primary example):
```bash
bash .claude/scripts/literature-briefing.sh 2>&1 | grep -A2 -i "Single Step Tableaux"
```
- **Before**: `1 chunk(s), ~30656 tokens`
- **After**: `77 chunk(s), ~30656 tokens`

Four spot-checks (three from the task description plus the one regression-risk case this report
adds):
```bash
bash .claude/scripts/literature-briefing.sh 2>&1 | grep -A2 -i "Intuitionistic Modal Logic\b"          # simpson_1994 → expect 206
bash .claude/scripts/literature-briefing.sh 2>&1 | grep -A2 -i "On an Intuitionistic Modal Logic"       # biermandepaiva_2000 → expect 53
bash .claude/scripts/literature-briefing.sh 2>&1 | grep -A2 -i "Collapsing Constructive"                # pacheco_2024 → expect 20 (chunk_count field=19; note off-by-one vs disk glob is pre-existing metadata, not introduced by this fix — verify against chunk_count field value 19, not disk count)
bash .claude/scripts/literature-briefing.sh 2>&1 | grep -A2 -i "Modal Logic (Oxford"                    # chagrovzakharyaschev_1997_modallogic → MUST STAY 6 chunk(s) (regression check)
```
Coverage-marker regression check (must be unchanged by the fix):
```bash
bash .claude/scripts/literature-briefing.sh 2>&1 | grep "lit-coverage"   # expect: mode=repo seg_count=34 sparse=false threshold=3, unchanged
```

## Appendix

- 34-doc classification data generated via the Finding C command; raw output available by
  re-running the command above (not persisted as a separate file — reproducible on demand).
- Global index totals: 321 entries, 124 parent (`parent_doc == null`), 197 children.
- `~/Projects/Literature/index.json` was read-only throughout this investigation; no writes were
  made to it or to any file under `~/Projects/Literature/`.

## Adversarial Self-Verification

| Claim | Source/Counterexample | Verification Method | Confidence |
|---|---|---|---|
| Lines 203-206 derive chunk_count via child-entry counting | `.claude/scripts/literature-briefing.sh:203-206` (quoted verbatim above) | Direct Read of current file | High |
| Line 224 applies `chunk_count=1` fallback | `.claude/scripts/literature-briefing.sh:224` (quoted verbatim above) | Direct Read of current file | High |
| Massacci parent has `chunk_count: 77`, 0 children | `jq` query against `~/Projects/Literature/index.json`, output captured above | Ran the jq command, inspected raw JSON output | High |
| Massacci currently reports `1 chunk(s)` in live briefing output | Live run: `bash .claude/scripts/literature-briefing.sh` | Ran the actual script end-to-end, grepped output | High |
| "19 of 34 documents, 848 chunk files" (task description's claim) | Attempted to reproduce via the class-(1)-only jq classification: only 8 documents have `chunk_count` present with 0 children; sum=536 | Ran classification jq loop across all 34 sub-index doc_ids against the live global index | High — **REFUTED**: the 19/848 figure conflates a fixable subset (8, chunk_count-backed) with a non-fixable-by-this-approach subset (11, chunk_count absent, values sourced from disk file counts not index.json) |
| Task description's proposed fix ("prefer chunk_count, fall back to child count only when chunk_count absent") is safe | Counter-example: `chagrovzakharyaschev_1997_modallogic` has `chunk_count: 997` (stale) AND 6 real children; live briefing currently reports the correct `6 chunk(s)` via the child-count path | Ran jq classification + live briefing run showing current correct `6 chunk(s)` output | High — **REFUTED**: literal fix as described would regress this document to 997 |
| Global mode (`--global`) is unaffected by the defect | Read lines 294-393 of `literature-briefing.sh`; grepped for `parent_doc`/`chunk_count` in that range — zero matches | Direct Read + grep on line range | High |
| `<!-- lit-coverage -->` marker is unaffected (counts documents, not chunks, in repo mode) | `literature-briefing.sh:290-292` (`coverage_count="${#briefing_lines[@]}"`); live output `seg_count=34 sparse=false` | Direct Read + live run | High |
| No other `.claude/scripts/` file duplicates the child-counting-with-fallback-to-1 pattern | `grep -rln "parent_doc" .claude/scripts/` → 5 files, none reproduce the specific counting+fallback logic (inspected each) | Grep + manual inspection of each matched file's relevant lines | High |
| `chunks.json` file length is a reliable third-tier chunk-count source for all documents | Counter-example: `chagrovzakharyaschev_1997_modallogic`'s `chunks.json` has 997 entries (matches stale `chunk_count`, not the true 6); same large-vs-small pattern observed for `church_1956`, `hughes_1996`, `mendelson_2016`, `negri_von_plato_2001`, `troelstra_schwichtenberg_2000`, `zakharyaschev_2001`, `gentzen_1935` (chunks.json lengths of 1025/581/654/376/573/306/108 vs. registered child counts of 7/4/6/7/7/4/5) | Ran `jq 'length' chunks.json` for all 34 sub-index docs, cross-referenced against child_count from Finding C | High — **REFUTED as a universal fallback**: only safe for documents with 0 registered children AND no consolidation step (i.e., class 4 documents specifically; not a substitute for class 2/3's child-count path) |
| Class-4 documents' true chunk counts (e.g. `rabinovich_2014:30`, `henkin_1949:27`) match on-disk `chunk_*.md` file counts | `find .../rabinovich_2014 -maxdepth 1 -name "chunk_*.md" \| wc -l` → 30; `.../henkin_1949` → 27 | Ran the exact glob-count commands, matched against task description's claimed figures | High |

**Contradiction Log**:
- Task description states the fix is "lowest risk" and repairs "19 of 34 documents (848 chunk
  files)". Verification shows the fix as literally described (a) repairs only 8 of 34 (536 chunk
  files) and (b) is not lowest-risk as stated — it requires the child-count-first inversion to
  avoid a regression on `chagrovzakharyaschev_1997_modallogic`. Resolution: this report's
  Recommendation 1 (corrected precedence) and Recommendation 2 (explicit 8-of-34 scope,
  class-4 documented as a follow-on) supersede the task description's fix wording and scope
  claim; the underlying root-cause diagnosis (mechanism, line numbers, Massacci data shape) is
  otherwise fully correct and unchanged.
- Task description states the sparse-coverage marker "must reflect the corrected count" after the
  fix. Verification shows the marker counts documents (currently 34, `sparse=false`), not chunks,
  in repo mode, and is therefore unaffected by any chunk-count-only fix. Resolution: this
  verification claim in the task description is incorrect and should not be carried into the
  plan's acceptance criteria; Recommendation 3 and the Verification section above replace it with
  the correct expectation ("marker unchanged, still `seg_count=34 sparse=false`").

No modifications to the underlying root-cause diagnosis were needed beyond the two corrections
above (scope: 8 not 19; fix precedence: child-count-first not chunk_count-first) — mechanism (A)
and data shape (B) verified exactly as claimed.
