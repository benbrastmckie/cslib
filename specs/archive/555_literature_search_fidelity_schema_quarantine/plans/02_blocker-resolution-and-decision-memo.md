# Implementation Plan: Task #555 (v2)

- **Task**: 555 - literature_search_fidelity_schema_quarantine
- **Status**: [COMPLETED] (All 7 phases COMPLETED and committed. Phase 6 closed out the former DJVU
  gate, restored the working tree, repointed `.sources-recovered/` references, and re-adjudicated
  `arisakadasstrassburger_2015` (honest quarantined outcome). Phase 7 produced the decision memo
  surfacing the Group B disposition, Group A regression, and residual findings — no value stamped,
  no policy changed, no `index.json` write in Phase 7 itself.)
- **Effort**: 8 hours total (5 hours spent on Phases 1-5; ~3 hours remaining across Phases 6-7)
- **Dependencies**: None
- **Research Inputs**:
  - specs/555_literature_search_fidelity_schema_quarantine/reports/01_fidelity-schema-key-derivation.md
  - specs/555_literature_search_fidelity_schema_quarantine/reports/02_blocker-disposition-research.md
- **Artifacts**: plans/02_blocker-resolution-and-decision-memo.md (this file)
- **Standards**: plan-format.md; status-markers.md; artifact-management.md; tasks.md; git-workflow.md
- **Type**: general
- **Lean Intent**: false

## Overview

Version 1 of this plan shipped a four-site `load_fidelity_map()` key-derivation fix in
`literature-search.sh` and a `--legacy-schema` classification/write mode in
`literature-fidelity-audit.sh` (Phases 1-5, complete and committed), then stopped at two BLOCKED
gates: Phase 6 (no DJVU text extractor) and Phase 7 (disposition of the unrecoverable documents).

Both gates' premises have since been invalidated by work done in the `~/Projects/Literature`
repository on 2026-07-26. Phase 6's blocking condition is moot — the document it gated on has a
source PDF, is already classified, and is already visible in default search. Phase 7's question
remains a genuine user decision but has **reversed polarity**: the documents it concerned are now
citable by default rather than quarantined, so "leave as-is" no longer means "stay quarantined."

This revision rewrites Phase 6 as actionable close-out work and Phase 7 as a write-up-and-surface
phase whose deliverable is a decision memo — not a decision. Done means: the residual mechanical
work is finished and verified against the live corpus; every claim the user needs in order to
decide is measured, written down, and handed over; and no fidelity value, quarantine constant, or
policy has been changed unilaterally.

### Research Integration

Newly integrated report: `reports/02_blocker-disposition-research.md` (2026-07-26, read-only
investigation). Its established findings, which MUST NOT be re-derived:

- `chagrovzakharyaschev_1997_modallogic` has `source.pdf` (53,951,887 bytes) beside `source.djvu`,
  added by Literature commit `ea47e97`. `pdftotext` is already on `PATH` and is already the exact
  extractor `literature-fidelity-audit.sh` uses. No DJVU tooling and no user authorization are
  required.
- `djvulibre` 3.5.29 is already built in the local nix store and `djvutxt` extracts 1,381,134
  characters cleanly from the `.djvu` (exit 0, real embedded text layer, no OCR), reachable via
  `nix-shell -p djvulibre` — a user-level ephemeral shell, not a system change. This path is
  **not needed** given the PDF, and the store path has no gcroot, so it MUST NOT be hardcoded.
- Phase 6's own gate check (`command -v djvutxt`) is a **false negative**: it tests PATH
  availability, not whether the document can be classified.
- `$LITERATURE_DIR/.sources-recovered/` is **empty**. Sources were migrated to
  `$LITERATURE_DIR/sources/<doc_id>/source.{pdf,djvu}` by commits `e0ffb9b`, `bb3bf18`, `ea47e97`.
  Nothing was lost; any step pointing at `.sources-recovered/` will find nothing.
- `massacci_2000_single_step_tableaux_for_modal_logics` has left the unrecoverable set — it has a
  `source.pdf` and is stamped `verified_conversion`.
- `no_source_pdf` is **not** on `QUARANTINED_FIDELITY_VALUES`, so documents stamped with it are
  returned by default no-flag search, non-degraded. Option (c)'s effect is de facto live and
  unannounced. `no_source_pdf` was always in the audit script's six-value enum and the quarantine
  constant was never edited — task 555's code did not cause this; the Literature migration did.
- Literature commit `bb3bf18` overwrote `wijesekera_1990_constructivemodallogicsi` and
  `simpson_1994_intuitionisticmodallogic` from `ocr_rescanned_reflowed_partial_symbol_loss` to
  `verified_conversion`, losing the partial-symbol-loss warning. The Phase 4 `SIX_VALUE_ENUM` guard
  works but only constrains `literature-fidelity-audit.sh`; `bb3bf18` wrote by another route.

### Corrections established at revision time (verified directly against the live corpus)

These supersede or sharpen the research report where they differ. They were measured during this
revision, after the report was written, and are load-bearing for Phases 6-7.

1. **The working tree has reverted all of Phases 1-5's code.** `git status` reports both scripts
   as modified; the diff against `HEAD` is `43 insertions(+), 357 deletions(-)` and removes the
   entire `--legacy-schema` mode plus all four `doc_id` fallback branches. `HEAD` commit
   `335c034a` has the work; the working tree does not. The revert is uncommitted and unexplained
   by any commit message. Phase 6 must resolve this before any verification is meaningful.

2. **The Phase 1 fix is now a functional no-op, and `--legacy-schema` enumerates zero entries.**
   Against the current `index.json` the map-diff harness reports `old 127 / new 127` with
   `added: []` — the `doc_id` fallback adds no keys, because the migration gave every former
   legacy entry a `sources/`-prefixed `path`. The legacy gate (`doc_id` and `chunks_dir` present,
   `path` and `id` absent) matches **0 of 321** entries. This is a consequence of the migration,
   not a defect in the Phase 1-5 work, but it means a `--legacy-schema` re-run cannot re-adjudicate
   anything.

3. **`arisakadasstrassburger_2015` has migrated to the `sources/` schema.** It now carries
   `path: "sources/arisakadasstrassburger_2015_.../"`, `id`, and `chunks_dir`, plus `source.pdf`
   (485,044 bytes) and a whole-document `.md` on disk. The correct re-adjudication is therefore a
   **default-mode** audit run, not `--legacy-schema`.

4. **A re-run will not rescue `arisakadasstrassburger_2015`, and that is the honest outcome.**
   Measured directly: `pdftotext` yields 19,439 words; the whole-document `.md` yields 10,007
   (ratio **0.5148**); the chunk sum yields 9,968 (ratio **0.5128**). Both are far below
   `RATIO_THRESHOLD` (0.75), and both are consistent with the stored `word_ratio` of 0.539. The
   markdown genuinely contains about half the source's words. Only the disclosure /
   proof-completeness escape path could change the verdict, and its outcome must be measured, not
   predicted.

5. **The `no_source_pdf` set is 66 documents, not 9.** Every one was checked against disk and all
   66 are genuinely sourceless (0 have a `source.*` file). The research report's "9" is the subset
   traceable to this task's original Group B; the index-wide population carrying the
   citable-by-default value is roughly seven times larger. The decision memo must state the real
   number.

6. **127 entries carry no `provenance_fidelity` at all** and therefore fail open to
   `unverified_summary`, which *is* quarantined. Current index-wide histogram:
   `verified_conversion` 125, none 127, `no_source_pdf` 66, `unadjudicated` 2,
   `not_yet_converted` 1.

7. **There is a second `unadjudicated` document**: `gabbay_1994` (`word_ratio` 0.11, no source on
   disk), not previously reported alongside `arisakadasstrassburger_2015`.

8. **`chagrovzakharyaschev_1997_modallogic` is already `verified_conversion`** with `word_ratio`
   1.0209, and default no-flag search already returns it non-degraded. Phase 6's chagrov work is
   verification and close-out, not classification.

9. **The only live `.sources-recovered/` references outside this task's own specs artifacts are
   documentation**, not code: `specs/literature/SOURCES.md:60`. Neither working-tree script
   references it; the `HEAD` audit script references it only inside the `--legacy-schema` mode.

### Prior Plan Reference

Supersedes `plans/01_fidelity-key-derivation-and-legacy-audit.md`. Phases 1-5 are carried forward
verbatim in substance and remain `[COMPLETED]`; only Phases 6-7 are rewritten.

### Roadmap Alignment

No `roadmap_path` was provided in the delegation context; no ROADMAP.md consultation performed.

## Goals & Non-Goals

**Goals**:

- Restore the working tree to the committed Phase 1-5 state so that any verification result is
  attributable to the corpus rather than to an unexplained uncommitted revert.
- Close out the former Phase 6 DJVU gate on the evidence that it is moot: confirm
  `chagrovzakharyaschev_1997_modallogic` is classified and default-search-visible via its
  `source.pdf`, and record that no install and no authorization were needed.
- Repoint every actionable `.sources-recovered/` reference at the canonical
  `sources/<doc_id>/source.{pdf,djvu}` layout, or mark it as historical.
- Re-adjudicate `arisakadasstrassburger_2015` mechanically through whichever audit mode its current
  schema actually selects, and record the honest outcome whatever it is.
- Verify that default no-flag `literature-search.sh` returns non-degraded results for the documents
  Phase 6 touches.
- Produce a decision memo that gives the user everything needed to decide the Group B disposition:
  the restated (b)/(c)/(d) options with concrete measured costs, the Group A regression, and an
  explicit statement that `no_source_pdf` is currently citable by default.

**Non-Goals**:

- Choosing the Group B disposition. The task description explicitly forbids resolving it
  unilaterally, and Phase 7 is a write-up, not a decision.
- Stamping any `provenance_fidelity` value on any of the 66 `no_source_pdf` documents, on the 127
  unstamped documents, or on `gabbay_1994`.
- Restoring Group A's `ocr_rescanned_reflowed_partial_symbol_loss` values. This reverses another
  repository's deliberate commit and is surfaced in the memo, not actioned.
- Any edit to `QUARANTINED_FIDELITY_VALUES` (`literature-search.sh:53`), in either direction.
- Loosening `RATIO_THRESHOLD` (0.75) or `PROOF_ADEQUACY_THRESHOLD` (0.6), or hand-stamping a better
  value, to make `arisakadasstrassburger_2015` pass.
- Installing `djvulibre` system-wide, hardcoding the nix store path, or any OCR/rasterization
  workaround. None is needed.
- Deciding whether the now-no-op Phase 1 fix and `--legacy-schema` mode should be retired as dead
  code. That is surfaced in the memo as a finding.
- Any change to `Cslib/` or any Lean source, or to any repository file outside
  `.claude/scripts/literature-search.sh` and `.claude/scripts/literature-fidelity-audit.sh` (plus
  this task's own `specs/555_.../` artifacts).

### File scope discipline

| Path | Classification | Permitted in this plan |
|------|----------------|------------------------|
| `.claude/scripts/literature-search.sh` | repo source | Yes — restore-from-HEAD only (Phase 6) |
| `.claude/scripts/literature-fidelity-audit.sh` | repo source | Yes — restore-from-HEAD only (Phase 6) |
| `specs/555_literature_search_fidelity_schema_quarantine/**` | task artifacts | Yes |
| `$LITERATURE_DIR/index.json` | **data, NOT repo source** | Phase 6 only, via the audit script's own backed-up write path |
| `specs/literature/SOURCES.md` | repo doc | Documentation-only annotation (Phase 6) |
| `Cslib/`, any `.lean` file | out of scope | **No** |

`$LITERATURE_DIR/index.json` lives in a different repository and is not tracked by this one. It is
**data**, not repo source. Phase 6 is the only phase permitted to cause a write to it, and only
through `literature-fidelity-audit.sh`'s existing backup-and-`cmp` path. Phase 7 must cause no
write to it at all.

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Restoring the scripts from HEAD discards a deliberate concurrent-session revert | H | M | Take `bash .claude/scripts/git-snapshot.sh 555 --no-revert` first, which preserves the working-tree state as a durable patch before any `git checkout HEAD -- <path>`. The revert is then recoverable, and the finding is surfaced in the Phase 7 memo for the user to decide deliberately. |
| Destructive-git guard blocks the restore | M | H | `git checkout -- <path>` on a dirty tree is forbidden by `.claude/rules/git-workflow.md` and blocked by `guard-destructive-git.sh` without a fresh snapshot. The snapshot in Phase 6 task 1 is a hard prerequisite, not a precaution. |
| Implementer treats `arisakadasstrassburger_2015`'s low ratio as a bug and adjusts thresholds | H | M | The ratio is measured at 0.5148/0.5128 under both candidate modes and is stated in this plan as the expected, honest result. Threshold changes are an explicit Non-Goal; Phase 6 verification asserts both constants are unchanged. |
| Implementer runs `--legacy-schema` for arisaka, gets an empty enumeration, and concludes failure | M | H | Phase 6 task 4 makes mode determination an explicit measured step with a decision table. Zero legacy entries is the documented expected result, not an error. |
| Phase 7 drifts into resolving the disposition | H | M | Phase 7 has an explicit MUST NOT, produces only a memo, modifies no data file, and its verification asserts `index.json` is byte-identical before and after and that `QUARANTINED_FIDELITY_VALUES` is unchanged. |
| A Phase 6 `--write` clobbers an honestly-stamped entry, as in Phase 4 | H | L | The `SIX_VALUE_ENUM` guard added in Phase 4 is restored along with the script. Phase 6 snapshots `index.json` to the scratchpad and diffs entry-by-entry, asserting the changed set is exactly the intended document. |
| The memo understates blast radius by repeating the report's "9 documents" | M | M | The measured figure is 66 genuinely-sourceless `no_source_pdf` documents plus 127 unstamped. Phase 6 re-measures both immediately before the memo is written so the numbers are current at hand-off. |
| `.sources-recovered/` repointing is treated as code work when no code references it | L | M | Verified: neither working-tree script references it; only `specs/literature/SOURCES.md:60` and this task's own historical artifacts do. Phase 6 task 3 scopes the work to a documentation annotation and an explicit re-verification after the HEAD restore reintroduces the audit script's legacy-mode reference. |

## Implementation Phases

**Dependency Analysis**:

| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2 | 1 |
| 3 | 3 | 2 |
| 4 | 4 | 3 |
| 5 | 5 | 4 |
| 6 | 6 | 5 |
| 7 | 7 | 6 |

Phases within the same wave can execute in parallel. Waves 1-5 are complete.

Phases 1-2 constituted Stage A and Phases 3-5 Stage B, both committed. Phases 6-7 constitute
Stage C: Phase 6 is mechanical close-out that may write data, Phase 7 is a pure write-up that
writes none. Commit at the end of each.

---

### Phase 1: Four-site key-derivation fix in literature-search.sh [COMPLETED]

- **Goal:** `load_fidelity_map()` builds keys from `doc_id` when `path` is not a `sources/`-prefixed
  string, at all four sites, with the `sources/` behavior unchanged.
- **Tasks:**
  - [x] Capture a pre-change baseline of the fidelity map and record `old keys: 95`.
        *(completed: old 95)*
  - [x] At `literature-search.sh:227`, replace the `continue`-on-non-`sources/`-path guard with the
        two-branch form: if `path` is a string starting with `sources/`, derive `dirname` and
        `fmap.setdefault(dirname, pf)` then `continue`; otherwise read `doc_id` and, if it is a
        non-empty string, `fmap.setdefault(doc_id, pf)`. *(completed)*
  - [x] Apply the byte-identical logic change at lines ~527, ~764, and ~908. *(completed: applied
        via single replace_all edit across all 4 byte-identical sites)*
  - [x] Extend the line-227 docstring to describe the dual-key behavior. *(completed)*
  - [x] Add a one-line note to each of the three secondary "see the primary do_search heredoc"
        comments that the `doc_id` fallback branch exists. *(completed)*
  - [x] Confirm `get_fidelity()` is untouched at all four sites. *(completed: grep confirms 4
        byte-identical occurrences of `fmap.get(doc_id) or "unverified_summary"`)*
- **Timing:** 45 minutes
- **Depends on:** none
- **Files modified:**
  - `.claude/scripts/literature-search.sh` - `load_fidelity_map()` body at 4 sites + docstring
- **Verification:** Map-diff harness reported `old 95 new 97`; `added` was exactly
  `['simpson_1994_intuitionisticmodallogic', 'wijesekera_1990_constructivemodallogicsi']`;
  `removed` and `changed` both empty. Committed at `63bf5184`.

  Note for Phase 6: against the *current* `index.json` this same harness now reports
  `old 127 / new 127`, `added: []`. The fix is correct and unchanged; the corpus moved underneath
  it. See "Corrections established at revision time" item 2.

---

### Phase 2: Group A end-to-end verification and fail-open regression [COMPLETED]

- **Goal:** Default (no-flag) search returns non-degraded, correctly-stamped results for the two
  Group A documents, and every Group B document plus every unknown `doc_id` still fail-opens to
  `unverified_summary`.
- **Tasks:**
  - [x] Run the Group A default-search checks and record `degraded`, `fallback_tier`, and per-result
        `provenance_fidelity`. *(completed: both Wijesekera and Simpson queries returned
        degraded=false, fallback_tier=bm25,
        provenance_fidelity=ocr_rescanned_reflowed_partial_symbol_loss. Also uncovered and fixed a
        real regression: the new docstring used markdown backticks inside the unquoted `<< PYEOF`
        heredoc, which bash expanded as command substitution, spewing "command not found" to stderr
        on every do_search call. Removed the backticks; stderr clean on rerun.)*
  - [x] Run the `--include-unverified` check and confirm the result set is a superset with the same
        Group A fidelity values. *(completed)*
  - [x] Confirm Group B documents still report `unverified_summary` under `--include-unverified` and
        are still absent from default search. *(completed: arisakadasstrassburger_2015 and
        marinmoralesstrassburger_2021 both still unverified_summary under the flag)*
  - [x] Exercise the `do_read` and `do_toc` sites so all four patched heredocs execute at least once.
        *(completed: --toc and --read both exercised cleanly, no stderr)*
  - [x] Commit Stage A. *(completed at `63bf5184`: `task 555 phase 2: restore legacy-schema fidelity
        key derivation`)*
- **Timing:** 30 minutes
- **Depends on:** 1
- **Files modified:** None (verification and commit only)
- **Verification:** Both default searches reported `"degraded": false` and `"fallback_tier": "bm25"`
  with the correct Group A fidelity values; Group B rows still read `unverified_summary`; `--toc`
  exited 0.

---

### Phase 3: --legacy-schema classification mode (read-only) [COMPLETED]

- **Goal:** `literature-fidelity-audit.sh --legacy-schema --dry-run` classifies the 18 legacy-schema
  entries and reproduces the report's hand-computed ratios, with default-mode output bit-for-bit
  unchanged.
- **Tasks:**
  - [x] Capture the pre-change default-mode baseline. *(completed: reconstructed the pre-edit file
        verbatim from the research-phase full read since the file predated any git-tracked commit;
        ran --dry-run, got 97 directories)*
  - [x] Add `--legacy-schema` to the argument loop and export a `LEGACY_SCHEMA` env var into the
        python heredoc, keeping `--dry-run`/`--write` orthogonal. *(completed)*
  - [x] Relax the startup guards for legacy mode. *(completed)*
  - [x] Add `enumerate_legacy_entries(idx)`: select entries where `doc_id` and `chunks_dir` are both
        present AND `path` is absent-or-null AND `id` is absent-or-null. *(completed)*
  - [x] Add `classify_legacy(entry)`: resolve the source, compute `pdf_words` via
        `pdf_word_count()`, compute `md_words` by summing `word_count_text()` over ALL `chunk_*.md`
        in `chunks_dir`. Reuse `disclosure_check()` and the proof-completeness path unchanged.
        *(completed)*
  - [x] Classify a legacy entry with no recovered source as `no_source_pdf` and one whose
        `pdf_word_count` returns 0 (DJVU) as `unadjudicated` with an explicit blocked-reason note.
        *(completed: tracked via a `djvu_blocked` flag distinct from the `frac is None`
        unadjudicated path)*
  - [x] Print the legacy report to stdout in the same TSV shape as default mode, keyed by `doc_id`.
        *(completed: factored the print/summary loop into a shared print_report())*
- **Timing:** 1.5 hours
- **Depends on:** 2
- **Files modified:**
  - `.claude/scripts/literature-fidelity-audit.sh` - arg parsing, startup guards, legacy enumeration
    and classification functions, report printing
- **Verification:** `DEFAULT MODE UNCHANGED` printed (empty diff). Legacy report listed 18 rows and
  reproduced all five hand-computed ratios within tolerance.

  Note for Phase 6: the startup guard added here requires `$LITERATURE_DIR/.sources-recovered/`,
  and `classify_legacy()` resolves sources from it. That directory is now empty and the legacy gate
  now matches 0 entries. This is the reference Phase 6 task 3 must repoint or mark historical.

---

### Phase 4: --legacy-schema write path with strict schema gating [COMPLETED]

- **Goal:** `--legacy-schema --write` stamps `provenance_fidelity` and `word_ratio` onto matched
  legacy entries by `doc_id` equality, and provably touches zero `sources/`-schema entries.
- **Tasks:**
  - [x] Snapshot the index before writing. *(completed)*
  - [x] Add `resolve_legacy_targets(idx, doc_id)`; never call `resolve_targets()` in legacy mode.
        *(completed)*
  - [x] Route the write loop by mode so the two write paths never interleave. *(completed: split
        into main_default()/main_legacy(), dispatched from main())*
  - [x] Confirm the existing backup-and-`cmp` step runs before the legacy write. *(completed:
        unchanged, mode-independent)*
  - [x] Stamp only entries whose computed value is a real classification; report `no_source_pdf` and
        the DJVU `unadjudicated` rows explicitly rather than silently skipping. *(completed. Also
        caught and fixed a real regression: the first write attempt clobbered Group A's
        pre-existing `ocr_rescanned_reflowed_partial_symbol_loss` with the generic detector's
        `verified_conversion`, producing 7 changed entries instead of the expected <=6. Restored
        Group A from the pre-write snapshot and added a `SIX_VALUE_ENUM` guard: any legacy entry
        whose current `provenance_fidelity` is already outside this script's six-value enum is left
        untouched and reported as "already honestly stamped".)*
  - [x] Run `--legacy-schema --write` twice to confirm idempotency. *(completed: first write stamped
        5/5 changed; second reported changed: 0, unchanged: 5)*
  - [x] Record the outcome for `arisakadasstrassburger_2015` without adjusting thresholds.
        *(completed: landed on `unadjudicated`, word_ratio 0.539 — a quarantined value. Recorded
        as-is; thresholds untouched.)*
  - [x] Commit. *(completed at `335c034a`: `task 555 phase 4: add legacy-schema mode to fidelity
        audit`)*
- **Timing:** 1.25 hours
- **Depends on:** 3
- **Files modified:**
  - `.claude/scripts/literature-fidelity-audit.sh` - legacy target resolution and mode-routed write
  - `$LITERATURE_DIR/index.json` - **data, not repo source**; 5 legacy entries stamped, backed up
    first to `index.json.bak.<ts>` by the script's own safety mechanism
- **Verification:** 5 changed entries, every one `legacy=True`, `NON-LEGACY TOUCHED: []`, idempotent
  on rerun.

---

### Phase 5: Post-stamp search verification for the recoverable documents [COMPLETED]

- **Goal:** Documents stamped with a non-quarantined value surface in default search; documents that
  landed on a quarantined value provably do not.
- **Tasks:**
  - [x] Run a default search targeting each newly-`verified_conversion` document. *(completed: all 4
        queries returned degraded=false, fallback_tier=bm25, provenance_fidelity=verified_conversion)*
  - [x] Confirm any document left at a quarantined value is still absent from default search and
        still visible under `--include-unverified`. *(completed: arisakadasstrassburger_2015 absent
        from default search, present as unadjudicated under the flag)*
  - [x] Re-run the Phase 1 map-diff harness. *(completed: old 95, new 102; added = the 2 Group A
        docs + 5 newly-stamped Group B docs; removed and changed both empty)*
  - [x] Write the implementation summary to `summaries/01_fidelity-key-derivation-summary.md`,
        stating explicitly which documents remain quarantined and why. *(completed)*
  - [x] Commit. *(completed)*
- **Timing:** 30 minutes
- **Depends on:** 4
- **Files modified:**
  - `specs/555_literature_search_fidelity_schema_quarantine/summaries/01_fidelity-key-derivation-summary.md` - new
- **Verification:** Each query returned `"degraded": false` with the corresponding document carrying
  `"verified_conversion"`; quarantined documents correctly absent.

---

### Phase 6: Blocker close-out — restore working tree, adjudicate, repoint [COMPLETED]

- **Goal:** The former Phase 6 gate is closed on the evidence that it is moot; the working tree
  matches its committed state; `arisakadasstrassburger_2015` has been re-adjudicated through the
  audit mode its current schema actually selects; every actionable `.sources-recovered/` reference
  is repointed or marked historical; and default no-flag `literature-search.sh` returns
  non-degraded results for the documents touched.
- **Tasks:**

  **6.1 — Restore the working tree to its committed state (hard prerequisite).**
  - [x] Confirm the divergence still exists: `git status --short` lists both scripts as modified and
        `git diff --stat` against HEAD shows the `--legacy-schema` mode and all four `doc_id`
        fallback branches removed. If the tree is already clean at HEAD, skip to 6.2 and record that.
        *(completed: confirmed 43 insertions/357 deletions against HEAD 335c034a before restore)*
  - [x] Take a durable snapshot **before** any restore:
        `bash .claude/scripts/git-snapshot.sh 555 --no-revert`. Use `--no-revert` — work continues
        after this point and the tree must not be reverted out from under it. This is required, not
        optional: `git checkout -- <path>` on a dirty tree is forbidden by
        `.claude/rules/git-workflow.md` and blocked by `guard-destructive-git.sh` without a fresh
        snapshot. Record the reported patch path. *(completed: patch at
        specs/555_literature_search_fidelity_schema_quarantine/working-progress-1785112536.patch,
        stash@{0}, untracked-backup-1785112536/; tree left unchanged per --no-revert)*
  - [x] Restore both scripts from the committed Phase 1-5 state:
        `git checkout HEAD -- .claude/scripts/literature-search.sh .claude/scripts/literature-fidelity-audit.sh`.
        Rationale: HEAD is the committed record of completed work, the revert is uncommitted and
        unexplained, and restoring is reversible from the snapshot. Do **not** interpret this as a
        judgement that the code should be kept — that question goes in the Phase 7 memo.
        *(completed)*
  - [x] Confirm the restore: `bash -n` clean on both, `grep -c 'doc_id = e.get("doc_id")'` returns
        4, and `grep -c -i legacy` on the audit script returns a non-zero count. *(completed: both
        bash -n clean, doc_id fallback count 4, legacy grep count 40)*

  **6.2 — Close out the chagrovzakharyaschev classification using the already-present source.pdf.**
  - [x] Record the disposition of the former gate in writing: `source.pdf` (53,951,887 bytes) sits
        beside `source.djvu`; `pdftotext` is on PATH and is already the audit script's extractor;
        the `.djvu` branch is never reached for this document. **No install and no user
        authorization are required.** *(completed: verified directly — source.pdf and source.djvu
        both present under sources/chagrovzakharyaschev_1997_modallogic/; pdftotext resolves via
        `which pdftotext`)*
  - [x] Record that the old gate check was a false negative: `command -v djvutxt` tests PATH, not
        classifiability. Do not re-use it as a verification. *(completed)*
  - [x] Confirm from `index.json` that the entry reads `provenance_fidelity: verified_conversion`
        with `word_ratio: 1.0209` and now carries `path`/`id` (i.e. it is a `sources/`-schema entry).
        *(completed: confirmed exactly — path="sources/chagrovzakharyaschev_1997_modallogic/",
        id set, provenance_fidelity=verified_conversion, word_ratio=1.0209)*
  - [x] Do **not** install `djvulibre`, do **not** hardcode the nix store path (it has no gcroot and
        is garbage-collectable), and do **not** attempt any OCR or rasterization workaround. If a
        `.djvu` path is ever wanted later, `nix-shell -p djvulibre` is a user-level ephemeral shell
        — note it as an option, take no action. *(completed: no install performed, no path
        hardcoded)*

  **6.3 — Repoint or historicize `.sources-recovered/` references.**
  - [x] Re-run the reference sweep after the 6.1 restore, since the restore reintroduces the audit
        script's legacy-mode references:
        `grep -rn 'sources-recovered' --include='*.sh' --include='*.md' .`
        *(completed: only literature-fidelity-audit.sh (4 code/comment sites) and
        specs/literature/SOURCES.md:60 plus this task's own historical artifacts and task
        554's historical handoffs/plans reference it)*
  - [x] In `.claude/scripts/literature-fidelity-audit.sh`, update the `--legacy-schema` startup
        guard and `classify_legacy()`'s source resolution to prefer
        `$LITERATURE_DIR/sources/<doc_id>/source.{pdf,djvu}`, falling back to
        `.sources-recovered/<doc_id>.{pdf,djvu}` only if present. The startup guard must no longer
        hard-fail on an absent-or-empty `.sources-recovered/`; with the migration complete it is
        expected to be empty. Update the header comment block to match. *(completed: startup guard
        now emits a `[fidelity-audit] Note:` instead of exiting 1;
        classify_legacy() tries sources/<doc_id>/source.{pdf,djvu} first, then
        RECOVERED_DIR/<doc_id>.{pdf,djvu}; header comments and usage text updated to match)*
  - [x] Annotate `specs/literature/SOURCES.md:60` to note that the recovered sources were migrated
        into `sources/<doc_id>/` and that `.sources-recovered/` is now empty. Documentation change
        only — do not restructure the file. *(completed)*
  - [x] Leave the historical references inside
        `specs/555_.../reports/01_*.md` and `plans/01_*.md` untouched. They are an accurate record
        of the state at the time they were written; rewriting history is not repointing.
        *(completed: not touched)*

  **6.4 — Re-adjudicate `arisakadasstrassburger_2015` through the correct mode.**
  - [x] Determine the mode from the entry's actual schema rather than assuming. Read its
        `path`, `id`, `chunks_dir` from `index.json` and apply this table:

        | Entry shape | Mode to run |
        |---|---|
        | `path` and `id` present (measured: this is the current shape) | **default mode** (`--dry-run` / `--write`) |
        | `doc_id` + `chunks_dir` only, `path`/`id` absent | `--legacy-schema` |

        *(completed: entry carries path="sources/arisakadasstrassburger_2015_.../",
        id set, chunks_dir set -- default mode selected)*
  - [x] Run `bash .claude/scripts/literature-fidelity-audit.sh --legacy-schema --dry-run` once and
        record that it enumerates **0 entries**. This is the documented expected result of the
        migration, **not a failure** — record it and move on. It is the evidence that
        `--legacy-schema` cannot be the vehicle for this re-adjudication. *(completed: ran, printed
        "Total directories: 0", exit 0)*
  - [x] Snapshot the index to the scratchpad before any write:
        `cp "$LITERATURE_DIR/index.json" "$SCRATCH/index.before-phase6.json"`. *(completed)*
  - [x] Run the default-mode audit and capture the `arisakadasstrassburger_2015` row. Then run
        `--write`. `$LITERATURE_DIR/index.json` is **data, not repo source** — this write goes
        through the script's existing backup-and-`cmp` path, which produces a timestamped
        `index.json.bak.<ts>`. *(completed: dry-run captured
        unadjudicated/0.539/md_words=10012/pdf_words=18575; --write ran, backup verified,
        190 entries stamped, 8 changed / 182 unchanged)*
  - [x] Record the honest outcome. **The expected result is that it stays quarantined.** Measured at
        revision time: `pdftotext` yields 19,439 words, the whole-document `.md` yields 10,007
        (ratio 0.5148), the chunk sum yields 9,968 (ratio 0.5128) — both far below
        `RATIO_THRESHOLD` (0.75) and consistent with the stored 0.539. Only the disclosure /
        proof-completeness escape path could change the verdict; measure it, do not predict it.
        *(completed: re-measured via the audit script itself rather than the plan's hand-computed
        figures -- md_words=10012, pdf_words=18575, ratio=0.539, exactly matching the pre-existing
        stored value; provenance_fidelity remained unadjudicated after --write. Confirmed
        quarantined: honest outcome, no threshold or value change.)*
  - [x] Do **not** adjust `RATIO_THRESHOLD` or `PROOF_ADEQUACY_THRESHOLD`, and do **not** hand-stamp
        a better value, to make this document surface. A quarantined outcome here is a correct
        outcome. *(completed: both constants confirmed unchanged, 0.75 and 0.6 respectively)*
  - [x] Diff `index.json` entry-by-entry against `$SCRATCH/index.before-phase6.json` and assert the
        changed set contains no document other than `arisakadasstrassburger_2015`. In particular
        assert Group A (`wijesekera_1990`, `simpson_1994`) is untouched by this run — the
        `SIX_VALUE_ENUM` guard restored in 6.1 is what prevents a repeat of the Phase 4 clobber.
        *(completed: entry-by-entry diff computed. `arisakadasstrassburger_2015` itself did not
        change (unadjudicated/0.539 before and after — it was already stamped, so it is absent from
        the diff, not present-and-identical). Group A confirmed byte-identical before/after.
        DEVIATION: the diff surfaced 8 changed entries not anticipated by the plan --
        burgess_1984_sec01..sec08, all remaining `verified_conversion` with word_ratio drifting
        from 1.0041 to 1.0033 (a ~0.08% shift, no value-class change). This is an incidental
        side effect of `--write` recomputing the full sources/ corpus (not scoped to arisaka alone
        — the script has no single-document mode), most likely from minor pdftotext/whitespace
        extraction non-determinism between runs. No provenance_fidelity value changed anywhere in
        the corpus. Recorded here and in the Phase 7 memo as a residual finding; not actioned per
        the Non-Goals (no threshold/value hand-editing).)*

  **6.5 — Re-measure the figures the Phase 7 memo depends on.**
  - [x] Re-count, immediately before Phase 7 so the memo's numbers are current: the number of
        entries stamped `no_source_pdf` (measured at revision time: **66**, all verified genuinely
        sourceless), the number with no `provenance_fidelity` at all (**127**), the number
        `unadjudicated` (**2**: `arisakadasstrassburger_2015` and `gabbay_1994`), and the full
        fidelity histogram. *(completed: re-measured directly against the post-write index --
        no_source_pdf=66 (0/66 have a source.* file, verified by directory listing),
        no-provenance_fidelity=127, unadjudicated=2 (arisakadasstrassburger_2015, gabbay_1994),
        verified_conversion=125, not_yet_converted=1; massacci_2000 confirmed
        verified_conversion with source.pdf present, i.e. left the unrecoverable set)*
  - [x] Commit Stage C part 1. Scope: the two scripts, `specs/literature/SOURCES.md`, this plan
        file, and the task directory. Message:
        `task 555 phase 6: close djvu gate, repoint recovered-source paths, re-adjudicate arisaka`.
        *(completed)*

- **Timing:** 1.5 hours
- **Depends on:** 5
- **Files to modify:**
  - `.claude/scripts/literature-search.sh` - restore from HEAD only (6.1)
  - `.claude/scripts/literature-fidelity-audit.sh` - restore from HEAD (6.1), then repoint source
    resolution and startup guard away from `.sources-recovered/` (6.3)
  - `specs/literature/SOURCES.md` - documentation annotation only (6.3)
  - `$LITERATURE_DIR/index.json` - **data, not repo source**; at most one entry re-stamped (6.4)
- **Verification:**
  ```bash
  cd /home/benjamin/Projects/cslib
  LIT="${LITERATURE_DIR:-$HOME/Projects/Literature}"

  # 6.1 restore landed
  bash -n .claude/scripts/literature-search.sh
  bash -n .claude/scripts/literature-fidelity-audit.sh
  grep -c 'doc_id = e.get("doc_id")' .claude/scripts/literature-search.sh   # expect: 4
  grep -c 'fmap.get(doc_id) or "unverified_summary"' .claude/scripts/literature-search.sh  # expect: 4

  # 6.3 no code path still hard-depends on .sources-recovered/
  grep -n 'sources-recovered' .claude/scripts/literature-fidelity-audit.sh
  bash .claude/scripts/literature-fidelity-audit.sh --legacy-schema --dry-run   # must exit 0

  # 6.5 default no-flag search is non-degraded for the documents Phase 6 touches
  for q in "Chagrov Zakharyaschev modal logic" \
           "constructive modal logic Wijesekera" \
           "Simpson proof theory modal logic"; do
    echo "== $q"
    bash .claude/scripts/literature-search.sh "$q" 5 \
      | jq -c '{degraded, fallback_tier, hits: [.results[] | {doc_id, provenance_fidelity}]}'
  done

  # arisaka: absent from default search if it stayed quarantined, visible under the opt-in flag
  bash .claude/scripts/literature-search.sh "nested sequents constructive modal logics" 5 \
    | jq -c '{degraded, hits: [.results[] | {doc_id, provenance_fidelity}]}'
  bash .claude/scripts/literature-search.sh --include-unverified "nested sequents constructive modal logics" 5 \
    | jq -r '.results[] | "\(.doc_id)\t\(.provenance_fidelity)"'

  # thresholds and quarantine constant untouched
  grep -n 'RATIO_THRESHOLD\s*=\|PROOF_ADEQUACY_THRESHOLD\s*=' .claude/scripts/literature-fidelity-audit.sh
  grep -n 'QUARANTINED_FIDELITY_VALUES=' .claude/scripts/literature-search.sh
  ```
  Expected: both scripts pass `bash -n`; both greps on `literature-search.sh` return 4;
  `--legacy-schema --dry-run` exits 0 and reports 0 entries rather than erroring on an empty
  `.sources-recovered/`; the three default searches all report `"degraded": false` with
  `chagrovzakharyaschev_1997_modallogic`, `wijesekera_1990_constructivemodallogicsi`, and
  `simpson_1994_intuitionisticmodallogic` present and carrying a non-quarantined value.
  `arisakadasstrassburger_2015` absent from default search and present under
  `--include-unverified` is a **pass**, not a failure. `RATIO_THRESHOLD` is still 0.75,
  `PROOF_ADEQUACY_THRESHOLD` still 0.6, and `QUARANTINED_FIDELITY_VALUES` still reads
  `"unverified_summary unverified_no_baseline unadjudicated"`.

---

### Phase 7: Decision memo — write up and surface, decide nothing [COMPLETED]

- **Goal:** Produce a single decision memo that gives the user everything needed to decide the
  Group B disposition, the Group A regression, and the residual findings.

  **This phase is a write-up, not a decision.** The task description explicitly forbids resolving
  the Group B disposition unilaterally. The implementer **MUST NOT** choose an option, **MUST NOT**
  stamp any `provenance_fidelity` value on any document, **MUST NOT** edit
  `QUARANTINED_FIDELITY_VALUES`, and **MUST NOT** cause any write to `$LITERATURE_DIR/index.json`.
  The deliverable is prose plus measurements, nothing else.

- **Deliverable:** `specs/555_literature_search_fidelity_schema_quarantine/summaries/02_group-b-decision-memo.md`
- **Tasks:**

  **7.1 — State the reversed premise up front.**
  - [x] Open the memo with the single most consequential fact: `no_source_pdf` is **not** on
        `QUARANTINED_FIDELITY_VALUES`, so **every document stamped with it is currently returned by
        default no-flag search, non-degraded, with no signal to the caller that no source exists.**
        State this plainly and early — it is currently live and unannounced. *(completed: memo
        section 1)*
  - [x] Give the measured blast radius from Phase 6.5, not the research report's figure: **66**
        documents stamped `no_source_pdf`, all verified genuinely sourceless (0 of 66 have a
        `source.*` file on disk). Note that the report's "9" was the subset traceable to this task's
        original Group B, and that the index-wide population is roughly seven times larger.
        *(completed: memo section 1)*
  - [x] Record the full current fidelity histogram and note that **127** entries carry no
        `provenance_fidelity` at all and therefore fail open to `unverified_summary`, which *is*
        quarantined. *(completed: memo section 1 table)*
  - [x] Record that `massacci_2000_single_step_tableaux_for_modal_logics` has **left** the set — it
        has a `source.pdf` and is stamped `verified_conversion` — so the remaining set contains
        nothing referenced by this repository's `specs/literature-index.json`. *(completed: memo
        section 1)*

  **7.2 — Restate options (b), (c), (d) against the current state, with concrete costs.**
  - [x] **Option (b) — stamp `unverified_no_baseline` on the sourceless set.** Files changed:
        `$LITERATURE_DIR/index.json` only (data, not repo source; a few `jq` edits). Effect: this is
        now a **rollback of live behavior**, not a no-op — it removes these documents from default
        search, since `unverified_no_baseline` is quarantined. Downstream: reachable only via
        `--include-unverified`. Citation risk: minimal; most conservative option. State the scope
        decision the user must also make: apply to the 9 originally in scope, or to all 66.
        *(completed: memo section 2)*
  - [x] **Option (c) — a non-quarantined value meaning "converted, no obtainable baseline."** Files
        changed: **none required — this is already the operative state** via `no_source_pdf`.
        Formalizing it means documenting `no_source_pdf` as a deliberate non-quarantined value in
        `literature-search.sh` and the audit script header. Downstream: `literature-search.sh`
        default search, `literature-briefing.sh` corpus selection, and every `--lit` briefing treat
        all 66 as citable. Citation risk: **high** — an agent citing one of these has no source
        against which any claim can be checked, which is precisely the failure mode the quarantine
        mechanism exists to prevent. *(completed: memo section 2)*
  - [x] **Option (d) — leave as-is.** Files changed: none. State explicitly that **(d) has changed
        meaning since it was first written**: "as-is" now means *citable in default search*, not
        *quarantined*. Substantively identical to accepting (c). Flag this plainly — a user who
        picks (d) believing it is the status-quo-conservative choice would be mistaken. *(completed:
        memo section 2)*
  - [x] Be explicit that no code in this repository caused the current state: `no_source_pdf` was
        always in the audit script's six-value enum, `QUARANTINED_FIDELITY_VALUES` was never edited,
        and the stamping was done by the Literature repo's `bb3bf18`. *(completed: memo section 2
        opening paragraph)*
  - [x] Present the options neutrally. Do **not** recommend one, and do **not** mark one as the
        default. *(completed: memo explicitly states no option is recommended or defaulted)*

  **7.3 — Write up the Group A regression as a separate decision item.**
  - [x] Report that Literature commit `bb3bf18` overwrote `wijesekera_1990_constructivemodallogicsi`
        and `simpson_1994_intuitionisticmodallogic` from `ocr_rescanned_reflowed_partial_symbol_loss`
        to `verified_conversion` (current `word_ratio` 0.9922 and 0.9828 respectively), losing the
        partial-symbol-loss warning that a citing agent previously received. *(completed: memo
        section 3 table)*
  - [x] State the fix cost honestly: 2 `jq` edits to `$LITERATURE_DIR/index.json` (data, not repo
        source), and nothing else. *(completed: memo section 3)*
  - [x] State the reason it is surfaced rather than actioned: it **reverses another repository's
        deliberate commit**. Both documents now have real source PDFs, so `verified_conversion` is
        arguably computable; what was lost is the explicit warning, not the ratio. *(completed:
        memo section 3)*
  - [x] Note that this task's Phase 4 `SIX_VALUE_ENUM` guard works but only constrains
        `literature-fidelity-audit.sh`; `bb3bf18` wrote by another route and bypassed it. If the
        user wants durable protection, that is a separate piece of work in the Literature repo, not
        here. *(completed: memo section 3, "Durability gap" paragraph)*

  **7.4 — Record the residual findings that need no decision but must not be lost.**
  - [x] The former Phase 6 DJVU gate is **closed, not waived**: `source.pdf` made it moot, no
        install and no authorization were needed, and the old `command -v djvutxt` check was a false
        negative. *(completed: memo section 4)*
  - [x] `arisakadasstrassburger_2015` — report the Phase 6.4 outcome and the measured ratios
        (0.5148 whole-document, 0.5128 chunk-sum, against a 0.75 threshold). If it remained
        quarantined, say so plainly and state that this is the honest verdict: the markdown really
        does contain about half the source's words. Note it is the only modal-logic document still
        quarantined and the one the task description called out as central, so the user may want to
        re-convert the source rather than re-adjudicate it — but do not do so here. *(completed:
        memo section 4 reports the Phase 6.4 re-measured figures — md_words 10,012 / pdf_words
        18,575 / ratio 0.539, essentially unchanged from the plan's earlier hand-computed figures —
        and states the quarantined outcome plainly)*
  - [x] `gabbay_1994` is a second `unadjudicated` document (`word_ratio` 0.11, no source on disk),
        not previously reported. *(completed: memo section 4)*
  - [x] `$LITERATURE_DIR/.sources-recovered/` is empty; sources live at
        `sources/<doc_id>/source.{pdf,djvu}`. Record what Phase 6.3 repointed. *(completed: memo
        section 4)*
  - [x] **The Phase 1-5 code is now a functional no-op.** The `doc_id` fallback adds 0 keys against
        the current index (`old 127 / new 127`, `added: []`) and the legacy gate matches 0 of 321
        entries, because the migration gave every former legacy entry a `sources/`-prefixed `path`.
        Report the uncommitted working-tree revert that Phase 6.1 restored, and put the question to
        the user: **keep the code as defensive coverage for any future legacy-schema ingest, or
        retire it deliberately as dead code?** Do not answer it. *(completed: memo section 4;
        question posed, not answered)*

  **7.5 — Close out.**
  - [x] Write the round-2 implementation summary to
        `specs/555_literature_search_fidelity_schema_quarantine/summaries/02_blocker-resolution-summary.md`,
        covering Phase 6's actions and pointing at the memo for the open decisions. *(completed)*
  - [x] Commit Stage C part 2. Scope: the task directory only. Message:
        `task 555 phase 7: write Group B decision memo and round-2 summary`. *(completed)*

- **Timing:** 1.5 hours
- **Depends on:** 6
- **Files to modify:**
  - `specs/555_literature_search_fidelity_schema_quarantine/summaries/02_group-b-decision-memo.md` - new
  - `specs/555_literature_search_fidelity_schema_quarantine/summaries/02_blocker-resolution-summary.md` - new
  - **No script changes. No `index.json` write. No fidelity value stamped.**
- **Verification:**
  ```bash
  cd /home/benjamin/Projects/cslib
  LIT="${LITERATURE_DIR:-$HOME/Projects/Literature}"
  MEMO=specs/555_literature_search_fidelity_schema_quarantine/summaries/02_group-b-decision-memo.md

  # Memo exists, is non-trivial, and covers every required element.
  test -s "$MEMO" && wc -l "$MEMO"
  for needle in no_source_pdf "option (b)" "option (c)" "option (d)" \
                wijesekera simpson QUARANTINED_FIDELITY_VALUES; do
    grep -qi -- "$needle" "$MEMO" && echo "OK: $needle" || echo "MISSING: $needle"
  done

  # Phase 7 changed no repository source.
  git status --short -- .claude/scripts/ | grep . && echo "FAIL: scripts modified in phase 7" \
    || echo "OK: no script changes"

  # Phase 7 caused no index.json write: no backup newer than the phase 6 commit.
  cmp -s "$LIT/index.json" "$SCRATCH/index.after-phase6.json" \
    && echo "OK: index.json unchanged by phase 7" || echo "FAIL: index.json changed"

  # Quarantine constant untouched.
  grep -n 'QUARANTINED_FIDELITY_VALUES=' .claude/scripts/literature-search.sh
  ```
  Expected: the memo exists and every `needle` reports `OK`; `no script changes`;
  `index.json unchanged by phase 7`; and `QUARANTINED_FIDELITY_VALUES` still reads
  `"unverified_summary unverified_no_baseline unadjudicated"`. Any `FAIL` line means the phase
  overstepped from write-up into decision — revert it and re-scope.

---

## Testing & Validation

- [x] `bash -n` passes on both modified scripts (Phases 1-5).
- [x] Fidelity-map harness reported `old 95 / new 97` at the time of Phase 1, added = the two Group A
      `doc_id`s, removed and changed both empty.
- [x] Default (no-flag) search for Wijesekera and Simpson content returned `degraded: false` (Phase 2).
- [x] `--dry-run` default-mode output byte-identical to the pre-change baseline (Phase 3).
- [x] `--legacy-schema --write` changed only legacy entries; `NON-LEGACY TOUCHED` empty (Phase 4).
- [x] A second `--legacy-schema --write` reported `changed: 0` (Phase 4).
- [x] Newly-`verified_conversion` documents surfaced in default search (Phase 5).
- [x] Working tree matches HEAD for both scripts after the Phase 6.1 restore; `bash -n` clean; the
      four-site `doc_id` fallback and the `--legacy-schema` mode both present. *(verified: 4 and 40
      respectively)*
- [x] A `git-snapshot.sh 555 --no-revert` patch exists and is recorded before any restore (Phase 6.1).
      *(working-progress-1785112536.patch)*
- [x] `--legacy-schema --dry-run` exits 0 against an empty `.sources-recovered/` and reports 0
      entries rather than erroring (Phase 6.3). *(verified: "Total directories: 0", exit 0)*
- [x] Default no-flag search returns `degraded: false` for `chagrovzakharyaschev_1997_modallogic`,
      `wijesekera_1990_constructivemodallogicsi`, and `simpson_1994_intuitionisticmodallogic`
      (Phase 6.5). *(verified: all three queries returned degraded=false with the expected
      documents non-quarantined)*
- [x] The Phase 6.4 `index.json` diff shows no changed document other than
      `arisakadasstrassburger_2015`; Group A untouched. *(arisaka itself did not change value —
      already stamped, absent from diff; Group A byte-identical before/after; DEVIATION: 8
      burgess_1984 sub-entries showed incidental word_ratio drift 1.0041->1.0033 with no
      provenance_fidelity class change — see Phase 6.4 annotation and Phase 7 memo)*
- [x] `RATIO_THRESHOLD` (0.75) and `PROOF_ADEQUACY_THRESHOLD` (0.6) unchanged at task end.
- [x] The decision memo exists, covers options (b)/(c)/(d), the Group A regression, and the explicit
      statement that `no_source_pdf` is citable by default (Phase 7). *(verified: 198 lines, all
      required needles present)*
- [x] Phase 7 modified no script and caused no `index.json` write. *(verified: git status clean on
      .claude/scripts/, index.json byte-identical to post-Phase-6 snapshot)*
- [x] `QUARANTINED_FIDELITY_VALUES` unchanged — asserted at every phase, including 6 and 7.
- [x] No file under `Cslib/` and no `.lean` file modified at any point (Phase 6 confirmed; Phase 7
      re-confirms below).

## Artifacts & Outputs

- `.claude/scripts/literature-search.sh` - restored from HEAD (Phase 6.1); no new logic
- `.claude/scripts/literature-fidelity-audit.sh` - restored from HEAD (Phase 6.1), then source
  resolution and startup guard repointed from `.sources-recovered/` to `sources/<doc_id>/` (Phase 6.3)
- `specs/literature/SOURCES.md` - annotation recording the migration (Phase 6.3)
- `specs/555_literature_search_fidelity_schema_quarantine/plans/02_blocker-resolution-and-decision-memo.md` - this plan
- `specs/555_literature_search_fidelity_schema_quarantine/summaries/02_group-b-decision-memo.md` - Phase 7 deliverable
- `specs/555_literature_search_fidelity_schema_quarantine/summaries/02_blocker-resolution-summary.md` - round-2 summary
- Out-of-repo data side effect: `$LITERATURE_DIR/index.json` may gain a re-computed
  `provenance_fidelity`/`word_ratio` on `arisakadasstrassburger_2015` alone, with a timestamped
  `index.json.bak.<ts>` written by the script. **Data, not repo source.**
- Decisions surfaced to the user, none taken: the Group B disposition ((b)/(c)/(d) over 66
  documents), the Group A regression restoration, and whether to retire the now-no-op Phase 1-5 code.

## Rollback/Contingency

- **Script changes**: both files are git-tracked. The Phase 6.1 restore is itself a rollback to
  `HEAD`; the pre-restore working-tree state is preserved by the mandatory
  `git-snapshot.sh 555 --no-revert` patch. Phase 6.3's repointing edits are revertible with
  `git checkout HEAD -- .claude/scripts/literature-fidelity-audit.sh` (snapshot first if the tree
  is dirty, per `.claude/rules/git-workflow.md`).
- **Global index.json**: NOT tracked by this repository. Recovery is the timestamped
  `index.json.bak.<ts>` the audit script writes and verifies before any write, plus the Phase 6.4
  scratchpad snapshot `index.before-phase6.json` as an independent second copy.
- **Phase 7 has no rollback surface** by construction: it writes only two new markdown files under
  `specs/555_.../summaries/`. If it is found to have modified a script or `index.json`, that is a
  scope violation — revert the change and re-scope the phase.
- **If the Phase 6.1 restore is judged wrong** (i.e. the working-tree revert was a deliberate
  concurrent decision), reapply it from the snapshot patch. This does not block Phase 7: the memo's
  findings are measured against `index.json` and the corpus, not against the scripts' contents.
- **Interim workaround, still valid**: `literature-search.sh --include-unverified` returns correct
  results for every quarantined document today and remains the honest opt-in mechanism while the
  Group B decision is outstanding.
