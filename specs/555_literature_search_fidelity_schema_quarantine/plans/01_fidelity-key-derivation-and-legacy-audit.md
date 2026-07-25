# Implementation Plan: Task #555

- **Task**: 555 - literature_search_fidelity_schema_quarantine
- **Status**: [IMPLEMENTING]
- **Effort**: 5 hours (Phases 1-5); Phases 6-7 are gates, not estimable work
- **Dependencies**: None
- **Research Inputs**: specs/555_literature_search_fidelity_schema_quarantine/reports/01_fidelity-schema-key-derivation.md
- **Artifacts**: plans/01_fidelity-key-derivation-and-legacy-audit.md (this file)
- **Standards**: plan-format.md; status-markers.md; artifact-management.md; tasks.md
- **Type**: general
- **Lean Intent**: false

## Overview

Index entries written under the legacy `doc_id`/`chunks_dir` schema are invisible to default
literature search because `load_fidelity_map()` derives its lookup key exclusively from a
`sources/`-prefixed `path` that these entries do not have. This plan ships the tractable half
first — a five-line, four-site key-derivation fix in `literature-search.sh` that restores the two
already-honestly-stamped Group A documents — then extends `literature-fidelity-audit.sh` with a
`--legacy-schema` mode that can classify the six source-recoverable Group B documents against
their recovered PDFs. Done means: default (no-flag) search returns `degraded: false` with correct
fidelity for Wijesekera 1990 and Simpson 1994; the audit script can compute and stamp fidelity for
legacy-schema entries without touching a single `sources/`-schema entry; and the two open
questions (DJVU tooling, disposition of the 10 unrecoverable documents) are raised as explicit
gates rather than silently resolved.

### Research Integration

The research report is empirically verified against the live corpus — the researcher patched a
scratch copy of `literature-search.sh`, ran real searches, and deleted it. The following are
established facts and MUST NOT be re-derived during implementation:

- All four `load_fidelity_map()` copies (`literature-search.sh:227,527,764,908`) are byte-identical
  in executable logic; only the comment/docstring differs. The fix is applied in place at all four
  sites. Factoring into a shared importable module is explicitly rejected (the four are separate
  `python3 <<PYEOF` subprocess invocations with no shared import path; a companion module plus
  `sys.path` wiring is disproportionate to a ~5-line logic change).
- The verified outcome of the fix: the old map has 95 keys, the new map has 97; exactly the two
  Group A `doc_id`s are added; zero keys removed, zero values changed. Fail-open is structurally
  preserved because `if pf is None: continue` still runs before either branch, and
  `get_fidelity()`'s `fmap.get(doc_id) or "unverified_summary"` is untouched.
- `literature-fidelity-audit.sh` excludes the legacy schema by its own documented design (header,
  lines 63-65) for three independent structural reasons: `classify_dir()` roots at
  `$LITERATURE_DIR/sources/<dir>` while legacy content lives at `$LITERATURE_DIR/<dir>/`; the `mds`
  filter excludes `chunk_NNNN.md`, which is the only content these directories hold; and
  `resolve_targets()` requires an `id` field that legacy entries lack. All three must be addressed
  by the new mode.
- Hand-computed word ratios for the five non-DJVU recoverable documents (Findings > Q3) are the
  expected values the new mode must reproduce.
- Recovered sources are named `$LITERATURE_DIR/.sources-recovered/<doc_id>.pdf` (exact `doc_id`
  match, confirmed against the directory listing) — no fuzzy filename matching is needed.

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

No `roadmap_path` was provided in the delegation context; no ROADMAP.md consultation performed.

## Goals & Non-Goals

**Goals**:

- Restore default-search visibility for the two Group A documents by fixing key derivation at all
  four `load_fidelity_map()` sites, with no behavior change for the 273 `sources/`-schema entries.
- Preserve fail-open semantics exactly and provably: a missing map entry resolves to
  `unverified_summary`, never to `verified_conversion`.
- Add a `--legacy-schema` mode to `literature-fidelity-audit.sh` that resolves sources from
  `.sources-recovered/`, treats `chunk_*.md` as the document body, and stamps by `doc_id` equality.
- Compute and (where honest) stamp fidelity for the five recoverable non-DJVU Group B documents.
- Raise the DJVU tooling gap and the 10-document disposition question as explicit, authorization-
  gated stopping points.

**Non-Goals**:

- Removing or altering any value in `QUARANTINED_FIDELITY_VALUES` (`literature-search.sh:53`). The
  fail-open-to-unverified design is deliberate and correct.
- Introducing a new non-quarantined fidelity value. That is option (c) of the Group B disposition
  and requires explicit user sign-off (Phase 7).
- Choosing between option (b) and option (c) for the 10 unrecoverable documents.
- Factoring `load_fidelity_map()` into a shared module.
- Loosening `RATIO_THRESHOLD` (0.75) or `PROOF_ADEQUACY_THRESHOLD` (0.6) to make any document pass.
- Any change to `Cslib/` Lean source, or to any file outside `.claude/scripts/literature-search.sh`
  and `.claude/scripts/literature-fidelity-audit.sh`.
- OCR-based or rasterization-based DJVU workarounds (changes the fidelity-computation method
  itself; out of scope without an explicit decision).

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| The new `doc_id` branch accidentally shadows or overwrites a `sources/`-schema key | H | L | The branch is reached only when `path` is not a `sources/`-prefixed string; `setdefault` is retained so a pre-existing key is never overwritten. Phase 1 verification asserts 0 removed and 0 changed keys. |
| Four-site patch applied inconsistently (one site missed or mistyped) | H | M | Phase 1 verification greps for an exact count of 4 occurrences of the new branch and runs `bash -n`; Phase 2 exercises `do_search`, and the `do_read`/`do_toc` sites are exercised explicitly. |
| `--legacy-schema` mode starts matching or writing `sources/`-schema entries | H | M | Gate the legacy target selector strictly on `doc_id` present AND `chunks_dir` present AND `path` absent AND `id` absent. Phase 3 diffs default `--dry-run` output against a pre-change baseline (must be byte-identical); Phase 4 asserts every changed entry carries the legacy schema. |
| Write to the global `index.json` corrupts or loses data | H | L | The script's existing backup-and-verify step (`index.json.bak.<ts>` plus `cmp`) runs before any write; Phase 4 additionally snapshots `index.json` to the scratchpad and diffs entry-by-entry after the write. |
| `arisakadasstrassburger_2015` (ratio 0.539) resolves to a quarantined value | M | M | This is an honest outcome, not a defect. Record it and stop; do not adjust thresholds or hand-stamp a better value to make it surface. |
| DJVU document cannot be classified (no `djvutxt`/`djvups`, PyMuPDF codec fails) | M | H (confirmed) | Encoded as Phase 6, a blocked gate requiring an environment change the implementer is not authorized to make. |
| Implementer resolves the 10 unrecoverable documents unilaterally | H | M | Encoded as Phase 7, a blocked gate with an explicit MUST NOT. Options (b) and (c) and their costs are stated but not chosen. |

## Implementation Phases

**Dependency Analysis**:

| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2 | 1 |
| 3 | 3 | 2 |
| 4 | 4, 6 | 3 |
| 5 | 5 | 4 |
| 6 | 7 | 5 |

Phases within the same wave can execute in parallel.

Phases 1-2 constitute Stage A: a self-contained, independently-committable milestone. Commit at the
end of Phase 2 before starting Phase 3. Phases 3-5 (Stage B) touch a different file
(`literature-fidelity-audit.sh`) with disjoint territory; the declared dependency on Phase 2 is a
sequencing decision (ship the tractable half first), not a code-level coupling.

---

### Phase 1: Four-site key-derivation fix in literature-search.sh [COMPLETED]

- **Goal:** `load_fidelity_map()` builds keys from `doc_id` when `path` is not a `sources/`-prefixed
  string, at all four sites, with the `sources/` behavior unchanged.
- **Tasks:**
  - [x] Capture a pre-change baseline of the fidelity map: run the harness in **Verification**
        below against the unpatched script's logic and record `old keys: 95`. *(completed: old 95)*
  - [x] At `literature-search.sh:227`, replace the `continue`-on-non-`sources/`-path guard with the
        two-branch form: if `path` is a string starting with `sources/`, derive `dirname` and
        `fmap.setdefault(dirname, pf)` then `continue`; otherwise read `doc_id` and, if it is a
        non-empty string, `fmap.setdefault(doc_id, pf)`. *(completed)*
  - [x] Apply the byte-identical logic change at lines ~527, ~764, and ~908 (line numbers shift as
        edits land; locate by `def load_fidelity_map`). *(completed: applied via single replace_all
        edit across all 4 byte-identical sites)*
  - [x] Extend the line-227 docstring to describe the dual-key behavior: directory-name key for
        `sources/`-schema entries, direct `doc_id` key for legacy `doc_id`/`chunks_dir`-schema
        entries. Keep the existing `(task #835)` reference as-is; do NOT add new task-number
        citations (`.claude/rules/no-task-references-in-deliverables.md`). *(completed)*
  - [x] Add a one-line note to each of the three secondary "see the primary do_search heredoc"
        comments that the `doc_id` fallback branch exists, per the file's existing convention.
        *(completed)*
  - [x] Confirm `get_fidelity()` is untouched at all four sites. *(completed: grep confirms 4
        byte-identical occurrences of `fmap.get(doc_id) or "unverified_summary"`)*
- **Timing:** 45 minutes
- **Depends on:** none
- **Files to modify:**
  - `.claude/scripts/literature-search.sh` - `load_fidelity_map()` body at 4 sites + docstring/comments
- **Verification:**
  ```bash
  cd /home/benjamin/Projects/cslib
  bash -n .claude/scripts/literature-search.sh
  grep -c 'doc_id = e.get("doc_id")' .claude/scripts/literature-search.sh   # expect: 4
  grep -c 'def load_fidelity_map' .claude/scripts/literature-search.sh      # expect: 4
  grep -c 'fmap.get(doc_id) or "unverified_summary"' .claude/scripts/literature-search.sh  # expect: 4

  python3 - <<'PY'
  import json, os
  lit = os.environ.get("LITERATURE_DIR") or os.path.expanduser("~/Projects/Literature")
  idx = json.load(open(os.path.join(lit, "index.json"), encoding="utf-8"))
  def old(idx):
      m = {}
      for e in idx.get("entries") or []:
          pf = e.get("provenance_fidelity")
          if pf is None: continue
          p = e.get("path")
          if not isinstance(p, str) or not p.startswith("sources/"): continue
          d = p[len("sources/"):].split("/", 1)[0]
          if d: m.setdefault(d, pf)
      return m
  def new(idx):
      m = {}
      for e in idx.get("entries") or []:
          pf = e.get("provenance_fidelity")
          if pf is None: continue
          p = e.get("path")
          if isinstance(p, str) and p.startswith("sources/"):
              d = p[len("sources/"):].split("/", 1)[0]
              if d: m.setdefault(d, pf)
              continue
          di = e.get("doc_id")
          if isinstance(di, str) and di: m.setdefault(di, pf)
      return m
  o, n = old(idx), new(idx)
  print("old", len(o), "new", len(n))
  print("added", sorted(set(n) - set(o)))
  print("removed", sorted(set(o) - set(n)))
  print("changed", sorted(k for k in set(o) & set(n) if not o[k] == n[k]))
  PY
  ```
  Expected: `old 95 new 97`; `added` is exactly
  `['simpson_1994_intuitionisticmodallogic', 'wijesekera_1990_constructivemodallogicsi']`;
  `removed` and `changed` are both empty. Any other result means the branch is mis-gated — stop
  and correct before Phase 2.

---

### Phase 2: Group A end-to-end verification and fail-open regression [COMPLETED]

- **Goal:** Default (no-flag) search returns non-degraded, correctly-stamped results for the two
  Group A documents, and every Group B document plus every unknown `doc_id` still fail-opens to
  `unverified_summary`.
- **Tasks:**
  - [x] Run the Group A default-search checks (see **Verification**) and record the exact
        `degraded`, `fallback_tier`, and per-result `provenance_fidelity` values. *(completed: both
        Wijesekera and Simpson queries return degraded=false, fallback_tier=bm25,
        provenance_fidelity=ocr_rescanned_reflowed_partial_symbol_loss. Also uncovered and fixed a
        real regression: the new docstring used markdown backticks around `sources/`/`doc_id`/etc.
        inside the unquoted `<< PYEOF` heredoc, which bash expanded as backtick command
        substitution, spewing "command not found" errors to stderr on every do_search call despite
        stdout JSON being correct. Removed the backticks; stderr is clean on rerun.)*
  - [x] Run the `--include-unverified` check and confirm the result set is a superset with the same
        Group A fidelity values (these entries are no longer quarantined, so the flag changes
        nothing for them). *(completed)*
  - [x] Confirm Group B documents still report `unverified_summary` under `--include-unverified`
        and are still absent from default search — the key fix must do nothing for them.
        *(completed: arisakadasstrassburger_2015 and marinmoralesstrassburger_2021 both still
        unverified_summary under --include-unverified)*
  - [x] Exercise the `do_read` and `do_toc` sites so all four patched heredocs are executed at least
        once. *(completed: --toc and --read both exercised cleanly, no stderr)*
  - [ ] Commit Stage A: `.claude/scripts/literature-search.sh` plus this plan file and the task
        directory. Message: `task 555 phase 2: restore legacy-schema fidelity key derivation`.
- **Timing:** 30 minutes
- **Depends on:** 1
- **Files to modify:**
  - None (verification and commit only)
- **Verification:**
  ```bash
  cd /home/benjamin/Projects/cslib
  # Group A restored: expect degraded=false, fallback_tier="bm25", and both doc_ids
  # carrying ocr_rescanned_reflowed_partial_symbol_loss.
  bash .claude/scripts/literature-search.sh "constructive modal logic Wijesekera" 5 \
    | jq '{degraded, fallback_tier, hits: [.results[] | {doc_id, provenance_fidelity}]}'
  bash .claude/scripts/literature-search.sh "Simpson proof theory modal logic" 5 \
    | jq '{degraded, fallback_tier, hits: [.results[] | {doc_id, provenance_fidelity}]}'

  # Fail-open preserved: Group B still unverified_summary under the opt-in flag.
  bash .claude/scripts/literature-search.sh --include-unverified "nested sequents constructive modal logic" 10 \
    | jq -r '.results[] | "\(.doc_id)\t\(.provenance_fidelity)"'

  # do_read / do_toc sites execute without error.
  bash .claude/scripts/literature-search.sh --toc wijesekera_1990_constructivemodallogicsi | head -20
  ```
  Expected: both default searches report `"degraded": false` and `"fallback_tier": "bm25"`, with
  `wijesekera_1990_constructivemodallogicsi` and/or `simpson_1994_intuitionisticmodallogic`
  carrying `"ocr_rescanned_reflowed_partial_symbol_loss"`. Group B rows still read
  `unverified_summary`. `--toc` exits 0.

---

### Phase 3: --legacy-schema classification mode (read-only) [COMPLETED]

- **Goal:** `literature-fidelity-audit.sh --legacy-schema --dry-run` classifies the 18 legacy-schema
  entries and reproduces the report's hand-computed ratios, with the default mode's output
  bit-for-bit unchanged.
- **Tasks:**
  - [x] Capture the pre-change default-mode baseline:
        `bash .claude/scripts/literature-fidelity-audit.sh --dry-run > "$SCRATCH/audit-baseline.tsv"`.
        *(completed: reconstructed the pre-edit file verbatim from the research-phase full read
        since the file predates any git-tracked commit, ran --dry-run, got 97 directories)*
  - [x] Add `--legacy-schema` to the argument loop and export a `LEGACY_SCHEMA` env var into the
        python heredoc. Keep `--dry-run`/`--write` orthogonal to it. *(completed)*
  - [x] Relax the startup guards for legacy mode: `sources/` must still exist for default mode, but
        legacy mode additionally requires `$LITERATURE_DIR/.sources-recovered/` and must error
        clearly if it is absent. *(completed)*
  - [x] Add `enumerate_legacy_entries(idx)`: select entries where `doc_id` and `chunks_dir` are both
        present AND `path` is absent-or-null AND `id` is absent-or-null. This gate is the entire
        safety boundary between the two schemas — implement it exactly. *(completed)*
  - [x] Add `classify_legacy(entry)`: resolve the source as
        `$LITERATURE_DIR/.sources-recovered/<doc_id>.pdf` (or `.djvu`); compute `pdf_words` via the
        existing `pdf_word_count()`; compute `md_words` by summing `word_count_text()` over ALL
        `chunk_*.md` in `chunks_dir` (the chunk-exclusion filter is deliberately NOT applied — for
        this schema the chunks are the document). Reuse `disclosure_check()` and the proof-
        completeness path unchanged for ratios below 0.75. *(completed)*
  - [x] Classify a legacy entry with no recovered source as `no_source_pdf` and one whose
        `pdf_word_count` returns 0 (DJVU) as `unadjudicated`, reported with an explicit
        blocked-reason note on stderr. Do not silently emit `unverified_no_baseline` for the DJVU
        case — the baseline exists, the extractor does not. *(completed: tracked via a
        `djvu_blocked` flag on the classification result, distinct from the `frac is None`
        unadjudicated path so Phase 4's write loop can key its skip decision off it precisely)*
  - [x] Print the legacy report to stdout in the same TSV shape as the default mode, keyed by
        `doc_id` instead of `dir`. No `index.json` write in this phase. *(completed: factored the
        print/summary loop into a shared print_report() used by both modes; no write occurred in
        this phase's testing)*
- **Timing:** 1.5 hours
- **Depends on:** 2
- **Files to modify:**
  - `.claude/scripts/literature-fidelity-audit.sh` - arg parsing, startup guards, legacy enumeration
    and classification functions, report printing
- **Verification:**
  ```bash
  cd /home/benjamin/Projects/cslib
  bash -n .claude/scripts/literature-fidelity-audit.sh

  # Default mode must be untouched.
  diff <(bash .claude/scripts/literature-fidelity-audit.sh --dry-run) "$SCRATCH/audit-baseline.tsv" \
    && echo "DEFAULT MODE UNCHANGED"

  # Legacy mode dry run.
  bash .claude/scripts/literature-fidelity-audit.sh --legacy-schema --dry-run
  ```
  Expected: `DEFAULT MODE UNCHANGED` prints (empty diff). The legacy report lists 18 rows and
  reproduces these ratios within +/-0.01:
  `biermandepaiva_2000_onanintuitionisticmodallogic` 1.0349,
  `marinmoralesstrassburger_2021_...` 1.0158,
  `pacheco_2024_collapsingconstructive...` 1.0298,
  `alechinamendlerdepaivaritter_2001_...` 1.0203 — all four classified `verified_conversion`;
  `arisakadasstrassburger_2015_...` 0.5390 routed through the disclosure/proof-completeness path;
  `chagrovzakharyaschev_1997_modallogic` reported `unadjudicated` with the DJVU blocked-reason note;
  the 10 unrecoverable documents reported `no_source_pdf`. A ratio outside tolerance means
  `md_words` is summing the wrong file set — correct it rather than adjusting the expectation.

---

### Phase 4: --legacy-schema write path with strict schema gating [COMPLETED]

- **Goal:** `--legacy-schema --write` stamps `provenance_fidelity` and `word_ratio` onto matched
  legacy entries by `doc_id` equality, and provably touches zero `sources/`-schema entries.
- **Tasks:**
  - [x] Snapshot the index before writing: `cp "$LITERATURE_DIR/index.json" "$SCRATCH/index.before.json"`.
        *(completed)*
  - [x] Add `resolve_legacy_targets(idx, doc_id)`: return the single entry whose `doc_id` equals the
        classified `doc_id` AND which passes the Phase 3 legacy gate. Never call
        `resolve_targets()` in legacy mode — its `path`-prefix and `id`-presence logic is for the
        other schema. *(completed)*
  - [x] Route the write loop by mode so legacy mode iterates legacy classifications only and default
        mode iterates directory classifications only. The two write paths must not interleave.
        *(completed: split into main_default()/main_legacy(), dispatched from main())*
  - [x] Confirm the existing backup-and-`cmp` step runs before the legacy write (it is mode-
        independent; verify, do not duplicate). *(completed: unchanged, mode-independent bash code
        at lines ~195-206)*
  - [x] Stamp only entries whose computed value is a real classification; leave `no_source_pdf` and
        the DJVU `unadjudicated` rows' handling explicit in the write summary rather than silently
        skipping them. *(completed. Also caught and fixed a real regression here: the first write
        attempt clobbered Group A's pre-existing, more specific
        `ocr_rescanned_reflowed_partial_symbol_loss` value with the generic detector's
        `verified_conversion`, producing 7 changed entries instead of the expected <=6. Restored
        Group A from the pre-write scratchpad snapshot and added a `SIX_VALUE_ENUM` guard: any
        legacy entry whose current `provenance_fidelity` is already set to a value outside this
        script's own six-value enum is left untouched and reported separately as "already honestly
        stamped" rather than being overwritten.)*
  - [x] Run `--legacy-schema --write`, then run it a second time to confirm idempotency (second run
        reports `changed: 0`). *(completed: first write stamped 5/5 changed; second write reported
        changed: 0, unchanged: 5)*
  - [x] Record the outcome for `arisakadasstrassburger_2015`. If it lands on `unverified_summary`,
        that is the honest result — record it and move on. Do NOT adjust `RATIO_THRESHOLD` or
        `PROOF_ADEQUACY_THRESHOLD`, and do NOT hand-stamp a better value. *(completed: landed on
        `unadjudicated` (word_ratio 0.539, undisclosed, no numbered statements to check) — a
        quarantined value per `QUARANTINED_FIDELITY_VALUES`. Recorded as-is; thresholds
        untouched.)*
  - [x] Commit: `task 555 phase 4: add legacy-schema mode to fidelity audit`.
- **Timing:** 1.25 hours
- **Depends on:** 3
- **Files to modify:**
  - `.claude/scripts/literature-fidelity-audit.sh` - legacy target resolution and mode-routed write loop
- **Verification:**
  ```bash
  cd /home/benjamin/Projects/cslib
  LIT="${LITERATURE_DIR:-$HOME/Projects/Literature}"
  bash .claude/scripts/literature-fidelity-audit.sh --legacy-schema --write
  bash .claude/scripts/literature-fidelity-audit.sh --legacy-schema --write   # idempotency: changed: 0

  python3 - <<'PY'
  import json, os
  lit = os.environ.get("LITERATURE_DIR") or os.path.expanduser("~/Projects/Literature")
  before = json.load(open(os.environ["SCRATCH"] + "/index.before.json", encoding="utf-8"))
  after = json.load(open(os.path.join(lit, "index.json"), encoding="utf-8"))
  def key(e): return e.get("doc_id") or e.get("id") or e.get("path")
  b = {key(e): e for e in before.get("entries") or []}
  changed = []
  for e in after.get("entries") or []:
      k = key(e); p = b.get(k)
      if p is None: continue
      if not p.get("provenance_fidelity") == e.get("provenance_fidelity") \
         or not p.get("word_ratio") == e.get("word_ratio"):
          legacy = ("doc_id" in e and "chunks_dir" in e
                    and e.get("path") is None and e.get("id") is None)
          changed.append((k, e.get("provenance_fidelity"), legacy))
  print("changed entries:", len(changed))
  for k, pf, legacy in changed: print(f"  {k}\t{pf}\tlegacy={legacy}")
  print("NON-LEGACY TOUCHED:", [k for k, _, legacy in changed if not legacy])
  PY
  ```
  Expected: at most 6 changed entries, every one with `legacy=True`, and
  `NON-LEGACY TOUCHED: []`. A non-empty `NON-LEGACY TOUCHED` list means the schema gate leaked —
  restore from the script's `index.json.bak.<ts>` backup and fix the gate before proceeding.

---

### Phase 5: Post-stamp search verification for the recoverable documents [COMPLETED]

- **Goal:** Documents that Phase 4 stamped with a non-quarantined value now surface in default
  (no-flag) search; documents that landed on a quarantined value provably do not.
- **Tasks:**
  - [x] Run a default search targeting each newly-`verified_conversion` document and record
        `degraded`, `fallback_tier`, and the returned `provenance_fidelity`. *(completed: all 4
        queries return degraded=false, fallback_tier=bm25, provenance_fidelity=verified_conversion)*
  - [x] Confirm that any document Phase 4 left at a quarantined value is still absent from default
        search and still visible under `--include-unverified` — the quarantine mechanism must still
        work. *(completed: arisakadasstrassburger_2015 absent from default search, present as
        unadjudicated under --include-unverified)*
  - [x] Re-run the Phase 1 map-diff harness to confirm the new map keys are exactly the Group A pair
        plus the newly-stamped legacy documents, with zero removals and zero changed values among
        the pre-existing keys. *(completed: old 95, new 102; added = the 2 Group A docs + 5 newly-
        stamped Group B docs (4 verified_conversion + arisaka's unadjudicated); removed and changed
        both empty)*
  - [x] Write the implementation summary to
        `specs/555_literature_search_fidelity_schema_quarantine/summaries/01_fidelity-key-derivation-summary.md`,
        stating explicitly which documents remain quarantined and why. *(completed)*
  - [x] Commit: `task 555 phase 5: verify post-stamp search visibility`.
- **Timing:** 30 minutes
- **Depends on:** 4
- **Files to modify:**
  - `specs/555_literature_search_fidelity_schema_quarantine/summaries/01_fidelity-key-derivation-summary.md` - new
- **Verification:**
  ```bash
  cd /home/benjamin/Projects/cslib
  for q in "intuitionistic modal logic Bierman de Paiva" \
           "fully labelled proof system intuitionistic modal" \
           "collapsing constructive and intuitionistic modal logics" \
           "categorical and Kripke semantics constructive S4"; do
    echo "== $q"
    bash .claude/scripts/literature-search.sh "$q" 5 \
      | jq '{degraded, fallback_tier, hits: [.results[] | {doc_id, provenance_fidelity}]}'
  done
  ```
  Expected: each query returns `"degraded": false` with the corresponding document carrying
  `"verified_conversion"`. A document Phase 4 left quarantined must NOT appear here — its absence
  is a pass, not a failure.

---

### Phase 6: GATE - DJVU extractor prerequisite [BLOCKED]

- **Goal:** Obtain authorization for the environment change required to classify
  `chagrovzakharyaschev_1997_modallogic`. **This phase is a gate. The implementer MUST stop here
  and surface the decision; it MUST NOT install packages or implement a workaround.**
- **Blocking condition:** Neither `djvutxt` nor `djvups` is installed on this machine, and this
  build of PyMuPDF (1.27.2) raises `FileDataError: Failed to open file` on the recovered `.djvu`.
  Installing `djvulibre` is a system-level change outside this task's declared file scope.
- **Tasks:**
  - [ ] Report to the user: this one document cannot be classified without a DJVU text extractor,
        and state the two candidate resolutions below.
  - [ ] Resolution 1 (preferred): user installs `djvulibre`, after which the Phase 3 legacy dry run
        is re-run for this document alone and Phase 4's write path stamps it with no code change.
  - [ ] Resolution 2 (requires separate explicit approval): rasterize-and-OCR the DJVU. This changes
        the fidelity-computation method itself and is NOT authorized by this plan.
  - [ ] Leave the document at `unadjudicated` with the blocked-reason note from Phase 3 until a
        resolution is chosen. Do not substitute `unverified_no_baseline` — a baseline exists.
- **Timing:** Not estimable (external dependency)
- **Depends on:** 3
- **Files to modify:**
  - None until the gate is resolved
- **Verification:**
  ```bash
  command -v djvutxt || echo "BLOCKED: no djvu extractor installed"
  ```
  Expected while blocked: `BLOCKED: no djvu extractor installed`. Once resolved, `djvutxt` resolves
  and `bash .claude/scripts/literature-fidelity-audit.sh --legacy-schema --dry-run` reports a
  non-zero `pdf_words` and a real classification for `chagrovzakharyaschev_1997_modallogic`.

---

### Phase 7: GATE - disposition of the 10 unrecoverable documents [BLOCKED]

- **Goal:** Obtain an explicit user decision on how the 10 documents with no recoverable source are
  handled. **This phase is a gate. The implementer MUST NOT choose between the options, MUST NOT
  stamp any value, and MUST NOT modify `QUARANTINED_FIDELITY_VALUES`.**
- **Blocking condition:** The choice is a policy decision about what downstream consumers may cite
  as authoritative, not an engineering call.
- **Tasks:**
  - [ ] Present option (b) — per-document adjudication to `unverified_no_baseline`. Cost: low
        engineering effort (a few `jq` edits). Effect: replaces a wrong fail-open default
        (`unverified_summary`, reached silently) with an honest explicit one. Does NOT restore
        default-search visibility, because `unverified_no_baseline` is itself on
        `QUARANTINED_FIDELITY_VALUES`. Downstream-citation risk: minimal.
  - [ ] Present option (c) — a new non-quarantined fidelity value. Cost: a system-wide semantic
        change to the shared quarantine vocabulary. Downstream-citation risk: high — an agent
        citing one of these documents would have no source PDF against which to check the claim,
        which is exactly the failure mode the quarantine mechanism exists to prevent.
  - [ ] Present option (d) — leave all 10 at the current `unverified_summary` fail-open and do
        nothing further.
  - [ ] Report the relevance asymmetry: only `massacci_2000_single_step_tableaux_for_modal_logics`
        is referenced by this repository's `specs/literature-index.json`. The other 9 are not
        referenced at all, and their `source_path` values point at another project's ephemeral
        scratch directories.
  - [ ] Stop and await the decision. Take no action on any of the 10.
- **Timing:** Not estimable (user decision)
- **Depends on:** 5
- **Files to modify:**
  - None until the gate is resolved
- **Verification:**
  ```bash
  cd /home/benjamin/Projects/cslib
  git diff --stat -- .claude/scripts/literature-search.sh | grep -c QUARANTINED || echo "QUARANTINE CONSTANT UNTOUCHED"
  grep -n 'QUARANTINED_FIDELITY_VALUES=' .claude/scripts/literature-search.sh
  ```
  Expected: the constant still reads
  `QUARANTINED_FIDELITY_VALUES="unverified_summary unverified_no_baseline unadjudicated"` — unchanged
  from its pre-task value. The gate is satisfied only by a recorded user decision, never by a code
  change made in its absence.

---

## Testing & Validation

- [ ] `bash -n` passes on both modified scripts.
- [ ] Fidelity-map harness reports `old 95 / new 97`, added = the two Group A `doc_id`s, removed and
      changed both empty (Phase 1).
- [ ] Default (no-flag) search for Wijesekera and Simpson content returns `degraded: false`,
      `fallback_tier: "bm25"`, and `ocr_rescanned_reflowed_partial_symbol_loss` (Phase 2).
- [ ] An unknown `doc_id` still resolves to `unverified_summary`; `get_fidelity()` unchanged at all
      four sites (Phase 1/2).
- [ ] Group B documents remain quarantined after the key fix alone (Phase 2).
- [ ] `--dry-run` default-mode output is byte-identical to the pre-change baseline (Phase 3).
- [ ] Legacy dry run reproduces the five hand-computed ratios within +/-0.01 (Phase 3).
- [ ] `--legacy-schema --write` changes only entries carrying the legacy schema; `NON-LEGACY
      TOUCHED` is empty (Phase 4).
- [ ] A second `--legacy-schema --write` reports `changed: 0` (idempotency, Phase 4).
- [ ] Newly-`verified_conversion` documents surface in default search; still-quarantined ones do not
      (Phase 5).
- [ ] `QUARANTINED_FIDELITY_VALUES` is unchanged at task end (Phases 1-7).

## Artifacts & Outputs

- `.claude/scripts/literature-search.sh` - four-site `load_fidelity_map()` fix plus docstring update
- `.claude/scripts/literature-fidelity-audit.sh` - `--legacy-schema` classification and write mode
- `specs/555_literature_search_fidelity_schema_quarantine/plans/01_fidelity-key-derivation-and-legacy-audit.md` - this plan
- `specs/555_literature_search_fidelity_schema_quarantine/summaries/01_fidelity-key-derivation-summary.md` - implementation summary (Phase 5)
- Two open gates reported to the user: DJVU extractor prerequisite (Phase 6) and the 10-document
  disposition decision (Phase 7)
- Out-of-repo side effect: `$LITERATURE_DIR/index.json` gains `provenance_fidelity`/`word_ratio` on
  up to 6 legacy entries, with a timestamped `index.json.bak.<ts>` backup written by the script

## Rollback/Contingency

- **Script changes**: both modified files are git-tracked. Revert with
  `git checkout HEAD -- .claude/scripts/literature-search.sh .claude/scripts/literature-fidelity-audit.sh`
  (safe only on a clean tree; otherwise run `bash .claude/scripts/git-snapshot.sh` first, per
  `.claude/rules/git-workflow.md`).
- **Global index.json**: NOT git-tracked. Recovery is the timestamped backup the audit script writes
  and verifies before any write: `cp "$LITERATURE_DIR/index.json.bak.<ts>" "$LITERATURE_DIR/index.json"`.
  The Phase 4 scratchpad snapshot `index.before.json` is a second independent copy.
- **Partial rollback**: Stage A (Phases 1-2) is committed independently of Stage B (Phases 3-5). If
  the audit extension proves unworkable, Stage A stands on its own and delivers the Group A fix with
  no dependency on Stage B.
- **Interim workaround if everything is reverted**: `literature-search.sh --include-unverified`
  returns correct results for all 18 documents today and remains the honest opt-in mechanism.
