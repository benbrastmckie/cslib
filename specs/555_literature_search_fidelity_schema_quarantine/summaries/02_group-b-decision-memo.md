# Decision Memo: Group B Disposition, Group A Regression, and Residual Findings

**Purpose**: This memo gives the user everything needed to decide the Group B fidelity
disposition. **It is a write-up, not a decision.** No `provenance_fidelity` value has been
stamped on any of the documents discussed below, `QUARANTINED_FIDELITY_VALUES` has not been
edited, and `$LITERATURE_DIR/index.json` has not been written by anything in this phase.

## 1. The reversed premise, stated plainly and first

`no_source_pdf` is **not** on `QUARANTINED_FIDELITY_VALUES`
(`"unverified_summary unverified_no_baseline unadjudicated"`, unchanged in
`.claude/scripts/literature-search.sh:53`). **Every document stamped `no_source_pdf` is
currently returned by default no-flag `literature-search.sh` search, non-degraded, with no
signal to the caller that no source exists to verify the claim against.** This is live today,
in this repository's default search behavior, and it is unannounced anywhere the caller would
see it.

**Measured blast radius (re-measured directly against the live corpus immediately before this
memo, not the earlier research report's figure)**: **66 documents** are stamped `no_source_pdf`.
All 66 were checked against disk and all 66 are genuinely sourceless — 0 of 66 have any
`source.*` file under their `sources/<doc_id>/` directory. The research report's earlier figure
of "9" was the subset traceable to this task's original Group B scope; the index-wide population
carrying this citable-by-default value is roughly **seven times larger** than that.

**Full current fidelity histogram** (re-measured after Phase 6's `--write` run):

| `provenance_fidelity` value | Count | Quarantined? |
|---|---|---|
| `verified_conversion` | 125 | No |
| (none — field absent) | 127 | Fails open to `unverified_summary`, which **is** quarantined |
| `no_source_pdf` | 66 | **No** — citable by default |
| `unadjudicated` | 2 | Yes |
| `not_yet_converted` | 1 | Yes |

The 127 entries with no `provenance_fidelity` field at all fail open to `unverified_summary` and
are therefore correctly quarantined by the existing fail-open design — they are not part of the
live-and-unannounced problem above, but they are a large population nonetheless and are recorded
here for completeness.

`massacci_2000_single_step_tableaux_for_modal_logics` has **left** the unrecoverable set: it has
a `source.pdf` on disk and is stamped `verified_conversion`. The remaining Group B population
(the 66 `no_source_pdf` documents) contains nothing this repository's
`specs/literature-index.json` currently references for active modal-logic work.

## 2. Options (b), (c), (d) restated against the current state, with concrete costs

**No code in this repository caused the current state.** `no_source_pdf` was always one of the
six values in `literature-fidelity-audit.sh`'s enum; `QUARANTINED_FIDELITY_VALUES` was never
edited in either direction by this task. The stamping of these 66 documents as `no_source_pdf`
(a non-quarantined value) was done by the `~/Projects/Literature` repository's own commits, not
by anything delivered here.

### Option (b) — stamp `unverified_no_baseline` on the sourceless set

- **Files changed**: `$LITERATURE_DIR/index.json` only. This is **data, not repo source** — a
  handful of `jq` edits, no script change.
- **Effect**: this is now a **rollback of live behavior**, not a no-op. `unverified_no_baseline`
  IS on `QUARANTINED_FIDELITY_VALUES`, so applying it removes these documents from default
  search entirely. They remain reachable only via `--include-unverified`.
- **Downstream**: `literature-search.sh` default search, `literature-briefing.sh` corpus
  selection, and every `--lit` briefing would stop treating these 66 as citable by default.
- **Citation risk**: minimal. This is the most conservative option.
- **A scope decision the user must also make**: apply to the 9 documents originally in this
  task's Group B scope, or to all 66 index-wide? The two are very different in blast radius.

### Option (c) — formalize a non-quarantined value meaning "converted, no obtainable baseline"

- **Files changed**: **none required — this is already the operative state**, via `no_source_pdf`
  itself. Formalizing it as a deliberate policy would mean documenting `no_source_pdf` explicitly
  as a permanent non-quarantined category in `literature-search.sh` and the audit script's header
  comment, rather than leaving its current non-quarantined status looking like an oversight.
- **Downstream**: `literature-search.sh` default search, `literature-briefing.sh` corpus
  selection, and every `--lit` briefing already treat all 66 as citable, unannounced.
- **Citation risk**: **high**. An agent citing one of these 66 has no source PDF or DJVU against
  which any specific claim (a definition, a rule figure, a quoted result) can be checked. This is
  precisely the failure mode the fidelity-quarantine mechanism was built to prevent.

### Option (d) — leave as-is

- **Files changed**: none.
- **`(d)` has changed meaning since it was first written.** When this task's original scope was
  drafted, "as-is" meant *quarantined* (Group B fail-open to `unverified_summary`). Today,
  "as-is" means *citable in default search, non-degraded, unannounced* — because the Literature
  repo's later migration stamped these documents `no_source_pdf` rather than leaving them
  unstamped. **Substantively, `(d)` is now identical to `(c)`** in its live effect, differing
  only in whether the state is documented as deliberate policy.
- A user who picks `(d)` believing it is the conservative, status-quo-preserving choice would be
  mistaken: the status quo is now the least conservative of the three options.

**No option is recommended here and none is marked as a default.** The choice belongs to the
user.

## 3. The Group A regression — a separate decision item

Literature repository commit `bb3bf18` overwrote two documents' `provenance_fidelity`:

| Document | Was | Now | Current `word_ratio` |
|---|---|---|---|
| `wijesekera_1990_constructivemodallogicsi` | `ocr_rescanned_reflowed_partial_symbol_loss` | `verified_conversion` | 0.9922 |
| `simpson_1994_intuitionisticmodallogic` | `ocr_rescanned_reflowed_partial_symbol_loss` | `verified_conversion` | 0.9828 |

`ocr_rescanned_reflowed_partial_symbol_loss` is **not** on `QUARANTINED_FIDELITY_VALUES` either,
so this overwrite did not change whether these documents surface in default search — both values
are non-quarantined. What was lost is the **explicit disclosure** that the conversion has known
partial symbol loss from OCR reflow — a warning a citing agent previously received and no longer
does.

**Fix cost, stated honestly**: 2 `jq` edits to `$LITERATURE_DIR/index.json` (data, not repo
source) would restore the prior value. Nothing else is required.

**Why this is surfaced rather than actioned**: restoring the prior value **reverses another
repository's deliberate commit**. Both documents now have real source PDFs on disk (per Phase 6
verification), so `verified_conversion` is arguably a computable, defensible value for them —
what was lost is the warning, not necessarily an incorrect ratio.

**Durability gap**: this task's Phase 4 `SIX_VALUE_ENUM` guard in
`literature-fidelity-audit.sh` works correctly, but it only constrains writes made through that
script. Commit `bb3bf18` wrote `index.json` by a different route entirely and bypassed the
guard. If the user wants durable protection against this class of regression, that protection
would need to live in the Literature repository itself (e.g., a pre-commit check on
`index.json` edits) — it is a separate piece of work, not something this task's file scope
(`literature-search.sh` and `literature-fidelity-audit.sh`) can provide.

## 4. Residual findings — no decision needed, but recorded so nothing is lost

**The former Phase 6 DJVU gate is closed, not waived.** `chagrovzakharyaschev_1997_modallogic`
already has `source.pdf` (53,951,887 bytes) beside `source.djvu`; `pdftotext` is on `PATH` and is
already the exact extractor `literature-fidelity-audit.sh` uses; the `.djvu` branch is never
reached for this document. No install and no user authorization were required. The old gate
check (`command -v djvutxt`) was a **false negative**: it tests `PATH` availability, not whether
the document is actually classifiable — this document was classifiable via the PDF the whole
time.

**`arisakadasstrassburger_2015` remains quarantined — the honest verdict, not a bug.** Its entry
has migrated to the `sources/` schema (`path`/`id` present), so re-adjudication ran through
default mode rather than `--legacy-schema` (which now enumerates 0 legacy entries index-wide, a
consequence of the same schema migration). The re-run measured, directly via the audit script:
`md_words = 10,012`, `pdf_words = 18,575`, `word_ratio = 0.539` — essentially unchanged from the
previously stored value and far below `RATIO_THRESHOLD` (0.75). The markdown conversion genuinely
contains only about half the source's words. It stayed `unadjudicated` after the re-run.
`arisakadasstrassburger_2015` is the only modal-logic document still quarantined, and the one
this task's originating description called out as central to the working modal-logic set. The
user may want to re-convert the source with a different pipeline rather than re-adjudicate the
existing conversion — but that is not done here.

**`gabbay_1994` is a second `unadjudicated` document** (`word_ratio` 0.11, no source found on
disk), not previously reported in this task's earlier artifacts.

**`$LITERATURE_DIR/.sources-recovered/` is empty.** Recovered sources were migrated into
`$LITERATURE_DIR/sources/<doc_id>/source.{pdf,djvu}`. Phase 6 repointed
`literature-fidelity-audit.sh`'s `--legacy-schema` startup guard (no longer hard-fails on an
absent/empty `.sources-recovered/`) and `classify_legacy()`'s source resolution (prefers
`sources/<doc_id>/`, falls back to `.sources-recovered/` only if present) to match, and annotated
`specs/literature/SOURCES.md:60` to record the migration.

**The Phase 1-5 code is now a functional no-op.** Against the current `index.json`, the `doc_id`
fallback added by Phase 1's four-site fix adds **zero** keys (`old 127 / new 127`, `added: []`),
and the `--legacy-schema` gate (`doc_id`+`chunks_dir` present, `path`/`id` absent) matches **0 of
321** entries — because the Literature repo's migration gave every former legacy-schema entry a
`sources/`-prefixed `path`. The working tree had reverted this code as an uncommitted,
unexplained diff (43 insertions / 357 deletions against `HEAD`); Phase 6.1 restored it from
`HEAD` behind a `git-snapshot.sh --no-revert` checkpoint (patch:
`specs/555_literature_search_fidelity_schema_quarantine/working-progress-1785112536.patch`).
Restoring was the conservative default — `HEAD` is the committed record of completed,
already-verified work, and the snapshot makes the revert recoverable if it turns out to have
been a deliberate concurrent decision. **The question this memo puts to the user, without
answering it: keep this code as defensive coverage for any future legacy-schema ingest pipeline,
or retire it deliberately as dead code now that the corpus has moved past the schema it
targets?**

**An incidental measurement side effect, recorded for completeness.** Phase 6.4's default-mode
`--write` run (needed to re-adjudicate `arisakadasstrassburger_2015`) recomputes ratios for the
entire `sources/` corpus — the script has no single-document targeting mode. Of 190 stamped
entries, 182 were unchanged and 8 changed: all 8 are `burgess_1984_sec01` through `_sec08`, all
remaining `verified_conversion` before and after, with `word_ratio` drifting from `1.0041` to
`1.0033` (a shift of about 0.08%, no change of value class). This is most likely minor
`pdftotext` extraction non-determinism between runs and is unrelated to arisaka or to Group
A/B. No `provenance_fidelity` value changed anywhere in the corpus as a result. It is recorded
here rather than actioned, per the same no-threshold-adjustment, no-hand-stamping discipline
applied to `arisakadasstrassburger_2015` itself.

## Summary for the user

Three things need a decision:

1. **Group B (66 `no_source_pdf` documents)**: choose `(b)` restore quarantine (and decide scope:
   9 or 66), `(c)` formalize the current citable-by-default state as deliberate policy, or `(d)`
   leave as-is (now equivalent in effect to `(c)`).
2. **Group A regression** (`wijesekera_1990`, `simpson_1994`): restore the
   `ocr_rescanned_reflowed_partial_symbol_loss` warning (2 `jq` edits to
   `$LITERATURE_DIR/index.json`), or accept the Literature repo's `verified_conversion`
   overwrite as final.
3. **Phase 1-5 code retirement**: keep the now-no-op `doc_id` fallback and `--legacy-schema` mode
   as defensive coverage, or remove them as dead code.

Nothing above has been decided or actioned by this phase. `arisakadasstrassburger_2015` staying
quarantined is the one outcome that was *not* left to the user — it is a measured, honest result
of re-running the existing audit pipeline with unchanged thresholds, not a policy choice.
