# Research Report: Task #555

**Task**: 555 - literature_search_fidelity_schema_quarantine
**Started**: 2026-07-25
**Completed**: 2026-07-25
**Effort**: small (single targeted key-derivation fix + a bounded audit-extension question)
**Dependencies**: None
**Sources/Inputs**:
- `.claude/scripts/literature-search.sh` (full read, all 1177 lines)
- `.claude/scripts/literature-fidelity-audit.sh` (full read, all 480 lines)
- `$LITERATURE_DIR/index.json` (291 entries, live)
- `$LITERATURE_DIR/.literature.db` (live SQLite FTS5 queries)
- `specs/literature-index.json` (per-repo sub-index, live)
- `$LITERATURE_DIR/.sources-recovered/` (live directory listing)
- `$LITERATURE_DIR/zotero-library.json`, `~/Zotero`, `~/Documents/Zotero` (live checks)
- Empirical verification: patched a scratch copy of `literature-search.sh` and ran real
  searches against the live corpus (no repo files modified)
**Artifacts**: this report
**Standards**: report-format.md, subagent-return.md

## Executive Summary

- The bug, the fix, and its effect were all empirically confirmed against the live corpus, not
  just read out of the source: patching a scratch copy of `literature-search.sh`'s
  `load_fidelity_map()` to add a `doc_id`-keyed fallback branch (alongside the existing
  `sources/`-path-prefix branch) makes a real default (no-flag) search for Wijesekera/Simpson
  content return non-degraded, non-empty results with the correct
  `ocr_rescanned_reflowed_partial_symbol_loss` fidelity — where the unpatched script returns
  `{"results": [], "degraded": true}`.
- **Q1 — key-derivation fix shape**: the four `load_fidelity_map()` copies
  (`literature-search.sh:227,527,764,908`) are byte-identical in executable logic (only the
  docstring/comment differs at line 227 vs. the three shortened "see primary" comments). Fix all
  four in place with the identical patch; do not factor into a shared importable module. See
  "Findings > Q1" for the rationale and the exact diff.
- **Q2 — Group A verification**: `bash .claude/scripts/literature-search.sh "constructive modal
  logic Wijesekera" 5` (and a Simpson-specific query) on the *unpatched* script returns
  `"degraded": true, "fallback_tier": "none", "results": []`. On the patched script the same
  invocation returns `"degraded": false, "fallback_tier": "bm25"` with 3 ranked results carrying
  `"provenance_fidelity": "ocr_rescanned_reflowed_partial_symbol_loss"`. Full transcripts in
  "Findings > Q2".
- **Q3 — recovered-PDF path**: `literature-fidelity-audit.sh` explicitly and by design never
  touches the 18 legacy `doc_id`/`chunks_dir` entries (its own header, lines 63-65, states this).
  It also cannot be pointed at the `.sources-recovered/` + per-doc `chunks_dir` layout unmodified:
  its `mds` discovery filters out every `chunk_NNNN.md` file, which is the *only* content these
  20 directories contain. `.djvu` extraction is explicitly unimplemented in the audit script and
  no djvu-text tool (`djvutxt`, `djvups`) or working PyMuPDF djvu codec exists on this machine —
  verified by direct probe. I hand-computed real word-ratios for 5 of the 6 recoverable-and-PDF
  Group-B docs against their recovered PDFs; 4 exceed the 0.75 verified-conversion threshold
  outright, 1 falls into the secondary disclosure/proof-completeness path. See "Findings > Q3".
- **Q4 — 10 unrecoverable docs**: options (b) and (c) are laid out with costs; 9 of the 10 are
  confirmed (by `source_path`) to originate from a different project's ephemeral scratch/session
  directories and are not referenced by cslib's own `specs/literature-index.json` at all — this
  materially lowers the urgency of a cslib-driven fix for those 9. Only
  `massacci_2000_single_step_tableaux_for_modal_logics` is cslib-relevant (it IS in
  `specs/literature-index.json`). Recommendation surfaced for user decision, not chosen. See
  "Findings > Q4".
- **Q5 — fail-open preserved**: confirmed by direct diff of the old vs. new key map built from
  the live index.json: 95 keys before, 97 after (only the two Group-A additions), zero removed
  keys, zero changed values. A missing map entry still resolves to `unverified_summary` via the
  unchanged `fmap.get(doc_id) or "unverified_summary"` line in `get_fidelity()`. See "Findings >
  Q5".
- **Zotero findings assessed as accurate but non-blocking for this task**: `~/Documents/Zotero`
  (939-item `storage/`) is confirmed the real profile; `~/Zotero` exists but has no `storage/` at
  all. `zotero-library.json` (400 records) contains zero matches for any of the 18 target docs.
  Neither fact blocks the Q1 fix or the Q3 audit path for the 6 non-djvu recoverable docs, since
  neither touches Zotero. They DO block any future attempt to re-acquire the 10 unrecoverable
  docs via the existing `/literature` Zotero-search pathway. See "Findings > Zotero Assessment".

## Context & Scope

Global `$LITERATURE_DIR/index.json` (291 entries total) carries two entry schemas: 273 entries
with `id` + `path` starting with `"sources/<dir>/"`, and (verified directly, not just from the
delegation context) **20** entries with `doc_id` + `chunks_dir` and no `path`/`id` fields at all.
Of those 20, 2 (`proofs_and_types`, `van_doorn_2015_propositional_calculus_coq`) are legacy
records that ALSO carry a proper `path="sources/..."` and `id` field from a later re-ingestion,
so they already resolve correctly today and are not part of this task's 18-doc problem set. The
remaining **18** are schema-B-only (`id: null`, `path: null`) — this is the exact set the
delegation context describes:

- **Group A (2, already honestly stamped)**: `wijesekera_1990_constructivemodallogicsi`,
  `simpson_1994_intuitionisticmodallogic` — `provenance_fidelity:
  "ocr_rescanned_reflowed_partial_symbol_loss"` (not in `QUARANTINED_FIDELITY_VALUES`).
- **Group B (16, `provenance_fidelity: null`)**: everything else. 6 of these 16 have a recovered
  source PDF/DJVU in `.sources-recovered/` (`arisakadasstrassburger_2015`,
  `marinmoralesstrassburger_2021`, `pacheco_2024`, `biermandepaiva_2000`,
  `alechinamendlerdepaivaritter_2001`, `chagrovzakharyaschev_1997` [djvu]). The remaining 10 are
  unrecoverable: `bonakdarpour_sheinvald_2023_finite_word_hyperlanguages`,
  `fadiheh_etal_2019_upec_processor_security_verification`,
  `finkbeiner_etal_2017_monitoring_hyperproperties`,
  `finkbeiner_etal_2018_rvhyper_runtime_verification_tool`,
  `guarnieri_etal_2021_hardware_software_contracts_secure_speculation`,
  `sousa_dillig_2016_cartesian_hoare_logic_k_safety`, `9789004252882-bp000004`,
  `the_modal_future_...z-lib.sk`, `wdb.cariani.santorio`,
  `massacci_2000_single_step_tableaux_for_modal_logics`.

`.sources-recovered/` (verified, ~17MB, 8 files) contains exactly: 7 PDFs + 1 `.djvu`
(`chagrovzakharyaschev_1997_modallogic.djvu`), matching all 8 of the recovered-doc names in the
delegation context (2 of the 8 — `wijesekera_1990`, `simpson_1994` — are Group A, recovered for
completeness even though their fidelity stamp is already fine).

`specs/literature-index.json` (cslib's per-repo sub-index, 20 entries) references 9 of the 18:
all of Group A and 7 of the 16 Group-B docs (the modal-logic-cluster ones, including
`massacci_2000_...` from the "unrecoverable 10"). The other 9 unrecoverable docs
(hyperproperties/security-verification papers, `the_modal_future_...`, `wdb.cariani.santorio`,
`9789004252882-bp000004`) are **not** referenced by cslib's sub-index at all — their
`source_path` fields point at another project's `/tmp/.../Philosophy-Papers-PossibleWorlds/...`
scratch directories or `specs/literature/` paths that do not exist in cslib's own
`specs/literature/` (checked directly: absent).

No files outside `specs/555_literature_search_fidelity_schema_quarantine/` were modified during
this research. The only "fix" applied was to a throwaway scratch copy of `literature-search.sh`
in the session scratchpad, used solely to empirically verify the fix before recommending it, and
deleted afterward.

## Findings

### Q1 — Exact shape of the key-derivation fix; fix all four sites or factor to one?

`load_fidelity_map()` appears at `literature-search.sh:227` (primary `do_search` heredoc),
`:527` (the unscoped-retry fallback inside `do_search`, used when a `--project` filter yields
zero results), `:764` (`do_read`), and `:908` (`do_toc`). Diffing all four function bodies
directly confirms: **the executable logic is byte-identical across all four** — only the
docstring at line 227 (a full multi-paragraph explanation) versus the three shortened
`# see the primary do_search heredoc` comments at the other sites differ. This was verified
programmatically (extracted each function body between `def load_fidelity_map` and
`def get_fidelity`, diffed pairwise — the only diff hunks are comment lines).

Current logic (all four sites):
```python
prefix = "sources/"
for e in idx.get("entries", []) or []:
    pf = e.get("provenance_fidelity")
    if pf is None:
        continue
    path = e.get("path")
    if not isinstance(path, str) or not path.startswith(prefix):
        continue
    dirname = path[len(prefix):].split("/", 1)[0]
    if dirname:
        fmap.setdefault(dirname, pf)
return fmap
```
Every schema-B entry has `path = None`, so `isinstance(path, str)` is `False` for all 18 (and for
the pre-2-in-273 duplicates too, though those already resolve via their own separate
`sources/`-prefixed record), and the entry is skipped — never entering `fmap` even when
`provenance_fidelity` is a real, non-null, non-quarantined value (Group A).

**Recommended fix** — add a second branch keyed directly by `doc_id` (which for entries in this
schema IS `chunks_data.doc_id` exactly, with no directory-name indirection needed, since there is
no `sources/<dir>/` path to derive one from):
```python
prefix = "sources/"
for e in idx.get("entries", []) or []:
    pf = e.get("provenance_fidelity")
    if pf is None:
        continue
    path = e.get("path")
    if isinstance(path, str) and path.startswith(prefix):
        dirname = path[len(prefix):].split("/", 1)[0]
        if dirname:
            fmap.setdefault(dirname, pf)
        continue
    doc_id = e.get("doc_id")
    if isinstance(doc_id, str) and doc_id:
        fmap.setdefault(doc_id, pf)
return fmap
```

**Apply this identically at all four sites; do not factor into a shared importable module.**
Rationale:
1. The four occurrences are separate `python3 <<PYEOF` heredocs launched as independent
   subprocess invocations from within one bash script — there is no interpreter state or import
   path shared between them today. Introducing a shared, importable `.py` module would mean a
   new companion file, `sys.path` wiring in four places, and a new on-disk dependency for a
   script that is currently fully self-contained; that is disproportionate to a 5-line logic
   change.
2. This exact duplication pattern (full docstring at the primary site, "see primary" comments at
   the other three) is the codebase's own established convention for this function already — the
   three secondary sites explicitly defer their documentation to the first. Fixing all four
   identically preserves that convention rather than introducing an inconsistent partial
   refactor.
3. A real regression check (see Q5) confirms an in-place four-site patch changes exactly 2 keys
   out of 97 with zero unintended side effects — a minimal, low-risk diff. Factoring to a shared
   module would be a materially larger and riskier change for the same behavioral result, and is
   better deferred to a dedicated future task if this function accumulates more logic later (it
   has not needed a second change since task #835 first introduced it).

Update the line-227 docstring to describe the new dual-key behavior (directory-name for
`sources/`-schema entries, direct `doc_id` for legacy `doc_id`/`chunks_dir`-schema entries); the
three secondary comments need only note the new branch exists, per their existing "see primary"
convention.

### Q2 — Verifying Group A restoration

**Before the fix** (current `literature-search.sh`, unpatched, run directly against the live
corpus):
```
$ bash .claude/scripts/literature-search.sh "constructive modal logic Wijesekera" 5
{
  "results": [],
  "degraded": true,
  "fallback_tier": "none",
  "query_error": null
}
```
Running with `--include-unverified` confirms the docs ARE indexed and matched, just quarantined:
```
$ bash .claude/scripts/literature-search.sh --include-unverified "constructive modal logic Wijesekera" 5
degraded: False  fallback_tier: bm25
wijesekera_1990_constructivemodallogicsi  unverified_summary   <- WRONG: should be ocr_rescanned_...
simpson_1994_intuitionisticmodallogic     unverified_summary   <- WRONG: should be ocr_rescanned_...
...
```

**After the fix** (verified by patching a scratch copy of the script and re-running the exact
same commands against the same live corpus, no repo files touched):
```
$ bash <patched-copy> "constructive modal logic Wijesekera" 5
{
  "results": [
    { "doc_id": "wijesekera_1990_constructivemodallogicsi", ...,
      "provenance_fidelity": "ocr_rescanned_reflowed_partial_symbol_loss",
      "match_tier": "bm25" },
    { "doc_id": "simpson_1994_intuitionisticmodallogic", ...,
      "provenance_fidelity": "ocr_rescanned_reflowed_partial_symbol_loss",
      "match_tier": "bm25" },
    ...
  ],
  "degraded": false,
  "fallback_tier": "bm25",
  "query_error": null
}

$ bash <patched-copy> "Simpson proof theory modal logic" 5
degraded: False  tier: bm25
simpson_1994_intuitionisticmodallogic  ocr_rescanned_reflowed_partial_symbol_loss
```

**What "non-degraded" looks like, precisely**: the envelope's top-level `"degraded"` field is
`false` and `"fallback_tier"` is `"bm25"` (not `"none"`/`"phrase_retry"`/`"trigram"`), AND at
least one result object's own `"provenance_fidelity"` is
`"ocr_rescanned_reflowed_partial_symbol_loss"` rather than `"unverified_summary"` (the latter
would indicate the query still only surfaced results via `--include-unverified`-style quarantine
bypass, or an unrelated doc). Any content-bearing query that a human would expect to hit
Wijesekera 1990 or Simpson 1994 chunks works for this check — the two above are not privileged,
just confirmed-working examples. No `--include-unverified` flag is needed post-fix; that flag
should return the identical result set (superset behavior is unaffected since these entries are
no longer quarantined in the first place).

### Q3 — Recovered-PDF path for the 8 recovered docs

**`literature-fidelity-audit.sh` does not, and structurally cannot without modification, consume
`.sources-recovered/` or the legacy schema.** This is not a gap to patch quietly — it's the
script's own documented design (header comment, lines 63-65): *"Entries using the unrelated
legacy `doc_id`/`chunks_dir` schema (no `path`/`id` fields, from a different ingestion pipeline,
live outside `sources/`) are never matched or written."* Three independent structural reasons,
all verified directly against the script and the live filesystem:

1. **Directory root mismatch**: `classify_dir()` operates on `$LITERATURE_DIR/sources/<dirname>`
   (via `SOURCES_DIR = "$LITERATURE_DIR/sources"`). The 18 legacy entries' actual content lives
   at `$LITERATURE_DIR/<dirname>/` directly (the `chunks_dir` field), one level up with no
   `sources/` prefix. `os.listdir(SOURCES_DIR)` never enumerates these directories at all.
2. **`.md` discovery excludes exactly the files these directories contain**: `classify_dir()`'s
   `mds` filter is `e.lower().endswith(".md") and not re.match(r"^chunk_\d+\.md$", e, re.IGNORECASE)`
   — i.e. it takes the *non*-chunk markdown as "the real converted document" and treats
   `chunk_NNNN.md` files as sub-artifacts to ignore. Verified directly: every one of these 18
   `chunks_dir` directories contains *only* `chunk_NNNN.md` files (checked
   `arisakadasstrassburger_2015`'s directory: 42 files, all `chunk_0001.md`...`chunk_0042.md`;
   same pattern for `chagrovzakharyaschev_1997`). Pointed at one of these directories unmodified,
   `classify_dir()` would find `has_md = False`, and — since a recovered PDF is present —
   classify the doc as `"not_yet_converted"` (a **misclassification**: it undercounts a document
   that IS already converted and chunked, just under the different chunking layout).
3. **`resolve_targets()` requires `"id" in e`**: `[e for e in idx.get("entries", []) if
   isinstance(e.get("path"), str) and e["path"].startswith(prefix) and "id" in e]` — none of the
   18 entries have an `id` field (`None`), so even a directory that DID get correctly classified
   would resolve to zero write targets (`kind == "no_match"`), and nothing would be stamped.

**`.djvu` is explicitly unimplemented and no working extractor exists on this machine.**
`pdf_word_count()` in the audit script:
```python
if pdf_path.lower().endswith(".djvu"):
    print(f"[warn] .djvu extraction not implemented, skipping: {pdf_path}", file=sys.stderr)
    return 0
```
— contributes 0 words, which for a lone-PDF directory drives `pdf_words_total == 0` ->
`"unverified_no_baseline"` (still quarantined, wrong reason). I checked for the two conversion
paths `literature-convert.sh`'s own `try_djvu()` already knows about (`djvutxt`, or
`djvups`+`ps2pdf`) — **neither `djvutxt` nor `djvups` is installed** (`which` returns nothing,
exit 3). I also tried PyMuPDF (`fitz`, present, v1.27.2) directly against the recovered
`chagrovzakharyaschev_1997_modallogic.djvu`: `fitz.open(...)` raises
`FileDataError: Failed to open file` — this build of PyMuPDF has no working DJVU codec either.
**Concrete consequence**: `chagrovzakharyaschev_1997_modallogic` cannot be classified via the
existing word-ratio detector on this machine without first installing `djvulibre`
(`djvutxt`/`djvups`) or an equivalent DJVU-to-text tool; this is an environment gap, not a script
bug, and is a prerequisite for any implementation phase that wants to close this doc.

**Concrete invocation and numbers for the other 5 non-djvu recoverable Group-B docs**: I
hand-computed the audit script's own word-ratio formula (`pdftotext -layout <pdf> -` word count
vs. concatenated `chunk_*.md` word count) directly against the live recovered PDFs and existing
chunks, replicating exactly what an extended audit invocation would compute:

| doc_id | pdf_words | md_words (all chunk_*.md) | ratio | vs. 0.75 threshold |
|---|---|---|---|---|
| `biermandepaiva_2000_onanintuitionisticmodallogic` | 10482 | 10848 | 1.0349 | verified_conversion (>=0.75) |
| `marinmoralesstrassburger_2021_...` | 9988 | 10146 | 1.0158 | verified_conversion (>=0.75) |
| `pacheco_2024_collapsingconstructive...` | 5164 | 5318 | 1.0298 | verified_conversion (>=0.75) |
| `alechinamendlerdepaivaritter_2001_...` | 10629 | 10845 | 1.0203 | verified_conversion (>=0.75) |
| `arisakadasstrassburger_2015_...` | 18575 | 10012 | 0.5390 | below threshold — needs the audit script's secondary disclosure/proof-completeness pass (not computed here; same as any other sub-0.75 doc today) |

**Recommended concrete path** (a decision for the implementation plan, not executed here): extend
`literature-fidelity-audit.sh` with a second mode (e.g. `--legacy-schema`) that: (a) enumerates
`idx["entries"]` where `doc_id` and `chunks_dir` are present and `path`/`id` are absent, (b)
resolves the source PDF/DJVU from `.sources-recovered/<doc_id>.{pdf,djvu}` instead of
`SOURCES_DIR/<dirname>`, (c) sums word counts over ALL `chunk_*.md` in `chunks_dir` as the
"md_words" side of the ratio (i.e. does NOT apply the chunk-exclusion filter — for this schema
the chunks ARE the document, there is no separate whole-document `.md`), (d) reuses the existing
`disclosure_check`/`proof_completeness_fraction` functions unchanged against that same chunk
text, and (e) stamps `provenance_fidelity`/`word_ratio` onto the matched entry by `doc_id`
equality instead of `resolve_targets()`'s `path`-prefix/`id`-presence matching. `.djvu` support
requires installing a DJVU text extractor first (or, as a fallback with lower fidelity, extending
`pdf_word_count()` to rasterize+OCR the djvu, which is a materially larger change and probably
not warranted for one document).

### Q4 — Options for the 10 unrecoverable docs (surfaced for user decision, not chosen)

Confirmed the exact 10, and confirmed only 1 (`massacci_2000_single_step_tableaux_for_modal_logics`)
is referenced by cslib's own `specs/literature-index.json`; the other 9 are not, and their
`source_path` values point to another project's ephemeral scratch directories or missing
`specs/literature/` files, not anything reachable from cslib.

- **Option (b): per-document adjudication.** A human (or an agent under explicit instruction, per
  the same disclosure standard `literature-fidelity-audit.sh` already uses) reads each of the 10
  documents' existing `chunk_*.md` content against known facts about the source (title, author,
  approximate length) and manually decides a value — most likely
  `provenance_fidelity: "unverified_no_baseline"` (a value already in the six-value enum,
  honestly describing "no source PDF exists to check against") stamped directly via a one-off jq
  patch, since `unverified_no_baseline` is explicitly listed as a legitimate enum value in the
  audit script's own docstring (line 38) for exactly this situation — a directory with no PDF at
  all. **Cost**: low engineering effort (a few jq edits), but `unverified_no_baseline` is
  currently IN `QUARANTINED_FIDELITY_VALUES` (`literature-search.sh:53`), so **this does not
  restore default-search visibility** — it only replaces a wrong fail-open default
  (`unverified_summary`, silently reached today) with an honest, explicit one
  (`unverified_no_baseline`, explicitly quarantined). **Downstream-citation risk**: minimal —
  these documents remain invisible to default search either way; the only change is that the
  *reason* recorded is now accurate, which matters if anyone later audits why a doc is
  quarantined.
- **Option (c): a new non-quarantined fidelity value.** E.g. `"unverified_no_baseline_admitted"`
  or similar, explicitly NOT added to `QUARANTINED_FIDELITY_VALUES`, so these 10 docs surface in
  default search despite having no PDF baseline to check fidelity against. **Cost**: touches the
  shared quarantine-value enum/vocabulary (a system-wide semantic change, not a per-doc data
  edit), and directly contradicts the delegation context's explicit constraint: *"The fail-
  open-to-unverified design is deliberate and MUST NOT be weakened by removing values from
  QUARANTINED_FIDELITY_VALUES"* — introducing a brand-new value that is deliberately excluded
  from that set for docs with literally no verifiable baseline is the same category of
  weakening, just via a new value rather than removing an old one. **Downstream-citation risk**:
  high — an agent citing one of these 10 docs' `unverified_no_baseline`-class chunks as
  authoritative would have zero means to check the claim against a source PDF; this is precisely
  the failure mode task #835's quarantine mechanism exists to prevent. Given 9 of the 10 are not
  even referenced by cslib's own sub-index, the risk/benefit ratio for cslib specifically is
  poor.
- These are laid out for the user to choose between (or to decide "leave as unverified_summary
  fail-open, do nothing further for these 10") — no unilateral choice was made here per the
  delegation instruction.

### Q5 — Fail-open semantics preserved

Verified directly by diffing the fidelity map built from the live index.json under the old vs.
new `load_fidelity_map()` logic:
```
old keys: 95   new keys: 97
added keys: ['simpson_1994_intuitionisticmodallogic', 'wijesekera_1990_constructivemodallogicsi']
removed keys: set()
changed-value keys: set()
```
Only the two Group-A entries gain a map entry; nothing existing changes or is removed. The reason
this is structurally guaranteed, not just empirically true today: the new `doc_id` branch is
reached only when `path` is NOT a `sources/`-prefixed string, and — same as the unchanged first
line of the loop body — `if pf is None: continue` still runs before either branch, so an entry
whose `provenance_fidelity` is `null` (all 16 Group-B docs, including the 6 that will later be
audited) is never added to `fmap` regardless of schema. `get_fidelity()`'s
`fmap.get(doc_id) or "unverified_summary"` is untouched, so any `doc_id` absent from the map — a
never-computed Group-B doc, a typo, a doc not yet ingested at all — still resolves to
`"unverified_summary"`, never to `"verified_conversion"`. Confirmed with a synthetic `"nonexistent_
doc_xyz"` lookup returning `"unverified_summary"` in the same test.

### Zotero Assessment

Both recorded findings were independently re-verified and are accurate, but neither is a
blocker for this task's core fix:
- `~/Documents/Zotero` has a populated `storage/` (939 entries) and is clearly the live profile;
  `~/Zotero` exists but has zero entries under any `storage/` path (only `zotero.sqlite`,
  `locate/`, `styles/`, `translators/` — a stale or non-primary profile). Several of the 18
  target docs' `source_path` fields already point into
  `/home/benjamin/Documents/Zotero/storage/...`, independently confirming this is the operative
  profile.
- `zotero-library.json` (400 records) contains zero title matches for any of Wijesekera, Simpson,
  Chagrov/Zakharyaschev, Bierman/de Paiva, Alechina, Marin, Pacheco, or Massacci — it is a stale
  export that predates (or never included) this task's 18 docs.
- **Relevance to this task**: the Q1 key-derivation fix and the Q3 audit-extension path for the 6
  non-djvu recoverable docs both operate entirely on `index.json` + already-recovered local files
  in `.sources-recovered/`; neither reads Zotero. These findings only matter if a future
  implementation phase wants to use the `/literature` Mode-A Zotero-search pathway to re-acquire
  the 10 still-unrecoverable docs — that pathway is currently non-functional for this purpose
  (stale export, wrong/incomplete profile data) and would need a fresh Better-BibTeX export
  pointed at `~/Documents/Zotero` before it could help, and even then most of the 10 do not
  appear to be Zotero-sourced items in the first place (their `source_path` values point at
  another project's scratch directories, not Zotero storage).

## Decisions

- Fix `load_fidelity_map()` at all four `literature-search.sh` sites identically (add a `doc_id`
  fallback branch); do not factor into a shared module — see Q1 rationale.
- Do not modify `QUARANTINED_FIDELITY_VALUES` under any option for Group B — confirmed no
  candidate fix requires or should touch this constant.
- Treat the 6 non-djvu-adjacent... (5 PDF + 1 djvu) recoverable Group-B docs as a distinct,
  separately-scoped follow-up requiring an `literature-fidelity-audit.sh` extension (not a
  same-PR change to `literature-search.sh`), since it touches a different script with different
  target-resolution logic and needs a DJVU-extractor environment dependency resolved first for
  1 of the 6.
- The 10 unrecoverable docs' disposition (option b vs. c vs. defer) is explicitly left for the
  user to decide, per the delegation instruction; no default was silently picked.

## Risks & Mitigations

- **Risk**: extending `literature-fidelity-audit.sh` to a new schema could accidentally start
  matching/writing to `sources/`-schema entries too if the new branch isn't carefully gated.
  **Mitigation**: gate the new branch strictly on `"doc_id" in e and "chunks_dir" in e and "path"
  not in e` (mirroring the existing script's own header-documented exclusion criterion), and add
  a regression check (as done here) diffing old vs. new stamped output before merging.
- **Risk**: `.djvu` support gap blocks 1 of the 6 recoverable Group-B docs indefinitely.
  **Mitigation**: treat as a separate, explicit environment prerequisite (install `djvulibre`) in
  the implementation plan rather than silently leaving `chagrovzakharyaschev_1997_modallogic`
  stuck at `unadjudicated`/`unverified_no_baseline`-by-omission; do not attempt an OCR-based
  workaround without an explicit decision, since that changes the fidelity-computation method
  itself.
- **Risk**: acting on Q4's option (c) would weaken the quarantine invariant the delegation context
  explicitly protects. **Mitigation**: this report presents but does not recommend option (c);
  any implementation must get explicit user sign-off before adding a new non-quarantined value.

## Context Extension Recommendations

- None specific to this task — the existing `literature-fidelity-audit.sh` header already
  documents its own legacy-schema exclusion (lines 63-65) accurately; no doc drift found there.

## Appendix

- Search queries used against the live corpus during verification: `"constructive modal logic
  Wijesekera"`, `--include-unverified "constructive modal logic Wijesekera"`, `"intuitionistic
  modal logic Simpson Kripke"` (no match — content-wording issue, not a fidelity issue), `"Simpson
  proof theory modal logic"` (matched).
- Live script/data references: `.claude/scripts/literature-search.sh:53` (`QUARANTINED_FIDELITY_
  VALUES`), `:227,527,764,908` (`load_fidelity_map` sites), `.claude/scripts/literature-fidelity-
  audit.sh:38` (six-value enum), `:63-65` (legacy-schema exclusion statement), `:194-209`
  (`pdf_word_count`, djvu skip), `:294-302` (`mds` chunk-exclusion filter), `:387-400`
  (`resolve_targets`, `id`-presence requirement).
- No file outside `specs/555_literature_search_fidelity_schema_quarantine/` was modified by this
  research; the verification patch was applied to and removed from a session-scratchpad copy
  only.
