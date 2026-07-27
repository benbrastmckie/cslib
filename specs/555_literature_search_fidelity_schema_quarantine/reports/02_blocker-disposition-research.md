# Blocker Disposition Research: Phase 6 (DjVu) and Phase 7 (10 unrecoverable docs)

**Date**: 2026-07-26
**Mode**: read-only investigation (no files modified)
**Headline**: Both blockers have been **overtaken by events**. Work done in the
`~/Projects/Literature` repository on 2026-07-26 — after this task's implementation summary was
written on 2026-07-25 — resolved the underlying condition of Blocker 1 and materially changed the
premise of Blocker 2. A previously-unreported regression to Group A was introduced by the same
work.

---

## 1. Blocker 1 (Phase 6): DjVu classification of `chagrovzakharyaschev_1997_modallogic`

**Verdict: (i) resolvable now with tooling already present — and in fact already resolved.**
This is **not** gated on a user-authorized system install.

### 1.1 The blocker's premise is stale in three independent ways

**(a) A source PDF now exists, so no DjVu tooling is needed at all.**

```
sources/chagrovzakharyaschev_1997_modallogic/
  source.djvu    7,152,341 bytes   (magic: AT&TFORM ... DJVM — valid DjVu)
  source.pdf    53,951,887 bytes   ← added 2026-07-26
```

`pdftotext` is already on `PATH` (`~/.nix-profile/bin/pdftotext`), which is the exact extractor
`literature-fidelity-audit.sh` already uses (line 203). The audit's `.djvu` stub at lines 195-199
("No djvutxt dependency assumed available … skipping") is simply never reached for this document
once the `.pdf` is the selected source. Added by commit `ea47e97` *"literature: consolidate the
two Chagrov & Zakharyaschev conversions"*.

**(b) The document has already been classified.** `index.json` currently records:

```
chagrovzakharyaschev_1997_modallogic → provenance_fidelity: "verified_conversion"
```

It is no longer `unadjudicated`, and `verified_conversion` is not quarantined, so it is already
visible in default search.

**(c) Even without the PDF, `djvutxt` works right now with no install.**

`djvulibre` 3.5.29 is **already built in the local nix store**:

```
/nix/store/wn787i4hxgjwhgg51m2yc1kl65xxjaxw-djvulibre-3.5.29-bin/bin/djvutxt
```

Verified against the actual file — clean extraction, exit 0, no stderr, no OCR:

```
$ djvutxt sources/chagrovzakharyaschev_1997_modallogic/source.djvu | wc -c
1381134
```

First bytes of extracted text confirm a real embedded text layer (not OCR):
`OXFORD LOGIC GUIDES: 35 / General Editors / DOV GABBAY / ANGUS MACINTYRE / DANA SCOTT …`

`nix-shell -p djvulibre --run 'command -v djvutxt'` also succeeds and resolves to that same store
path. This is a **user-level ephemeral shell, not a system-level change** — it does not touch
`configuration.nix`, home-manager, or `/run/current-system`. The plan's stated blocking
condition ("Installing `djvulibre` is a system-level change outside this task's declared file
scope") does not apply to this path.

### 1.2 Honest caveats on the nix path

Neither caveat affects resolution (a), which needs no DjVu tooling at all.

- The `-bin` store path has **no gcroot** (`nix-store --query --roots` returns empty), so it is
  garbage-collectable. Hardcoding the absolute store path into a script would be fragile.
- `nix-shell -p djvulibre` fetched two paths (`djvulibre-…-dev`, `stdenv-linux`) from
  `cache.nixos.org`, so it is not strictly offline, though the binary itself was already local.

### 1.3 What the plan's own gate check now reports

Phase 6's verification is `command -v djvutxt || echo "BLOCKED: …"`. That check still prints
`BLOCKED`, because the store path is not on `PATH`. **The gate's check is now a false negative**:
it tests PATH availability, not whether the document can be classified — and the document both
can be and already has been.

---

## 2. Blocker 2 (Phase 7): disposition of the unrecoverable documents

**Verdict: (ii) still genuinely a user decision — but the premise has shifted substantially, and
one of the three options appears to be de facto in effect already, without a recorded decision.**

### 2.1 Current state of the set

`massacci_2000_single_step_tableaux_for_modal_logics` is **no longer in the unrecoverable set**.
It now has `source.pdf` (269,417 bytes) and is stamped `verified_conversion`. The task
description's claim that it was "NOT recoverable … source gone" is stale. Since it was the only
one of the ten referenced by this repo's `specs/literature-index.json`, **the entire remaining
set is now unrelated to this repository's modal-logic working set.**

The remaining ten split as:

| doc_id | fidelity | chunks | source on disk | relevance |
|---|---|---|---|---|
| `arisakadasstrassburger_2015_onnestedsequentsforconstructivemodallogics` | `unadjudicated` | 40 | **yes (1 file)** | modal logic (cut-free CS5) |
| `9789004252882-bp000004` | `no_source_pdf` | 6 | none | unrelated (book chapter) |
| `bonakdarpour_sheinvald_2023_finite_word_hyperlanguages` | `no_source_pdf` | 52 | none | unrelated |
| `fadiheh_etal_2019_upec_processor_security_verification` | `no_source_pdf` | 61 | none | unrelated |
| `finkbeiner_etal_2017_monitoring_hyperproperties` | `no_source_pdf` | 5 | none | unrelated |
| `finkbeiner_etal_2018_rvhyper_runtime_verification_tool` | `no_source_pdf` | 8 | none | unrelated |
| `guarnieri_etal_2021_hardware_software_contracts_secure_speculation` | `no_source_pdf` | 73 | none | unrelated |
| `sousa_dillig_2016_cartesian_hoare_logic_k_safety` | `no_source_pdf` | 68 | none | unrelated |
| `the_modal_future_…_cariani_fabrizio_…` | `no_source_pdf` | 107 | none | unrelated (Cariani) |
| `wdb.cariani.santorio` | `no_source_pdf` | 59 | none | unrelated (Cariani) |

`arisakadasstrassburger_2015` is the one anomaly: it lists a source file present on disk yet
remains `unadjudicated` (which *is* quarantined). It is the only modal-logic item left in this
set, and it is the "cut-free CS5 source" the task description calls out as central.

### 2.2 The consequential finding: 9 of these are now citable in default search

`no_source_pdf` is **not** on the quarantine list:

```
literature-search.sh:53
QUARANTINED_FIDELITY_VALUES="unverified_summary unverified_no_baseline unadjudicated"
```

Verified empirically — a default, no-flag search returns them, non-degraded:

```
$ bash .claude/scripts/literature-search.sh "monitoring hyperproperties runtime verification"
  doc_id: finkbeiner_etal_2018_rvhyper_runtime_verification_tool
  provenance_fidelity: "no_source_pdf"
  match_tier: "bm25"
```

Before commit `bb3bf18`, these entries had no `provenance_fidelity` at all, so `get_fidelity()`
failed open to `unverified_summary` — which **is** quarantined — and they were excluded from
default search. Stamping them `no_source_pdf` moved them from *quarantined* to *citable*.

**This is materially the outcome of option (c)** — a non-quarantined value meaning "converted, no
obtainable baseline" — now in effect. It reached that state without the Phase 7 decision being
recorded. Two honest qualifications:

- `no_source_pdf` was **always** part of the audit script's six-value enum (line 38) and was
  **never** on the quarantine list. No one invented a new value, and
  `QUARANTINED_FIDELITY_VALUES` was never edited. Task 555's code is not the cause.
- What changed is *which documents carry it*, done by the Literature-repo migration, not by this
  task.

The honesty exposure the plan warned about is nonetheless now live: an agent citing one of these
9 documents has no source PDF against which any claim can be checked, and default search gives no
degraded signal.

### 2.3 Regression: Group A's human-adjudicated stamp was overwritten

Confirmed by direct comparison against git history:

```
$ git show bb3bf18~1:index.json | jq '… wijesekera_1990 … .provenance_fidelity'
"ocr_rescanned_reflowed_partial_symbol_loss"        ← before

current index.json
"verified_conversion"                                ← now
```

Both `wijesekera_1990_constructivemodallogicsi` and `simpson_1994_intuitionisticmodallogic` lost
the specific, human-adjudicated OCR-loss value and now read as generic `verified_conversion`.

This is precisely the clobbering that this task's Phase 4 `SIX_VALUE_ENUM` guard was added to
prevent. The guard works — but it only constrains `literature-fidelity-audit.sh`. Commit
`bb3bf18` ("migrate legacy doc_id corpus into sources/, adjudicate fidelity") wrote to
`index.json` by another route and bypassed it. Both documents now have real source PDFs present,
so `verified_conversion` is arguably *computable*; the loss is the explicit
partial-symbol-loss warning that a citing agent previously received.

### 2.4 Costs of each option, restated against the current state

Not a recommendation — the task description explicitly forbids resolving this unilaterally.

**Option (b) — stamp `unverified_no_baseline` on the 9.**
Files changed: `$LITERATURE_DIR/index.json` only (a few `jq` edits). Effect: **reverts** their
current default-search visibility, since `unverified_no_baseline` is quarantined. Downstream:
they become reachable only via `--include-unverified`. Citation risk: minimal — this is the most
conservative option and restores the pre-`bb3bf18` visibility while replacing a silent fail-open
with an explicit honest value. Note this is now a *rollback* of live behavior, not a no-op.

**Option (c) — a non-quarantined value for "no obtainable baseline".**
Files changed: none required — **this is already the operative state** via `no_source_pdf`.
Formalizing it would mean documenting `no_source_pdf` as a deliberate non-quarantined value in
`literature-search.sh` and the audit script header. Downstream: `literature-search.sh` default
search, `literature-briefing.sh` corpus selection, and `--lit` briefings all treat these 9 as
citable. Citation risk: **high**, and currently unannounced — the plan's own words: "an agent
citing one of these documents would have no source PDF against which to check the claim, which is
exactly the failure mode the quarantine mechanism exists to prevent."

**Option (d) — leave as-is.**
Files changed: none. Effect: identical to accepting option (c) in substance, since "as-is" now
means "citable in default search", not "quarantined" as it did when the plan was written. Worth
stating plainly because (d) has silently changed meaning since Phase 7 was authored.

**Option (e) — new, not in the original three: restore Group A.**
Files changed: `$LITERATURE_DIR/index.json` (2 entries). Restore
`ocr_rescanned_reflowed_partial_symbol_loss` on `wijesekera_1990` and `simpson_1994`. Independent
of the (b)/(c)/(d) choice, and arguably a straightforward bug fix rather than a policy decision —
but it reverses a value another repository's commit deliberately wrote, so it is surfaced rather
than actioned.

Separately, `arisakadasstrassburger_2015` (quarantined `unadjudicated`, has a source file on
disk, and is the modal-logic item of genuine interest here) looks classifiable now and may simply
need a re-run of `--legacy-schema` rather than any policy decision.

---

## 3. Correction to the recorded task state

The task description states that 8 recovered files are preserved in
`$LITERATURE_DIR/.sources-recovered/` (~17 MB). **That directory is empty.** The recovered
sources were instead migrated into their canonical per-document directories under
`$LITERATURE_DIR/sources/<doc_id>/source.{pdf,djvu}` by commits `e0ffb9b`, `bb3bf18`, and
`ea47e97`. Nothing was lost — the files are durable and in a better location — but any future
step that looks for them under `.sources-recovered/` will find nothing.

---

## 4. Summary

| Blocker | Status | Basis |
|---|---|---|
| Phase 6 — DjVu | **(i) resolvable now; already resolved** | `source.pdf` present (53.9 MB) → `pdftotext` suffices; independently, `djvutxt` in nix store extracts 1,381,134 chars cleanly; index already reads `verified_conversion` |
| Phase 7 — 10 docs | **(ii) still a user decision, premise shifted** | `massacci_2000` recovered and no longer in set; 9 remaining are stamped `no_source_pdf`, which is non-quarantined, so option (c)'s effect is already live and unannounced |
| *(new)* Group A regression | **needs a decision** | `bb3bf18` overwrote `ocr_rescanned_reflowed_partial_symbol_loss` → `verified_conversion` on `wijesekera_1990` and `simpson_1994`, bypassing the `SIX_VALUE_ENUM` guard |

Phase 6's gate can be closed without any user authorization. Phase 7's gate remains genuinely
open, but the decision the user is now being asked to make is *"should the 9 stay citable?"* —
the reverse polarity of the question the plan posed, because the default has already moved.
