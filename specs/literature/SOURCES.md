# Pending Literature Sources

Sources referenced by tasks but not yet full-text ingested into the global
Literature corpus (`~/Projects/Literature/`). Each needs a PDF acquired, then
`/literature <path-to-pdf>` (Mode B) to convert + FTS-index, and
`bash .claude/scripts/zotero-index-add.sh` / sub-index update to register.

## S5 / KB5 tableau termination (task 504 follow-up)

Both are the canonical references for terminating modal tableau calculi where the
edge-local modal-depth-decrement measure (`RuleApplicationSpec.rankStep`) fails —
directly grounding task 504's proven Phase-2 obstruction
(`modalApplyOneS5_rankStep_not_dischargeable`).

- **Massacci, F. (2000).** *Single Step Tableaux for Modal Logics: Computational
  Properties, Complexity and Methodology.* Journal of Automated Reasoning 24(3),
  319–364. DOI: 10.1023/A:1006155811656. BibKey: `Massacci2000`.
  Status: **✅ ACQUIRED + INGESTED** (2026-07-14, user-supplied PDF). Global corpus
  `doc_id: massacci_2000_single_step_tableaux_for_modal_logics` (77 chunks); source
  PDF at `~/Projects/Literature/massacci_2000_single_step_tableaux_for_modal_logics/source.pdf`;
  registered in `specs/literature-index.json` sub-index. Searchable via
  `literature-search.sh`.
  Why: uniform terminating single-step tableaux across the modal cube incl.
  S5/K5/KB5; the loop-checking / prefix-management termination machinery.

- **Goré, R. (1999).** *Tableau Methods for Modal and Temporal Logics.* In Handbook
  of Tableau Methods (eds. D'Agostino, Gabbay, Hähnle, Posegga), 297–396. Kluwer.
  DOI: 10.1007/978-94-017-1754-0_6. BibKey: `Gore1999`.
  Status: **PDF not acquired** (paywalled, Kluwer handbook chapter). No open-access
  copy found via automated discovery.
  Why: canonical survey of loop-checking and termination for modal tableaux,
  including the S5 case.

### Acquisition options
1. Zotero: if either PDF is in the user's Zotero library, export/attach and ingest
   via `/literature`.
2. Institutional access: download from the publisher (Springer / SpringerLink) and
   drop the PDF here, then run `/literature specs/literature/<file>.pdf`.
3. Preprints: Goré maintains technical-report versions of much of this material
   (ANU/RSISE tech reports) that may be openly available; Massacci's earlier
   conference papers (TABLEAUX/CADE) overlap substantially and may be OA.

---

# Part II — Indexed Documents Whose Source File Is Gone

The entries below are **already chunked and searchable** in the global corpus (via
`literature-search.sh --include-unverified`), but their **source file no longer exists
anywhere on disk**. Without a source there is no baseline for
`literature-fidelity-audit.sh` to classify against, so they cannot earn a
`provenance_fidelity` stamp and remain quarantined from default search.

**Why they vanished.** Ingestion records a `source_path` pointing at wherever the file sat at
ingest time. For six of these that was a session-scoped scratchpad under `/tmp/claude-*/`,
which is periodically cleaned; for three it was `specs/literature/` in this repo, and the files
were later removed. None were ever committed to git (verified via `git log --all`), so there is
no history to restore from.

A further eight documents were found still alive and have been **preserved** — four of them
rescued directly out of `/tmp` scratchpads that were pending cleanup. Those are safe and are not
listed here. **Update**: these recovered sources were subsequently migrated from
`$LITERATURE_DIR/.sources-recovered/<doc_id>.{pdf,djvu}` into the canonical
`$LITERATURE_DIR/sources/<doc_id>/source.{pdf,djvu}` layout; `.sources-recovered/` is now empty
and no longer holds any live sources.

**Massacci 2000 is NOT in this list.** It was briefly believed lost because its `source_path`
pointed at a deleted staging copy, but the real PDF was present all along at
`$LITERATURE_DIR/massacci_2000_single_step_tableaux_for_modal_logics/source.pdf` (269 KB). The
stale pointer has been corrected in the global index; no action is needed. See Part I above,
which already recorded it as acquired.

**What to do with each entry.** Either re-acquire the source, drop it in `specs/literature/`,
and re-ingest with `/literature <path>`; or retire the index entry, since chunks with no
recoverable source can never pass verification.

## Cariani / temporal-semantics group

Ingested 2026-07-06 from `specs/literature/`, later removed. Relevance to the current Lean
proof-theory work is indirect (tense and future-directed semantics rather than tableaux), so
re-acquire only if that line of work is still live.

### Kamp — Formal Properties of 'Now'

| Field | Value |
|---|---|
| doc_id | `9789004252882-bp000004` |
| Author | Hans Kamp (dedicated to the memory of Arthur Prior) |
| Chunks | 6 |
| Was at | `specs/literature/9789004252882-BP000004.pdf` |

The identifier `9789004252882` is a Brill ISBN; `BP000004` is the chapter.

### Cariani — The Modal Future: A Theory of Future-Directed Thought and Talk

| Field | Value |
|---|---|
| doc_id | `the_modal_future_..._z-library.sk_1lib.sk_z-lib.sk` (full id in index.json) |
| Author | Fabrizio Cariani |
| Type | Monograph, Cambridge University Press |
| Chunks | 107 |

The doc_id embeds a z-library mirror provenance. If re-acquired, prefer a legitimate copy, and
rename the doc_id on re-ingest so mirror-site names do not persist in the index.

### Cariani & Santorio — Will Done Better: Selection Semantics, Future Credence, and Indeterminacy

| Field | Value |
|---|---|
| doc_id | `wdb.cariani.santorio` |
| Authors | Fabrizio Cariani, Paolo Santorio |
| Chunks | 59 |
| Source note | White Rose eprints (Leeds / Sheffield / York), `eprints.whiterose.ac.uk` |

Open access via White Rose — likely the easiest of these to recover.

## Hyperproperties / verification group

All six were ingested 2026-07-06 from a scratchpad belonging to a **different project**
(`-home-benjamin-Philosophy-Papers-PossibleWorlds`), not this repo. They appear unrelated to
CSLib's Lean formalisation work. The likely correct action is to retire these entries from this
corpus, or re-home them under whichever project actually uses them, rather than re-acquire.

| doc_id | Title / authors | Chunks |
|---|---|---|
| `bonakdarpour_sheinvald_2023_finite_word_hyperlanguages` | Finite-Word Hyperlanguages — B. Bonakdarpour, S. Sheinvald | 52 |
| `fadiheh_etal_2019_upec_processor_security_verification` | Processor Hardware Security Vulnerabilities and their Detection by Unique Program Execution Checking — M. R. Fadiheh et al. | 61 |
| `finkbeiner_etal_2017_monitoring_hyperproperties` | Monitoring Hyperproperties — B. Finkbeiner, C. Hahn, M. Stenger, L. Tentrup | 5 |
| `finkbeiner_etal_2018_rvhyper_runtime_verification_tool` | RVHyper: A Runtime Verification Tool for Temporal Hyperproperties — B. Finkbeiner et al. | 8 |
| `guarnieri_etal_2021_hardware_software_contracts_secure_speculation` | Hardware-Software Contracts for Secure Speculation — M. Guarnieri et al. | 73 |
| `sousa_dillig_2016_cartesian_hoare_logic_k_safety` | Cartesian Hoare Logic for Verifying k-Safety Properties — M. Sousa, I. Dillig | 68 |

## Related open issues

- **Search visibility.** Even with sources re-acquired, every document using the
  `doc_id`/`chunks_dir` index schema stays hidden from default `literature-search.sh` until the
  fidelity-map key derivation is fixed — it currently keys only off a `sources/` path prefix.
  Tracked as its own task.
- **Recurrence.** Ingestion writes `source_path` into session-scoped temp directories. Until the
  pipeline copies sources into durable storage at ingest time, every future scratchpad ingest
  will eventually land in this list.
- **Zotero.** The Better BibTeX export at `$LITERATURE_DIR/zotero-library.json` is stale (400
  records, dated 2026-07-01) and contains none of these. The live profile is `~/Documents/Zotero`
  — note **not** `~/Zotero`, which also exists and is a different, stale profile. Re-export
  before relying on Zotero-based discovery.
