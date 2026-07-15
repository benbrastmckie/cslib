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
