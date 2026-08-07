---
title: "CSLib Tableau: private lemmas cause cross-file re-derivation at scale"
created: 2026-08-07
tags: [PATTERN, cslib, lean4, private, duplication, module-organisation, tableau]
topic: "Module organisation and visibility in Cslib/Logics/Modal/Tableau"
source: "task-557: modal_tableau_refactor_abstractions_boneyard"  # task-ref-ok inline, category 7
modified: 2026-08-07
---

# CSLib Tableau: private lemmas cause cross-file re-derivation at scale

In `Cslib/Logics/Modal/Tableau/`, 77 comment-attested "Local re-derivation of X
(unavailable across files)" sites exist because `FmpMeasure.lean` marks 50 declarations
`private`.

Concrete duplication counts:

- `modalSubfmls_trans` is re-derived in three files — `S5Simplification.lean:97`,
  `FiveSimplification.lean:736`, `BDriver.lean:211`
- `modalKnownWorlds_fold_spec` in four
- `hasEdge_addEdge_cases` in four

**Guidance**: prefer `private` only for genuinely file-local helpers. A lemma another
module will need must be public.

Deduplicating this is mechanical and behaviour-preserving by construction, and it shrinks
oversized files *before* anyone splits them — so it is worth doing ahead of a module split,
not after.

## Connections
<!-- Add links to related memories using [[filename]] syntax -->
