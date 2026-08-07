---
title: "Tableau loop-check blocking: record an identification, not an edge"
created: 2026-08-07
tags: [TECHNIQUE, modal-logic, tableau, loop-checking, soundness, filtration, S4, massacci]
topic: "Modal tableau loop-checking and soundness obligations"
source: "task-557: modal_tableau_refactor_abstractions_boneyard"  # task-ref-ok inline, category 7
modified: 2026-08-07
---

# Tableau loop-check blocking: record an identification, not an edge

When a modal tableau loop-check blocks a minting step, adding an accessibility edge
`src -> wBlock` creates a soundness obligation `m.r (f src) (f wBlock)` that an
existentially-quantified witness model cannot supply.

Both source calculi avoid this:

- **Massacci2000** Definition 10.2's SST-interpretation is explicitly *not* required
  injective, so the blocked world is identified with its shorter modal copy; Pruning
  Lemma 8.2 deletes the descendant-closed subtree rather than linking to it.
- **ChagrovZakharyaschev1997** Theorem 5.51 constructs the relation as a subset of the
  ambient one (`S_{n+1} ⊆ R_Grz`), so the box-propagation condition (HSm1) is immediate.

**Diagnostic**: if the completeness side constructs its model
(`extractModelWith Relation.ReflTransGen`) while the soundness side quantifies
existentially over an arbitrary model, the two disagree about what a model *is* — and a
loop-back edge is harmless to one and fatal to the other.

## Connections
<!-- Add links to related memories using [[filename]] syntax -->
