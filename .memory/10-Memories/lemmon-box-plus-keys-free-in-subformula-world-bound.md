---
title: "Lemmon box-plus keys are free in a subformula-indexed world bound"
created: 2026-08-07
tags: [TECHNIQUE, modal-logic, filtration, box-plus, lemmon, finite-model-property, S4, chagrov-zakharyaschev]
topic: "Filtration and birth keys in modal tableau finite-model-property arguments"
source: "task-557: modal_tableau_refactor_abstractions_boneyard"  # task-ref-ok inline, category 7
modified: 2026-08-07
---

# Lemmon box-plus keys are free in a subformula-indexed world bound

Enriching filtration or birth keys from the unwrapped `psi` to the Lemmon box-plus pair
`{psi, box psi}` costs **nothing** in a world bound of the form `2^(2*|Sub phi|)`, because
`modalSubfmls (.box a) = .box a :: modalSubfmls a` makes `box psi` already a member of
`Sub phi` whenever `T(box psi)@w` sits on a universe-closed branch.

**Why box-plus rather than `psi` alone**: a world `y` satisfying `psi ∧ box psi` makes the
filtration constraint composable across a further step, whereas `psi` alone tells you
nothing about the next world (ChagrovZakharyaschev1997, print p. 142). Corollary 5.32 names
S4 explicitly as admitting filtration via the Lemmon construction.

**Do not iterate, and do not enlarge the filter instead.** The source never iterates
box-plus beyond depth 1; where more discriminating power is needed it enlarges the filter
`Sigma` (Theorems 5.34/5.35 use `{box theta -> theta, dia box theta}`), which *does* change
the codomain and is therefore expensive. Enrich with box-plus, not with the filter.

**Caveat**: the Lemmon filtration is defined for transitive models only, so this is not a
Foundations-level abstraction.

## Connections
<!-- Add links to related memories using [[filename]] syntax -->
