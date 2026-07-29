---
title: "T-signed implications are copied to every sibling world, so world creation is not injective into subformula positions"
created: 2026-07-29
tags: [PATTERN, cslib, lean4, tableau, intuitionistic-logic, persistence, counterexample]
topic: "Intuitionistic tableau world-creation counting"
source: "task-317: propositional_tableau_completeness"  # task-ref-ok inline, category 7
modified: 2026-07-29
---

# T-signed implications are copied to every sibling world, so world creation is not injective into subformula positions

In the CSLib intuitionistic tableau (`Cslib/Logics/Propositional/Tableau/Intuitionistic/`), a
T-signed formula placed at a world `w` gets copied to **every** sibling world created from `w` —
via `propagatePersistence` at creation, and independently via `applyAllTImpRules`'s broader
accessible-world copy channel, which is run to fixpoint on every expansion step.

If that T-formula is itself `.imp`-shaped and BETA-resolves to an F-signed instance at each
copy's own label, then the **same static `.imp`-node position** of the original formula can fire
the world-creating rule once per sibling copy.

Consequence: world-creation events do **not** injectively map to distinct static
subformula-tree positions — contrary to what several in-file docstrings in `Scheme.lean`
previously asserted. This was verified via `lean_run_code` against the real functions with
`Atom := Nat`, not by hand-proof.

Any future world-count bound for this tableau needs an amortized / potential-function argument,
not a naive injection into subformula positions.

## Connections
<!-- Add links to related memories using [[filename]] syntax -->
- [[eval-computable-definitions-before-assuming-invariants]]
- [[two-design-fixes-must-be-checked-for-mutual-compatibility]]
- [[intuitionistic-tableau-fitting-split-over-lindenbaum]]
