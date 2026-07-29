---
title: "When two obligations are each resolved by a different design change, test the conjunction"
created: 2026-07-29
tags: [PATTERN, formalization-design, orchestration, churn, cslib, root-cause]
topic: "Alternating plan versions as a symptom of incompatible design fixes"
source: "task-317: propositional_tableau_completeness"  # task-ref-ok inline, category 7
modified: 2026-07-29
---

# When two obligations are each resolved by a different design change, test the conjunction

When two proof obligations in a formalization are each "resolved" by a different design change,
check that the two changes are **mutually compatible** before planning any further work on
either.

CSLib's intuitionistic tableau added an accessible-world copy channel for `T(phi -> psi)` to make
`sat_timp` provable. That channel is exactly what makes world creation unbounded, destroying the
world bound the *other* obligation needs. Each dispatch inherited the other's docstring as fact
and never tested the conjunction.

Symptom to watch for: many plan versions alternating between two lemmas without either
converging. That pattern usually means the two fixes are in direct tension, not that either lemma
is merely hard.

## Connections
<!-- Add links to related memories using [[filename]] syntax -->
- [[timp-sibling-copies-break-world-creation-injection]]
- [[eval-computable-definitions-before-assuming-invariants]]
