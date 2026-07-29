---
title: "#eval a computable Lean definition against a property before trying to prove it"
created: 2026-07-29
tags: [PATTERN, lean4, cslib, verification, anti-pattern, formalization-design]
topic: "Executable definitions make their own invariants testable"
source: "task-317: propositional_tableau_completeness"  # task-ref-ok inline, category 7
modified: 2026-07-29
---

# #eval a computable Lean definition against a property before trying to prove it

Before proving anything about a **computable** Lean definition, `#eval` it against the property
you are about to assume.

In CSLib's intuitionistic tableau, twelve plan versions tried to prove a world bound
`nextWorld <= complexity + 1` for an expansion loop that provably does not terminate at all. A
single `#eval` at four fuel values would have refuted the bound at the outset, before any of that
planning effort.

Executable definitions make their own invariants testable. Treat an untested assumed invariant
over computable code as **unverified**, no matter how many docstrings or prior reports state it
as fact.

## Connections
<!-- Add links to related memories using [[filename]] syntax -->
- [[timp-sibling-copies-break-world-creation-injection]]
- [[validated-fast-language-reimplementation-as-search-instrument]]
- [[executed-conformance-before-completeness-proofs]]
