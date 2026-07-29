---
title: "A validated fast-language re-implementation is a legitimate search instrument for slow computable Lean definitions"
created: 2026-07-29
tags: [TECHNIQUE, lean4, research-method, verification, tooling]
topic: "Searching the space of counterexamples outside Lean, confirming inside it"
source: "task-317: propositional_tableau_completeness"  # task-ref-ok inline, category 7
modified: 2026-07-29
---

# A validated fast-language re-implementation is a legitimate search instrument for slow computable Lean definitions

When a Lean formalization's definitions are computable but too slow to `#eval` at scale, porting
them to a fast language is a legitimate research instrument — provided the discipline that makes
it trustworthy is followed:

1. Port **line-by-line** from the source files, not from your mental model of them.
2. **Validate against a known Lean-computed data point BEFORE using it** for anything.
3. Use it only to **SEARCH** — never as evidence in its own right.
4. **Re-confirm every conclusion** with Lean `#eval` on the unmodified library.

In CSLib's intuitionistic tableau this turned a pair of `#eval` timeouts into a decisive
Lean-verified counterexample.

## Connections
<!-- Add links to related memories using [[filename]] syntax -->
- [[eval-computable-definitions-before-assuming-invariants]]
- [[timp-sibling-copies-break-world-creation-injection]]
