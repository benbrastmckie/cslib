---
title: "Run the decision procedure on a known corpus before investing in completeness proofs"
created: 2026-07-26
tags: [TECHNIQUE, tableau, conformance, rule-completeness, decision-procedure, cslib]
topic: "Executed conformance testing finds tableau defects type-checking cannot"
source: "Task 552: tableau_calculus_conformance_rule_completeness_repair"
modified: 2026-07-26
---

# Run the decision procedure on a known corpus before investing in completeness proofs

A tableau calculus can be fully sorry-free, green under `lake build`, and carry landed
invariant-preservation proofs **while still returning the wrong verdict on textbook-valid
formulas**.

In one dispatch, 44 `#eval` probes against two sorry-free CSLib tableaux found 12 wrong
verdicts, six of which no prior research report had recorded across multiple hard-mode
dispatches.

The defect class is **rule-set incompleteness**, invisible to the type checker because every
landed lemma is about invariant *preservation*, not about *which formulas close*. Run the
decision procedure on a known-valid/known-invalid corpus **before** investing in completeness
proofs.

## Connections
<!-- Add links to related memories using [[filename]] syntax -->
- [[cslib-tests-conformance-harness-imports-eval]]
