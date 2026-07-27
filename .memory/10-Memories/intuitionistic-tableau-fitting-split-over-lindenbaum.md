---
title: "Intuitionistic tableau T-implication: the Fitting split is the minimal fix, not Lindenbaum completion"
created: 2026-07-26
tags: [PATTERN, intuitionistic-tableau, Fitting1983, truth-lemma, bivalence, Lindenbaum]
topic: "Intuitionistic tableau T-implication rule design"
source: "Task 552: tableau_calculus_conformance_rule_completeness_repair"
modified: 2026-07-26
---

# Intuitionistic tableau T-implication: the Fitting split is the minimal fix, not Lindenbaum completion

When an intuitionistic tableau's persistent `T(φ→ψ)` rule is **positive-only** (it only ever
adds `T(ψ)` where `T(φ)` is already present), the completeness truth lemma's T-imp case is
blocked.

The recorded remedy in such situations is often a Lindenbaum-style "decide every subformula at
every fresh world" completion rule — which branches `2^|Sub(φ₀)|` ways. **That is over-scoped.**

Because the truth lemma is bidirectional (proving both the T-forces and F-refutes directions
simultaneously), the standard Fitting Ch.4 branching rule

    T(φ→ψ)@w  ⟶  [F(φ)@w'] | [T(ψ)@w']

supplies exactly the disjunction needed. Full subformula bivalence is never required.

## Connections
<!-- Add links to related memories using [[filename]] syntax -->
