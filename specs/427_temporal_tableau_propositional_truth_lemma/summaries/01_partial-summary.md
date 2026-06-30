# Task 427 — Partial Implementation Summary

## Status: PARTIAL (one isolated hole remains)

The propositional truth lemma `temporalTruthLemma_propositional` is **structurally complete and
validated**; only the `imp` case of the auxiliary lemma remains as a single documented `sorry`.

## Landed (committed, green build)
- `IsPropositional` inductive predicate.
- `Formula.one_le_complexity` (proved `unfold Formula.complexity; split <;> omega`).
- Bridge lemmas `any_pos_mem`, `any_neg_mem`, `mem_to_any_pos`, `mem_to_any_neg` (with `omit [Hashable Atom]`).
- `temporalTruthLemma_propositional_aux` — strong induction on `Formula.complexity` via Nat fuel.
  **zero**, **atom**, **bot** cases proved sorry-free.
- Public `temporalTruthLemma_propositional` — wired as a one-liner over the aux at `n := φ.complexity`.
  Typechecks.

## Remaining (the ONLY hole)
- The `| imp hφ' hψ' =>` case of `temporalTruthLemma_propositional_aux` (one `sorry`, currently ~line 366
  of Cslib/Logics/Temporal/Tableau/Completeness.lean). All needed hypotheses are in scope:
  `ih` (strong IH over smaller complexity), `hrule` (saturation condition), `hopen`, `hφ'`, `hψ'`, `hle`.
  Strategy fully specified in research report §4a/§4c (rule-firing decision table + per-rule closing logic).
  F-direction leaves portable from WIP lines 721–1000.

## Why partial
Four successive cslib-implementation-agent dispatches each exhausted their context window
("prompt too long") on the interactive proof-state exploration required for the Łukasiewicz-encoded
imp case analysis — exactly the difficulty the task description warned of. The orchestrator
hand-landed all mechanical scaffolding and validated the strong-induction approach (Lean accepts the
structure and all base cases), reducing the original monolithic blocker to one isolated, fully-specified hole.

## Next action
A dedicated, narrowly-scoped effort (or manual proof) on the single imp case. The scaffold guarantees
the structure is correct; the remaining work is the per-rule-shape case analysis only.

Last green commit: 687f4962
