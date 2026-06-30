---
title: "Tasks 426 & 427 share Completeness.lean — serialize, do not parallelize"
created: 2026-06-30
tags: [temporal-tableau, orchestration, territory, cslib, task-426, task-427]
topic: "Temporal tableau completeness implementation"
source: "orchestrate 426,427,425,301 (session sess_1782818123_ab1047)"
modified: 2026-06-30
---

# Tasks 426 & 427 share Completeness.lean — serialize, do not parallelize

Tasks **426** (time-ordering / `ordConstraints` redesign) and **427** (propositional
truth lemma) are **logically independent** (correctly declared with no `dependencies`
between them), but they **both edit the same file**
`Cslib/Logics/Temporal/Tableau/Completeness.lean`:

- **426** works in the `ordConstraints_strict` / `openBranch_branchSat` / ordering region
  (and also `TimeOrdering.lean`, `Rules.lean`, `Saturation.lean`, `Soundness.lean`).
- **427** works in the propositional-truth-lemma region
  (`IsPropositional`, `Formula.one_le_complexity`, `any_*`/`mem_to_any_*` bridges,
  `temporalTruthLemma_propositional_aux`, `temporalTruthLemma_propositional`).

**Consequence for orchestration**: dispatching `/orchestrate 426,427` (or any parallel
implement of both) on a single working tree races on `Completeness.lean` — concurrent
agents read a stale view and clobber each other's edits. **Always serialize 426 and 427**
(run one to a committed green state, then the other), or give each agent an isolated git
worktree. This is a *territory/shared-resource* constraint, NOT a logical task dependency,
so it must not be encoded as a `dependencies` edge (that would falsely imply one needs the
other's output).

## Other findings from the same run

- **427's imp case reliably overflows interactive agents.** Four `cslib-implementation-agent`
  dispatches each hit "prompt too long" (~110 min total, zero durable imp-case progress) on
  the Łukasiewicz-encoded imp case analysis. The mechanical scaffolding (helpers, bridge
  lemmas, `_aux` structure, base cases, public lemma) was hand-landed by the orchestrator and
  is green; only the imp case remains as one isolated documented `sorry`. Future attempts
  should decompose the imp case into per-rule-shape sub-holes with a build+commit after each,
  or be done manually — not attempted as one monolithic interactive proof.

- **425 → {426,427} is appropriate**; both 425 and 426 touch `openBranch_branchSat` (426
  redesigns it to `D=ℤ/f=instant`, 425 consumes it). **301 → {426,427,425}** is correct but
  non-minimal (426/427 are transitively implied via 425).

## Connections
<!-- Add links to related memories using [[filename]] syntax -->
