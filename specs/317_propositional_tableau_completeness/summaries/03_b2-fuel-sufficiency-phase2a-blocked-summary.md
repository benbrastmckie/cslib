# Phase 2a Summary: Measure Spike — R1 Gate BLOCKED

- **Task**: 317 - Close the two residual B2 sorries in the propositional tableau completeness proof
- **Status**: TBD
- **Started**: TBD
- **Completed**: TBD
- **Artifacts**: TBD
- **Standards**: TBD
- **Plan**: `plans/03_b2-fuel-sufficiency.md`, Phase 2a
- **Outcome**: BLOCKED (legitimate, expected outcome per the plan's own R1 risk gate)
- **Files changed**: none in `Cslib/` (no edits made — the R1 gate blocked before any def/lemma
  was written). Plan, progress, and handoff metadata updated only.

## What was attempted

Phase 2a's mission was to define a measure (`intExpMeasure`) on the intuitionistic expansion
state, intended to strictly decrease per `intStepBranch` step, mirroring the classical
`classicalExpMeasure` (`Classical/Completeness.lean:471-639`). Before writing any code, the
plan mandates an R1 gate: verify the candidate measure does not increase on the world-creating
`F(φ→ψ)` rule.

Read-only investigation covered:
- `classicalBranchComplexity` / `classicalExpMeasure` / `classicalApplyOne_output_complexity`
  (`Classical/Completeness.lean:471-639`) — the template.
- `intStepBranch` / `intExpandBranches` (`Expansion.lean:150-258`) — confirmed `F(→)` is a
  `.linearResult`, structurally like a classical alpha-rule (extends one branch, does not split).
- `intFImpRule` / `propagatePersistence` / `posFormulasAt` (`Rules.lean:126-159`) — the actual
  rule semantics for world creation.
- `Proposition.complexity` (`Subformula.lean:191-226`) — confirmed atoms/`⊥` = 0, so only
  compound formulas contribute to any complexity-based measure.
- `applyAllTImpRules` / `applyPersistenceFixpoint` (`Expansion.lean:118-139`) — confirmed these
  only handle `T(φ→ψ)` modus-ponens propagation, not general compound reduction.

## Why the gate blocked

`intFImpRule` emits `T(φ)@w', F(ψ)@w'` (whose combined complexity is exactly
`complexity(φ→ψ) − 1`, matching the classical identity) **plus** `propagatePersistence b w w'`,
which unconditionally copies **every** `T`-signed formula currently at world `w` — including
compounds already marked `expanded` at `w` — to fresh labels at `w'`. Because `expanded`-set
membership is checked by exact `(sign, formula, label)` triple, a copy at the new world label is
never already-expanded, so it must be reprocessed. This means a single `F(→)` step can inject an
arbitrary amount of extra unexpanded compound complexity into the branch, bounded only by the
ambient state at `w`, not by `complexity(φ→ψ)`.

Both plan-proposed candidates fail for this reason:
1. `Σ 3^complexity` over unexpanded compound occurrences: the exponential wrapper cannot rescue
   an increase, because it only "wins" via a branching split (`2·3^(c−1) < 3^c`); `F(→)` does not
   split (it is `.linearResult`, not `.branchingResult`).
2. A multiset measure replacing a compound by strictly-smaller subformulas: the persistence
   copies are not subformulas of `φ→ψ` being replaced — they are unrelated, pre-existing
   T-formulas from `w`, appended in addition to the rule's own output.

This is a genuine termination-argument gap (the algorithm does terminate, via an implicit
finite-model/bounded-worlds argument behind the `2^(2·complexity+2)` fuel bound), not a Lean
tactics problem. No natural per-step-decreasing raw-complexity Nat measure captures it.

## Plan Deviations

Per the plan's own Postmortem Constraint 5 (ZERO-DEBT) and the explicit Phase 2a escalation
instruction ("If no natural measure survives F(→), STOP... this is a legitimate successful
outcome for a blocked-by-design phase"), no deviation occurred — this is the plan's designed
contingency path, followed exactly. No placeholder, sorry, or axiom was introduced; no public
or private signature was added or changed in `Scheme.lean`.

## Next steps

A dedicated measure-design research spike is needed before Phase 2a can proceed. Candidate
directions (not attempted, out of a spike's scope): (a) a measure over the finite subformula ×
world closure rather than raw branch occurrences; (b) a lexicographic/product measure with
"remaining world-creation budget" as the primary decreasing component; (c) investigating whether
`propagatePersistence` could be soundness-preservingly restricted to avoid duplicating
already-fully-discharged compounds (a `Rules.lean`/`Expansion.lean` semantics change, out of this
plan's current Scheme.lean-only territory — would need its own plan revision and risk analysis).

See `plans/03_b2-fuel-sufficiency.md` Phase 2a section and
`.orchestrator-handoff.json` blocker `R1-measure` for full detail.
