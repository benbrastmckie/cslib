# Summary: S5 Termination Machinery Plan v5, Phases 0-7

- **Task**: 515 - s5_universal_rule_termination_unblock_504
- **Status**: [IN PROGRESS] (phases 0-7 of 24 complete; phase 8 onward remain)
- **Started**: 2026-07-15T00:00:00Z
- **Completed**: 2026-07-16 (this dispatch: phase 7)
- **Effort**: ~8 hours (8 phases: kill test, rule, congruence, refutation, arithmetic, generalization, invariant, counting crux)
- **Dependencies**: Task 514 (literature grounding); Task 504 (parent, `modalApplyOneS5`/`extractModelS5*`/`modalTruthLemmaS5` landed)
- **Artifacts**:
  - `Cslib/Logics/Modal/Tableau/S5Simplification.lean` (modified)
  - `Cslib/Logics/Modal/Tableau/BDriver.lean` (modified)
  - `Cslib/Logics/Modal/Tableau/FrameCompleteness.lean` (modified)
  - `specs/515_s5_universal_rule_termination_unblock_504/plans/05_s5-termination-machinery.md` (phase status updates)
- **Standards**: `.claude/rules/artifact-formats.md`, `.claude/rules/state-management.md`, `.claude/rules/git-workflow.md`, `.claude/rules/plan-format-enforcement.md`
- **Type**: cslib

## Overview

Plan v5 replaces the birth-key pigeonhole architecture (plan v2, dead per deep research) with a
witness-reuse S5 rule and a linear tag-injection world budget, retargeted at K's own
termination machinery. This dispatch executed Phases 0-6 of the 24-phase plan (the S5 chain,
Phases 0-14, is independent of and precedes the Euclidean 5/KB5 route, Phases 15-23). Every
phase closed sorry-free, CI-green, with an incremental commit.

## What Changed

- **Phase 0**: Scratch-verified (no file edit) that mint tags `(pos,ψ)`/`(neg,ψ)` derived from
  `◇ψ`/`□ψ` subformulas are reachable in `modalSubfmls`/`signedSubfmls` under the
  `neg φ = φ.imp .bot` encoding, via the existing public `modalSubfmls_self_mem`.
- **Phase 1** (`S5Simplification.lean`): Landed `witnessWorldS5`, `modalApplyOneS5w`
  (guard-less witness-reuse rule intercepting exactly the two K-inherited mint shapes),
  `witnessWorldS5_mem`, two `rfl` bridges, and `modalApplyOneS5w_eq_of_not_mint_shape`.
- **Phase 2** (`S5Simplification.lean`): Landed `hintikka_congr`
  (`modalHintikkaSetGen modalApplyOneS5w ↔ modalHintikkaSetGen modalApplyOneS5`), porting the
  entire landed countermodel half of S5 completeness with zero edits to `FrameCompleteness.lean`.
- **Phase 3** (`S5Simplification.lean`, `FrameCompleteness.lean`): Landed the R7 (fuel
  domination) refutation as four `decide`-backed theorems chaining single
  `modalStepBranchGen modalApplyOneS5` steps (the full fuel-wrapped driver does not
  kernel-reduce, same limitation `LoopChecking.lean` already documents). Corrected three
  docstrings: the file-header note, the `modalTableauS5` note (was: "modalFuel is sufficient
  here too" -- false by execution), and `FrameCompleteness.lean`'s 5/KB5 note (was a scheduling
  framing; corrected to the proven frame-class inclusion obstruction, citing
  `probes/five-s5-separation.lean` by theorem name, stated as a route obstruction not an
  impossibility).
- **Phase 4** (`S5Simplification.lean`): Landed `modalOps`, `modalOps_le_complexity`,
  `modalOps_lt_worldBound` (the load-bearing arithmetic bounding mint tags by K's own
  `modalWorldBound`), `mintTags`, `mintTags_card_le_modalOps`.
- **Phase 5** (`BDriver.lean`): Generalized `modalExpandBranchesGen_openBranch_accSourcesKnown`'s
  double induction over an abstract predicate (`modalExpandBranchesGen_openBranch_gen`),
  re-derived the original B theorem from it (zero regression), and landed the new
  `modalExpandBranchesGen_openBranch_accTargetsKnown` -- previously missing across the whole
  repo and required as `modalOpenBranchS5_countermodel`'s `hTgt` argument.
- **Phase 6** (`S5Simplification.lean`): Landed `S5wTagInv`, `usedTags`, `usedTags_mono`, two
  new subformula-closure lemmas (`mem_mintTags_of_diamond_mem`/`_of_box_mem`), and
  `modalApplyOneS5w_outputs_tags`.
- **Phase 7** (`S5Simplification.lean`): Landed the counting crux -- `S5wWorldInv`,
  `modalStepBranchS5w_preserves_worldInv`, `modalMaxWorld_lt_worldBound_of_S5w` -- plus the
  supporting `witnessWorldS5_none_not_mem_usedTags` helper, `modalApplyOneS5w_fresh_local`,
  `modalStepBranchS5w_preserves_accTargetsKnown`, and the central per-call dichotomy
  `modalApplyOneS5w_step`. This is the drop-in replacement for
  `modalMaxWorld_lt_worldBound_of_phiBound`: no rank, no potential, no pigeonhole, no powerset,
  no birth keys.

## Decisions

- Phase 3's R7 refutation could not embed a `decide`/`rfl` proof of the full fuel-wrapped
  `modalExpandBranchesGen` (its nested well-founded recursion does not kernel-reduce even at
  small fuel). Substituted a chain of four single `modalStepBranchGen` steps (each genuinely
  non-recursive and `decide`-reducible), matching the same evidentiary strength and independently
  cross-checked against the research report's `#eval` table (fuel 10/20/40 -> maxWorld 5/10/20).
- Phase 6's `modalApplyOneS5w_outputs_tags` statement was left as `...` in the plan; landed as
  the conjunction of two directional per-mint-shape lemmas rather than a single combined form.
- Phase 7's `modalStepBranchS5w_preserves_worldInv` takes `accTargetsKnown b acc` as a THIRD
  hypothesis beyond the plan's literal two-hypothesis signature -- a documented, necessary
  deviation (not an optional embellishment): K's own `boxPos`/`diamondNeg` propagation shapes
  emit at `acc.successorsOf w`, which is unbounded by `modalMaxWorld` without it. The
  `accTargetsKnown` preservation instantiation itself was free (a corollary of the already-landed
  generic `modalStepBranch_preserves_accTargetsKnown_gen`).
- `modalMaxWorld_lt_worldBound_of_S5w` needed only `hW : S5wWorldInv`, not `hT : S5wTagInv`,
  narrower than the plan's stated `(hT) (hW)` signature -- the chain
  `modalMaxWorld b ≤ (usedTags φ₀ b).card ≤ (mintTags φ₀).card ≤ modalOps φ₀ < modalWorldBound φ₀`
  never touches `S5wTagInv` directly.

## Impacts

- Phases 9-14 (the rest of the S5 chain: spec split, rank-free loop invariant, step
  preservation, the parametric Hintikka lift + K/T/B regression gate) and Phases 15-23 (the
  Euclidean 5/KB5 route) remain unattempted. Phase 8 (the R1 scratch gate -- soundness re-proof
  feasibility) is the necessary next step, and writes no production Lean.
- No existing declaration was renamed, removed, or had its statement weakened. All new
  declarations are purely additive.

## Follow-ups

- Next dispatch: Phase 8, the R1 scratch probe (soundness re-proof feasibility) -- a GATE phase
  with a documented kill condition (>~400 line re-proof estimate triggers a pivot to fallback 2).

## References

- `specs/515_s5_universal_rule_termination_unblock_504/plans/05_s5-termination-machinery.md`
- `specs/515_s5_universal_rule_termination_unblock_504/.orchestrator-handoff.json`
- `specs/515_s5_universal_rule_termination_unblock_504/reports/03_s5-infrastructure-deep-research.md`
- `specs/515_s5_universal_rule_termination_unblock_504/probes/five-s5-separation.lean`
