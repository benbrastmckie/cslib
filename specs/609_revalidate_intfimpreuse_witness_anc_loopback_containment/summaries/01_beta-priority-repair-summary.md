# Implementation Summary: Beta-Priority Repair of Loop-Back Containment

- **Task**: 609 - Re-validate `intFImpReuseWitnessAnc?` loop-back containment as the branch grows
- **Plan**: `plans/01_beta-priority-repair.md`
- **Status**: COMPLETED (all 9 phases)
- **Started**: 2026-08-09
- **Completed**: 2026-08-10
- **Artifacts**: `reports/01_loopback-revalidation-repair.md`, `plans/01_beta-priority-repair.md`, `handoffs/01`-`13`
- **Standards**: CONTRIBUTING.md, NOTATION.md, ORGANISATION.md

## Overview

Landed repair V1 (beta-priority) from the research report and closed every downstream proof
obligation it unblocked.

The root problem: `intFImpReuseWitnessAnc?` recorded a loop-back edge on a `Sfor`-containment
check at the moment the branch reused an ancestor world, then never re-validated that containment
as the branch kept growing. That forced a false choice between two frames — the AUGMENTED frame
carried `IFimpAccess` but refuted positive persistence, while the RAW frame carried persistence
but refuted `IFimpAccess`. Neither could instantiate `truthLemma`, which needs both.

`intStepBranchPrio` now defers world-creating rules and re-validates loop-back containment as the
branch grows, so the augmented frame carries **both** facts simultaneously. That collapsed
`openBranch_countermodel`'s remaining existential into a direct `truthLemma` instantiation, and
the discharge cascaded downstream to `intuitionisticTableau_complete` (DP-3).

The intuitionistic and minimal propositional tableau completeness development is now fully
sorry-free. See **Impacts** below for the precise scope of that claim.

## What Changed

Phase by phase:

1. **`intStepBranchPrio`** (Expansion.lean) -- additive beta-priority stepper: first pass skips
   world-creating formulas, falls through to the original `intStepBranch` on `none`. Bridges
   (`none`-iff, `some`-exists with the `sf ∉ e` strengthening) landed alongside, unused by
   anything yet.
2. Re-based the six proofs that used to unfold `intStepBranch` directly onto a shared
   `IStepShape` predicate, so both steppers can share proof infrastructure.
3. Swapped `intExpandBranches.go`'s call site to `intStepBranchPrio`, verdict-preservingly
   (conformance corpus: 14 IPC-valid rows `CLOSED`, 6 open rows `OPEN`, including the
   complexity-9 divergence witness, all unchanged).
4. Promoted `phiRef4` from a refutation witness to a passing assertion; re-pointed
   `BetaSplitRefutation.lean`'s narrative at the repaired calculus.
5. Landed the freeze lemma justified by beta-priority, replacing `IReuseContain_mono`'s old
   snapshot-existential dependency.
6. Dropped the snapshot existential from `IReuseContain` entirely; re-threaded the freeze
   argument through the `key` induction (the plan's largest phase, split across several
   sub-dispatches: investigation, an `isAccessible`-reverse lemma, items b/c, origin-tracking
   machinery, and final closure).
7. Exported augmented-frame positive persistence (`hpersAug`) from
   `intExpandBranches_openBranch_sat` as a 7th, χ-general conjunct.
8. Discharged `openBranch_countermodel` by committing to the AUGMENTED `augSets` witness,
   closing all three existential conjuncts from one `truthLemma` instantiation at that frame.
   Added the new additive `IntMinScheme.modelBot_uc` structure field (both `intScheme` and
   `minScheme` instances discharge it) since `S.modelBot` upward-closure cannot be recovered
   generically from `bot_truth`/`no_contradiction` alone for an abstract scheme.
9. Discharged `intuitionisticTableau_complete` (DP-3) by pinning its hypothesis to
   `IValid.{_, 0} φ` (mirroring `minimalTableau_complete`'s existing `MValid.{_, 0}` pin) and
   adding the `IValid` analogue of the `ULift`-based universe-descent bridge (`ivalid_descend` /
   `ivalid_universe_invariant`) so downstream `Decidable`/biconditional consumers keep their
   original, unpinned public statements. Fixed two further downstream breaks this pin exposed
   (`Intuitionistic/DecisionProcedure.lean`, `SequentCalculus/LJ/Decidability.lean`) and brought
   four files' stale "carries a deferred sorryAx" documentation up to date.

## Decisions

- **Committed to the augmented frame, not the raw one**, for `openBranch_countermodel`'s witness.
  This is the whole point of the repair: pre-repair, the augmented frame was refuted for positive
  persistence (`CslibTests/BetaSplitRefutation.lean`, `firstViolation = some (2,1,2)`), which is
  why the choice was previously unavailable.
- **`IReuseContain` restated in bare, snapshot-free form** rather than weakening it to keep
  `IReuseContain_mono` provable. `IReuseContain_mono` and `IReuseContain_snoc` were removed
  outright rather than retained as dead-but-compiling wrappers.
- **Phase 7's conclusion extended in place** with a 7th conjunct rather than adding a separate
  corollary, with a type-checking `example` feeding it straight into `truthLemma` via `exact` to
  confirm the shape match mechanically.
- **Phase 6's six anticipated bespoke case-split proofs collapsed to one uniform substitution**
  by adding an origin-containment conjunct to `IReuseFrozenOrigin` plus one corollary — a
  simplification found only by attempting the wiring rather than surveying for it.

### Excluded constructions (per task description, never attempted)

`rawEdges` as the conjunct-2 witness for `openBranch_countermodel`, pruning at blocked worlds,
pruning at strictly-blocked worlds, the greatest `IFimpAccess`-supported fixpoint, the maximal
atom-inclusion frame, V2 (retract-on-violation), and V3 (cyclic edges). All are recorded as
history in the relevant docstrings, not re-derived.

## Impacts

Verification at final state:

- `lake build` (full, 3325 jobs): green.
- `lake exe checkInitImports`: clean.
- `lake lint`: zero findings attributable to any file this task touched.
- `lake exe lint-style`: clean.
- `lake shake --add-public --keep-implied --keep-prefix`: no suggestion for any touched file.
- `lake exe mk_all --module`: no update necessary.
- `lake test`: green, 9397 jobs, zero `✖` marks.
- Axiom count: 26 (unchanged from pre-task baseline).
- Vacuous-definition grep: 1 (unchanged, pre-existing `Computability/URM/Basic.lean` false
  positive).
- `lean_verify` on every discharged theorem (`openBranch_countermodel`, `tableau_complete`,
  `intuitionisticTableau_complete`, `minimalTableau_complete`, `instDecidableDerivableIntPropAxiom`,
  `instDecidableLJDerivable`, `ivalid_descend`): standard axioms only
  (`{propext, Classical.choice, Quot.sound}` or a strict subset), no `sorryAx`.

### Sorry-count claim: precise scope

**`Cslib/Logics/Propositional/` is sorry-free.** Verified by direct source inspection, not by
build warnings: every remaining `sorry` occurrence under that tree is a prose mention inside a
docstring or a `## Notes on sorry` section, not a proof obligation.

**This is NOT repo-wide sorry-freeness, and the `lake build` signal alone cannot establish that
it is.** Unsuppressed `declaration uses 'sorry'` warnings are now 0, but roughly 19 real
tactic-position sorries remain in `Cslib/Logics/Bimodal/`, each wrapped in
`set_option warn.sorry false in` and therefore structurally invisible to that metric (18
suppression sites across 5 files). Those are tracked against the separate upstream
`port_continuous_completeness_bimodal` work and were never in this task's scope.

## Follow-ups

- **Task 606 is superseded.** "Discharge or restate the four propositional tableau completeness
  theorems and verify the TFAE fold" names four sites (DP-3 through DP-6); all four are now
  sorry-free (DP-3 by this task's Phase 9, DP-4 by task 605, DP-5/DP-6 by this task's earlier
  phases). Re-scope or close it rather than dispatching it as originally written.
- **The `lake build` sorry metric undercounts and should not be quoted as repo-wide.** Any future
  claim of repo-wide sorry-freeness must inspect sources directly, since
  `set_option warn.sorry false in` silences the warning the metric counts.

## Plan Deviations

- **Phase 8**: added `IntMinScheme.modelBot_uc` as a new additive structure field rather than
  sourcing `hbuc` from `openBranch_rawEdges_both_upward_closed` as the plan's Phase 8 text
  suggested -- that lemma is stated for the concrete `minBranchBotForces`, not an abstract
  `S.modelBot`, and no generic derivation exists without an unestablished totality/bivalence
  fact. See Phase 8's handoff (`handoffs/12_phase8-complete.md`) for the full analysis.
- **Phase 9**: the `IValid.{_, 0}` pin required updating `Intuitionistic/DecisionProcedure.lean`
  and `SequentCalculus/LJ/Decidability.lean` (not named in the plan's "Files to modify" list for
  this phase) to keep the build green -- an unavoidable consequence of the pin, mirroring how
  605's own `MValid.{_, 0}` pin required `Minimal/DecisionProcedure.lean`'s bridge lemmas.
  Additionally updated four more files' "Notes on sorry" prose
  (`Minimal/DecisionProcedure.lean`, `Metalogic/IntDecidability.lean`,
  `Metalogic/MinDecidability.lean`, plus `Minimal/Completeness.lean`'s own notes) that made the
  same now-false "carries a deferred sorryAx" claim about the theorems this phase discharged --
  a scope expansion beyond the plan's literally-named files, done for documentation accuracy
  rather than any build requirement. See `handoffs/13_phase9-complete-plan-done.md` for the full
  record, including the task 606 reconciliation.

## References

- Plan: `plans/01_beta-priority-repair.md`
- Research: `reports/01_loopback-revalidation-repair.md`
- Phase handoffs: `handoffs/10_phase6-complete.md`, `handoffs/11_phase7-complete.md`,
  `handoffs/12_phase8-complete.md`, `handoffs/13_phase9-complete-plan-done.md`
- Frame-adequacy analysis and DP-5 restructure source:
  `specs/604_prove_countermodel_forcing_conjunct_over_constructed_frame/reports/01_conjunct2-frame-adequacy.md`
  (sections 3, 4, 6)
- Machine evidence for excluded constructions: `CslibTests/BetaSplitRefutation.lean`,
  `CslibTests/WitnessProbe.lean`, `CslibTests/TableauConformance.lean`
