# Implementation Summary: Beta-Priority Repair of Loop-Back Containment

- **Task**: 609 - Re-validate `intFImpReuseWitnessAnc?` loop-back containment as the branch grows
- **Plan**: `plans/01_beta-priority-repair.md`
- **Status**: COMPLETED (all 9 phases)

## Outcome

Landed repair V1 (beta-priority) from the research report and closed every downstream proof
obligation it unblocked. The intuitionistic propositional tableau's completeness development is
now **fully sorry-free**: the repo-wide declaration-level sorry count (the authoritative
`lake build` "declaration uses 'sorry'" signal) went from a starting baseline of several open
sites down to **zero**.

## What changed, phase by phase

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
9. Discharged `intuitionisticTableau_complete` (DP-3), the last declaration-level sorry in the
   repo, by pinning its hypothesis to `IValid.{_, 0} φ` (mirroring `minimalTableau_complete`'s
   existing `MValid.{_, 0}` pin) and adding the `IValid` analogue of the `ULift`-based
   universe-descent bridge (`ivalid_descend` / `ivalid_universe_invariant`) so downstream
   `Decidable`/biconditional consumers keep their original, unpinned public statements. Fixed
   two further downstream breaks this pin exposed (`Intuitionistic/DecisionProcedure.lean`,
   `SequentCalculus/LJ/Decidability.lean`) and brought four files' stale "carries a deferred
   sorryAx" documentation up to date.

## Verification (final state)

- `lake build` (full, 3325 jobs): green.
- `lake exe checkInitImports`: clean.
- `lake lint`: zero findings attributable to any file this task touched.
- `lake exe lint-style`: clean.
- `lake shake --add-public --keep-implied --keep-prefix`: no suggestion for any touched file.
- `lake exe mk_all --module`: no update necessary.
- `lake test`: green, 9397 jobs, zero `✖` marks.
- Declaration-level sorry count: **0** (repo-wide).
- Axiom count: 26 (unchanged from pre-task baseline).
- Vacuous-definition grep: 1 (unchanged, pre-existing `Computability/URM/Basic.lean` false
  positive).
- `lean_verify` on every discharged theorem (`openBranch_countermodel`, `tableau_complete`,
  `intuitionisticTableau_complete`, `minimalTableau_complete`, `instDecidableDerivableIntPropAxiom`,
  `instDecidableLJDerivable`, `ivalid_descend`): standard axioms only
  (`{propext, Classical.choice, Quot.sound}` or a strict subset), no `sorryAx`.

## Excluded constructions (per task description, never attempted)

`rawEdges` as the conjunct-2 witness for `openBranch_countermodel`, pruning at blocked worlds,
pruning at strictly-blocked worlds, the greatest `IFimpAccess`-supported fixpoint, the maximal
atom-inclusion frame, V2 (retract-on-violation), and V3 (cyclic edges). All are recorded as
history in the relevant docstrings, not re-derived.

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

## Roadmap / follow-up

Task 606 ("Discharge or restate the four propositional tableau completeness theorems") is now
superseded: all four sites it names (DP-3 through DP-6) are sorry-free as of this task's
completion. It should be re-scoped or closed rather than dispatched as originally written.
