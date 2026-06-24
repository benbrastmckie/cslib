# Task 338: MCS Generic Migration — Summary

**Status**: COMPLETED
**Session**: sess_1782319118_5be8e3_338

## Outcome

Migrated `Temporal/Metalogic/MCS.lean` to use the generic MCS infrastructure
(`Foundations/Logic/Metalogic/GenericMCS.lean` via `MCSProperties`), following the
pattern of `Modal/Metalogic/GenericMCSBridge.lean`.

## Phases

- **Phase 1** (committed `df72a01e`): Created
  `Cslib/Logics/Temporal/Metalogic/GenericMCSBridge.lean` (227 lines) proving the
  propositional-fragment equivalence between the tree-based `temporalDerivationSystem`
  and `algebraicDerivationSystem (S := HilbertBX)` — the critical-path prerequisite.
- **Phase 2** (committed `54ebbd5d`): Rewired the Temporal MCS wrappers in `MCS.lean`
  (`mcs_bot_not_mem`, `mcs_neg_of_not_mem`, `mcs_not_mem_of_neg`,
  `mcs_mem_iff_neg_not_mem`, `theoremInMcs`, `mcs_mp_axiom`) to thin forwarders to
  `MCSProperties` via the bridge. Net −29 lines in MCS.lean.
- **Phase 3** (verified): All three downstream consumers — `DenseCompleteness`,
  `DenseMCS`, `OrderedSeedConsistency` — build without modification.
- **Phase 4** (CI): Scoped builds green —
  `lake build Cslib.Logics.Temporal.Metalogic.MCS` (636 jobs),
  `lake build DenseCompleteness DenseMCS` (944 jobs). Zero sorry/admit in modified files.
- **Phase 5** (decision gate): Propositional MCS migration **deferred** to a follow-up
  task, per the research recommendation — `Propositional/Metalogic/MCS.lean` is blocked
  by its arbitrary `Axioms` parameterization, which does not fit the generic
  `algebraicDerivationSystem` bridge without further design work. Temporal-specific
  lemmas (MCS.lean lines 142-484) preserved untouched.

## Deferred follow-up

Propositional MCS generic migration remains as a roadmap item (blocked on resolving the
arbitrary `Axioms` parameterization vs. the generic bridge's fixed derivation system).

## Note on verification scope

CI was verified via scoped builds of the Temporal metalogic territory. A full
`lake build` / `lake test` was not used because a concurrent session has unrelated
in-progress edits to `Propositional/NaturalDeduction/Normalization.lean` (task 332) and
`Propositional/Tableau/Intuitionistic/Soundness.lean` (tasks 316/317) that would
contaminate full-tree results. Those files are outside task 338's scope.
