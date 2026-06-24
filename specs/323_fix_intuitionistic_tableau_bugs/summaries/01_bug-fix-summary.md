# Implementation Summary: Task #323

- **Task**: 323 - Fix Intuitionistic Tableau Implementation Bugs
- **Status**: [COMPLETED]
- **Session**: sess_1782300877_b26f83
- **Date**: 2026-06-24

## Overview

Fixed two bugs in the intuitionistic propositional tableau decision procedure:

1. **Bug 1** (`isIntuitionisticallyClosed` in `Expansion.lean`): The closure check only tested for T(⊥) via the `IntuitionisticClosure` instance, missing complementary T(φ)/F(φ) pairs. This caused `p -> p` to return `.openBranch` instead of `.closed`.

2. **Bug 2** (`intTImpRule` in `Rules.lean`): The T(φ → ψ) rule used `(· >= w)` as a Kripke accessibility proxy. Since Nat is linearly ordered, sibling worlds (e.g., world 1 and world 2 both created from world 0) were incorrectly treated as accessible to each other. This caused `((p->bot)->q) v (p->r)` to close incorrectly.

## Changes Made

### `Rules.lean`

- Added `IEdges` type alias (`List (Nat × Nat)`) for parent-child accessibility edges
- Added `isAccessible` function computing the reflexive-transitive closure of parent-child edges via DFS
- Updated `intFImpRule` to return a third component: the new parent-child edge `(w', w)`
- Updated `intTImpRule` to accept `edges : IEdges` parameter and use `isAccessible edges w` instead of `(· >= w)`
- Updated `IntRuleResult.linearResult` to carry `Option (Nat × Nat)` for the new edge (world-creating rules return `some edge`, alpha rules return `none`)
- Updated `intApplyRuleFull` to thread the edge through world-creating case

### `Expansion.lean`

- Fixed `isIntuitionisticallyClosed` (Bug 1): added `|| Branch.hasContradiction b` to the closure check
- Updated `applyAllTImpRules` to accept and pass `edges : IEdges` to `intTImpRule`
- Updated `applyPersistenceFixpoint` to accept and pass `edges`
- Updated `intExpandBranches` to carry a parallel `edgeSets : List IEdges` list (one edge set per branch); threaded through the `go` inner loop; updated edges when world-creating rules fire, propagate current edges to both sub-branches on branching rules
- Updated `intuitionisticTableau` and `minimalTableau` to initialize with `[[]]` (empty edge set for root world)

### `Intuitionistic/Soundness.lean`

- Updated pattern match in `intRule_preserves_sat` to use new `linearResult newForms _ _` (3-arg) pattern
- Extended `intClosed_unsatisfiable` with Case 2 for complementary pairs (following the `minClosed_unsatisfiable` pattern from `Minimal/Soundness.lean`)
- Updated `intExpandBranches_closed_unsat` signature to include `edgeSets : List IEdges` parameter (still sorry'd - was sorry'd before)
- Updated `intuitionisticTableau_sound` call to pass `_ _ _ _` (extra wildcard for edgeSets)

### `Minimal/Soundness.lean`

- Updated `minimalTableau_sound` call to `intExpandBranches_closed_unsat` to pass the extra `_` for `edgeSets`

## Test Results

All `#eval` tests pass:

| Formula | Expected | Result |
|---------|----------|--------|
| `p -> p` | closed | closed |
| `((p->bot)->q) v (p->r)` | open | openBranch |
| `(p /\ (p->q)) -> q` | closed | closed |
| `p -> (q -> p)` | closed | closed |
| `p v ~p` | open | openBranch |
| `~~p -> p` | open | openBranch |
| `(p->q) v (q->p)` | open | openBranch |

## Verification Results

- `lake build Cslib.Logics.Propositional.Tableau.Intuitionistic.DecisionProcedure` - PASSED
- `lake build Cslib.Logics.Propositional.Tableau.Minimal.DecisionProcedure` - PASSED
- `lake exe lint-style` on modified files - PASSED (no warnings)
- Zero new sorries introduced (pre-existing `intExpandBranches_closed_unsat` sorry preserved)
- Zero new axioms introduced
- All modified files import `Cslib.Init`

**Pre-existing failures (unrelated to this task)**:
- `Cslib.Logics.Propositional.Tableau.Classical.Completeness` - was broken before, not touched
- `Cslib.Logics.Propositional.NaturalDeduction.Normalization` - pre-existing working-tree modification

## Plan Deviations

- The `intApplyRule` function (non-`Full` variant) was not updated to return the edge. It's only used as a helper and the branching infrastructure only goes through `intApplyRuleFull`. This is appropriate because `intApplyRule` returns an `Option (List × Nat)` which doesn't match the new 3-tuple signature of `intFImpRule`. *(deviation: altered - intApplyRule now uses pattern matching to discard edge from intFImpRule, keeping its original return type)*

- The `IntRuleResult` type was extended with an `Option (Nat × Nat)` in `linearResult` rather than creating a separate `edgeUpdate` in the result type. This is simpler and achieves the same goal. *(deviation: altered - simpler encoding than plan suggested)*

- `intExpandBranches_closed_unsat` signature includes `edgeSets` but the `edgeSets.length = branches.length` constraint was not added (the sorry proof doesn't need it yet). *(deviation: altered - constraint omitted from sorry stub)*
