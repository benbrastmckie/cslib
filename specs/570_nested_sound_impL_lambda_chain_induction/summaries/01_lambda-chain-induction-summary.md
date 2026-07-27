# Implementation Summary: Nested-Sequent `impL` Soundness — Phase 1

**Task**: Land `lemma4_7_ii` and correct the module docstring's (i)/(ii) duplication claim.
**Plan**: `plans/01_lambda-chain-induction-plan.md`, Phase 1 of 8.
**Status**: Phase 1 `[COMPLETED]`. Phases 2-8 not started.

## What Was Done

Added `lemma4_7_ii` to
`Cslib/Logics/Modal/Metalogic/Constructive/Nested/Soundness.lean`, immediately after
`lemma4_7_i_ii`:

```lean
theorem lemma4_7_ii (D : Proposition Atom) {A B C : Proposition Atom}
    (h : Derivable (@CS5ModalAxiom Atom) ((A.and B).imp C)) :
    Derivable (@CS5ModalAxiom Atom) (((D.imp A).and (D.and B)).imp (D.and C))
```

Proof shape: a single `deductionTheorem` discharge of the conjunctive hypothesis
`(D ⊃ A) ∧ (D ∧ B)`, then `andE1`/`andE2` projections to extract `D` and `B` from the second
conjunct, `modus_ponens` against the first conjunct for `A`, `andI` to recombine `A ∧ B`, `modus
_ponens` against the (weakened) input hypothesis for `C`, and a final `andI` to rebuild `D ∧ C`.
This needs only one `deductionTheorem` discharge (vs. `lemma4_7_i_ii`'s two), because `D` is
reachable via a nested `andE` projection on the single conjunctive hypothesis rather than needing
its own separate discharge.

Also corrected the previously-false "same formula" claim in three places:
- The module docstring's "Lemma 4.7(i)/(ii): A Documented Source Duplication" section, renamed to
  "Lemma 4.7(i) and (ii): Distinct Statements", now stating both formulas explicitly and noting
  they are landed as two separate Lean facts.
- The `## Lemma 4.7` section-header docstring immediately above `lemma4_7_i_ii`.
- `lemma4_7_i_ii`'s own docstring, which previously claimed "This is Lemma 4.7(i) *and* (ii)";
  now states it covers part (i) only and points to `lemma4_7_ii` for part (ii).

`lemma4_7_i_ii` was not renamed, per the plan's explicit constraint.

## Verification

```
lake build Cslib.Logics.Modal.Metalogic.Constructive.Nested.Soundness
```
Result: fails with exactly the two pre-existing, named diagnostics and no others —
`Soundness.lean:1368:2: Missing cases: _, (NestedProof.cut (InputCtx.mk _ _ _) _ _ _)` and
`Soundness.lean:1345:8: declaration uses 'sorry'`. Both are scheduled for repair in later phases
(Phase 7 and Phase 5 respectively) and are explicitly out of scope for Phase 1.

```
grep -n "theorem lemma4_7_ii " Cslib/Logics/Modal/Metalogic/Constructive/Nested/Soundness.lean
```
Result: exactly one hit, at line 541.

```
bash .claude/scripts/lean-sorry-census.sh Cslib
```
Result: `sorry_count: 41`, unchanged — Phase 1 adds no sorry and removes none.

## Plan Deviations

None. All four Phase 1 task-checklist items were executed as specified.

## Next Steps

Phase 2 (repair `InputCtx.outputPruning` and restructure the `Λ = []` pruning bridge in
`Context.lean`/`Translation.lean`/`Rules.lean`) is unblocked (`depends on: none`) and has disjoint
file territory from Phase 1.
