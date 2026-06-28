# Task 316 — Revised Soundness Plan (v3)

## Goal

Fill the sorry in `intExpandBranches_closed_unsat` at
`Cslib/Logics/Propositional/Tableau/Intuitionistic/Soundness.lean:368`.

## Strategy: Contrapositive + Strong Induction

**Key insight from BimodalLogic**: prove the CONTRAPOSITIVE:

> If there exists some branch `b ∈ branches` and some `worldOf` such that
> `intBranchSatisfied val botForces worldOf b`, then
> `intExpandBranches branches ... fuel closurePred ≠ .closed`

This is logically equivalent to the original statement but MUCH easier to prove because:
- You thread ONE satisfiable (branch, worldOf) pair through the induction
- You never need to construct worldOf for all branches simultaneously
- The existential worldOf' from `intRule_preserves_sat` naturally replaces the current worldOf

### Reference: BimodalLogic proof structure

BimodalLogic (`Theories/Bimodal/Metalogic/Decidability/Saturation.lean:1141-1185`)
uses this exact pattern with three components:

1. **`expandBranchWithFuel_sound`**: `Nat.strongRecOn` on fuel
2. **`foldl_preserves_findClosure`**: inner loop induction on the pending list
3. **`tryBranch_inr`**: per-branch step lemma

## Phase 1: Helper Lemmas

### 1a. `applyPersistenceFixpoint_preserves_sat`

```
If intBranchSatisfied val botForces worldOf b
and worldOf respects accessibility (isAccessible edges w w' → worldOf w ≤ worldOf w')
then intBranchSatisfied val botForces worldOf (applyPersistenceFixpoint b edges fuel)
```

Proof: by induction on fuel. Each step of `applyAllTImpRules` adds T(ψ) at w'
when T(φ→ψ) at w and T(φ) at w' with w accessible to w'. By IForces semantics,
if `IForces val botForces (worldOf w) (φ → ψ)` and `worldOf w ≤ worldOf w'` and
`IForces val botForces (worldOf w') φ`, then `IForces val botForces (worldOf w') ψ`.

### 1b. `closurePred_false_of_sat`

```
If intBranchSatisfied val botForces worldOf b, then closurePred b = false
```

Follows from `closed_unsat` (the callback parameter): if closurePred were true,
the branch would be unsatisfiable, contradiction.

## Phase 2: Inner Loop Lemma (`go_sat_not_closed`)

```lean
private lemma go_sat_not_closed
    ... (all the go parameters) ...
    (hsat : ∃ b ∈ pending ++ done, ∃ worldOf, intBranchSatisfied val botForces worldOf b)
    (ih_fuel : ∀ fuel' < fuel, ∀ branches' ...,
        (∃ b ∈ branches', ∃ worldOf, intBranchSatisfied ...) →
        intExpandBranches ... fuel' ... ≠ .closed) :
    go pending ... done ... ≠ .closed
```

Proof: by induction on `pending`.
- **Base `pending = []`**: go returns `.closed`, but the satisfiable branch must be in
  `done`. Every branch in `done` was checked with `closurePred` after persistence — but
  a satisfiable branch can't be closed (by `closurePred_false_of_sat`). Contradiction
  with how branches reach `done` (only closed branches are added to done).
  
  Wait — actually `go [] = .closed` means all pending branches were processed. The
  satisfiable branch can't be in pending (it's empty). If it's in done, that means
  `closurePred bPers = true` was satisfied for it, but that contradicts satisfiability.
  So the satisfiable branch must still be in pending — contradiction with pending = [].
  
  Actually this needs more care. The satisfiable branch could have been TRANSFORMED
  (extended by a rule) and is now in the recursive call, not in pending or done.

**Revised approach**: Track which branch is satisfiable more carefully.

Better: prove by induction on pending, maintaining that the satisfiable branch is
EITHER (a) in the pending list, or (b) was already expanded into a recursive
`intExpandBranches` call that returned non-closed.

For each branch b_head in pending:
- If b_head IS the satisfiable branch:
  - After persistence: still satisfiable (by Phase 1a)
  - closurePred = false (by Phase 1b)
  - intStepBranch returns some result (or none → .openBranch, not .closed)
  - Linear result: `intRule_preserves_sat` gives ∃ worldOf', satisfiable extended branch.
    Recursive call has this satisfiable branch → by ih_fuel, not closed. ✓
  - Branching result: `intRule_preserves_sat` gives ∃ br ∈ branches', satisfiable.
    Recursive call has this satisfiable sub-branch → by ih_fuel, not closed. ✓
  - Not applicable: returns .openBranch → not .closed ✓
- If b_head is NOT the satisfiable branch:
  - If closurePred b_head = true: go continues with rest. Satisfiable branch still in rest. IH on rest.
  - If closurePred b_head = false: step expands b_head.
    - Linear/branching: recursive call to intExpandBranches. The satisfiable branch is in `rest`,
      which becomes part of the new branches list. By ih_fuel, not closed. ✓
    - none/notApplicable: returns .openBranch → not .closed ✓

## Phase 3: Main Theorem

```lean
lemma intExpandBranches_closed_unsat ... := by
  -- Prove contrapositive: sat → not closed
  suffices h : ∀ fuel branches ...,
      (∃ b ∈ branches, ∃ worldOf, intBranchSatisfied ...) →
      intExpandBranches ... ≠ .closed by
    intro fuel ... branches ... h_closed b hb worldOf hsat
    exact absurd h_closed (h fuel branches ... ⟨b, hb, worldOf, hsat⟩)
  intro fuel
  induction fuel using Nat.strongRecOn with
  | _ n ih =>
    intro branches ...
    cases n with
    | zero => -- fuel = 0: findSome? finds the non-closed branch
    | succ k => -- fuel = k+1: use go_sat_not_closed with ih
```

## Notes

- Use `set_option maxHeartbeats 3200000` (BimodalLogic needed this)
- The `go` function is accessed as `intExpandBranches.go` in the proof
- `intRule_preserves_sat` is already sorry-free (lines 82-263)
- Build verification: `lake build Cslib.Logics.Propositional.Tableau.Intuitionistic.Soundness`
