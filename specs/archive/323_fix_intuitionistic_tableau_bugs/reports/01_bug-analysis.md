# Bug Analysis: Intuitionistic Tableau Implementation Bugs

- **Task**: 323 - Fix Intuitionistic Tableau Bugs
- **Date**: 2026-06-24
- **Agent**: cslib-research-agent
- **Session**: sess_1750824000_orchestrate_323

## Executive Summary

Two bugs in the intuitionistic propositional tableau decision procedure cause incorrect results. Bug 1 (missing complementary-pair closure) produces false negatives -- valid formulas like `p -> p` are reported as open. Bug 2 (spurious sibling-world persistence) produces false positives -- invalid formulas like `((p->bot)->q) v (p->r)` are incorrectly closed. Both bugs have been verified with `#eval` tests. Concrete fixes are identified for both.

## Bug 1: Missing Complementary-Pair Closure Check

### Location

- **File**: `Cslib/Logics/Propositional/Tableau/Intuitionistic/Expansion.lean`, line 67
- **Function**: `isIntuitionisticallyClosed`

### Current Code

```lean
def isIntuitionisticallyClosed (b : IBranch Atom) : Bool :=
  @ClosureCondition.isClosed _ _ IntuitionisticClosure.instClosureConditionOfBEqOfHasBot b
```

The `IntuitionisticClosure` instance (in `Cslib/Foundations/Logic/Tableau/ClosureCondition.lean`, line 108) only checks for T(bot) at any label. It does NOT check for complementary pairs T(phi)/F(phi) at the same label.

### Why This Is Wrong

In intuitionistic Kripke semantics, a branch containing both T(phi) at world w and F(phi) at world w is unsatisfiable -- the forcing relation cannot simultaneously hold and fail for the same formula at the same world. The standard intuitionistic tableau closure condition is:

> A branch closes when it contains T(bot) at any label, OR when it contains T(phi) and F(phi) at the same label for any formula phi.

The docstring at line 65 states "Unlike classical closure, complementary pairs do NOT close a branch" -- this is incorrect. Complementary pairs DO close intuitionistic branches. The confusion may stem from conflating intuitionistic closure with minimal closure (where only atomic complementary pairs close a branch in some presentations).

### Verification

```
#eval intuitionisticTableau (p.imp p)  -- Returns .openBranch (BUG!)
```

The branch returned for p -> p contains: T(p) @ w1, F(p) @ w1, F(p->p) @ w0. The branch has `hasContradiction = true` but `hasBotPos = false`.

### Affected Formulas (verified by #eval)

| Formula | Expected | Actual (buggy) | With fix |
|---------|----------|----------------|----------|
| `p -> p` | closed | openBranch | closed |
| `(p /\ (p -> q)) -> q` | closed | openBranch | closed |
| `p -> (q -> p)` | closed | openBranch | closed |

### Recommended Fix

Add `|| Branch.hasContradiction b` to `isIntuitionisticallyClosed`:

```lean
def isIntuitionisticallyClosed (b : IBranch Atom) : Bool :=
  @ClosureCondition.isClosed _ _ IntuitionisticClosure.instClosureConditionOfBEqOfHasBot b
    || Branch.hasContradiction b
```

Alternatively, update the `IntuitionisticClosure` instance itself in `ClosureCondition.lean` to also check `findContradiction`, matching the `ClassicalClosure` pattern. This is architecturally cleaner but has wider impact.

### Soundness Impact

The `intClosed_unsatisfiable` lemma in `Soundness.lean` (line 269) must be updated to also handle the complementary-pair case. Currently it only handles T(bot). The new case follows the same pattern as `minClosed_unsatisfiable` in `Minimal/Soundness.lean` (line 126), which already handles complementary pairs via `Branch.hasContradiction`.

### Note on IntuitionisticClosure Instance

There is a design choice here: modify the `IntuitionisticClosure` instance in `ClosureCondition.lean` to include complementary pairs, or keep the instance as-is and only modify `isIntuitionisticallyClosed`. The first approach is cleaner (the typeclass becomes semantically correct), but it changes foundational infrastructure. The second approach is local (only modifies Expansion.lean) and leaves the typeclass as a "T(bot)-only" primitive that callers extend. I recommend the second approach (local fix) for minimal disruption.

## Bug 2: Spurious Sibling-World Persistence (intTImpRule)

### Location

- **File**: `Cslib/Logics/Propositional/Tableau/Intuitionistic/Rules.lean`, line 129-141
- **Function**: `intTImpRule`

### Current Code

```lean
def intTImpRule (phi psi : Proposition Atom) (w : Nat) (b : IBranch Atom) :
    List (ISF Atom) :=
  let worldsAbove := (b.map (·.label)).filter (· >= w) |>.eraseDups
  worldsAbove.filterMap fun w' => ...
```

The filter `(· >= w)` uses the natural number ordering as a proxy for Kripke accessibility. This is a LINEAR order: for any two worlds w1 and w2, either w1 >= w2 or w2 >= w1. But the actual Kripke tree is a PARTIAL order where sibling worlds are incomparable.

### Why This Is Wrong

When the F(imp) rule fires at world w, it creates a new child world w' = nextWorld. The intended accessibility relation is the reflexive-transitive closure of the parent-child relation:
- w0 (root) can access all worlds (it is an ancestor of everything)
- w1 (child of w0) can access w1 and descendants of w1
- w2 (child of w0, sibling of w1) can access w2 and descendants of w2
- w1 CANNOT access w2, and w2 CANNOT access w1

But with Nat ordering, since w2 = 2 >= 1 = w1, the `intTImpRule` treats w2 as accessible from w1.

### Concrete Trace

For formula `((p -> bot) -> q) v (p -> r)`:

1. Initial: F(((p->bot)->q) v (p->r)) @ w0
2. F(v) rule: F((p->bot)->q) @ w0, F(p->r) @ w0
3. F((p->bot)->q) at w0 creates w1: T(p->bot) @ w1, F(q) @ w1
4. F(p->r) at w0 creates w2: T(p) @ w2, F(r) @ w2
5. Persistence fixpoint (`applyAllTImpRules`): T(p->bot) @ w1 fires for all w' >= 1 with T(p) at w'. World w2 has label 2 >= 1 and T(p) at w2. So T(bot) is added at w2.
6. T(bot) at w2 closes the branch via `isIntuitionisticallyClosed`.

Step 5 is wrong: w2 is a sibling of w1, not a descendant. T(p->bot) at w1 should only fire at w1 itself and descendants of w1.

### Verification

```
#eval intuitionisticTableau bug2Formula  -- Returns .closed (BUG!)
```

This formula is NOT intuitionistically valid. Kripke countermodel: diamond frame w0 -> w1, w0 -> w2, w1 and w2 incomparable. Set p true only at w1, q and r false everywhere. Then (p->bot)->q fails at w0 (p->bot fails at w0 since p holds at w1, so vacuously true; but q is false). And p->r fails at w0 (p at w1, r false at w1).

### Verification that Bug 2 persists after Bug 1 fix

```
-- With isIntClosedFixed (adding hasContradiction):
#eval intExpandBranches ... isIntClosedFixed bug2Formula  -- Still returns .closed (BUG!)
```

Bug 2 is independent of Bug 1. Fixing Bug 1 alone does not resolve Bug 2.

### Affected Formulas (verified by #eval)

| Formula | Expected | Actual (buggy) | After Bug 1 fix only |
|---------|----------|----------------|---------------------|
| `((p->bot)->q) v (p->r)` | open | closed | closed (still buggy) |
| `p v (p->bot)` (excluded middle) | open | open | open (OK) |
| `((p->bot)->bot) -> p` (DNE) | open | open | open (OK) |
| `(p->q) v (q->p)` (linearity) | open | open | open (OK) |

Bug 2 requires a specific pattern: T(phi->psi) at one world and T(phi) at a sibling world created by a different F(->). Not all non-valid formulas trigger it.

### Recommended Fix

Track the parent-child accessibility relation explicitly and replace Nat ordering with actual accessibility checking.

#### Data Structure Changes

Add an accessibility relation parameter to the functions that use it:

```lean
/-- Check if world w' is accessible from world w in the given parent map.
    Accessibility = reflexive-transitive closure of parent-child. -/
def isAccessible (parentOf : Nat -> Option Nat) (w w' : Nat) : Bool :=
  if w == w' then true  -- reflexivity
  else
    -- Walk up from w' following parent chain; check if w is an ancestor
    let rec go (curr : Nat) (fuel : Nat) : Bool :=
      match fuel with
      | 0 => false
      | fuel' + 1 =>
        match parentOf curr with
        | none => false  -- reached root without finding w
        | some parent =>
          if parent == w then true
          else go parent fuel'
    go w' (w' + 1)  -- fuel bounded by world number
```

#### Function Signature Changes

1. **`intTImpRule`**: Add `parentOf : Nat -> Option Nat` parameter. Replace `(· >= w)` with `isAccessible parentOf w`.

2. **`applyAllTImpRules`**: Add `parentOf` parameter, pass to `intTImpRule`.

3. **`applyPersistenceFixpoint`**: Add `parentOf` parameter, pass to `applyAllTImpRules`.

4. **`intFImpRule`**: Return the new parent relationship along with formulas and next world counter. New return type: `List (ISF Atom) x Nat x (Nat x Nat)` where the last component is `(newWorld, parentWorld)`.

5. **`intExpandBranches`**: Add `parentMaps : List (Nat -> Option Nat)` parallel list (one per branch). When F(imp) creates a new world, update the parent map.

6. **`intStepBranch`**: Thread `parentOf` through.

#### Alternative: Use `List (Nat x Nat)` for Parent Edges

Instead of `Nat -> Option Nat`, use a list of parent edges `List (Nat x Nat)` where each pair is `(child, parent)`. This is simpler to construct and thread:

```lean
def isAccessible (edges : List (Nat x Nat)) (w w' : Nat) : Bool :=
  if w == w' then true
  else
    let rec go (curr : Nat) (fuel : Nat) : Bool :=
      match fuel with
      | 0 => false
      | fuel' + 1 =>
        match edges.find? (fun (c, _) => c == curr) with
        | none => false
        | some (_, parent) => if parent == w then true else go parent fuel'
    go w' (w' + 1)
```

The expansion loop starts with `edges = []` (root w0 has no parent). When F(imp) at world w creates world w', append `(w', w)` to the edges list.

### Soundness Impact

The soundness proof for `applyAllTImpRules_preserves_sat` (not yet written, currently sorry) will actually become SIMPLER with proper accessibility tracking. The current proof needs branch-local monotonicity of `worldOf` (as analyzed in report 04_b4-hard-research.md). With proper accessibility:
- `intTImpRule` only fires at genuinely accessible worlds
- The semantic justification `worldOf w <= worldOf w'` holds by construction for parent-child pairs
- No need for the global Nat-ordering monotonicity hack

### Impact on Completeness

The completeness proof (`Completeness.lean`) has sorry'd proofs. The fix must ensure that the countermodel construction from an open saturated branch still works. Since we are making the persistence rule MORE restrictive (only firing along actual accessibility paths rather than all Nat-greater worlds), saturation means fewer formulas on the branch. The truth lemma must account for this, but the key inductive steps remain valid because:
- For T(phi -> psi) at w: saturation means for all accessible w' with T(phi) at w', T(psi) is at w'. This is exactly the Kripke forcing condition.
- The countermodel's accessibility IS the parent-child relation, so the truth lemma's inductive hypothesis matches the saturation condition.

## Files Requiring Modification

| File | Changes |
|------|---------|
| `Intuitionistic/Expansion.lean` | Fix `isIntuitionisticallyClosed` (Bug 1); add `parentOf`/edges parameter to `applyAllTImpRules`, `applyPersistenceFixpoint`, `intStepBranch`, `intExpandBranches`; update `intuitionisticTableau` and `minimalTableau` call sites |
| `Intuitionistic/Rules.lean` | Add `parentOf`/edges parameter to `intTImpRule`; update `intFImpRule` to return parent edge; add `isAccessible` helper; update `intApplyRuleFull` signature |
| `Intuitionistic/Soundness.lean` | Update `intClosed_unsatisfiable` for complementary-pair case; update `intRule_preserves_sat` and `intExpandBranches_closed_unsat` signatures for accessibility parameter |
| `Intuitionistic/Completeness.lean` | Update `intTruthLemma` and `intuitionisticTableau_complete` for new signatures (currently sorry'd) |
| `Intuitionistic/DecisionProcedure.lean` | No direct changes (uses `intuitionisticTableau` which is updated internally) |
| `Minimal/Soundness.lean` | Update call to `intExpandBranches_closed_unsat` for new signature |
| `Minimal/Completeness.lean` | Update for new signatures (currently sorry'd) |
| `Minimal/DecisionProcedure.lean` | No direct changes |

## Recommended Fix Order

1. **Phase 1**: Add `isAccessible` and parent-edge tracking infrastructure to `Rules.lean`
2. **Phase 2**: Modify `intTImpRule` to use `isAccessible` instead of Nat ordering (Bug 2 fix)
3. **Phase 3**: Thread `edges` through `Expansion.lean` functions
4. **Phase 4**: Fix `isIntuitionisticallyClosed` to add `hasContradiction` (Bug 1 fix)
5. **Phase 5**: Update soundness proofs in `Soundness.lean` and `Minimal/Soundness.lean`
6. **Phase 6**: Update completeness stubs in `Completeness.lean` and `Minimal/Completeness.lean`
7. **Phase 7**: Verify with `#eval` tests and `lake build`

Phase 1-4 are the core fixes. Phases 5-6 update the sorry-tagged proofs.

## Test Matrix

After both fixes, the following should hold:

| Formula | Intuitionistic Validity | Expected Result |
|---------|------------------------|-----------------|
| `p -> p` | valid | .closed |
| `(p /\ (p -> q)) -> q` | valid | .closed |
| `p -> (q -> p)` | valid | .closed |
| `(p -> (q -> r)) -> ((p -> q) -> (p -> r))` | valid | .closed |
| `((p->bot)->q) v (p->r)` | NOT valid | .openBranch |
| `p v (p->bot)` | NOT valid | .openBranch |
| `((p->bot)->bot) -> p` | NOT valid | .openBranch |
| `(p->q) v (q->p)` | NOT valid | .openBranch |
| `(p->bot) v ((p->bot)->bot)` | NOT valid | .openBranch |

## Interaction with Task 316

Task 316 (propositional tableau soundness) has a sorry'd `intExpandBranches_closed_unsat` lemma. The B4 blocker documented in report 04_b4-hard-research.md identified the `worldOf` monotonicity issue. The Bug 2 fix (proper accessibility tracking) actually simplifies the B4 resolution:

- With Nat ordering: proof needs branch-local monotonicity invariant for `worldOf`
- With proper accessibility: `worldOf` monotonicity follows from the parent-child construction

The soundness proof approach from report 04 (existential `worldOf'` via `Function.update`) remains valid and is simplified by the accessibility fix.
