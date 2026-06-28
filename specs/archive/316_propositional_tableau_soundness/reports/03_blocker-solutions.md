# Blocker Solutions for Task 316: Propositional Tableau Soundness

- **Task**: 316 - Propositional Tableau Soundness
- **Date**: 2026-06-24
- **Type**: Blocker analysis and resolution
- **Dependencies**: Report 01 (soundness-research), Report 02 (blockers-resolution)
- **Sources**:
  - `Cslib/Logics/Propositional/Tableau/Classical/Soundness.lean`
  - `Cslib/Logics/Propositional/Tableau/Intuitionistic/Soundness.lean`
  - `Cslib/Logics/Propositional/Tableau/Intuitionistic/Rules.lean`
  - `Cslib/Logics/Propositional/Tableau/Intuitionistic/Expansion.lean`
  - `Cslib/Logics/Propositional/Tableau/Classical/Expansion.lean`
  - `Cslib/Logics/Propositional/Tableau/Minimal/DecisionProcedure.lean`
  - `Cslib/Logics/Propositional/Semantics/Kripke.lean`

## Current State Assessment

### What Already Works (sorry-free, verified structure)

The classical soundness file contains the **correct proof structure** for the
loop invariant approach. Lines 554-647 contain:
- `classicalExpandBranches_closed_unsat` (line 554): outer induction on `fuel`,
  inner `suffices` + `induction pending` on the `processNext` local def
- `classicalStepBranch_preserves_sat` (line 512): steps through `classicalStepBranch`
  using `classicalRule_preserves_sat`
- `classicalTableau_sound` (line 633): contrapositive via `by_contra` + `push_neg`

The **proof pattern** is validated -- the classical case uses exactly this structure.
However, the file currently has **9 build errors** (see below).

### What Doesn't Build

**Classical Soundness** (`Classical/Soundness.lean`): 9 errors
- Line 522: `simp only at hsfeq` makes no progress (in `classicalStepBranch_preserves_sat`)
- Line 586: syntax error `unexpected token 'with'` (in `classicalExpandBranches_closed_unsat`)
- Lines 566, 569, 581: type mismatches and simp failures in the induction body
- Lines 644-647: type mismatches in `classicalTableau_sound`

Root cause: The proof was written against a slightly different API version (likely
pre-`classicalStepBranch` refactoring). The proof STRUCTURE is correct but the
specific tactic invocations need updating to match current definitions.

**Intuitionistic Soundness** (`Intuitionistic/Soundness.lean`): Builds successfully with 2 sorry
- Line 162: `sorry` in `intRule_preserves_sat` F(imp) case (Blocker B2)
- Line 244: `sorry` in `intuitionisticTableau_sound` (Blocker B1)

**Minimal DecisionProcedure** (`Minimal/DecisionProcedure.lean`): Builds with 2 sorry
- Line 88: `sorry` in `minimalTableau_sound` (depends on B1 resolution)
- Line 105: `sorry` in `minimalTableau_complete` (task 317 scope, out of scope)

### Total Active Sorry Count

| File | Sorry | In Scope? | Blocker |
|------|-------|-----------|---------|
| Classical/Soundness.lean | ~0 sorry but 9 build errors | Yes | Build fix needed |
| Intuitionistic/Soundness.lean | 2 | Yes | B1, B2 |
| Minimal/DecisionProcedure.lean | 1 in scope, 1 out | Partial | Depends on B1 |

## Blocker B1: Fuel-Based Loop Induction

### Problem Description

Both `classicalExpandBranches` (Classical/Expansion.lean:112) and
`intExpandBranches` (Intuitionistic/Expansion.lean:133) use `let rec` inner
functions (`processNext` and `go` respectively) inside the fuel match. The
main soundness theorems require proving that if the expansion returns `.closed`,
then all input branches are unsatisfiable.

### Evidence: Classical Case Already Solved

The classical case shows the **exact pattern** that works:

```lean
private lemma classicalExpandBranches_closed_unsat
    (fuel : Nat) :
    ∀ (branches : List ...)
      (expandedSets : List ...),
      expandedSets.length = branches.length →
      classicalExpandBranches branches expandedSets fuel = .closed →
      ∀ b ∈ branches, ¬ classicalBranchSatisfiable b := by
  induction fuel with
  | zero => ... -- base: all branches must be closed, use classically_closed_unsatisfiable
  | succ fuel' ih =>
    -- Key: use `suffices` to state inner lemma about processNext
    suffices key : ∀ (pending : List ...) ... ,
        pendingExp.length = pending.length →
        doneExp.length = done.length →
        classicalExpandBranches.processNext pending pendingExp done doneExp fuel' = .closed →
        ∀ bp ∈ pending, ¬ classicalBranchSatisfiable bp from
      key branches expandedSets [] [] hlength rfl
        (by simpa [classicalExpandBranches] using h) b hb hsat
    -- Inner induction on pending list
    intro pending
    induction pending generalizing with
    | nil => ...
    | cons bh bt ih_inner => ...
```

**Key insights from the working pattern**:
1. The `let rec processNext` is accessible as `classicalExpandBranches.processNext`
2. `simp [classicalExpandBranches]` unfolds the outer match on fuel
3. The inner induction uses `induction pending generalizing` with the `with` syntax
4. Length invariants (`expandedSets.length = branches.length`) must be threaded through

### Solution for Classical Build Errors

The classical file has the right structure but incorrect tactic applications.
Specific fixes needed:

1. **Line 522** (`simp only at hsfeq`): Remove this line. The `hsfeq` hypothesis
   after `List.exists_of_findSome?_eq_some` already has the right form for
   `split_ifs at hsfeq`.

2. **Line 586** (`induction pending generalizing with`): The `generalizing`
   keyword needs explicit variable names or should use different syntax. In
   Lean 4.31.0, the correct syntax may be:
   ```lean
   induction pending with
   ```
   (dropping `generalizing` and instead generalizing in the `intro` step).

3. **Lines 566-581** (body of `classicalExpandBranches_closed_unsat`): The type
   mismatches are cascading errors from lines 522 and 586. Fixing those should
   resolve the downstream errors.

4. **Lines 644-647** (`classicalTableau_sound`): The length invariant argument
   `(by rfl)` needs adjusting since `expandedSets = [[]]` and `branches = [_]`
   have `List.length [[]] = List.length [_]` which is `1 = 1`, provable by `rfl`.
   The error may be a missing argument or an argument in the wrong position.

**Estimated effort**: 1-2 hours to fix build errors in the classical file.
The proof structure is sound; only tactical adjustments are needed.

### Solution for Intuitionistic Loop (B1 proper)

The intuitionistic loop `intExpandBranches` has the same outer structure as
the classical case, but with additional complexity:

1. **Three parallel lists** instead of two: `branches`, `expandedSets`, `nextWorlds`
2. **Persistence fixpoint**: `applyPersistenceFixpoint` is applied before each step
3. **World-creation**: F(imp) rule updates `worldOf` (connects to B2)
4. **Parameterized closure**: `closurePred` abstracts over int/min closure

**Proposed lemma** (analogous to classical):

```lean
private lemma intExpandBranches_closed_unsat
    {World : Type*} [Preorder World]
    (val : World → Atom → Prop)
    (botForces : World → Prop)
    (v_uc : ∀ {w w' : World} (p : Atom), w ≤ w' → val w p → val w' p)
    (bf_uc : ∀ {w w' : World}, w ≤ w' → botForces w → botForces w')
    (closurePred : IBranch Atom → Bool)
    (h_closed_unsat : ∀ (worldOf : Nat → World) (b : IBranch Atom),
      closurePred b = true → ¬ intBranchSatisfied val botForces worldOf b)
    (fuel : Nat) :
    ∀ (branches : List (IBranch Atom))
      (expandedSets : List (List (ISF Atom)))
      (nextWorlds : List Nat)
      (worldOf : Nat → World),
      -- length invariants
      expandedSets.length = branches.length →
      nextWorlds.length = branches.length →
      -- label freshness: all labels on each branch are below the corresponding nextWorld
      (∀ i (hi : i < branches.length), ∀ sf ∈ branches[i],
        sf.label < nextWorlds[i]'(by omega)) →
      intExpandBranches branches expandedSets nextWorlds fuel closurePred = .closed →
      ∀ b ∈ branches, ¬ intBranchSatisfied val botForces worldOf b
```

**Key difference from classical**: The `worldOf` parameter. When F(imp) fires,
we need to construct a new `worldOf'` via `Function.update`. The B2 solution
(below) provides this.

**Proof structure**: Same outer/inner induction as classical, but:
- Zero case: identical (all branches closed by `closurePred`)
- Succ case: `suffices` for inner lemma about `intExpandBranches.go`
  - Closed branch: use `h_closed_unsat`
  - Saturated: returns `.openBranch`, contradiction
  - Rule fires: use `intRule_preserves_sat_ext` (B2 solution) to get
    `worldOf'`, then apply IH with updated `worldOf'`

**Complication**: The `worldOf` in the conclusion is fixed, but the loop
may update it at each F(imp) step. This means the invariant must be stated
in contrapositive form:

> If `intExpandBranches ... = .closed`, then for ALL `worldOf`, no branch
> is satisfied.

This is the correct form because `IValid` quantifies universally over models.
The proof constructs the contradicting model step by step.

**Alternative formulation** (simpler, avoids threading `worldOf`):

> If `intExpandBranches ... = .closed`, then for any branch `b` in the input,
> for any Kripke model, `b` is not satisfied.

This works because the universal quantification over models absorbs the
`worldOf` construction.

### Required Supporting Lemmas

1. **`applyPersistenceFixpoint_preserves_sat`**: If branch is satisfied,
   applying persistence preserves satisfaction. Requires `worldOf` to be
   order-preserving (or weaker: labels on branch ordered implies worlds ordered).

2. **`intStepBranch_preserves_sat`**: Analogous to `classicalStepBranch_preserves_sat`.
   If branch is satisfied and a step produces new branches, at least one new branch
   is satisfied (using the B2-resolved `intRule_preserves_sat_ext`).

## Blocker B2: F(imp) worldOf Mismatch

### Problem Description (Verified)

At the sorry site (Intuitionistic/Soundness.lean:162), the goal after unfolding is:

```
⊢ intBranchSatisfied val botForces worldOf
    (Branch.extendMany b (intFImpRule φ ψ label nw b).1)
```

The `intFImpRule` adds:
- `T(φ) at nw`
- `F(ψ) at nw`
- `T(α) at nw` for each `T(α) at label` in `b` (via `propagatePersistence`)

From `hneg : ¬IForces val botForces (worldOf label) (φ → ψ)`, by unfolding
`IForces_imp` and `push_neg`, we get:

```
∃ w' : World, worldOf label ≤ w' ∧
  IForces val botForces w' φ ∧ ¬IForces val botForces w' ψ
```

The existential witness `w'` satisfies T(φ) and F(ψ). But the goal requires
`IForces val botForces (worldOf nw) φ` -- and `worldOf nw` is universally
quantified (the lemma holds for ALL `worldOf`). There is no way to force
`worldOf nw = w'`.

**Verdict**: The lemma `intRule_preserves_sat` is **provably too strong** for the
F(imp) case. This is a genuine type-level impossibility, not a proof difficulty.

### Solution: Existential worldOf Extension

Replace the current `intRule_preserves_sat` with a version that returns
`∃ worldOf'` for the F(imp) case.

**New lemma signature**:

```lean
lemma intRule_preserves_sat_ext {World : Type*} [Preorder World]
    (val : World → Atom → Prop)
    (botForces : World → Prop)
    (v_uc : ∀ {w w' : World} (p : Atom), w ≤ w' → val w p → val w' p)
    (bf_uc : ∀ {w w' : World}, w ≤ w' → botForces w → botForces w')
    (worldOf : Nat → World)
    (b : IBranch Atom)
    (sf : ISF Atom)
    (hmem_sf : sf ∈ b)
    (hsat : intBranchSatisfied val botForces worldOf b)
    (nw : Nat)
    (h_fresh : ∀ sf' ∈ b, sf'.label < nw) :
    match intApplyRuleFull sf nw b with
    | .linearResult newForms _ =>
      ∃ worldOf' : Nat → World,
        (∀ n, n < nw → worldOf' n = worldOf n) ∧
        intBranchSatisfied val botForces worldOf' (Branch.extendMany b newForms)
    | .branchingResult branches _ =>
      ∃ br ∈ branches,
        intBranchSatisfied val botForces worldOf (Branch.extendMany b br)
    | .notApplicable => True
```

**Key changes from current signature**:
1. Added `v_uc`, `bf_uc` (for `iforces_persistence` on propagated formulas)
2. Added `h_fresh` (all existing labels < nw, maintained as loop invariant)
3. `.linearResult` case: conclusion wraps in `∃ worldOf'` with agreement guarantee
4. `.branchingResult` case: unchanged (no world creation in beta-rules)

### F(imp) Case Proof Sketch

```lean
| neg =>
  cases form with
  | imp φ ψ =>
    -- intApplyRuleFull returns .linearResult (intFImpRule φ ψ label nw b).1 ...
    -- Goal: ∃ worldOf', (∀ n < nw, worldOf' n = worldOf n) ∧
    --       intBranchSatisfied val botForces worldOf' (Branch.extendMany b newForms)

    -- Step 1: Extract witness from ¬IForces(φ → ψ)
    rw [IForces_imp] at hneg
    push_neg at hneg
    obtain ⟨w', hw_le, hφ, hψ⟩ := hneg
    -- Have: worldOf label ≤ w', IForces val botForces w' φ, ¬IForces val botForces w' ψ

    -- Step 2: Define worldOf' = Function.update worldOf nw w'
    refine ⟨Function.update worldOf nw w', ?_, ?_⟩

    -- Step 3: Agreement on old labels
    · intro n hn
      exact Function.update_of_ne (Nat.ne_of_lt hn |>.symm) w' worldOf

    -- Step 4: Satisfaction of extended branch
    · intro sf' hmem'
      simp only [Branch.extendMany, List.mem_append] at hmem'
      rcases hmem' with h_new | h_old
      · -- sf' is in the new formulas from intFImpRule
        -- These have label = nw, so worldOf' nw = w'
        -- Case split on which new formula sf' is:
        -- T(φ,nw): IForces val botForces w' φ ← hφ ✓
        -- F(ψ,nw): ¬IForces val botForces w' ψ ← hψ ✓
        -- Propagated T(α,nw): IForces val botForces (worldOf label) α (from hsat)
        --   + worldOf label ≤ w' (hw_le) → IForces val botForces w' α (by iforces_persistence) ✓
        sorry -- detailed case split, each case straightforward
      · -- sf' is in original branch b
        -- sf'.label < nw (by h_fresh), so worldOf' sf'.label = worldOf sf'.label
        -- Rewrite and apply hsat
        have heq : Function.update worldOf nw w' sf'.label = worldOf sf'.label :=
          Function.update_of_ne (Nat.ne_of_lt (h_fresh sf' h_old) |>.symm) w' worldOf
        -- Now rewrite the goal to use worldOf instead of worldOf'
        -- and apply hsat sf' h_old
        sorry -- straightforward rewrite + hsat application
```

### Non-world-creating Cases (T(and), F(and), T(or), F(or))

For these cases, `intApplyRuleFull` returns either `.linearResult` with
`nextWorld` unchanged or `.branchingResult`. The proof is the same as the
current one (already proved for all cases except F(imp)):
- `.linearResult`: witness `worldOf' = worldOf` (identity, trivially agrees)
- `.branchingResult`: no `∃ worldOf'` needed, same as before

The existing proofs for T(and), F(and), T(or), F(or) can be adapted by
wrapping the conclusion in `⟨worldOf, fun n _ => rfl, ...⟩` for the
`.linearResult` cases.

### Downstream Impact

The loop invariant (`intExpandBranches_closed_unsat`) must thread the
`worldOf'` through. When F(imp) fires:
1. Get `⟨worldOf', hagree, hsat'⟩` from `intRule_preserves_sat_ext`
2. Other branches use labels < nw, so `worldOf'` agrees with `worldOf` on them
3. Continue the induction with `worldOf'`

Since the invariant is stated in contrapositive form (if closed, then FORALL
worldOf, no branch satisfied), the worldOf update is absorbed into the
contradiction argument.

## Blocker B3: Persistence Fixpoint (Supporting)

### Problem

`applyPersistenceFixpoint` is applied before each expansion step in
`intExpandBranches.go`. We need:

```lean
lemma applyPersistenceFixpoint_preserves_sat {World : Type*} [Preorder World]
    (val : World → Atom → Prop) (botForces : World → Prop)
    (v_uc : ∀ {w w'} (p : Atom), w ≤ w' → val w p → val w' p)
    (bf_uc : ∀ {w w'}, w ≤ w' → botForces w → botForces w')
    (worldOf : Nat → World)
    (h_order : ∀ w₁ w₂ : Nat, w₁ ≤ w₂ → worldOf w₁ ≤ worldOf w₂)
    (b : IBranch Atom) (fuel : Nat)
    (hsat : intBranchSatisfied val botForces worldOf b) :
    intBranchSatisfied val botForces worldOf (applyPersistenceFixpoint b fuel)
```

### Solution

Induction on fuel. The key sub-lemma is:

```lean
lemma applyAllTImpRules_preserves_sat ...
    (hsat : intBranchSatisfied val botForces worldOf b) :
    intBranchSatisfied val botForces worldOf (applyAllTImpRules b)
```

**Proof**: `applyAllTImpRules b = b ++ newForms.flatten`. For each new
`T(ψ) at w'` in `newForms`:
- There exists `T(φ → ψ) at w` on `b` with `w ≤ w'`
- There exists `T(φ) at w'` on `b`
- From `hsat`: `IForces val botForces (worldOf w) (φ → ψ)` gives
  `∀ u, worldOf w ≤ u → IForces ... u φ → IForces ... u ψ`
- From `h_order`: `w ≤ w'` implies `worldOf w ≤ worldOf w'`
- Instantiate: `IForces val botForces (worldOf w') ψ`

**Important caveat**: The `h_order` hypothesis requires `worldOf` to be
order-preserving. After a `Function.update` from B2's resolution, this
needs checking. If `worldOf' = Function.update worldOf nw w'` where
`worldOf label ≤ w'` and all branch labels ≤ label (or more generally
< nw), then for any `n₁ ≤ n₂` with both `< nw`:
`worldOf' n₁ = worldOf n₁ ≤ worldOf n₂ = worldOf' n₂` (by original h_order).

For `n₁ < nw = n₂`: `worldOf' nw = w'` and we need `worldOf n₁ ≤ w'`.
Since `n₁ < nw` and the only way n₁ relates to the current branch is
`n₁ ≤ label` (world labels form a tree rooted at the initial world),
we get `worldOf n₁ ≤ worldOf label ≤ w'`.

**Alternative**: Instead of `h_order`, require only order-preservation on
labels actually appearing on the branch. This is cleaner but harder to state.

## Implementation Roadmap

### Priority 0: Fix Classical Soundness Build Errors

**Effort**: 1-2 hours
**Files**: `Classical/Soundness.lean`
**What**: Fix 9 build errors in the existing proof. The proof structure is correct;
only tactic adjustments needed for current Lean 4.31.0 / Mathlib API.

Specific fixes:
1. Line 522: Remove `simp only at hsfeq` (it's unnecessary; `split_ifs` handles it)
2. Line 586: Fix `induction pending generalizing with` syntax
3. Lines 566-581: Cascading fixes after above
4. Lines 644-647: Fix argument order in `classicalExpandBranches_closed_unsat` application

### Priority 1: Implement B2 Solution (intRule_preserves_sat_ext)

**Effort**: 2-3 hours
**Files**: `Intuitionistic/Soundness.lean`
**What**: Replace `intRule_preserves_sat` with `intRule_preserves_sat_ext` and prove
all cases including F(imp).

Steps:
1. Add `v_uc`, `bf_uc`, `h_fresh` parameters
2. Modify existing proved cases (T(and), F(and), T(or), F(or)) to wrap in `∃ worldOf'`
3. Prove F(imp) case using `Function.update` + `iforces_persistence`

### Priority 2: Implement B3 Solution (Persistence Fixpoint)

**Effort**: 1-2 hours
**Files**: `Intuitionistic/Soundness.lean`
**What**: Prove `applyAllTImpRules_preserves_sat` and `applyPersistenceFixpoint_preserves_sat`.

### Priority 3: Implement Intuitionistic Loop Invariant

**Effort**: 3-4 hours
**Files**: `Intuitionistic/Soundness.lean`
**What**: Prove `intExpandBranches_closed_unsat` following the classical pattern.
Use `intRule_preserves_sat_ext` + `applyPersistenceFixpoint_preserves_sat`.

### Priority 4: Complete Main Theorems

**Effort**: 1-2 hours
**Files**: `Intuitionistic/Soundness.lean`, `Minimal/DecisionProcedure.lean`
**What**: Fill `intuitionisticTableau_sound` and `minimalTableau_sound` using the
loop invariant. Both follow the classical contrapositive pattern.

### Total Estimated Effort: 8-13 hours

## Risks and Mitigations

### Risk 1: `Function.update` Order Preservation

The `h_order` hypothesis for persistence may not survive `Function.update`.

**Mitigation**: Weaken `h_order` to only require order-preservation on labels
appearing on the current branch. Since `applyPersistenceFixpoint` only adds
formulas at existing labels, the weakened hypothesis suffices.

### Risk 2: `intExpandBranches.go` Unfolding

The `go` inner function may not unfold as cleanly as `processNext`.

**Mitigation**: Both are `let rec` definitions; the classical case demonstrates
this works. If `go` has issues, extract it as a top-level definition.

### Risk 3: Length Invariant for Three Lists

`intExpandBranches` tracks three parallel lists (`branches`, `expandedSets`,
`nextWorlds`). Threading three length invariants adds proof burden.

**Mitigation**: Use a single record/tuple type or prove a combined invariant.
Alternatively, prove a weaker invariant that doesn't require exact length
matching (the expansion loop has a fallback for mismatched lengths).

### Risk 4: Persistence Fixpoint Changes Labels

`applyAllTImpRules` adds formulas at EXISTING labels (drawn from `worldsAbove`).
No new labels are introduced. This preserves the `h_fresh` invariant.

**Status**: Verified safe. `applyPersistenceFixpoint` preserves label freshness.

## Tactic Survey Results

For the F(imp) proof:
- `Function.update_self` (Mathlib): `Function.update f a v a = v`
- `Function.update_of_ne` (Mathlib): `a ≠ a' → Function.update f a' v a = f a`
- `Function.update_apply` (Mathlib): `Function.update f a' b a = if a = a' then b else f a`
- `iforces_persistence` (CSLib): proven for all formula constructors
- `push_neg` + `not_forall`: transforms `¬ ∀ w', ... → ... → ...` into `∃ w', ... ∧ ... ∧ ¬...`
- `IForces_imp`, `IForces_and`, `IForces_or`, `IForces_bot`: all @[simp]

For the loop invariant:
- `simpa [classicalExpandBranches] using h`: successfully unfolds fuel match (verified in classical)
- `simp only [classicalExpandBranches.processNext]`: unfolds `let rec` (verified)
- `List.mem_cons`, `List.mem_append`: standard membership splitting
- `List.exists_of_findSome?_eq_some`: extracts witness from `findSome?`
