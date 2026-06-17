# Research Report: Tactic Goal-Count Warnings in Cases.lean

## File Under Analysis

`Cslib/Logics/Bimodal/Metalogic/Separation/DedekindZ/Cases.lean`

## Summary

All 4 tactic goal-count warnings are concentrated in a single theorem, `case1_psi_bool_only` (lines 196-221). The warnings are caused by chained `apply` calls on single semicolon-separated lines, where each successive `apply` operates only on the first goal but leaves earlier-created sibling goals unfocused.

## Warning Inventory

### Warning 1: Line 209, Column 14

```
warning: The following tactic starts with 2 goals and ends with 3 goals,
1 of which is not operated on.
```

**Context**: Line 209 reads `apply h_or; apply h_or`.

The first `apply h_or` transforms the single `case1Psi` goal into 2 subgoals (left and right of the outer `or`). The second `apply h_or` then operates on goal 1 only (the left disjunct), splitting it into 2 more subgoals. Goal 2 from the first `apply` (the right disjunct, line 219-221) is left unfocused.

**Affected tactic**: The second `apply h_or` at column 14.

### Warning 2: Line 210, Column 17

```
warning: The following tactic starts with 2 goals and ends with 3 goals,
1 of which is not operated on.
```

**Context**: Line 210 reads `· apply h_and; apply h_and; apply h_and` (inside the `·` focus from line 210).

After the first `apply h_and` creates 2 goals (left and right of the `and`), the second `apply h_and` operates on goal 1, creating a third goal. Goal 2 from the first `apply h_and` is not yet operated on.

**Affected tactic**: The second `apply h_and` at column 17.

### Warning 3: Line 210, Column 30

```
warning: The following tactic starts with 3 goals and ends with 4 goals,
2 of which are not operated on.
```

**Context**: Same line 210, the third `apply h_and`.

Now there are 3 goals (from the two prior applies). The third `apply h_and` operates on goal 1, splitting it into 2. Goals 2 and 3 (from the prior applies) remain unfocused.

**Affected tactic**: The third `apply h_and` at column 30.

### Warning 4: Line 215, Column 17

```
warning: The following tactic starts with 2 goals and ends with 3 goals,
1 of which is not operated on.
```

**Context**: Line 215 reads `· apply h_and; apply h_and` (inside a `·` focus block).

After the first `apply h_and` creates 2 goals, the second `apply h_and` operates on goal 1 only, leaving goal 2 unfocused.

**Affected tactic**: The second `apply h_and` at column 17.

## Root Cause Analysis

All 4 warnings share the same root cause: **semicolon-chained `apply` calls that create unfocused goals**. When `apply f` is used where `f` takes 2 arguments, it creates 2 subgoals. A subsequent `apply g` on the same tactic line (via `;`) operates on the first subgoal only, leaving the second unfocused. The proof still works because the subsequent `· exact ...` focus blocks close the remaining goals, but the intermediate state has unfocused goals which triggers the Lean linter warning.

The current proof structure (lines 208-221):

```lean
unfold case1Psi
apply h_or; apply h_or           -- Warning 1: 2nd apply h_or
· apply h_and; apply h_and; apply h_and  -- Warnings 2, 3: 2nd and 3rd apply h_and
  · exact ...
  · exact ...
  · exact ...
  · exact ...
· apply h_and; apply h_and       -- Warning 4: 2nd apply h_and
  · exact ...
  · exact ...
  · exact ...
· have hev_uf : ... := ...
  exact ...
```

## Recommended Fix

Replace the chained `apply` calls with properly focused `· ...` blocks that nest the proof tree. Each `apply` that creates multiple goals should have its subgoals explicitly focused using `·` notation.

### Proposed restructured proof (lines 208-221)

```lean
unfold case1Psi
apply h_or
· apply h_or
  · apply h_and
    · apply h_and
      · apply h_and
        · exact (⟨ha, hq⟩ : untlUnderBoolOnly (.snce a q) A B)
        · exact (⟨ha, hB⟩ : untlUnderBoolOnly (.snce a B) A B)
      · exact u_free_untl_under_bool B A B hB
    · exact Or.inl ⟨rfl, rfl⟩
  · apply h_and
    · apply h_and
      · exact u_free_untl_under_bool A A B hA
      · exact (⟨ha, hB⟩ : untlUnderBoolOnly (.snce a B) A B)
    · exact (⟨ha, hq⟩ : untlUnderBoolOnly (.snce a q) A B)
· have hev_uf : isUFree (Formula.and (Formula.and (Formula.and A q) (.snce a B)) (.snce a q)) = true := by
    simp [Formula.and, Formula.neg, isUFree, hA, hq, ha, hB]
  exact (⟨hev_uf, hq⟩ : untlUnderBoolOnly (.snce _ q) A B)
```

### Key changes

1. **Line 209**: Split `apply h_or; apply h_or` into two focused blocks: `apply h_or` at the top level, then `· apply h_or` for the first disjunct.

2. **Line 210**: Split `apply h_and; apply h_and; apply h_and` into nested focused blocks: `· apply h_and` / `· apply h_and` / `· apply h_and` each as separate focus levels.

3. **Line 215**: Split `apply h_and; apply h_and` into `· apply h_and` / `· apply h_and` with proper nesting.

4. **Lines 219-221**: The third `· ...` block (the `hev_uf` block for the `snce` case) stays as the second top-level `·` of the outer `apply h_or`.

## Codebase Pattern Survey

The CSLib codebase uses several patterns for handling multi-goal tactics:

1. **Focus with `·` blocks** (most common): Each `apply` gets its own `·` block with subgoals nested underneath. This is the standard approach in `Cslib/Logics/Bimodal/Metalogic/Separation/` and throughout CSLib.

2. **`<;>` combinator**: Used when the same tactic should be applied to all resulting goals (e.g., `apply Iff.intro <;> intro h`). Not applicable here since each subgoal needs different handling.

3. **`all_goals`**: Used in `HierarchyCaseSep.lean` when many goals share the same proof shape. Not applicable here since each subgoal has distinct proof terms.

The recommended fix uses pattern 1, which is consistent with how the rest of this file and neighboring files in the Separation directory handle their proofs.

## Verification Plan

After applying the fix:
1. Run `lake build Cslib.Logics.Bimodal.Metalogic.Separation.DedekindZ.Cases` and confirm zero warnings
2. Verify no new errors introduced
3. The proof logic is unchanged -- only the tactic tree structure is restructured for proper focusing

## Risk Assessment

**Low risk**: The fix is purely structural (adding `·` focus blocks and removing `;` chains). No proof logic changes. The same `apply` and `exact` calls are used in the same order; only the focusing/nesting is corrected.
