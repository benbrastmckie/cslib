# Research Report: Fix `backward.isDefEq.respectTransparency` Workaround

**Task**: 286
**File**: `Cslib/Computability/Languages/OmegaRegularLanguage.lean`
**Theorem**: `IsRegular.eq_fin_iSup_hmul_omegaPow`
**Session**: sess_1750711200_a3b2c1_286

## Problem Summary

Lines 193-194 contain a TODO and `set_option` workaround:

```lean
-- TODO: fix proof to work with backward.isDefEq.respectTransparency
set_option backward.isDefEq.respectTransparency false in
```

The workaround disables `backward.isDefEq.respectTransparency` (default `true` since Lean 4)
for the entire theorem `IsRegular.eq_fin_iSup_hmul_omegaPow`. The comment at line 217 confirms
the exact location where this is needed: `simpa [mem_def]` at line 218.

## Root Cause Analysis

### What the option controls

`backward.isDefEq.respectTransparency` controls how implicit arguments are handled during
`isDefEq` checks in proof automation (`simp`, `rw`, `simpa`, etc.). When `true` (default),
implicit arguments are checked at a stricter transparency level. When `false`, implicit
arguments get a transparency bump to `.default`, which unfolds semireducible definitions
more aggressively.

### Why the workaround was needed

The proof constructs an equivalence:

```lean
have eq := (eq_prod.trans finProdFinEquiv).symm
```

This `eq : Fin (Nat.card na.start * Nat.card na.accept) ~= na.start x na.accept` is used to
witness an existential via `use eq.invFun (...)`. After `use`, the goal contains:

```
eq (eq.invFun (x_s, h_s, x_t, h_t))
```

The `simpa [mem_def]` call at line 218 needs to close the goal by unifying this expression
with `(x_s, h_s, x_t, h_t)` (i.e., `Equiv.right_inv`). With `respectTransparency = true`,
the `isDefEq` check during `simpa`'s finishing `assumption` step operates at reducible
transparency for implicit arguments, which is too strict to unfold the `Equiv` structure
components and see that `eq (eq.invFun x) = x`.

### Why this is a Lean elaboration limitation, not a CSLib bug

The issue is that `simpa` combines `simp` simplification with an `assumption`-like finishing
step. The finishing step uses `isDefEq` at the caller's transparency level. When
`respectTransparency = true`, implicit arguments in the matching are checked at a strict level
that cannot resolve `Equiv.toFun (Equiv.invFun x) = x` definitionally. This is a known
performance vs. completeness trade-off in Lean's elaborator -- the stricter default was
introduced to prevent expensive unfolding in Mathlib's simp calls.

## Solution: Verified Fix

The workaround can be completely removed by restructuring the proof to avoid relying on
`simpa`'s implicit `isDefEq` check. The fix has been verified to compile without
`set_option backward.isDefEq.respectTransparency false`.

### Changes (3 sites in the proof)

**1. Remove the TODO comment and `set_option` (lines 193-194)**

Delete:
```lean
-- TODO: fix proof to work with backward.isDefEq.respectTransparency
set_option backward.isDefEq.respectTransparency false in
```

**2. Change `eq.invFun` to `eq.symm` (line 216)**

Replace:
```lean
    use eq.invFun ((s, h_s), (t, h_t))
```
With:
```lean
    use eq.symm ((s, h_s), (t, h_t))
```

This uses the canonical coercion path (`eq.symm` via `FunLike`) instead of the raw structure
field (`eq.invFun`), which allows `Equiv.apply_symm_apply` to match.

**3. Replace `simpa [mem_def]` with explicit rewrite (lines 217-218)**

Replace:
```lean
    -- The following `simp` is where the `set_option` above is needed.
    simpa [mem_def]
```
With:
```lean
    simp only [Equiv.apply_symm_apply]
    exact h_mem
```

The `simp only [Equiv.apply_symm_apply]` rewrites `eq (eq.symm x)` to `x`, reducing the goal
to exactly `h_mem`. Then `exact h_mem` closes it without needing any transparency gymnastics.

### Why this fix works

The original `simpa [mem_def]` attempted two things in one step:
1. Simplify the goal (unfold `mem_def`)
2. Close it via `assumption` (which needs `isDefEq` at reducible transparency)

Step 2 fails because `eq (eq.invFun x)` cannot be reduced to `x` at reducible transparency.

The fix separates these concerns:
- `simp only [Equiv.apply_symm_apply]` explicitly rewrites `eq (eq.symm x) = x` using a
  proper simp lemma (this works at any transparency since it's a rewrite, not an `isDefEq` check)
- `exact h_mem` then matches the simplified goal syntactically (no transparency issue)

### Diff

```diff
--- a/Cslib/Computability/Languages/OmegaRegularLanguage.lean
+++ b/Cslib/Computability/Languages/OmegaRegularLanguage.lean
@@ -190,8 +190,6 @@
   use Unit + State, inferInstance, (na.loop, {inl ()})
   exact NA.Buchi.loop_language_eq

--- TODO: fix proof to work with backward.isDefEq.respectTransparency
-set_option backward.isDefEq.respectTransparency false in
 /-- An omega-language is regular iff ... -/
 theorem IsRegular.eq_fin_iSup_hmul_omegaPow ...
@@ -213,9 +211,9 @@
     simp only [mem_iSup]
     refine (?_, by grind)
     rintro (s, h_s, t, h_t, h_mem)
-    use eq.invFun ((s, h_s), (t, h_t))
-    -- The following `simp` is where the `set_option` above is needed.
-    simpa [mem_def]
+    use eq.symm ((s, h_s), (t, h_t))
+    simp only [Equiv.apply_symm_apply]
+    exact h_mem
   . rintro (n, l, m, _, rfl)
```

## Alternatives Investigated and Rejected

| Approach | Result | Reason for rejection |
|----------|--------|---------------------|
| `simpa using h_mem` | Fails without `set_option` | `simpa`'s finishing `assumption` still needs transparency bump |
| `simpa! [mem_def]` | Fails without `set_option` | `!` enables auto-unfold for simp but not for final `assumption` |
| `convert h_mem using 2 <;> simp` | Fails without `set_option` | `simp` subgoals still contain `eq (eq.symm x)` terms |
| `simp only [eq.right_inv]` | No progress | `eq.right_inv` uses `.toFun`/`.invFun` not coercion syntax; simp can't match |
| `simp only [Equiv.apply_symm_apply]` (with `invFun`) | No progress | `Equiv.apply_symm_apply` matches `e (e.symm x)` not `e (e.invFun x)` |
| `let eq` instead of `have eq` | Fails | Transparency not the only issue; `simpa`'s `assumption` still fails |
| `simp only [Equiv.invFun_as_coe, Equiv.apply_symm_apply]; exact h_mem` | Builds | Works but less clean than using `eq.symm` directly |

## Tactic Survey Results

| Tactic | Applicable | Result |
|--------|-----------|--------|
| `simp only [Equiv.apply_symm_apply]` + `exact h_mem` | Yes | Closes goal cleanly |
| `simpa [Equiv.apply_symm_apply]` | No | `assumption` step still fails at reducible transparency |
| `convert h_mem` | No | Generates subgoals that simp cannot close without set_option |

## Implementation Complexity

**Difficulty**: Low (mechanical edit, 3 change sites, all in one theorem)
**Risk**: None (the fix has been verified to compile)
**Lines changed**: -4 / +3 (net: -1 line)
**Dependencies**: None -- uses only `Equiv.apply_symm_apply` from Mathlib, already imported

## Recommendation

Proceed directly to implementation. The fix is verified, mechanical, and removes both the
`set_option` workaround and the TODO comment. No plan phase is strictly needed, but may be
used if the orchestrator requires it.
