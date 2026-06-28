# Build Repair Handoff: Normalization.lean exists_stronglyNormal_form

## Status at Handoff

The build is NOT green. Falling back to baseline (1 sorry) as instructed.

## What Was Fixed

1. **`| ind triple ih =>`** → **`| h triple ih =>`** at line ~1854: Fixed case name for WellFounded.induction.

2. **`Prod.Lex.inr` (28 occurrences)** → **`Prod.Lex.right`**: Bulk replaced throughout exists_stronglyNormal_form.

3. **`Prod.Lex.inl` (11 occurrences)** → **`Prod.Lex.left`**: Bulk replaced.

4. **`isDershowitzMannaLT_all_lt_add` apply failure** at line 1758: Added `rw [Multiset.add_comm]` before apply to fix RHS form.

5. **Timeout in commuting conversion proofs** (h_6, h_7, h_8): Replaced `cases DA' <;> cases DB' <;> simp_all [...]` with targeted have-lemmas:
   - `hDA'_mf`: maximalFormulas equality
   - `hDA'_cs`: commutingSum equality
   Then case-split only on D' (10 cases instead of 100).

6. **Wrong induction syntax**: Replaced `induction h : ... using WellFounded.induction ... generalizing ... with | h ... =>` with `suffices ... from this _ rfl; intro triple; apply (...).induction (C := ...) (a := ...); intro triple ih G A d h`.

## Remaining Issues (Why Fallback Was Needed)

### Issue 1: `Prod.Lex.right` Usage Semantics

The prior agent wrote `apply Prod.Lex.right; apply Prod.Lex.right; omega` extensively throughout `exists_stronglyNormal_form`. However, `Prod.Lex.right` requires proving EQUALITY of the first components (not just existence). For `andI G D₁ D₂`, proving `(D₁.mf, D₁.cs, D₁.nc) <lex (D₁.mf + D₂.mf, D₁.cs + D₂.cs, 1+D₁.nc+D₂.nc)` via `Prod.Lex.right` requires `D₁.mf = D₁.mf + D₂.mf` which only holds when `D₂.mf = ∅`. The correct proof needs case analysis:
- If D₂.mf ≠ ∅: use `Prod.Lex.left` with `isDershowitzMannaLT_add_right`
- If D₂.mf = ∅: use `Prod.Lex.right rfl` then recurse to commutingSum/nodeCount

### Issue 2: `rw [h]` vs `rw [← h]` in ih_d

After restructuring the induction, `h : (d.mf, d.cs, d.nc) = triple` (not `triple = (d.mf, ...)` as before). The `ih_d` proof uses `rw [h] at hlt` to convert `(d.mf, d.cs, d.nc)` to `triple` in `hlt`, which is correct. But the `ih` provided by the induction uses `WellFoundedRelation.rel` (the canonical well-founded relation) while the proof uses `(· < ·)` explicitly - these need to be reconciled.

### Issue 3: Timeout at Line 1704

The `reduceRoot_decreases_normMeasure` theorem still times out. The h_6, h_7, h_8 cases have `simp only [commutingSum, hDA'_cs, hDB'_cs]; cases D' <;> simp_all [commutingSum, nodeCount] <;> omega` which times out. The `simp_all` with `isStronglyNormal` is expensive because Lean tries to simplify 10 constructors × complex hypotheses. The fix is to avoid `simp_all` in favour of targeted `simp only`.

### Issue 4: `rw [show ...]` failures in h_6, h_7

The `rw [show ... from by simp only [maximalFormulas]; rw [hDA'_mf, hDB'_mf]; cases D' <;> simp [maximalFormulas]]` may fail because the `rw [hDA'_mf]` finds the LHS `(andE1 _ DA').maximalFormulas` but the current goal after `simp only [maximalFormulas]` may not expose this pattern cleanly.

## Correct Approach for Successor Agent

### Option A: Prove nodeCount-based inequality more carefully

For structural recursion cases in `exists_stronglyNormal_form` (andI, andE1, andE2, orI1, orI2, impI, impE), the correct proof pattern for `ih_d` calls is:

```lean
-- For andI: D₁ is strictly smaller by nodeCount
apply ih_d
-- Goal: Prod.Lex DM (Prod.Lex < <) (D₁.mf, D₁.cs, D₁.nc) (d.mf, d.cs, d.nc)
-- After simp [h, maximalFormulas, commutingSum, nodeCount]:
-- = (D₁.mf, D₁.cs, D₁.nc) <lex (D₁.mf + D₂.mf, D₁.cs + D₂.cs, 1+D₁.nc+D₂.nc)
rcases Multiset.eq_zero_or_pos D₂.mf with hD₂ | hD₂
· -- D₂.mf = ∅
  simp [maximalFormulas] at h ⊢
  rcases Nat.eq_zero_or_pos D₂.cs with hD₂cs | hD₂cs
  · -- cs also 0, use nodeCount
    apply Prod.Lex.right; · simp [hD₂, hD₂cs, ← h]
    apply Prod.Lex.right; · simp [hD₂cs, ← h]  
    omega
  · -- cs > 0, use commutingSum
    apply Prod.Lex.right; · simp [hD₂, ← h]
    apply Prod.Lex.left; omega
· -- D₂.mf ≠ ∅
  apply Prod.Lex.left
  simp [maximalFormulas, ← h]
  exact isDershowitzMannaLT_add_right (Multiset.nonempty_iff_ne_zero.mp (Multiset.pos_iff_ne_zero.mp hD₂))
```

This is the core pattern needed throughout the proof.

### Option B: Simplify the Proof Strategy

Consider using `Nat.measure` or `WellFounded.recursion` pattern with `decreasing_by` if available, or reformulate using `Nat.strongRecOn` on a single combined measure (encoded as `d.nodeCount`). The nodeCount alone is sufficient for structural recursion, and for the `by_cases h_sn` / `reduceRoot` cases, the `reduceRoot_decreases_normMeasure` theorem can be used.

## Files Modified in This Session

- `Cslib/Logics/Propositional/NaturalDeduction/Normalization.lean`: Multiple edits, then RESTORED to baseline.

## Backup Location

The in-progress (still broken) proof is saved at:
`specs/332_normalization_termination_proof/handoffs/normalization-in-progress-YYYYMMDD-HHMMSS.lean`
