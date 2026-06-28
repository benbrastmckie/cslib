# Research Report: CI Lint Fixes for CutElimination.lean

## Target File

`Cslib/Logics/Propositional/SequentCalculus/LK/CutElimination.lean`

## Issue Summary

Running `lake build Cslib.Logics.Propositional.SequentCalculus.LK.CutElimination` produces
10 warnings total: 1 maxHeartbeats comment, 8 long-line warnings, and 1 unused variable.

## Issue 1: Missing maxHeartbeats Comment (Line 112)

**Warning**: "Please, add a comment explaining the need for modifying the maxHeartbeat limit"

**Current content (line 112)**:
```lean
set_option maxHeartbeats 800000 in
```

**Required fix**: Add a comment between the `in` keyword and the `mutual` block explaining
why the heartbeat increase is needed. The linter (`linter.style.maxHeartbeats`) checks for
trailing content after the `in` token.

**Fix**:
```lean
set_option maxHeartbeats 800000 in
-- Cut admissibility mutual recursion block requires extended heartbeats for case analysis
```

**Reference pattern** from `Cslib/Logics/Bimodal/Metalogic/Separation/DedekindZ/QLemma.lean:98-99`:
```lean
set_option maxHeartbeats 800000 in
-- Ported from BimodalLogic, heartbeats needed for case analysis
```

## Issue 2: Long Lines (8 instances, all >100 chars)

Each line exceeds the 100-character limit enforced by `linter.style.longLine`.

### Line 147 (101 chars)

**Current**:
```lean
      have hA : sizeOf A < sizeOf (Proposition.and A B) := by rw [Proposition.and.sizeOf_spec]; omega
```

**Fix**: Break after `:= by`:
```lean
      have hA : sizeOf A < sizeOf (Proposition.and A B) := by
        rw [Proposition.and.sizeOf_spec]; omega
```

### Line 148 (101 chars)

**Current**:
```lean
      have hB : sizeOf B < sizeOf (Proposition.and A B) := by rw [Proposition.and.sizeOf_spec]; omega
```

**Fix**: Break after `:= by`:
```lean
      have hB : sizeOf B < sizeOf (Proposition.and A B) := by
        rw [Proposition.and.sizeOf_spec]; omega
```

### Line 250 (102 chars)

**Current**:
```lean
      (d₁a.mono (Finset.subset_insert _ _) (Finset.insert_subset_insert _ (Finset.subset_insert _ _)))
```

**Fix**: Break before the second parenthesized argument:
```lean
      (d₁a.mono (Finset.subset_insert _ _)
        (Finset.insert_subset_insert _ (Finset.subset_insert _ _)))
```

### Line 251 (102 chars)

**Current**:
```lean
      (d₁b.mono (Finset.subset_insert _ _) (Finset.insert_subset_insert _ (Finset.subset_insert _ _)))
```

**Fix**: Break before the second parenthesized argument:
```lean
      (d₁b.mono (Finset.subset_insert _ _)
        (Finset.insert_subset_insert _ (Finset.subset_insert _ _)))
```

### Line 501 (101 chars)

**Current**:
```lean
      have hA : sizeOf A < sizeOf (Proposition.imp A B) := by rw [Proposition.imp.sizeOf_spec]; omega
```

**Fix**: Break after `:= by`:
```lean
      have hA : sizeOf A < sizeOf (Proposition.imp A B) := by
        rw [Proposition.imp.sizeOf_spec]; omega
```

### Line 502 (101 chars)

**Current**:
```lean
      have hB : sizeOf B < sizeOf (Proposition.imp A B) := by rw [Proposition.imp.sizeOf_spec]; omega
```

**Fix**: Break after `:= by`:
```lean
      have hB : sizeOf B < sizeOf (Proposition.imp A B) := by
        rw [Proposition.imp.sizeOf_spec]; omega
```

### Line 527 (101 chars)

**Current**:
```lean
        (d₁'.mono (Finset.Subset.refl _) (Finset.insert_subset_insert _ (Finset.subset_insert A' _)))
```

**Fix**: Break before the second argument:
```lean
        (d₁'.mono (Finset.Subset.refl _)
          (Finset.insert_subset_insert _ (Finset.subset_insert A' _)))
```

### Line 535 (101 chars)

**Current**:
```lean
        (d₁'.mono (Finset.insert_subset_insert _ (Finset.subset_insert B' _)) (Finset.Subset.refl _))
```

**Fix**: Break before the second argument:
```lean
        (d₁'.mono (Finset.insert_subset_insert _ (Finset.subset_insert B' _))
          (Finset.Subset.refl _))
```

## Issue 3: Unused Variable `hB` (Line 857)

**Warning**: "Variable name `hB` is not explicitly referenced. The binding can be removed
(if unused) or named `_` (if used implicitly)."

**Current (line 857)**:
```lean
    (fun B hB Γ' Δ' d₁' d₂' => cutAdmissibility B Γ' Δ' d₁' d₂')
```

The variable `hB` is the proof that `sizeOf B < sizeOf C` (from the `CutIH` type alias on
line 96-101). It is passed to `cutAdmissibility` implicitly via the `termination_by sizeOf C`
clause -- the well-founded recursion machinery uses `hB` to verify that `B` is strictly smaller,
but `cutAdmissibility` does not take `hB` as an explicit argument.

**Fix**: Rename `hB` to `_` since it is used implicitly (not explicitly referenced):
```lean
    (fun B _ Γ' Δ' d₁' d₂' => cutAdmissibility B Γ' Δ' d₁' d₂')
```

## Risk Assessment

All 10 fixes are purely mechanical:
- No proof logic changes
- No type signature changes
- No import changes
- Line breaks only add whitespace at valid continuation points
- The `hB -> _` rename preserves the binding (it is used implicitly for termination)

**Risk**: Negligible. The only non-trivial risk is that line breaks in the mutual block could
interact with Lean's whitespace-sensitive parsing, but all proposed breaks are at standard
continuation points (after `:= by`, before function arguments). A `lake build` after the
edits will confirm correctness.

## Verification Plan

After applying all fixes:
1. `lake build Cslib.Logics.Propositional.SequentCalculus.LK.CutElimination` -- should produce
   zero warnings
2. `lake test` -- should pass (no behavioral changes)
