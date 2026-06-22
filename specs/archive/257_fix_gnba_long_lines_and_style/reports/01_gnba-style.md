# Research Report: Fix Style Issues in GNBA.lean and OmegaRegular.lean

## Task 257

**Session**: sess_1781994910_0cdf2d_257
**Files**: `Cslib/Logics/LTL/Semantics/GNBA.lean` (1483 lines), `Cslib/Logics/LTL/Semantics/OmegaRegular.lean` (342 lines)

## Issue 1: Lines Exceeding 100 Characters in GNBA.lean

All 7 long lines confirmed at their documented positions (task 256 did not shift line numbers in GNBA.lean). Each line and its recommended fix:

### Line 912 (101 chars)

```lean
          if B i ∈ Formula.gnbaAcceptSet φ ((Formula.untlFinset φ).toList.get ⟨idx.val, hlen_i⟩) then
```

**Context**: Inside the `hctr_trans` have-statement (lines 906-922). The `idx` and `hlen_i` are already bound via `let` on lines 909-911 immediately above. The long expression is the `gnbaAcceptSet` call with an inline list-get argument.

**Fix**: Break the `if` condition onto its own line by introducing a `let` for the chi value:

```lean
          let χ_i := (Formula.untlFinset φ).toList.get ⟨idx.val, hlen_i⟩
          if B i ∈ Formula.gnbaAcceptSet φ χ_i then
```

This follows the same `let`-binding pattern already used for `idx` and `hlen_i` on lines 909-911. The name `χ_i` is consistent with how the same expression is named elsewhere in the file (see lines 1268, 1330).

### Line 929 (105 chars)

```lean
      have hK_ne : Formula.gnbaK φ ≠ 0 := Nat.pos_iff_ne_zero.mp (Nat.lt_of_le_of_lt (Nat.zero_le _) hlt)
```

**Context**: Inside `hctr_step` (lines 925-933). This is a `have` with a long proof term.

**Fix**: Break after `:=` and indent the proof term:

```lean
      have hK_ne : Formula.gnbaK φ ≠ 0 :=
        Nat.pos_iff_ne_zero.mp (Nat.lt_of_le_of_lt (Nat.zero_le _) hlt)
```

This is the standard Lean 4 style for long proof terms -- break after `:=`.

### Line 1023 (102 chars)

```lean
      have hprev_advance : (ctr (t₀ + 1 + d_first)).val = (ctr (t₀ + 1 + (d_first - 1))).val + 1 := by
```

**Context**: Inside `hctr_induction_step` area (around line 1015-1027). A `have` with a long type signature followed by `:= by`.

**Fix**: Break the type signature across two lines:

```lean
      have hprev_advance :
          (ctr (t₀ + 1 + d_first)).val = (ctr (t₀ + 1 + (d_first - 1))).val + 1 := by
```

### Line 1352 (108 chars)

```lean
          have hP_min_exists : ∃ t_min : ℕ, (fun s => s ≥ t ∧ B s ∈ Formula.gnbaAcceptSet φ χ_m) t_min := by
```

**Context**: Inside the acceptance cycle proof (around line 1345-1360). A `have` statement with a long existential type.

**Fix**: Break after the colon and indent the type, then put `:= by` on the next line:

```lean
          have hP_min_exists :
              ∃ t_min : ℕ, (fun s => s ≥ t ∧ B s ∈ Formula.gnbaAcceptSet φ χ_m) t_min := by
```

Alternatively, simplify the type using beta-reduced form (the `(fun s => ...) t_min` pattern is just `t_min ≥ t ∧ ...`):

```lean
          have hP_min_exists :
              ∃ t_min : ℕ, t_min ≥ t ∧ B t_min ∈ Formula.gnbaAcceptSet φ χ_m := by
```

The beta-reduced form is cleaner and shorter but changes the type syntactically. If `Nat.find` is used downstream with the lambda form, the lambda form should be kept for definitional compatibility. Check the proof body (line 1353: `exact ⟨t_acc, ht_acc_ge, ht_acc_mem⟩`). This does NOT use `Nat.find`, so the beta-reduced form is safe and preferred.

### Line 1421 (110 chars)

```lean
          haveI hd_P_dec : DecidablePred (fun d : ℕ => d ≤ d_acc ∧ B (t + d) ∈ Formula.gnbaAcceptSet φ χ_m) :=
```

**Context**: Providing a DecidablePred instance for `Nat.find` (lines 1419-1422).

**Fix**: Break after `:` and indent the type:

```lean
          haveI hd_P_dec :
              DecidablePred (fun d : ℕ => d ≤ d_acc ∧ B (t + d) ∈ Formula.gnbaAcceptSet φ χ_m) :=
```

### Line 1427 (105 chars)

```lean
          have hd_min_minimal : ∀ d' < d_min, ¬(d' ≤ d_acc ∧ B (t + d') ∈ Formula.gnbaAcceptSet φ χ_m) :=
```

**Context**: Extracting the minimality property from `Nat.find_min` (lines 1427-1428).

**Fix**: Break after `:` and indent the type:

```lean
          have hd_min_minimal :
              ∀ d' < d_min, ¬(d' ≤ d_acc ∧ B (t + d') ∈ Formula.gnbaAcceptSet φ χ_m) :=
```

### Line 1435 (112 chars)

```lean
            exact absurd ⟨Nat.le_of_lt_succ (Nat.lt_succ_of_le (le_trans (Nat.le_of_lt hs) hd_min_bound)), hmem⟩
```

**Context**: Inside the minimality proof, providing a contradiction (lines 1434-1436).

**Fix**: Break the anonymous constructor across lines:

```lean
            exact absurd
              ⟨Nat.le_of_lt_succ (Nat.lt_succ_of_le (le_trans (Nat.le_of_lt hs) hd_min_bound)),
               hmem⟩
```

Or, more readably, use a `have` to name the first component:

```lean
            have hle := Nat.le_of_lt_succ
              (Nat.lt_succ_of_le (le_trans (Nat.le_of_lt hs) hd_min_bound))
            exact absurd ⟨hle, hmem⟩ (hd_min_minimal s hs)
```

The simpler line-break approach is preferred since it is purely cosmetic and less likely to introduce issues.

## Issue 2: Instance Naming in OmegaRegular.lean

### Current Code (line 142)

```lean
instance instInhabitedSetAtom {Atom : Type*} : Inhabited (Set Atom) := ⟨∅⟩
```

### Problems

1. **Name violates Mathlib convention**: Instance names should follow the auto-generated pattern `instClassType` (e.g., `Set.instInhabited`) or be anonymous. The name `instInhabitedSetAtom` includes a non-standard suffix `Atom`.

2. **Likely redundant**: Mathlib provides `Set.instInhabited` in `Mathlib.Data.Set.Basic` with type `{α : Type u} → Inhabited (Set α)`. This is transitively imported via `GNBA.lean`'s import of `Mathlib.Data.Set.Finite.Basic`. Since OmegaRegular.lean imports GNBA.lean, the Mathlib instance should already be available.

### Recommended Fix

**Option A (preferred): Delete the instance entirely.** If `Set.instInhabited` from Mathlib is already available transitively, this local instance is redundant and should be removed (along with its docstring on line 141). Verify with `lake build Cslib.Logics.LTL.Semantics.OmegaRegular` after deletion.

**Option B (fallback): Make it anonymous.** If removal breaks something (unlikely but possible if there's a universe issue since Mathlib's is for `Type u` and this is for `Type*`), change to:

```lean
instance : Inhabited (Set Atom) := ⟨∅⟩
```

This follows Mathlib convention for instances that are straightforward and whose auto-generated name is sufficient.

## Implementation Plan

### Phase 1: Fix Long Lines in GNBA.lean

1. Line 912: Add `let χ_i` binding before the `if` statement
2. Line 929: Break after `:=` onto next line
3. Line 1023: Break type signature after `:`
4. Line 1352: Break after `:` and beta-reduce the lambda (OR just break)
5. Line 1421: Break after `:` onto next line
6. Line 1427: Break after `:` onto next line
7. Line 1435: Break the `exact absurd` arguments across lines

### Phase 2: Fix Instance in OmegaRegular.lean

1. Delete lines 141-142 (`instInhabitedSetAtom` and its docstring)
2. Run `lake build Cslib.Logics.LTL.Semantics.OmegaRegular` to verify
3. If build fails, fall back to Option B (anonymous instance)

### Phase 3: Verification

1. Run `awk 'length > 100' Cslib/Logics/LTL/Semantics/GNBA.lean` to confirm zero long lines
2. Run `lake build` to verify everything compiles
3. Run `lake exe lint-style` to confirm no remaining style violations

## Risk Assessment

- **Low risk**: All changes are purely cosmetic line breaks or redundant instance removal
- **Line 912 (`let χ_i`)**: Introducing a `let` in a `have` body is semantically neutral since it is definitionally equal
- **Line 1352 beta-reduction**: Safe since `Nat.find` is not used on this existential
- **Instance deletion**: Mathlib's `Set.instInhabited` covers the same type; universe polymorphism in `Type*` vs `Type u` should unify. If not, fallback to anonymous instance is trivial.

## Tactic Survey Results

No proof changes required -- all fixes are formatting-only (line breaks) or dead code removal (redundant instance). No tactic survey needed.
