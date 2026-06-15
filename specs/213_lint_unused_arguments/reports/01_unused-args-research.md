# Task 213: Research Report -- Unused Hypothesis Lint Errors

## Summary

Running `lake build` reveals **28 "does not use the following hypothesis in its type"** warnings
across 3 files in `Cslib/Logics/Bimodal/Metalogic/Separation/`. All warnings involve typeclass
instances (`[DecidableEq Atom]` or `[DecidablePred pred]`) that appear as declaration parameters
but are not referenced in the declaration's return type. The instances ARE used in proof bodies but
should be moved out of the type signature.

There are **zero** warnings in Temporal files -- all 28 are in Bimodal Separation files.

## Affected Files and Declarations

### File 1: `Cslib/Logics/Bimodal/Metalogic/Separation/FormulaOps.lean`

**1 warning** -- explicit signature parameter.

| Line | Declaration | Unused Instance | Used In Body? |
|------|------------|-----------------|---------------|
| 183 | `exists_n_fresh_atoms` | `[DecidableEq Atom]` | Yes (`List.mem_toFinset`) |

**Context**: The theorem is NOT inside a `variable [DecidableEq Atom]` section. It has the
instance explicitly in its own signature. The callers (lines 225, 231, 242, 248) are all inside
`section FreshnessOps` which has `variable [DecidableEq Atom]`, so they would auto-synthesize
the instance even if it were removed from the theorem's type.

### File 2: `Cslib/Logics/Bimodal/Metalogic/Separation/IntHelpers.lean`

**2 warnings** -- explicit signature parameters.

| Line | Declaration | Unused Instance | Used In Body? |
|------|------------|-----------------|---------------|
| 53 | `Int.exists_least_above` | `[DecidablePred pred]` | Yes (`inferInstanceAs` at line 65) |
| 80 | `Int.exists_greatest_below` | `[DecidablePred pred]` | Yes (`inferInstanceAs` at line 90) |

**Context**: These are standalone theorems (not in a section with the variable). The instance
is used to construct `Nat.find` via `inferInstanceAs`. Non-decidable classical versions
(`exists_least_above'` and `exists_greatest_below'` at lines 109 and 119) already exist and
are the versions most callers actually use.

**Callers of decidable versions**:
- `DedekindZ/QLemma.lean:149,322` -- calls `Int.exists_least_above` with explicit `haveI : DecidablePred ... := Classical.decPred _`
- `DedekindZ/QLemma.lean:377` -- calls `Int.exists_greatest_below` with same pattern
- `DedekindZ/Cases.lean:1377` -- calls `Int.exists_greatest_below` with same pattern

All callers manually create `DecidablePred` via `Classical.decPred` before calling.

### File 3: `Cslib/Logics/Bimodal/Metalogic/Separation/Hierarchy/HierarchyDefs.lean`

**25 warnings** -- all from `section DecEq` (lines 164-987) which declares `variable [DecidableEq Atom]`.

The section contains both theorems that need `DecidableEq` (via `abstractUntl`/`abstractSnce`
which use `if psi1 = x` equality checks) and theorems that do NOT need it. The affected
theorems fall into two contiguous blocks:

#### Block A: Junction-depth theorems (lines 328-583) -- 12 warnings

| Line | Declaration |
|------|------------|
| 328 | `count_U_zero_iff_U_free` |
| 532 | `junction_depth_bounds` |
| 552 | `junction_depth_le_jdU` |
| 556 | `junction_depth_le_jdS` |
| 560 | `jd_imp_le_left` |
| 563 | `jd_imp_le_right` |
| 566 | `jd_box_le` |
| 569 | `jd_untl_le_left` |
| 573 | `jd_untl_le_right` |
| 577 | `jd_snce_le_left` |
| 581 | `jd_snce_le_right` |

All of these involve purely structural induction on `Formula Atom` and never use equality
testing. They are pure `Nat` monotonicity lemmas.

Note: `count_U_zero_iff_U_free` at line 328 is separated from the main junction-depth block
(lines 532-583) by the `abstract_untl_count_le` and `abstract_untl_count_zero_of_single`
theorems (lines 344-373) which DO use `DecidableEq`.

#### Block B: Separability combinators and replaceUntlArgs (lines 778-985) -- 13 warnings

| Line | Declaration |
|------|------------|
| 778 | `separable_with_type_imp_separable` |
| 784 | `is_separable_with_U_type_of_equiv` |
| 791 | `imp_separable_with_type` |
| 802 | `u_free_separable_with_type` |
| 811 | `untl_s_free_separable_with_type` |
| 820 | `or_separable_with_U_type` |
| 837 | `and_separable_with_U_type` |
| 850 | `neg_separable_with_U_type` |
| 872 | `replace_untl_args_has_single_U_type` |
| 883 | `replace_untl_args_u_free_eq` |
| 900 | `replace_untl_args_preserves_S_free` |
| 915 | `replace_untl_args_preserves_separated` |
| 936 | `replace_untl_args_equiv` |
| 973 | `is_separable_with_U_type_replace_args` |

Note: `replace_untl_args_preserves_separated` (line 915) calls `replace_untl_args_u_free_eq`
which also does not need `DecidableEq`. The entire block from `isSeparableWithUType` definition
(line 775) through the end of the section uses only `intEquiv`, `hasSingleUType`,
`isSyntacticallySeparated`, `isSFree`, and structural induction -- none requiring `DecidableEq`.

**Callers**: All callers of these theorems are in `HierarchyCaseSep.lean` and
`HierarchyCompletion.lean`, both of which have `variable [DecidableEq Atom]` in their own
section scope. Removing `[DecidableEq Atom]` from these theorems' types is safe.

## Fix Categories

### Category A: Remove explicit `[Instance]` from signature, add to proof body (3 declarations)

**Applies to**: FormulaOps.lean and IntHelpers.lean declarations.

These theorems have typeclass instances explicitly in their signature that the return type
doesn't depend on. The fix is to remove the instance from the binder and introduce it in
the proof body via `haveI`.

**FormulaOps `exists_n_fresh_atoms`**:
```lean
-- BEFORE:
theorem exists_n_fresh_atoms [DecidableEq Atom] [Infinite Atom]
    (fs : Finset Atom) (n : Nat) : ...

-- AFTER:
theorem exists_n_fresh_atoms [Infinite Atom]
    (fs : Finset Atom) (n : Nat) : ... := by
  haveI : DecidableEq Atom := Classical.decEq Atom
  ...
```

**IntHelpers `Int.exists_least_above` and `Int.exists_greatest_below`**:
```lean
-- BEFORE:
theorem Int.exists_least_above
    {pred : Int → Prop} {t : Int}
    (hex : ∃ n, t < n ∧ pred n) [DecidablePred pred] : ...

-- AFTER:
theorem Int.exists_least_above
    {pred : Int → Prop} {t : Int}
    (hex : ∃ n, t < n ∧ pred n) : ... := by
  haveI : DecidablePred pred := Classical.decPred pred
  ...
```

**Impact on callers**:
- `exists_n_fresh_atoms`: All callers are in FreshnessOps section with `[DecidableEq Atom]`.
  They auto-synthesize and will not break. No changes needed.
- `Int.exists_least_above` / `Int.exists_greatest_below`: 4 call sites, all of which manually
  create `haveI : DecidablePred ... := Classical.decPred _` before calling. These `haveI`
  lines become unnecessary but harmless (they'll produce no lint warning since they're
  hypotheses, not section variables). Optionally clean them up for tidiness.
- `Int.exists_least_above'` / `Int.exists_greatest_below'`: The primed versions call the
  unprimed versions and provide `haveI : DecidablePred pred := Classical.decPred pred`.
  After the fix, the primed versions become exact duplicates. They could be:
  (a) kept as-is (their `haveI` becomes redundant but harmless), or
  (b) converted to simple `alias` declarations, or
  (c) removed if no callers outside the file use them (but they DO have callers in
      NegationEquiv.lean).

**Recommended approach for IntHelpers**: Make the unprimed versions classical (remove
`[DecidablePred pred]`, add `haveI` using `Classical.decPred`). Then convert the primed
versions to aliases:
```lean
theorem Int.exists_least_above' := @Int.exists_least_above
theorem Int.exists_greatest_below' := @Int.exists_greatest_below
```

### Category B: Use `omit [DecidableEq Atom] in` for section-inherited instances (25 declarations)

**Applies to**: All 25 warnings in HierarchyDefs.lean.

These theorems are inside `section DecEq` which has `variable [DecidableEq Atom]`. The
instance is auto-included by Lean but not used in these theorems' types.

**Approach 1 (recommended): Scoped subsections with batch `omit`**

Use named subsections with batch `omit` for the two contiguous blocks. This avoids
25 individual `omit ... in` annotations.

```lean
-- Block A: Before line 328
section NoDecEqJD  -- or any descriptive name
omit [DecidableEq Atom]

theorem count_U_zero_iff_U_free ...
-- ... junction depth theorems ...
theorem jd_snce_le_right ...

end NoDecEqJD

-- Block B: Before line 775
section NoDecEqSep
omit [DecidableEq Atom]

def isSeparableWithUType ...
theorem separable_with_type_imp_separable ...
-- ... all separability theorems ...
theorem is_separable_with_U_type_replace_args ...

end NoDecEqSep
```

**Approach 2 (alternative): Individual `omit ... in` per declaration**

```lean
omit [DecidableEq Atom] in
theorem count_U_zero_iff_U_free ...
```

This is the pattern already used elsewhere in CSLib (e.g., `WorldHistory.lean`,
`NestingDepth.lean`, `ParametricCanonical.lean`, `Propositional/Defs.lean`).

**Approach 3 (alternative): Close and reopen section**

End `section DecEq` before line 328, then reopen after line 583. Close again before
line 775, reopen after line 985. This is disruptive and changes the section structure
unnecessarily.

**Recommendation**: Approach 1 for the large contiguous blocks (junction depth block,
separability block). For the isolated `count_U_zero_iff_U_free` at line 328, which is
separated from the junction depth block by two DecidableEq-dependent theorems, use
individual `omit [DecidableEq Atom] in`.

Wait -- on re-examination, `count_U_zero_iff_U_free` (line 328) is followed by
`abstract_untl_count_le` (line 344) which DOES need `DecidableEq`, so it can't be in the
same batch omit block as the junction depth theorems at 532+. Therefore:

- Line 328: `omit [DecidableEq Atom] in` for `count_U_zero_iff_U_free` alone
- Lines 532-583: `section` + `omit` for the junction depth block (10 theorems)
- Lines 775-985: `section` + `omit` for the separability block (14 declarations including `def isSeparableWithUType` and `def replaceUntlArgs`)

Actually, `def isSeparableWithUType` at line 775 and `def replaceUntlArgs` at line 863 are
definitions, not theorems. Let me verify they don't have warnings.

Looking at the warning list, the definitions `isSeparableWithUType` (line 775) and
`replaceUntlArgs` (line 863) are NOT in the warnings -- only the theorems about them are.
But putting the defs inside the `omit` block is still correct since they also don't use
`DecidableEq`.

**Impact on callers**: All callers of these theorems have `[DecidableEq Atom]` in their
own section scope. The theorems' types will simply no longer require `[DecidableEq Atom]`,
which is strictly less restrictive. No caller changes needed.

## Complete Fix Plan Summary

| File | Declarations | Fix | Complexity |
|------|-------------|-----|-----------|
| FormulaOps.lean | 1 (`exists_n_fresh_atoms`) | Remove `[DecidableEq Atom]` from sig, add `haveI` in body | Low |
| IntHelpers.lean | 2 (`exists_least_above`, `exists_greatest_below`) | Remove `[DecidablePred pred]` from sig, add `haveI` in body; optionally alias primed versions | Low |
| HierarchyDefs.lean | 1 (`count_U_zero_iff_U_free`) | `omit [DecidableEq Atom] in` | Trivial |
| HierarchyDefs.lean | 10 (junction depth block, lines 532-583) | Wrap in subsection with `omit [DecidableEq Atom]` | Low |
| HierarchyDefs.lean | 14 (separability block, lines 775-985) | Wrap in subsection with `omit [DecidableEq Atom]` | Low |
| **Total** | **28** | | **Low** |

## Risk Assessment

**Risk: LOW**

- All fixes are purely cosmetic/type-level -- no proof logic changes
- `omit` is already used in the codebase (11 existing uses across 5 files)
- Removing unused instances from types is strictly less restrictive
- All callers have the instances available in their own scopes
- The existing `linter.unusedSectionVars false` in HierarchyDefs.lean should be checked:
  it may no longer be needed after the `omit` fixes

## Build Verification

After implementation, verify with:
```bash
lake build 2>&1 | grep "does not use the following hypothesis"
```
Expected: 0 warnings.

Also run full CI:
```bash
lake build && lake exe checkInitImports && lake exe lint-style && lake test
```

## Other Warnings Noted (Out of Scope)

During analysis, other warning categories were observed in the Bimodal Separation files:
- ~40 "This simp argument is unused" warnings in DenseValidity.lean
- ~12 "Try this: intro" suggestions in DenseValidity.lean and Soundness.lean
- ~36 "`show` tactic" and "tactic does nothing" warnings in HierarchyCaseSep.lean
- ~7 "maxHeartbeat limit" comment warnings in HierarchyCaseSep.lean
- 2 "Variable name not explicitly referenced" in HierarchyInduction.lean
- 1 "open Classical" warning in SeparationThm.lean
- Multiple `sorry` warnings (separate task scope)

These are separate lint categories and not part of the unused hypothesis task.
