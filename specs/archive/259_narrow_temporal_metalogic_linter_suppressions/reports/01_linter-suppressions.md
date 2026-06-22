# Research Report: Narrow Linter Suppressions in Temporal/Metalogic/

Task 259 | Session: sess_1781994910_0cdf2d_259

## Overview

Four files in `Cslib/Logics/Temporal/Metalogic/` contain 13 file-wide `set_option linter.*`
suppressions. This report identifies which declarations trigger each warning and recommends
whether each suppression can be (a) removed by fixing the underlying issue, (b) narrowed
to declaration-level scope, or (c) must remain file-wide.

## Suppression Inventory

| File | Suppression | Line | Status |
|------|-------------|------|--------|
| CompletenessHelpers.lean | `linter.style.setOption` | 28 | Removable (meta) |
| CompletenessHelpers.lean | `linter.unusedSimpArgs` | 29 | Narrow to 4 decls |
| CompletenessHelpers.lean | `linter.flexible` | 30 | Narrow to 2 decls |
| DenseCompleteness.lean | `linter.unusedSectionVars` | 32 | Fixable by reordering |
| DenseCompleteness.lean | `linter.unusedSimpArgs` | 33 | Narrow to 2 decls |
| DenseCompleteness.lean | `linter.style.setOption` | 34 | Removable (meta) |
| DenseCompleteness.lean | `linter.dupNamespace` | 35 | Remove entirely |
| GeneralizedNecessitation.lean | `linter.unusedSimpArgs` | 23 | Narrow to 2 decls |
| GeneralizedNecessitation.lean | `linter.style.setOption` | 24 | Removable (meta) |
| GeneralizedNecessitation.lean | `linter.flexible` | 25 | Narrow to 1 decl |
| GeneralizedNecessitation.lean | `linter.style.emptyLine` | 26 | Structural (section) |
| TemporalContent.lean | `linter.style.emptyLine` | 22 | Remove entirely |
| TemporalContent.lean | `linter.style.longLine` | 23 | Fix 6 lines, then remove |

**Total**: 13 suppressions -> 4 removable, 3 fixable, 4 narrowable, 2 structural

---

## File-by-File Analysis

### 1. CompletenessHelpers.lean (3 suppressions)

**Path**: `Cslib/Logics/Temporal/Metalogic/CompletenessHelpers.lean`

#### 1a. `linter.style.setOption` (line 28) -- REMOVE

Meta-suppression that exists only to silence warnings about the other `set_option` lines.
Once all other `set_option` lines (including `maxHeartbeats 3200000` on line 31) are scoped
with `set_option ... in`, this line becomes unnecessary and should be deleted.

**Dependency**: Requires `maxHeartbeats` to also be scoped to declaration-level.

#### 1b. `linter.unusedSimpArgs` (line 29) -- NARROW to 4 declarations

**Affected declarations**:
- `deriveDne` (lines 80-96): `simp [List.mem_cons, ctx2]` at lines 88-89. The `ctx2` is a
  `let` binding; it may be delta-reduced by simp automatically making it an unused explicit arg.
- `deriveHNec` (lines 98-110): `simp only [Formula.allFuture, Formula.allPast,
  Formula.someFuture, Formula.somePast, Formula.neg, Formula.top, Formula.swapTemporal]` at
  line 107. Some unfolding lemmas (e.g., `Formula.someFuture`, `Formula.somePast`) may be
  redundant for normalizing `swap(G(swap(phi))) = H(phi)`.
- `deriveAndTopIntro` (lines 113-126): `simp [List.mem_cons, ctx]` at lines 120, 124.
  Same pattern as `deriveDne`.
- `mcs_dne` (lines 129-144): `simp [List.mem_cons] at hx` at line 135.

**Implementation**: Add `set_option linter.unusedSimpArgs false in` before each of these 4
declarations. Better yet, try removing unused simp arguments (test with `simp?` to find
minimal sets).

#### 1c. `linter.flexible` (line 30) -- NARROW to 2 declarations

**Affected declarations**:
- `deriveHNec` (lines 98-110): `simp only [...]` at line 107 followed by `rw [...]` at
  line 109. Classic flexible-then-rigid pattern.
- `mcs_dne` (lines 129-144): `simp [...] at hx; exact hx \triangleright h` at line 135.
  `simp` modifies `hx` (flexible), then `\triangleright` rewrites rigidly.

**Implementation**: Add `set_option linter.flexible false in` before `deriveHNec` and
`mcs_dne`. Alternatively, refactor to use `simp only` that includes the rewrite lemma,
avoiding the flexible-then-rigid chain.

#### 1d. `maxHeartbeats 3200000` (line 31) -- NOT a linter but affects 1a

This is not a linter suppression but its file-wide scope triggers `style.setOption`.
Must be scoped to specific declarations to enable removing `style.setOption`.

**Likely needs elevated heartbeats** (8 of 22 declarations): `deriveDne`, `deriveHNec`,
`deriveAndTopIntro`, `mcs_dne`, `mcs_ff_imp_f`, `mcs_pp_imp_p`, `mcs_g_trans`, `mcs_h_trans`.

**Likely fine with defaults** (14 of 22): All other declarations (simple MCS properties,
canonical model definitions, truth lemma directions, existence witnesses).

---

### 2. DenseCompleteness.lean (4 suppressions)

**Path**: `Cslib/Logics/Temporal/Metalogic/DenseCompleteness.lean`

#### 2a. `linter.unusedSectionVars` (line 32) -- FIX by reordering

**Root cause**: `neg_consistent_of_not_derivable_dense` (line 217) is within scope of
`variable [Denumerable (Formula Atom)]` (line 69) but does not use `Denumerable`. Its proof
only constructs derivation trees via axioms, modus ponens, and deduction theorem -- pure
syntactic manipulation that doesn't need `Denumerable`.

**Fix**: Move `neg_consistent_of_not_derivable_dense` ABOVE line 69 (before the `Denumerable`
variable declaration), placing it between the "Dense Axiom Membership" section and the
"Propagation" section. Then it won't pick up the unused constraint.

**Alternative**: Add `set_option linter.unusedSectionVars false in` before just that theorem,
or add `omit [Denumerable (Formula Atom)]` before it and `recall [Denumerable (Formula Atom)]`
after it.

#### 2b. `linter.unusedSimpArgs` (line 33) -- NARROW to 2 declarations

**Affected declarations**:
- `dense_indicator_in_all_limit_points` (line 85): `simp only [Formula.allFuture,
  Formula.allPast, Formula.somePast, Formula.neg, Formula.top, Formula.swapTemporal,
  Formula.swapTemporal_involution]` at lines 144-145. Some of these unfolding lemmas may
  be redundant.
- `neg_consistent_of_not_derivable_dense` (line 217): `simp only [Set.mem_singleton_iff]`
  at line 225.

**Implementation**: Add `set_option linter.unusedSimpArgs false in` before these 2 declarations.
Better yet, use `simp?` to find the minimal lemma sets.

#### 2c. `linter.style.setOption` (line 34) -- REMOVE

Meta-suppression. Eliminated once all other `set_option` lines use `in` form.

#### 2d. `linter.dupNamespace` (line 35) -- REMOVE ENTIRELY

**Analysis**: All declarations in this file have FQNs like
`Cslib.Logic.Temporal.dense_indicator_in_dense_mcs` -- no repeated namespace segments.
The `dupNamespace` suppression was likely cargo-culted from files like `MCS.lean` and
`DerivationTree.lean`, which genuinely define `Temporal.`-prefixed declarations (e.g.,
`Temporal.SetMaximalConsistent`) inside namespace `Cslib.Logic.Temporal`, creating
`Cslib.Logic.Temporal.Temporal.SetMaximalConsistent`.

No declaration in DenseCompleteness.lean uses the `Temporal.` prefix in its name. This
suppression can be removed without any other changes.

---

### 3. GeneralizedNecessitation.lean (4 suppressions)

**Path**: `Cslib/Logics/Temporal/Metalogic/GeneralizedNecessitation.lean`

#### 3a. `linter.unusedSimpArgs` (line 23) -- NARROW to 2 declarations

**Affected declarations**:
- `pastNecessitation` (lines 77-88): `simp only [Formula.swapTemporal_allFuture,
  Formula.swapTemporal, Formula.swapTemporal_involution]` at lines 86-87. One or more of
  these three lemmas may be unused.
- `pastKDist` (lines 112-124): Same `simp only [...]` at lines 122-123.

**Implementation**: Add `set_option linter.unusedSimpArgs false in` before `pastNecessitation`
and `pastKDist`. Better yet, use `simp?` to find the minimal set.

#### 3b. `linter.style.setOption` (line 24) -- REMOVE

Meta-suppression. Eliminated once all other `set_option` lines use `in` form.

#### 3c. `linter.flexible` (line 25) -- NARROW to 1 declaration

**Affected declaration**:
- `reverseDeduction` (lines 48-56): `by intro x hx; simp; right; exact hx` at line 53.
  Bare `simp` is flexible, followed by rigid `right; exact hx`.

**Implementation**: Add `set_option linter.flexible false in` before `reverseDeduction`.
Alternatively, replace bare `simp` with `simp only [List.mem_cons]` or the specific lemma
needed for the membership goal.

#### 3d. `linter.style.emptyLine` (line 26) -- STRUCTURAL, document why

**Root cause**: The `@[expose] public section` on line 29 wraps all declarations in a single
command. The `emptyLine` linter fires on `\n\n` patterns inside commands. Blank lines between
declarations inside this section (standard formatting) trigger the linter.

This is a structural consequence of the `@[expose] public section` pattern used by ALL
temporal metalogic files. The blank lines between declarations are standard Lean formatting
and removing them would significantly hurt readability.

**Options**:
1. Keep file-wide suppression with a documenting comment (recommended)
2. Replace blank lines with `--` comment lines (ugly, not recommended)
3. Remove the section wrapper and use per-declaration `@[expose] public` (large refactor)

**Recommendation**: Keep as file-wide suppression with a comment:
```lean
-- Structural: blank lines between declarations inside @[expose] public section
set_option linter.style.emptyLine false
```

If the implementation plan includes narrowing this, note that `set_option ... in` cannot
help here because the issue is the blank lines between declarations, not within any single
declaration.

---

### 4. TemporalContent.lean (2 suppressions)

**Path**: `Cslib/Logics/Temporal/Metalogic/TemporalContent.lean`

#### 4a. `linter.style.emptyLine` (line 22) -- REMOVE ENTIRELY

**Analysis**: No consecutive empty lines exist anywhere in this file. No whitespace-only lines
were found. The file ends cleanly after `end Cslib.Logic.Temporal.Metalogic`. This suppression
was added preemptively or cargo-culted from another file.

**Wait**: The file also uses `@[expose] public section` (line 25). If blank lines between
declarations inside the section trigger `emptyLine`, this suppression IS needed for the same
structural reason as GeneralizedNecessitation.lean. Before removing, verify by actually
deleting the line and building.

**Recommendation**: Try removing and building. If it triggers warnings, keep with documenting
comment.

#### 4b. `linter.style.longLine` (line 23) -- FIX 6 lines, then REMOVE

**6 long lines** (all `have` type annotations with long `DerivationTree` types):

| Line | Chars | Declaration | Fix |
|------|-------|-------------|-----|
| 113 | 121 | `f_content_iff_not_neg_in_g_content` | Break after `[]` |
| 127 | 101 | `f_content_iff_not_neg_in_g_content` | Break after `:` |
| 146 | 121 | `f_content_iff_not_neg_in_g_content` | Break after `[]` |
| 184 | 117 | `p_content_iff_not_neg_in_h_content` | Break after `[]` |
| 194 | 101 | `p_content_iff_not_neg_in_h_content` | Break after `:` |
| 222 | 117 | `p_content_iff_not_neg_in_h_content` | Break after `[]` |

All can be fixed by line-breaking. Example fix for line 113:
```lean
-- Before (121 chars):
    have h_sf_impl : DerivationTree FrameClass.Base [] ((Formula.someFuture phi).imp (Formula.someFuture phi.neg.neg)) :=

-- After (two lines, both <= 89 chars):
    have h_sf_impl : DerivationTree FrameClass.Base []
        ((Formula.someFuture phi).imp (Formula.someFuture phi.neg.neg)) :=
```

**Implementation**: Fix all 6 lines, then remove the `style.longLine` suppression entirely.

---

## Implementation Plan Recommendation

### Phase 1: Easy removals (zero risk)

1. **TemporalContent.lean**: Fix 6 long lines (line breaks), remove `style.longLine`
2. **DenseCompleteness.lean**: Remove `dupNamespace` suppression (no declarations need it)
3. **TemporalContent.lean**: Try removing `style.emptyLine`, build to verify

### Phase 2: Narrowing to declaration scope

4. **CompletenessHelpers.lean**: Scope `unusedSimpArgs` to 4 declarations with `in`
5. **CompletenessHelpers.lean**: Scope `flexible` to 2 declarations with `in`
6. **CompletenessHelpers.lean**: Scope `maxHeartbeats` to ~8 declarations with `in`
7. **CompletenessHelpers.lean**: Remove `style.setOption` (now unnecessary)
8. **DenseCompleteness.lean**: Scope `unusedSimpArgs` to 2 declarations with `in`
9. **DenseCompleteness.lean**: Scope `maxHeartbeats` to heavy declarations with `in`
10. **DenseCompleteness.lean**: Remove `style.setOption` (now unnecessary)
11. **GeneralizedNecessitation.lean**: Scope `unusedSimpArgs` to 2 declarations with `in`
12. **GeneralizedNecessitation.lean**: Scope `flexible` to 1 declaration with `in`
13. **GeneralizedNecessitation.lean**: Scope `maxHeartbeats` to heavy declarations with `in`
14. **GeneralizedNecessitation.lean**: Remove `style.setOption` (now unnecessary)

### Phase 3: Structural fixes

15. **DenseCompleteness.lean**: Move `neg_consistent_of_not_derivable_dense` above
    `variable [Denumerable ...]` to fix `unusedSectionVars`, then remove suppression

### Phase 4: Document unavoidable suppressions

16. **GeneralizedNecessitation.lean**: Keep `style.emptyLine` with documenting comment
    (structural consequence of `@[expose] public section` pattern)
17. **TemporalContent.lean**: If `style.emptyLine` removal fails, keep with comment

### Phase 5: Build verification

18. Run `lake build Cslib.Logics.Temporal.Metalogic.CompletenessHelpers` after changes
19. Run `lake build Cslib.Logics.Temporal.Metalogic.DenseCompleteness` after changes
20. Run `lake build Cslib.Logics.Temporal.Metalogic.GeneralizedNecessitation` after changes
21. Run `lake build Cslib.Logics.Temporal.Metalogic.TemporalContent` after changes
22. Run `lake build` for full project verification

## Expected Outcome

| Metric | Before | After |
|--------|--------|-------|
| File-wide suppressions | 13 | 1-2 (emptyLine only) |
| Declaration-scoped suppressions | 0 | ~11-15 |
| Completely removed suppressions | 0 | 4-5 |
| Fixed underlying issues | 0 | 7-8 (long lines, reordering) |

## Risk Assessment

- **Low risk**: Removing `dupNamespace` from DenseCompleteness, fixing long lines in
  TemporalContent, removing meta-`style.setOption` after scoping other options
- **Medium risk**: Scoping `maxHeartbeats` to individual declarations (might miss a heavy
  declaration, but build will immediately catch this)
- **Low risk**: Moving `neg_consistent_of_not_derivable_dense` above the variable declaration
  (pure reordering, no semantic change)
- **Zero risk**: Narrowing `unusedSimpArgs` and `flexible` to declaration level (same
  suppression, just scoped)

## Key Insight: `@[expose] public section` and emptyLine

The `@[expose] public section` pattern is used by ALL temporal metalogic files (20+ files).
This pattern makes `linter.style.emptyLine` structurally unavoidable for any file with blank
lines between declarations. If the project wants to eliminate this suppression entirely, it
would require either:
1. Replacing `@[expose] public section` with per-declaration annotations across all files
2. Changing Lean formatting style to remove blank lines between declarations (unreadable)
3. Requesting an upstream linter change to exempt `section` commands

For now, documenting the structural necessity is the pragmatic approach.
