# Task 212: Simp Lint Error Research

## Executive Summary

The `lake lint` `simpNF` linter reports 25 errors across 6 files in the Bimodal logic
subsystem. All 25 errors share a common root cause: derived connectives (`neg`, `diamond`,
`and`, `or`, `top`, `someFuture`, `somePast`, `allFuture`, `allPast`, `always`) are defined
as `abbrev`s that unfold to primitive constructors (`imp`, `bot`, `box`, `untl`, `snce`),
so simp lemmas for primitive constructors fire on the LHS before the derived lemma can apply.

**Error breakdown**: 23 "LHS already simplifies" + 2 "simp can prove this"

**Recommended fix**: Remove `@[simp]` from all 25 declarations. All downstream usages are
via explicit `rw [lemma_name]`, `simp only [lemma_name]`, or `.mp`/`.mpr` -- none require
the lemma to be in the global simp set.

## Root Cause Analysis

### Why Derived Connective Simp Lemmas Fail

In `Cslib.Logic.Bimodal.Formula` (and similarly in `Modal.Proposition` and
`Temporal.Formula`), derived connectives are `abbrev`s:

```lean
abbrev Formula.neg (φ : Formula Atom) : Formula Atom := .imp φ .bot
abbrev Formula.diamond (φ : Formula Atom) : Formula Atom := .neg (.box (.neg φ))
abbrev Formula.and (φ₁ φ₂ : Formula Atom) : Formula Atom := .imp (.imp φ₁ (.imp φ₂ .bot)) .bot
abbrev Formula.top : Formula Atom := .imp .bot .bot
-- etc.
```

Because `abbrev` unfolds transparently, when the simpNF checker sees a lemma like:

```lean
@[simp] theorem subst_neg : (Formula.neg phi).subst q r = Formula.neg (phi.subst q r)
```

the LHS `(Formula.neg phi).subst q r` is really `(Formula.imp phi Formula.bot).subst q r`,
and the existing `@[simp] theorem subst_imp` fires first, simplifying it to
`(phi.subst q r).imp (Formula.bot.subst q r)`, and then `@[simp] theorem subst_bot`
simplifies `Formula.bot.subst q r` to `Formula.bot`.

The same pattern applies to all 25 errors.

### The Two "Simp Can Prove" Cases

For `int_truth_allPast` and `int_truth_allFuture` in `Separation/Defs.lean`, simp can
close the entire goal by combining `int_truth_neg`, `int_truth_somePast`/`int_truth_someFuture`,
`not_exists`, `not_and`, and `not_not`. These lemmas are "redundant" in the global simp set.

## Complete Error Inventory

### File 1: Embedding/ModalEmbedding.lean (2 errors)

| Line | Declaration | Type | LHS Simplifies Via |
|------|-------------|------|---------------------|
| 58 | `Modal.Proposition.toBimodal_neg` | LHS simplifies | `toBimodal_imp`, `toBimodal_bot` |
| 63 | `Modal.Proposition.toBimodal_diamond` | LHS simplifies | `toBimodal_imp`, `toBimodal_box`, `toBimodal_bot` |

**Downstream usage**: None. These lemma names are never referenced outside their definition.

**Fix**: Remove `@[simp]` from both.

### File 2: Embedding/PropositionalEmbedding.lean (1 error)

| Line | Declaration | Type | LHS Simplifies Via |
|------|-------------|------|---------------------|
| 98 | `PL.Proposition.toBimodal_neg` | LHS simplifies | `toBimodal_imp`, `toBimodal_bot` |

**Downstream usage**: None. The `simp [*]` proofs on lines 107 and 113 work via primitive
constructor simp lemmas plus induction hypotheses.

**Fix**: Remove `@[simp]`.

### File 3: Embedding/TemporalEmbedding.lean (1 error)

| Line | Declaration | Type | LHS Simplifies Via |
|------|-------------|------|---------------------|
| 67 | `Temporal.Formula.toBimodal_neg` | LHS simplifies | `toBimodal_imp`, `toBimodal_bot` |

**Downstream usage**: None.

**Fix**: Remove `@[simp]`.

### File 4: Metalogic/ConservativeExtension/ExtFormula.lean (10 errors)

| Line | Declaration | Type | LHS Simplifies Via |
|------|-------------|------|---------------------|
| 163 | `embedFormula_neg` | LHS simplifies | `embedFormula_imp` |
| 167 | `embedFormula_and` | LHS simplifies | `embedFormula_imp` |
| 171 | `embedFormula_or` | LHS simplifies | `embedFormula_imp` |
| 191 | `embedFormula_diamond` | LHS simplifies | `embedFormula_imp`, `embedFormula_box` |
| 195 | `embedFormula_someFuture` | LHS simplifies | `embedFormula_untl`, `embedFormula_imp` |
| 199 | `embedFormula_somePast` | LHS simplifies | `embedFormula_snce`, `embedFormula_imp` |
| 203 | `embedFormula_allFuture` | LHS simplifies | `embedFormula_imp`, `embedFormula_untl` |
| 207 | `embedFormula_allPast` | LHS simplifies | `embedFormula_imp`, `embedFormula_snce` |
| 211 | `embedFormula_always` | LHS simplifies | `embedFormula_imp`, `embedFormula_snce`, `embedFormula_untl` |

**Downstream usage**: None. These lemma names are never referenced outside their definition file.

**Fix**: Remove `@[simp]` from all 10 declarations (lines 163, 167, 171, 191, 195, 199, 203, 207, 211).

### File 5: Metalogic/Separation/Defs.lean (4 errors)

| Line | Declaration | Type | Simplifies Via |
|------|-------------|------|----------------|
| 68 | `int_truth_allPast` | simp can prove | `int_truth_neg`, `int_truth_somePast`, `not_exists`, `not_and`, `not_not` |
| 80 | `int_truth_allFuture` | simp can prove | `int_truth_neg`, `int_truth_someFuture`, `not_exists`, `not_and`, `not_not` |
| 119 | `int_truth_and` | LHS simplifies | `int_truth_neg` |
| 131 | `int_truth_top` | LHS simplifies | `int_truth_neg` |

**Downstream usage**:
- `int_truth_allPast`: Used in `rw`, `simp only`, `.mp` calls in 5+ files
- `int_truth_allFuture`: Used in `rw`, `simp only`, `.mp` calls in 4+ files
- `int_truth_and`: Used in `rw`, `.mp`/`.mpr` calls in 3+ files
- `int_truth_top`: No downstream usage

All downstream references are explicit (not relying on `@[simp]`).

**Fix**: Remove `@[simp]` from all 4 declarations (lines 68, 80, 119, 131).

### File 6: ProofSystem/Substitution.lean (7 errors)

| Line | Declaration | Type | LHS Simplifies Via |
|------|-------------|------|---------------------|
| 90 | `subst_neg` | LHS simplifies | `subst_imp`, `subst_bot` |
| 95 | `subst_and` | LHS simplifies | `subst_imp`, `subst_bot` |
| 101 | `subst_or` | LHS simplifies | `subst_imp`, `subst_bot` |
| 107 | `subst_diamond` | LHS simplifies | `subst_imp`, `subst_box`, `subst_bot` |
| 114 | `subst_someFuture` | LHS simplifies | `subst_untl`, `subst_imp`, `subst_bot` |
| 121 | `subst_somePast` | LHS simplifies | `subst_snce`, `subst_imp`, `subst_bot` |
| 128 | `subst_allFuture` | LHS simplifies | `subst_imp`, `subst_untl`, `subst_bot` |
| 136 | `subst_allPast` | LHS simplifies | `subst_imp`, `subst_snce`, `subst_bot` |

**Downstream usage**: All 8 lemmas are referenced in `axiomSubst` (lines 252-436 of the
same file) via `simp only [Formula.subst_neg, ...]`. These are explicit `simp only` calls
that work regardless of whether the lemma is in the global `@[simp]` set.

**Fix**: Remove `@[simp]` from all 8 declarations (lines 90, 95, 101, 107, 114, 121, 128, 136).

**Note**: The error count says 7 but I count 8 declarations affected. Let me verify: looking
at the lint output, `subst_allPast` at line 136 is the last one reported. Yes, the lint
output shows errors at lines 90, 95, 101, 107, 114, 121, 128, 136 = 8 errors. However, the
task description says 25 total = 23 LHS + 2 can-prove. Let me recount: 2 + 1 + 1 + 10 + 4 + 8
= 26. Actually, the 10 from ExtFormula.lean should be 9 (not counting `embedFormula_always`
separately if it was combined in the lint output). Let me recount from the lint output directly.

**Recount from lint output**: The lint output shows exactly 25 error lines:
- ModalEmbedding.lean: 2 (lines 58, 63)
- PropositionalEmbedding.lean: 1 (line 98)
- TemporalEmbedding.lean: 1 (line 67)
- ExtFormula.lean: 9 (lines 163, 167, 171, 191, 195, 199, 203, 207, 211)
- Separation/Defs.lean: 4 (lines 68, 80, 119, 131)
- Substitution.lean: 8 (lines 90, 95, 101, 107, 114, 121, 128, 136)

Total: 2 + 1 + 1 + 9 + 4 + 8 = 25. Confirmed.

## Alternative Fix Approaches Considered

### Alternative A: Restate LHS in Normal Form

For each "LHS already simplifies" lemma, we could restate the LHS as the simplified form.
For example, change:

```lean
@[simp] theorem subst_neg : (Formula.neg phi).subst q r = Formula.neg (phi.subst q r)
```

to:

```lean
@[simp] theorem subst_neg : ((phi.imp .bot).subst q r) = (phi.subst q r).imp .bot
```

**Rejected** because:
1. The restated LHS is identical to what `subst_imp` + `subst_bot` already produce, making
   the lemma trivially provable by `rfl` and redundant in the simp set.
2. The RHS with explicit `.imp ... .bot` is less readable than `Formula.neg`.
3. No downstream code depends on these being in the global simp set.

### Alternative B: Use `@[nolint simpNF]`

We could suppress the warnings with `@[simp, nolint simpNF]`.

**Rejected** because:
1. The lint is correct: these lemmas truly cannot fire as simp lemmas since their LHS
   is not in normal form.
2. Using `nolint` would mask a real issue rather than fixing it.
3. CSLib already uses `nolint simpNF` sparingly (only 3 existing instances in the codebase),
   suggesting a preference for proper fixes.

### Alternative C: Change `abbrev` to `def` for Derived Connectives

Making derived connectives `def` instead of `abbrev` would prevent transparent unfolding,
allowing derived simp lemmas to fire.

**Rejected** because:
1. This would be a massive breaking change affecting the entire codebase.
2. `abbrev` is the correct choice for definitional abbreviations.
3. The current approach where primitive constructor lemmas suffice is the standard Lean/Mathlib
   pattern.

## Recommended Fix: Remove `@[simp]`

Remove `@[simp]` from all 25 declarations. This is the correct Lean/Mathlib-idiomatic fix:

1. **Primitive constructor simp lemmas are sufficient**: `subst_imp`, `subst_bot`,
   `subst_box`, etc. already handle all cases because derived connectives unfold.
2. **Explicit references are unaffected**: All downstream code uses `rw [lemma]`,
   `simp only [lemma]`, or `.mp`/`.mpr` -- none depend on the global simp set.
3. **The lemmas remain available**: Removing `@[simp]` does not remove the lemma;
   it just removes it from the default `simp` set.
4. **No breakage expected**: Since the linter confirms the LHS already simplifies via
   other simp lemmas, bare `simp` calls already work without these lemmas.

### Implementation Checklist

For each file, the fix is simply changing `@[simp]` to nothing (or to just the docstring
attribute). The lemma statement and proof remain unchanged.

| File | Lines to Edit | Change |
|------|---------------|--------|
| `Cslib/Logics/Bimodal/Embedding/ModalEmbedding.lean` | 59, 64 | Remove `@[simp]` |
| `Cslib/Logics/Bimodal/Embedding/PropositionalEmbedding.lean` | 99 | Remove `@[simp]` |
| `Cslib/Logics/Bimodal/Embedding/TemporalEmbedding.lean` | 68 | Remove `@[simp]` |
| `Cslib/Logics/Bimodal/Metalogic/ConservativeExtension/ExtFormula.lean` | 163, 167, 171, 191, 195, 199, 203, 207, 211 | Remove `@[simp]` |
| `Cslib/Logics/Bimodal/Metalogic/Separation/Defs.lean` | 68, 80, 119, 131 | Remove `@[simp]` |
| `Cslib/Logics/Bimodal/ProofSystem/Substitution.lean` | 90, 95, 101, 107, 114, 121, 128, 136 | Remove `@[simp]` |

### Verification Plan

1. Apply all 25 `@[simp]` removals
2. Run `lake build` to verify no compilation errors
3. Run `lake lint` to verify the 25 simpNF errors are gone
4. Run `lake test` to verify no test regressions

### Risk Assessment

**Risk: LOW**. The change is purely attribute removal. No lemma statements or proofs change.
No downstream code depends on these being in the global simp set (verified by grep).

The only theoretical risk is a bare `simp` call somewhere that previously benefited from
one of these 25 lemmas. However, the linter explicitly confirms that the LHS of each lemma
already simplifies via other simp lemmas, so any bare `simp` call that would have used
these lemmas already succeeds without them.
