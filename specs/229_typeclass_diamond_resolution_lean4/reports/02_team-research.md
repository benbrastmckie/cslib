# Research Report: Task #229 (Round 2)

**Task**: Compare `class abbrev` vs true diamond for CSLib connective hierarchy
**Date**: 2026-06-17
**Mode**: Team Research (4 teammates)

## Summary

`class abbrev` is empirically confirmed to work for CSLib's hierarchy. The instance chaining solves the `TemporalConnectives` synthesis gap — but only when `FutureTemporalConnectives` and `TemporalConnectives` are also `class abbrev` (not just `BimodalConnectives`). The true diamond also works but `set_option structureDiamondWarning false` has zero Mathlib precedent and would face reviewer pushback. `class abbrev` for `Type*`-valued bundles also has no Mathlib precedent (only 3 Prop-valued uses), but is a less contentious divergence.

## Key Findings

### 1. `class abbrev` Instance Chaining Works (Confirmed Empirically)

All 9 synthesis tests pass when the hierarchy uses `class abbrev`:

```lean
example [BimodalConnectives F] : TemporalConnectives F := inferInstance      -- passes
example [BimodalConnectives F] : ModalConnectives F := inferInstance          -- passes
example [BimodalConnectives F] : FutureTemporalConnectives F := inferInstance -- passes
```

**Critical caveat**: Changing only `BimodalConnectives` to `class abbrev` is insufficient. The minimum migration is:
- `FutureTemporalConnectives` → `class abbrev`
- `TemporalConnectives` → `class abbrev`
- `BimodalConnectives` → `class abbrev`

`PropositionalConnectives` and `ModalConnectives` can remain as `class extends`.

### 2. True Diamond: Warning Suppression Has Zero Mathlib Precedent

`set_option structureDiamondWarning false` appears **0 times** in all of Mathlib and all lake packages. This would be the first such suppression in the Lean ecosystem. Reviewers would likely reject it.

The diamond itself is definitionally safe (confirmed by `rfl` in Round 1), but the suppression optics are bad.

### 3. `class abbrev` Limitations (Verified)

| Limitation | Impact on CSLib |
|---|---|
| Cannot add new methods/fields | None today — all bundles are pure operator collections |
| `@[reducible]` cannot be applied | None — CSLib doesn't use this on connective classes |
| Only 3 Mathlib uses (all Prop-valued) | PR must justify the divergence |
| Requires temporal classes to also change | 3 classes must migrate, not just 1 |

**The escape hatch works**: `class extends` can extend a `class abbrev` and add new fields:
```lean
class RichBundle (F : Type*) extends BimodalConnectives F where
  extraMethod : F → Prop
```
So if a future bundle needs methods, it uses `class extends` on top of a `class abbrev` base.

### 4. Scaling Comparison

With N logic bundles sharing `PropositionalConnectives`:

| Metric | Flat + Bridges | True Diamond | `class abbrev` |
|---|---|---|---|
| Bridge instances for N=5 | ~12 (realistic) | 0 | 0 |
| Warning suppressions | 0 | ~8 per file | 0 |
| Lines changed to add logic K | K-1 bridges | 1 suppression | 0 |
| Reviewer risk | None (standard) | High (no precedent) | Medium (uncommon) |

### 5. Concrete Instance Syntax Preserved

Both syntaxes work with `class abbrev`:
```lean
-- Flat fields (current CSLib style):
instance : BimodalConnectives (Formula Atom) where
  bot := .bot; imp := .imp; box := .box; untl := .untl; snce := .snce

-- Component-grouped fields:
instance : BimodalConnectives (Formula Atom) where
  toModalConnectives := { bot := .bot, imp := .imp, box := .box }
  toHasUntil := { untl := .untl }
  toHasSince := { snce := .snce }
```

### 6. `simp`, Notation, and Definitional Equality All Preserved

- `@[simp]` lemmas stated with `[ModalConnectives F]` fire correctly in `[BimodalConnectives F]` contexts
- Notation like `□ φ` (defined on `HasBox.box`) works identically
- Cross-path projections are definitionally equal (proved by `rfl`)

## Conflicts Resolved

**Conflict: Does `class abbrev` fix the gap or not?**
- Teammate A: Yes, all synthesis works (tested with all-`class abbrev` hierarchy)
- Teammate C: No, same gap persists (tested with only `BimodalConnectives` as `class abbrev`)

**Resolution**: Both are correct. The gap persists when only `BimodalConnectives` changes. It is resolved when `FutureTemporalConnectives` and `TemporalConnectives` also become `class abbrev`. The auto-constructor instance registered by `class abbrev` is what enables synthesis chaining — if the intermediate classes lack it, the chain breaks.

## Recommendations

### Recommended path: `class abbrev` (hybrid)

1. Change 3 classes to `class abbrev`:
   - `FutureTemporalConnectives`
   - `TemporalConnectives`
   - `BimodalConnectives`

2. Keep 2 classes as `class extends`:
   - `PropositionalConnectives`
   - `ModalConnectives`

3. Keep all 7 atomic classes unchanged:
   - `HasBot`, `HasImp`, `HasBox`, `HasUntil`, `HasSince`, `HasNext`, `HasAnd`, `HasOr`

4. PR description must justify the `class abbrev` choice with:
   - Instance chaining benefit (no bridge instances needed)
   - Scaling benefit for future logics
   - Escape hatch for bundles needing methods

### Fallback path: Keep `class extends` + add bridge instances

If reviewers reject `class abbrev`, add two bridge instances at priority 100:
```lean
instance (priority := 100) [BimodalConnectives F] : FutureTemporalConnectives F where ...
instance (priority := 100) [BimodalConnectives F] : TemporalConnectives F where ...
```

This is the standard Mathlib pattern and will not face pushback.

## Teammate Contributions

| Teammate | Angle | Status | Key Finding |
|----------|-------|--------|------------|
| A | Empirical testing | completed | `class abbrev` chaining works; hybrid requires 3 classes to change |
| B | Scaling analysis | completed | `class abbrev` scales O(N) vs O(intersections) for bridges |
| C | Adversarial testing | completed | Gap is symmetric (both designs need same bridges unless temporal also changes); only 3 Mathlib uses |
| D | Ecosystem/strategy | completed | Warning suppression has 0 Mathlib precedent; hybrid mixing confirmed |
