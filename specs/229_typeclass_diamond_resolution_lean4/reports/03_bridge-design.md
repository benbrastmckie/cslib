# Research Report: Mixin + Bridge Instance Design for BimodalConnectives

- **Task**: 229 - typeclass_diamond_resolution_lean4
- **Date**: 2026-06-17
- **Focus**: Design and verify the minimal mixin + bridge instance approach

## Summary

The proposed design change -- switching `BimodalConnectives` primary parent from `ModalConnectives` to `TemporalConnectives` and adding `HasBox` as atomic mixin -- is verified to compile, preserve all existing instance syntax, maintain definitional equality across all paths, and require exactly ONE bridge instance. The total change set is 2 files, approximately 15 lines modified.

## 1. New Design Compiles

Verified via self-contained Lean snippet reproducing the full hierarchy:

```lean
-- NEW DESIGN
class BimodalConnectives (F : Type*) extends TemporalConnectives F, HasBox F
```

All inherited instances resolve automatically from `[BimodalConnectives F]`:

| Instance | Path | Status |
|----------|------|--------|
| `TemporalConnectives F` | Direct parent | passes |
| `FutureTemporalConnectives F` | via TemporalConnectives | passes |
| `PropositionalConnectives F` | via FutureTemporalConnectives | passes |
| `HasBot F` | via PropositionalConnectives | passes |
| `HasImp F` | via PropositionalConnectives | passes |
| `HasUntil F` | via FutureTemporalConnectives | passes |
| `HasSince F` | via TemporalConnectives | passes |
| `HasBox F` | Direct parent | passes |
| `ModalConnectives F` | **FAILS** without bridge | expected |

## 2. Bridge Instance Design

Exactly one bridge instance is needed:

```lean
/-- Bridge: `BimodalConnectives` provides `ModalConnectives` by combining the inherited
    `PropositionalConnectives` (from the `TemporalConnectives` parent chain) with the
    `HasBox` mixin. Priority 100 ensures this does not compete with direct instances. -/
instance (priority := 100) [BimodalConnectives F] : ModalConnectives F where
  bot := HasBot.bot
  imp := HasImp.imp
  box := HasBox.box
```

With this bridge, `inferInstance : ModalConnectives F` succeeds from `[BimodalConnectives F]`.

No bridge is needed for `FutureTemporalConnectives` or `TemporalConnectives` -- both are inherited automatically through the `extends TemporalConnectives F` chain.

## 3. No Instance Loops

The bridge creates a one-way path: `BimodalConnectives -> ModalConnectives`. Since `ModalConnectives` does NOT extend `BimodalConnectives`, there is no cycle. Verified empirically:

- `[ModalConnectives F]` alone still resolves `PropositionalConnectives F` and `HasBox F` correctly (no interference from the bridge).
- The bridge only fires when `BimodalConnectives F` is in context.

## 4. Definitional Equality

All projection paths produce definitionally equal results (proved by `rfl`):

```lean
-- Bridge bot = HasBot.bot
example [inst : BimodalConnectives F] :
    (inferInstance : ModalConnectives F).toPropositionalConnectives.toHasBot.bot =
    (HasBot.bot : F) := rfl

-- Bridge box = HasBox.box
example [inst : BimodalConnectives F] :
    (inferInstance : ModalConnectives F).toHasBox.box =
    (HasBox.box : F → F) := rfl

-- TemporalConnectives path agrees with bridge path
example [inst : BimodalConnectives F] :
    (inferInstance : ModalConnectives F).toPropositionalConnectives.toHasBot.bot =
    inst.toTemporalConnectives.toFutureTemporalConnectives.toPropositionalConnectives.toHasBot.bot := rfl
```

## 5. Downstream Impact Analysis

### Files Requiring Changes

| File | Change | Lines |
|------|--------|-------|
| `Cslib/Foundations/Logic/Connectives.lean` | Change `extends` target + add bridge + update docstring | ~12 lines |
| (no other files) | | |

### Files NOT Requiring Changes

| File | Reason |
|------|--------|
| `Cslib/Logics/Bimodal/Syntax/Formula.lean` | Instance fields are identical: `bot`, `imp`, `box`, `untl`, `snce` |
| `Cslib/Foundations/Logic/ProofSystem.lean` | `BimodalTMHilbert` uses atomic `HasBot`, `HasImp`, `HasBox`, `HasUntil`, `HasSince` constraints, not bundled connective classes |
| `Cslib/Logics/Modal/Basic.lean` | Independent `ModalConnectives` instance, unaffected |
| `Cslib/Logics/Temporal/Syntax/Formula.lean` | Independent `TemporalConnectives` instance, unaffected |
| `Cslib/Logics/LTL/Syntax/Formula.lean` | Independent `LTLConnectives` instance, unaffected |
| `Cslib/Foundations/Logic/Axioms.lean` | Only mentions `ModalConnectives` in comments, not in code |

### Projection Names

The old design generates projections: `toModalConnectives`, `toHasUntil`, `toHasSince`.
The new design generates projections: `toTemporalConnectives`, `toHasBox`.

Grep confirms **zero** uses of `toModalConnectives`, `toBimodalConnectives`, `toTemporalConnectives`, or `toFutureTemporalConnectives` projection paths anywhere in the CSLib codebase. No code references these generated projections, so the rename is invisible.

### BimodalTMHilbert

The `BimodalTMHilbert` class (ProofSystem.lean line 456) uses individual `[HasBot F] [HasImp F] [HasBox F] [HasUntil F] [HasSince F]` constraints in its type signature. It does NOT reference `BimodalConnectives` or any bundled connective class. No change needed.

## 6. Concrete Instance Syntax Preserved

The existing instance in `Bimodal/Syntax/Formula.lean`:

```lean
instance : BimodalConnectives (Formula Atom) where
  bot := .bot
  imp := .imp
  box := .box
  untl := .untl
  snce := .snce
```

compiles identically under both old and new designs. Lean's `where` syntax resolves field names regardless of which `extends` path provides them. Verified empirically.

## 7. Exact Changes for Connectives.lean

### Change 1: BimodalConnectives class definition (line 150-153)

**Before:**
```lean
/-- Bimodal connectives: modal connectives plus until and since.
    Note: we extend `ModalConnectives` and add `HasUntil`/`HasSince` directly
    rather than extending `TemporalConnectives`, to avoid a typeclass diamond. -/
class BimodalConnectives (F : Type*) extends ModalConnectives F, HasUntil F, HasSince F
```

**After:**
```lean
/-- Bimodal connectives: temporal connectives plus necessity.
    Extends `TemporalConnectives` (propositional + until + since) with `HasBox` as an
    atomic mixin. A bridge instance provides `ModalConnectives` synthesis. -/
class BimodalConnectives (F : Type*) extends TemporalConnectives F, HasBox F
```

### Change 2: Add bridge instance (after the class definition)

```lean
/-- Bridge: `BimodalConnectives` provides `ModalConnectives` by combining the inherited
    `PropositionalConnectives` (from the `TemporalConnectives` parent chain) with the
    `HasBox` mixin. Priority 100 avoids competing with direct instances. -/
instance (priority := 100) [BimodalConnectives F] : ModalConnectives F where
  bot := HasBot.bot
  imp := HasImp.imp
  box := HasBox.box
```

### Total Lines Changed

- 4 lines modified (class definition + docstring)
- 5 lines added (bridge instance + docstring)
- **Total: ~9 lines in 1 file**

No other files require modification.

## 8. Comparison with class abbrev Approach (Plan 03)

The existing plan (03_class-abbrev-refactor.md) proposes converting 3 classes to `class abbrev`. The mixin + bridge approach is a simpler alternative:

| Metric | class abbrev (Plan 03) | Mixin + Bridge (This Report) |
|--------|----------------------|------------------------------|
| Classes changed | 3 (FutureTemporalConnectives, TemporalConnectives, BimodalConnectives) | 1 (BimodalConnectives) |
| Files changed | 1 | 1 |
| Lines changed | ~15 | ~9 |
| Bridge instances | 0 | 1 |
| Mathlib precedent | 3 (all Prop-valued) | Standard pattern |
| Reviewer risk | Medium (uncommon pattern) | Low (standard Mathlib pattern) |
| Gains `TemporalConnectives` from `[BimodalConnectives]` | Yes | Yes |
| Gains `ModalConnectives` from `[BimodalConnectives]` | Yes | Yes (via bridge) |
| Gains `FutureTemporalConnectives` from `[BimodalConnectives]` | Yes | Yes (via TemporalConnectives chain) |
| Future extensibility | class extends can build on class abbrev | Standard extends chain + bridges as needed |

## 9. Recommendation

The mixin + bridge approach is the **simpler, more conservative** option. It uses entirely standard Lean 4 patterns (no `class abbrev` precedent questions), changes fewer lines, and achieves the same instance synthesis goals. The one bridge instance is the only "cost," and it is a well-understood Mathlib pattern.

If the user prefers zero bridge instances, the `class abbrev` approach from Plan 03 remains viable. But for minimal risk and minimal diff, the mixin + bridge design is recommended.
