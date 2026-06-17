# Research Report: Task #229

**Task**: Typeclass diamond resolution in Lean 4 — BimodalConnectives design
**Date**: 2026-06-17
**Mode**: Team Research (4 teammates)

## Summary

The central discovery across all teammates: **the typeclass diamond is not forbidden in Lean 4**. It compiles with a suppressible `structureDiamondWarning` (not an error), and in CSLib's specific hierarchy the two paths to `PropositionalConnectives` are **definitionally equal** (proved by `rfl`). The current diamond-avoidance design is correct but carries a hidden cost: `TemporalConnectives` cannot be synthesized from `BimodalConnectives`. Three viable paths forward exist, ranked below.

## Key Findings

### 1. The Diamond Is Safe in Lean 4 (High Confidence)

Lean 4 handles typeclass diamonds automatically via "first parent wins" resolution:
- Diamond inheritance via `extends` produces a **warning**, not an error
- `set_option structureDiamondWarning false` suppresses it (Lean's own test suite does this)
- The first listed parent wins for shared ancestor fields; the second path is reconstructed synthetically
- Lean 4.19.0 (May 2025, PR #7302) improved default value handling in diamonds but did not change the fundamental mechanics
- No RFC or structural change to class inheritance was found for 2025-2026

Teammate C verified with live Lean tests that the two paths to `PropositionalConnectives` through `ModalConnectives` and `TemporalConnectives` produce **definitionally equal** results:

```lean
theorem abstract_diamond_defeq (F : Type) [inst : BimodalDiamond F] :
    inst.toModalConnectives.toPropositionalConnectives =
    inst.toTemporalConnectives.toFutureTemporalConnectives.toPropositionalConnectives := rfl
```

The constructors for the diamond and flat designs are **structurally identical** — same stored fields, same memory layout.

### 2. The Current Design's Hidden Cost (High Confidence)

`BimodalConnectives` currently extends `ModalConnectives` + `HasUntil` + `HasSince`. This means:
- `inferInstance : TemporalConnectives F` **fails** when only `[BimodalConnectives F]` is in scope
- `inferInstance : FutureTemporalConnectives F` also fails
- Any lemma stated with `[TemporalConnectives F]` is invisible in bimodal contexts
- Any `@[simp]` lemma with temporal bundle constraints won't fire in bimodal contexts

**Current impact is zero**: all proof-system classes (`TemporalBXHilbert`, `BimodalTMHilbert`, etc.) use atomic `[HasBot F] [HasImp F] [HasUntil F] [HasSince F]` constraints, not bundles. But this is an undocumented invariant — future code using `[TemporalConnectives F]` will silently break.

### 3. The Reverse Design (TemporalConnectives + HasBox) Has the Mirror Problem (High Confidence)

The user's proposed alternative of extending `TemporalConnectives` + `HasBox` creates the exact mirror gap:
- `TemporalConnectives` IS automatically synthesized (good)
- `ModalConnectives` is NOT synthesized (bad — same problem, opposite direction)

Both the current design (Option A) and the reverse (Option B) are symmetric in their limitations. Neither is strictly better — the choice depends on which parent is more commonly needed independently.

### 4. Mathlib's Mixin Pattern Matches CSLib's Current Design (High Confidence)

Mathlib uses the same pattern: extend the primary parent, add atomic mixins, provide convenience instances at priority 100. Examples:
- `CommGroup extends Group G, CommMonoid G` (primary chain + mixin)
- `instance (priority := 100) CommGroup.toCancelCommMonoid` (bridge instance)

CSLib's design is correct but **missing the bridge instance** that Mathlib always provides.

### 5. `class abbrev` Eliminates Diamonds Structurally (Medium Confidence)

Lean 4's `class abbrev` creates bundled names whose constructors are automatically registered as instances:

```lean
class abbrev BimodalConnectives (F : Type*) :=
  ModalConnectives F, HasUntil F, HasSince F
```

Any type with instances of all component classes automatically gains `BimodalConnectives`. This eliminates ALL diamond concerns and scales linearly to future extensions (`EpistemicConnectives`, `DeonticConnectives`, etc.). The trade-off: `class abbrev` cannot add new methods (only bundles existing ones) and loses the explicit hierarchy structure that `extends` provides.

## Synthesis

### Conflicts Resolved

**Conflict 1: Keep current vs. use true diamond**
- Teammates A and B recommend keeping Option A (current) + convenience instances
- Teammate C recommends the true diamond (Option C) as the superior long-term design
- Teammate D recommends `class abbrev` as the best structural solution

**Resolution**: All three approaches are viable. The choice depends on CSLib's design philosophy:

| Approach | Pros | Cons |
|----------|------|------|
| **A: Keep current + bridge instances** | No warning, Mathlib-aligned, minimal churn | Requires manual bridge instances for each intersection |
| **C: True diamond + suppress warning** | Both parents available, cleanest semantics | Suppressible warning, less common in Lean ecosystem |
| **D: `class abbrev`** | Eliminates all diamonds, future-proof | Loses `extends` hierarchy, cannot add methods to bundles |

**Conflict 2: Which parent should be primary (if keeping flat design)?**
- Teammate A: `ModalConnectives` (CSLib is modal-logic-heavy)
- User preference: `TemporalConnectives` (temporal operators feel more fundamental in bimodal context)
- Teammate C: Both are symmetric — the choice is aesthetic

**Resolution**: In CSLib's current codebase, `Cslib/Logics/Modal/` is substantially larger than `Cslib/Logics/Temporal/`. Users are more likely to come from the modal side. However, the reverse argument is valid: in a bimodal logic, the temporal operators (until, since) are the "novel" addition over standard modal logic, making temporal the more interesting specialization to preserve. Either choice works — the bridge instance resolves the asymmetry.

### Gaps Identified

1. **No bridge instance exists today** — `[BimodalConnectives F] : TemporalConnectives F` is absent from CSLib
2. **The comment in Connectives.lean misleads** — "to avoid a typeclass diamond" suggests correctness concern, but the real concern is a compiler warning
3. **`FutureTemporalConnectives` is also affected** — needs its own bridge instance
4. **The atomic-class-only invariant is undocumented** — if future code uses bundle constraints, the missing-instance gap bites silently
5. **`class abbrev` has not been tested on CSLib** — needs a proof-of-concept branch

### Recommendations

**Immediate (low effort)**:
1. Add bridge instances for `TemporalConnectives` and `FutureTemporalConnectives` from `BimodalConnectives` at priority 100 in `Connectives.lean`
2. Update the comment on `BimodalConnectives` to explain the design rationale accurately (it avoids a `structureDiamondWarning`, not a correctness issue)

**Medium-term (moderate effort)**:
3. Evaluate `class abbrev` in a branch — change all bundled classes to `class abbrev` and run the test suite. If it passes, adopt it as the standard pattern for connective bundles.

**If extending TemporalConnectives + HasBox is preferred**:
4. Switch to `extends TemporalConnectives F, HasBox F` and add a bridge instance `[BimodalConnectives F] : ModalConnectives F` at priority 100. This is equally valid to the current design — the choice is which parent to privilege.

**If the true diamond is preferred**:
5. Use `extends ModalConnectives F, TemporalConnectives F` with `set_option structureDiamondWarning false`. This is the cleanest design and has been verified as definitionally safe. Both parents are automatically available. The warning suppression is legitimate (Lean's own test suite uses it).

## Teammate Contributions

| Teammate | Angle | Status | Confidence |
|----------|-------|--------|------------|
| A | Lean 4 mechanisms + BimodalConnectives trade-off | completed | high |
| B | Mitigation patterns + Mathlib mixin analysis | completed | high |
| C | Critic — assumption validation + live testing | completed | high |
| D | Strategic direction + `class abbrev` proposal | completed | medium-high |

## References

- Lean 4 test suite: `tests/elab/diamond1.lean` through `diamond5.lean`
- Lean 4.19.0 release notes (PR #7302, #7314, #7717)
- Lean 4 Class Declarations reference: https://lean-lang.org/doc/reference/latest/Type-Classes/Class-Declarations/
- Lean 4 Instance Synthesis reference: https://lean-lang.org/doc/reference/latest/Type-Classes/Instance-Synthesis/
- Mathlib `Algebra/Group/Defs.lean`: forgetful inheritance pattern, `CommGroup.toCancelCommMonoid`
- Mathlib `Algebra/AffineMonoid/Basic.lean`: `class abbrev IsAffineMonoid` example
- "Multiple-inheritance hazards in dependently-typed algebraic hierarchies" (arXiv:2306.00617)
- "Use and abuse of instance parameters in the Lean mathematical library" (arXiv:2202.01629)
- "Tabled Typeclass Resolution" (arXiv:2001.04301)
- CSLib `Cslib/Foundations/Logic/Connectives.lean` (lines 150-153)
