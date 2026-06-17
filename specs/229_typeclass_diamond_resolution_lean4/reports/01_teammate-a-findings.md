# Teammate A Findings: Lean 4 Diamond Inheritance and BimodalConnectives Design

**Task**: 229 — Typeclass diamond resolution in Lean 4, applied to CSLib's BimodalConnectives

**Focus**: Current Lean 4 mechanisms for handling typeclass diamonds + the specific BimodalConnectives trade-off

---

## Key Findings

### 1. Lean 4's Built-in Diamond Handling

**Lean 4 does NOT produce a hard error for diamond inheritance.** It resolves diamonds automatically using a "first parent wins" rule. This is confirmed directly by Lean 4's own test suite (`tests/elab/diamond1.lean` through `diamond5.lean`).

The key evidence from `tests/elab/diamond4.lean`:

```lean
class A (α : Type) where
  one  : α
  zero : α

class B (α : Type) extends A α where
  add : α → α → α

class C (α : Type) extends A α where
  mul : α → α → α

set_option structureDiamondWarning false

class D (α : Type) extends B α, C α   -- DIAMOND: both B and C extend A
```

The generated projection `D.toC` shows Lean's resolution strategy:
```lean
@[implicit_reducible] def D.toC : {α : Type} → [self : D α] → C α :=
fun (α : Type) (self : D α) => @C.mk α (@B.toA α (@D.toB α self)) (@D.mul α self)
```

The first parent (`B`) wins for the shared ancestor (`A`): `D.toC` reconstructs `C` by pulling `A` through `B`'s path (`@B.toA`), not directly. This means `D.toA` is definitionally equal to `B.toA applied to self`, not `C.toA`.

**Key behaviors**:
- Diamond via `extends` is **NOT a hard error** in Lean 4
- It produces a **warning** (`structureDiamondWarning`) that can be suppressed with `set_option structureDiamondWarning false`
- Resolution is deterministic: **first listed parent wins** for the shared ancestor fields
- The non-primary path is reconstructed (not stored), ensuring no field duplication
- As of Lean 4.19.0 (May 2025, PR #7302), default values in diamond scenarios now correctly respect the structure resolution order

**The warning, not error, distinction is critical**: The comment in CSLib's `Connectives.lean` says "to avoid a typeclass diamond" — this means "to avoid the warning and conceptual confusion", not "to avoid a compile error".

### 2. The `structureDiamondWarning` Option

Lean 4 produces a warning (not error) when a diamond is detected via `extends`. The option `set_option structureDiamondWarning false` suppresses this warning. Lean 4's own test suite uses this option extensively, confirming that diamond inheritance is a supported pattern — just one that Lean wants to alert developers about.

This means the **third alternative** for BimodalConnectives would work:
```lean
class BimodalConnectives (F : Type*) extends ModalConnectives F, TemporalConnectives F
```
...but would produce a `structureDiamondWarning` because both `ModalConnectives` and `TemporalConnectives` extend `PropositionalConnectives`.

### 3. Lean 4 RFCs and Recent Changes (2025-2026)

- **Lean 4.19.0 (May 2025, PR #7302)**: Changed how fields are elaborated in `structure`/`class`. Every field is now a local variable; all parents appear in local context. Default values now respect the structure resolution order in diamond scenarios. This made "magic field definitions" impossible.
- **Lean 4.19.0 (PR #7314)**: Each structure parent is fully elaborated before processing the next.
- **Lean 4.19.0 (PR #7717)**: Refactored structure instance notation to simulate flat representation with special handling for diamond inheritance.
- **No RFC specifically for eliminating diamond warnings** was found. The feature is considered stable and supported.

### 4. The Three Options for BimodalConnectives

The hierarchy is:
```
PropositionalConnectives (HasBot, HasImp)
   /            \
ModalConnectives    FutureTemporalConnectives
(+ HasBox)          (+ HasUntil)
     |                    |
     |             TemporalConnectives
     |             (+ HasSince)
      \                  /
    BimodalConnectives (target)
```

**Option A (current)**: `extends ModalConnectives F, HasUntil F, HasSince F`
- No diamond: `HasUntil` and `HasSince` are atomic (no ancestor)
- `ModalConnectives` is first-class parent: `ModalConnectives` instances are trivially available
- `TemporalConnectives` is NOT a parent: users who need `TemporalConnectives` from `BimodalConnectives` need a convenience instance

**Option B**: `extends TemporalConnectives F, HasBox F`
- No diamond: `HasBox` is atomic (no ancestor)
- `TemporalConnectives` is first-class parent: `TemporalConnectives` instances trivially available
- `ModalConnectives` is NOT a parent: users need convenience instances
- `FutureTemporalConnectives` is available transitively (through `TemporalConnectives`)

**Option C (true diamond)**: `extends ModalConnectives F, TemporalConnectives F`
- Diamond: both extend `PropositionalConnectives` (and `FutureTemporalConnectives` via `TemporalConnectives`)
- Produces `structureDiamondWarning`
- `ModalConnectives` wins for shared fields; `TemporalConnectives` is reconstructed
- Both `ModalConnectives` and `TemporalConnectives` are first-class parents (trivial instance derivation in both directions)
- Clean semantics: most expressive, most natural

---

## Recommended Approach

### For BimodalConnectives: Keep the current Option A

**Recommendation: Maintain `extends ModalConnectives F, HasUntil F, HasSince F`**

Rationale:

1. **Modal logic is the primary use case in CSLib**. The library has extensive modal logic content (`Cslib/Logics/Modal/`). Users working with bimodal logics are more likely to come from the modal side than the temporal side. Making `ModalConnectives` the first-class parent is the correct priority.

2. **The "missing" direction is cheaper to supply**. If a user has `[BimodalConnectives F]` and needs `[TemporalConnectives F]`, a single convenience instance suffices:
   ```lean
   instance [BimodalConnectives F] : TemporalConnectives F where
     bot := HasBot.bot
     imp := HasImp.imp
     untl := HasUntil.untl
     snce := HasSince.snce
   ```
   The converse (needing `ModalConnectives` from `BimodalConnectives` under Option B) is equally cheap. The choice is symmetric in this regard.

3. **Option C would work but introduces baggage**. Extending both `ModalConnectives` and `TemporalConnectives` directly would be the most semantically natural design, but: (a) it produces `structureDiamondWarning`, which CSLib may want to avoid for clean CI; (b) it requires deeper Lean 4 understanding to audit; (c) the practical benefit (slightly fewer convenience instances) is minimal.

4. **The current design is already correct and in PR**. Changing it requires re-review. The marginal benefit of Option B or C does not justify churn.

**However**, there is one design refinement worth considering: adding a convenience instance from `BimodalConnectives` to `TemporalConnectives` (and possibly `FutureTemporalConnectives`). This would give users coming from the temporal side clean access without requiring them to know the internals:

```lean
instance [BimodalConnectives F] : TemporalConnectives F where
  bot := HasBot.bot
  imp := HasImp.imp
  untl := HasUntil.untl
  snce := HasSince.snce
```

### For the Diamond Warning

If Option C were chosen (`extends ModalConnectives F, TemporalConnectives F`), the warning can be suppressed with:
```lean
set_option structureDiamondWarning false in
class BimodalConnectives (F : Type*) extends ModalConnectives F, TemporalConnectives F
```

This is legitimate — Lean 4's own test suite does exactly this. But for CSLib, it's better to avoid the warning entirely by using the current Option A design.

---

## What Mathlib Does

Mathlib's approach to algebraic hierarchy diamonds:

1. **Extension over mixins** (from `algebra/hierarchy_design`): "Generally in mathlib we use the extension mechanism (`comm_ring extends ring`) rather than mixins." This prefers Option A/B style (one parent is the "main" chain, others are atomic) over Option C (extending two bundled parents).

2. **Forgetful inheritance**: The "rich extends poor" principle. In Mathlib, `CommMonoid extends Monoid` and `CommMonoid extends CommSemigroup`, both of which extend `Semigroup` — creating a diamond. Lean handles this automatically. Mathlib accepts diamonds in the algebraic hierarchy as a necessary cost of expressiveness.

3. **Performance-aware bundling**: Mathlib uses "partially unbundled" structures where types are parameters but operators remain bundled. This keeps the number of typeclass variables small while minimizing deep nesting that causes exponential blowup.

4. **The key insight**: Mathlib prioritizes **which parent is the "natural" chain** and extends that first. `CommMonoid` extends `Monoid` (not `CommSemigroup`) as the primary chain because monoids are the more fundamental concept in the ring hierarchy. Analogously, for `BimodalConnectives`, `ModalConnectives` is the "natural" primary chain for CSLib's logic hierarchy.

---

## Evidence / Examples

### From Lean 4 Test Suite

`tests/elab/diamond1.lean`: Class diamond with `FooAC extends FooComm, FooAssoc` (both extend `Foo`) — works with warning suppressed.

`tests/elab/diamond4.lean`: Explicit typeclass diamond `D extends B, C` (both extend `A`). `D.toC` reconstructs `C` via `B`'s path to `A`. No error, just a warning.

`tests/elab/diamond5.lean`: `Semiring extends AddMonoid, Monoid` (both extend `Numeric`), plus `Monoid extends Semigroup, Numeric` — multiple diamonds stacked. This is the Lean 4 algebraic hierarchy pattern.

### From CSLib History

The BimodalConnectives diamond comment was present from the **first commit** (`task 14 phase 1: connective typeclass hierarchy`, commit `dd268c3b`). The design was intentional from the start: avoid the diamond by extending `ModalConnectives` plus atomic mixins rather than extending two bundled parents.

### From Mathlib Docs

`CommMonoid` depends on 7 ancestor classes in a diamond pattern. Mathlib accepts this and uses tabled typeclass resolution (Lean 4's built-in) to handle the performance implications. The documented strategy is: prefer bundled extension over mixins, tolerate diamonds when they arise naturally from the hierarchy.

---

## Confidence Level

| Question | Confidence | Basis |
|----------|------------|-------|
| Lean 4 does NOT hard-error on diamonds | **High** | Lean 4 test suite diamond1-5, official docs |
| Diamond produces a warning (`structureDiamondWarning`) | **High** | Test files use `set_option structureDiamondWarning false` |
| First parent wins in resolution | **High** | `D.toC` output in diamond4.lean.out.expected |
| Current Option A is the right choice for CSLib | **High** | ModalConnectives is primary; atomic mixins avoid warning |
| Option C (true diamond) would work but adds baggage | **High** | Test suite confirms functionality; warning is real |
| Mathlib prefers extension over mixins for bundled classes | **High** | `algebra/hierarchy_design` docs |
| Convenience instances from BimodalConnectives to TemporalConnectives may be worth adding | **Medium** | Depends on how often temporal logic users need TemporalConnectives separately |

---

## Summary

Lean 4 handles typeclass diamonds automatically via "first parent wins" with a `structureDiamondWarning` (not an error). The current CSLib design of `BimodalConnectives extends ModalConnectives F, HasUntil F, HasSince F` correctly avoids the diamond warning while keeping `ModalConnectives` as the primary parent — the right priority for CSLib's modal-logic-heavy codebase. The alternative of extending both `ModalConnectives` and `TemporalConnectives` would work but adds a suppressible warning and conceptual complexity. The atomic-mixin approach (Option A) aligns with Mathlib's documented preference for "extension over mixins" applied at the top level of the hierarchy.
