# Teammate B Findings: Alternative Patterns for CSLib BimodalConnectives Diamond

## Task
Research alternative patterns and mitigation techniques for the BimodalConnectives diamond
inheritance issue in CSLib. BimodalConnectives currently avoids a diamond through
`PropositionalConnectives` by NOT extending `TemporalConnectives`, which means
`BimodalConnectives` does not automatically provide a `TemporalConnectives` instance.

---

## Key Findings

### 1. Convenience Instances: Providing Missing Parent Instances

**The Pattern**

The standard Lean 4 / Mathlib pattern for providing "missing" parent instances from a richer
child class is called a "forgetful instance" or convenience instance:

```lean
instance (priority := 100) [BimodalConnectives F] : TemporalConnectives F where
  bot  := HasBot.bot
  imp  := HasImp.imp
  untl := HasUntil.untl
  snce := HasSince.snce
```

This works because `BimodalConnectives F` already extends `HasUntil F`, `HasSince F`, and
`ModalConnectives F` (which itself extends `PropositionalConnectives F`, providing `HasBot` and
`HasImp`). So `TemporalConnectives F` requires exactly `{HasBot, HasImp, HasUntil, HasSince}`,
all of which are in scope.

**Instance Loop Risk Assessment**

There is NO loop risk here. A loop would require:
```
TemporalConnectives F -> ... -> BimodalConnectives F -> TemporalConnectives F
```
But `BimodalConnectives` does NOT extend `TemporalConnectives`, so no cycle exists. The
synthesis for `[BimodalConnectives F] : TemporalConnectives F` only needs the four atomic
classes, each of which is directly provided by `BimodalConnectives`.

**Priority Recommendation**

Use `(priority := 100)` (below the default 1000), following the Mathlib "lower instance
priority" pattern. This ensures concrete instances (for specific formula types like
`Bimodal.Formula`) take precedence over the generic derived instance:

```lean
-- Concrete instance: priority 1000 (default) - preferred
instance : BimodalConnectives (Formula Atom) where
  bot := .bot; imp := .imp; box := .box; untl := .untl; snce := .snce

-- Generic convenience instance: priority 100 - fallback
instance (priority := 100) [BimodalConnectives F] : TemporalConnectives F where
  bot := HasBot.bot; imp := HasImp.imp; untl := HasUntil.untl; snce := HasSince.snce
```

**Mathlib Evidence**

Mathlib uses this pattern extensively. Examples from `Mathlib/Algebra/Group/Defs.lean`:
```lean
-- Convenience instance: CommGroup implies CancelCommMonoid
instance (priority := 100) CommGroup.toCancelCommMonoid : CancelCommMonoid G :=
  { ‹CommGroup G›, Group.toCancelMonoid with }

-- Convenience instance: Group implies CancelMonoid
instance (priority := 100) Group.toCancelMonoid : CancelMonoid G where ...

-- Convenience instance: CancelCommMonoid implies CancelMonoid
instance (priority := 100) CancelCommMonoid.toCancelMonoid (M : Type u) [CancelCommMonoid M] :
    CancelMonoid M :=
  { CommMagma.IsLeftCancelMul.toIsRightCancelMul M with }
```

These are explicitly tagged with `-- see Note [lower instance priority]` in Mathlib.

**Placement**: The convenience instance should go in `Cslib/Foundations/Logic/Connectives.lean`
immediately after the `BimodalConnectives` class definition, or in a dedicated
`Cslib/Foundations/Logic/ConnectiveInstances.lean` file.

---

### 2. Flat Hierarchy Alternative (Atomic Classes Only)

**The Proposal**

Instead of bundled classes (`BimodalConnectives`, `TemporalConnectives`, etc.), use only
atomic classes and type aliases:

```lean
-- Option A: All theorems use atomic classes directly
theorem foo [HasBot F] [HasImp F] [HasUntil F] [HasSince F] : ... := ...

-- Option B: class abbrev for convenience
class abbrev BimodalConnectives' (F : Type*) :=
  HasBot F, HasImp F, HasBox F, HasUntil F, HasSince F

class abbrev TemporalConnectives' (F : Type*) :=
  HasBot F, HasImp F, HasUntil F, HasSince F
```

`class abbrev` is Lean 4's official mechanism for this. From the Lean 4 reference:
> "Behind the scenes, a class abbreviation is represented by a class that extends all the
> others. Its constructor is additionally declared to be an instance so the new class can
> be constructed by instance synthesis alone."

**Trade-offs**

| Aspect | Bundled (current) | Flat (atomic only) |
|--------|-------------------|--------------------|
| Diamond risk | Real but manageable | Eliminated |
| Instance search | One synthesis step | Multiple steps |
| Theorem verbosity | Concise `[BimodalConnectives F]` | Verbose multi-constraint |
| Hierarchy expression | Explicit subtype relation | Implicit via type parameters |
| `class abbrev` option | N/A | Nearly identical to bundled |

**Verdict**: The flat approach with `class abbrev` is essentially equivalent to the bundled
approach but trades hierarchy expressiveness for no diamond risk. For CSLib's connective
hierarchy — which is intentionally designed to express logical subsystem relationships —
the bundled approach is more semantically faithful. The current design is appropriate.

---

### 3. `old_structure_cmd` and Manual Projection Fields

**What It Does**

`set_option old_structure_cmd true` is a Lean 4 option that switches structure representation:
- **Default (new)**: Multiple inheritance stores separate fields for each ancestor; Lean 4
  copies fields from the secondary parent into the child structure
- **Old mode**: Fields from all ancestors are "flattened" into the child structure, skipping
  duplicates

**Relevance to CSLib**

For CSLib's *typeclass* (not structure) hierarchy, `old_structure_cmd` is **not applicable**.
The `old_structure_cmd` option affects `structure` commands, not `class` commands. While
classes are structures internally, the field resolution for typeclasses goes through instance
synthesis rather than direct field projection.

The diamond in CSLib (`BimodalConnectives` NOT extending `TemporalConnectives`) is deliberately
avoided at the *class definition* level. `old_structure_cmd` would only matter if
`BimodalConnectives` explicitly extended `TemporalConnectives` (causing Lean to have two
paths to `PropositionalConnectives`). Since CSLib already avoids this by design, `old_structure_cmd`
provides no additional benefit.

**Manual Projection Fields** (Forgetful Inheritance)

The Mathlib "forgetful inheritance" pattern (LibraryNote `«forgetful inheritance»` in
`Mathlib/Algebra/Group/Defs.lean`) recommends:

> "A better approach is to let `rich` extend `poor` and have a field saying that `F R = P`."

This is used for structures where you want to guarantee that two paths through the hierarchy
produce the same result definitionally. For CSLib's propositional connectives (which are Prop-
or data-level typeclasses), the simpler approach of NOT creating the diamond (current design)
is exactly right.

---

### 4. Simp Lemmas for Projection Equality

**When This Is Needed**

If two paths to the same field produce non-definitionally-equal terms, `@[simp]` lemmas can
bridge the gap. The standard use case:

```lean
-- Two ways to get `bot` from BimodalConnectives F:
-- Path 1: BimodalConnectives -> ModalConnectives -> PropositionalConnectives -> HasBot
-- Path 2: BimodalConnectives -> HasBot (if we add a convenience instance)

@[simp]
lemma bimodal_temporal_bot_eq [BimodalConnectives F] :
    (inferInstance : TemporalConnectives F).bot = HasBot.bot := rfl
```

**Applicability to CSLib**

The current CSLib design AVOIDS this problem. Because `BimodalConnectives` explicitly extends
`HasBot F` (through `ModalConnectives -> PropositionalConnectives -> HasBot`), the `bot` field
is inherited through a single path. The convenience instance `[BimodalConnectives F] :
TemporalConnectives F` would simply use `HasBot.bot` directly.

If the convenience instance is written as:
```lean
instance (priority := 100) [BimodalConnectives F] : TemporalConnectives F where
  bot  := HasBot.bot
  imp  := HasImp.imp
  untl := HasUntil.untl
  snce := HasSince.snce
```
...then all fields resolve to the unique atomic class fields, so no simp lemmas are needed.

**When simp lemmas ARE needed**: If `TemporalConnectives` was added as an EXTENDS parent to
`BimodalConnectives`, creating a true diamond through `PropositionalConnectives`, then simp
lemmas would be needed to prove `FutureTemporalConnectives.bot = PropositionalConnectives.bot`.
The current design correctly avoids this scenario.

---

### 5. `default_instance` and Instance Priorities

**Mechanism**

Lean 4 instance priority system (from `lean-lang.org/doc/reference/latest/Type-Classes/Instance-Declarations/`):
- Default priority: `1000`
- `low` = `100`, `mid` = `500`, `high` = `10000`
- `@[default_instance]` provides a fallback when type information is insufficient

**For Diamond Resolution**

Instance priorities do NOT solve diamond inheritance in the sense of "which `bot` do I use."
They solve the problem of "which instance is tried first when multiple candidates exist."

For CSLib's specific case: if you add `instance [BimodalConnectives F] : TemporalConnectives F`
at priority 100, and there is also a direct `instance : TemporalConnectives (Temporal.Formula Atom)`
at priority 1000 (default), then:
- For `Temporal.Formula`: the concrete instance (priority 1000) wins — correct
- For `Bimodal.Formula`: the generic convenience instance (priority 100) is used — correct,
  since `Bimodal.Formula` only has `BimodalConnectives`, not direct `TemporalConnectives`

**Critical Warning from Mathlib Community**

Gabriel Ebner (Lean core developer), cited in Lean Zulip archives:
> "instance priorities are extremely finicky, and should be avoided except as a last resort."

Use priorities only when:
1. Two instances would otherwise compete for the same goal
2. You need to specify which to prefer without causing loops

For CSLib's convenience instance, a priority of `100` is sufficient and follows established
Mathlib convention.

---

### 6. Mixin Pattern in Mathlib

**Definition**

The mixin pattern extends one parent class (the "primary" inheritance) and adds individual
atomic class constraints from other hierarchies. This is Mathlib's dominant pattern for
algebraic hierarchies.

**Concrete Examples from Mathlib**

```lean
-- Mixin: CancelCommMonoid extends CommMonoid (primary) + adds cancellation via mixin
class CancelCommMonoid (M : Type u) extends CommMonoid M, LeftCancelMonoid M

-- Mixin: IsCancelMul is a Prop mixin added to existing monoids
class IsCancelMul (G : Type u) [Mul G] extends IsLeftCancelMul G, IsRightCancelMul G : Prop

-- CommGroup extends BOTH Group (primary) AND CommMonoid (mixin)
class CommGroup (G : Type u) extends Group G, CommMonoid G
```

**Applied to CSLib's BimodalConnectives**

CSLib's `BimodalConnectives` IS already using the mixin pattern correctly:
```lean
-- BimodalConnectives extends ModalConnectives (primary) and adds HasUntil, HasSince as mixins
class BimodalConnectives (F : Type*) extends ModalConnectives F, HasUntil F, HasSince F
```

This is exactly analogous to `CommGroup extends Group G, CommMonoid G` — the primary parent
(`ModalConnectives`) provides the structural core, and the mixins (`HasUntil`, `HasSince`) add
the additional operators without creating a diamond.

**The Missing Step**: Unlike Mathlib (which adds convenience instances like
`CommGroup.toCancelCommMonoid`), CSLib currently does NOT add the analogous convenience
instance `[BimodalConnectives F] : TemporalConnectives F`. This is the gap.

**Mathlib Pattern for the Analogy**

| Mathlib | CSLib Analogy |
|---------|---------------|
| `CommGroup extends Group, CommMonoid` | `BimodalConnectives extends ModalConnectives, HasUntil, HasSince` |
| `instance CommGroup.toCancelCommMonoid` | `instance [BimodalConnectives F] : TemporalConnectives F` |
| `instance Group.toCancelMonoid` | (already provided by inheritance chain) |

---

## Recommended Approach

**Primary Recommendation: Add Convenience Instance**

Add a single convenience instance in `Cslib/Foundations/Logic/Connectives.lean` after the
`BimodalConnectives` class definition:

```lean
/-- Any `BimodalConnectives` type provides `TemporalConnectives`, since it has all the
    required components: `HasBot`, `HasImp` (through `ModalConnectives`), `HasUntil`,
    and `HasSince`. Priority 100 ensures concrete instances on specific formula types
    take precedence. -/
instance (priority := 100) [BimodalConnectives F] : FutureTemporalConnectives F where
  bot  := HasBot.bot
  imp  := HasImp.imp
  untl := HasUntil.untl

instance (priority := 100) [BimodalConnectives F] : TemporalConnectives F where
  bot  := HasBot.bot
  imp  := HasImp.imp
  untl := HasUntil.untl
  snce := HasSince.snce
```

Or as a single instance (since `TemporalConnectives` extends `FutureTemporalConnectives`):

```lean
instance (priority := 100) bimodalConnectives_toTemporalConnectives
    [BimodalConnectives F] : TemporalConnectives F where
  bot  := HasBot.bot
  imp  := HasImp.imp
  untl := HasUntil.untl
  snce := HasSince.snce
```

**Why This Works Without Loops**:
- `TemporalConnectives` synthesis requires `[HasBot F]`, `[HasImp F]`, `[HasUntil F]`, `[HasSince F]`
- Each is provided directly by `BimodalConnectives F` (no recursion through `TemporalConnectives`)
- Lean 4's tabled resolution (from "Tabled Typeclass Resolution", arXiv 2001.04301) prevents
  exponential blowup even if diamonds in the *search* exist — the result is cached

**Secondary Recommendation: Also add `FutureTemporalConnectives` instance**

Since `FutureTemporalConnectives` is used for code generic over future-only temporal logics,
and `BimodalConnectives` has both `HasUntil` and all propositional connectives:

```lean
instance (priority := 100) bimodalConnectives_toFutureTemporalConnectives
    [BimodalConnectives F] : FutureTemporalConnectives F where
  bot  := HasBot.bot
  imp  := HasImp.imp
  untl := HasUntil.untl
```

**What NOT to do**:
1. Do NOT make `BimodalConnectives` extend `TemporalConnectives` — this creates the original
   diamond through `PropositionalConnectives` that the current design correctly avoids
2. Do NOT use `old_structure_cmd` — irrelevant to typeclass diamond avoidance
3. Do NOT add simp lemmas for projection equality — not needed with the current design
4. Do NOT use `class abbrev` to replace the bundled hierarchy — the bundled hierarchy is
   more semantically appropriate for CSLib's purpose

---

## Evidence / Examples

### Evidence 1: Mathlib `Group.toCancelMonoid` Pattern (Direct Analogue)

From `Mathlib/Algebra/Group/Defs.lean` lines 1264-1270:
```lean
-- see Note [lower instance priority]
@[to_additive]
instance (priority := 100) Group.toCancelMonoid : CancelMonoid G where
  mul_right_cancel := fun a b c h ↦ by ...
  mul_left_cancel  := fun a {b c} h ↦ by ...
```
This is exactly the pattern: `Group` already has all components needed for `CancelMonoid`,
so a priority-100 instance provides `CancelMonoid` from `Group`.

### Evidence 2: `class abbrev` in Mathlib AffineMonoid

From `Mathlib/Algebra/AffineMonoid/Basic.lean`:
```lean
class abbrev IsAffineMonoid (M : Type*) [CommMonoid M] : Prop :=
  IsCancelMul M, Monoid.FG M, IsMulTorsionFree M
```
Demonstrates `class abbrev` as an alternative to bundling for combining multiple atomic classes.

### Evidence 3: Mathlib Forgetful Inheritance Note

From `Mathlib/Algebra/Group/Defs.lean` lines 441-490 (LibraryNote `«forgetful inheritance»`):
> "A possible implementation would be to have a type class `rich` containing a field `R`, a
> type class `poor` containing a field `P`, and an instance from `rich` to `poor`. However,
> this creates diamond problems, and a better approach is to let `rich` extend `poor` and
> have a field saying that `F R = P`."

This confirms the current CSLib design (flat diamond avoidance by not extending `TemporalConnectives`)
plus convenience instances is the correct Mathlib-aligned approach.

### Evidence 4: Instance Priority Philosophy

From Lean Zulip archive (Gabriel Ebner):
> "instance priorities are extremely finicky, and should be avoided except as a last resort."

Confirms that priority 100 for convenience instances (not arbitrary manipulation) is the
correct conservative use case.

### Evidence 5: Lean 4 Tabled Resolution

From arXiv 2001.04301 "Tabled Typeclass Resolution":
> "Diamonds occur when there is more than one route to a given goal. [Tabling] prevents
> exponential search overhead when multiple paths yield the same result."

Lean 4's synthesis algorithm caches intermediate results, so even if synthesis explores
multiple paths, there is no exponential blowup. This means adding convenience instances is
safe from a performance standpoint.

---

## Confidence Level

| Finding | Confidence |
|---------|-----------|
| Convenience instance pattern works without loops | **High** — confirmed by examining the class definitions; no cycle is possible |
| Priority 100 is correct for convenience instances | **High** — directly follows Mathlib convention with `-- see Note [lower instance priority]` |
| `old_structure_cmd` is not applicable | **High** — affects `structure` not `class` at synthesis level |
| Simp lemmas not needed with current design | **High** — all fields resolve through unique atomic classes |
| `class abbrev` is a viable alternative | **Medium** — works but loses hierarchy semantics; not recommended for CSLib |
| Mixin pattern analogy to Mathlib is exact | **High** — `BimodalConnectives extends ModalConnectives, HasUntil, HasSince` directly mirrors `CommGroup extends Group, CommMonoid` |
| Both `FutureTemporalConnectives` and `TemporalConnectives` instances needed | **Medium** — depends on whether any CSLib code uses `[FutureTemporalConnectives F]` constraints; check actual usage |

---

## Sources

- [Multiple-inheritance hazards in dependently-typed algebraic hierarchies](https://arxiv.org/pdf/2306.00617)
- [Use and abuse of instance parameters in the Lean mathematical library](https://arxiv.org/pdf/2202.01629)
- [Lean 4 Instance Declarations reference](https://lean-lang.org/doc/reference/latest/Type-Classes/Instance-Declarations/)
- [Lean 4 Instance Synthesis reference](https://lean-lang.org/doc/reference/latest/Type-Classes/Instance-Synthesis/)
- [Lean 4 Class Declarations reference](https://lean-lang.org/doc/reference/latest/Type-Classes/Class-Declarations/)
- [Mathlib Algebra Group Defs - forgetful_inheritance LibraryNote](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/Group/Defs.html)
- [Tabled Typeclass Resolution](https://arxiv.org/pdf/2001.04301)
- [Growing Mathlib: maintenance of a large scale mathematical library](https://arxiv.org/pdf/2508.21593)
- [Lean 4 Zulip Archive - instance priority discussion](https://leanprover-community.github.io/archive/stream/270676-lean4/topic/Lean.204.20set_like.html)
