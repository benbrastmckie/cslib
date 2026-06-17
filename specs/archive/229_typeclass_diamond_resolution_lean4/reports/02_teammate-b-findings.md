# Teammate B Findings (Round 2): Diamond Scaling with N Logics

**Task**: 229 — Typeclass diamond resolution in Lean 4
**Round**: 2 (alternatives/scaling focus)
**Date**: 2026-06-17

---

## Research Questions Addressed

1. How many diamonds form with N logic bundles (5-logic concrete count)?
2. Does `class abbrev` scale cleanly for N-way intersections?
3. How many `set_option structureDiamondWarning false` lines does true diamond need?
4. How many bridge instances does the flat approach need?
5. Which approach handles "adding a new logic" best?

---

## 1. Counting the Diamonds: N=5 Concrete Analysis

### The Diamond Structure

All 5 logic bundles share `PropositionalConnectives` as a common ancestor:

```
PropositionalConnectives (HasBot, HasImp)
   |         |          |         |         |
Modal     Temporal  Epistemic  Deontic   Dynamic
(HasBox) (HasUntil  (HasK_i)  (HasObl)  (HasProg)
          HasSince)
```

Every pair of logic bundles that both extend `PropositionalConnectives` creates a diamond when combined. Since ALL 5 logics extend `PropositionalConnectives`, **every intersection bundle creates a diamond**.

### Pairwise Intersections: C(5,2) = 10

```
Modal+Temporal         (already exists as BimodalConnectives)
Modal+Epistemic        (EpistemicModalConnectives)
Modal+Deontic          (DeonticModalConnectives)
Modal+Dynamic          (DynamicModalConnectives)
Temporal+Epistemic     (EpistemicTemporalConnectives)
Temporal+Deontic       (DeonticTemporalConnectives)
Temporal+Dynamic       (DynamicTemporalConnectives)
Epistemic+Deontic      (EpistemicDeonticConnectives)
Epistemic+Dynamic      (EpistemicDynamicConnectives)
Deontic+Dynamic        (DeonticDynamicConnectives)
```

### Triple Intersections: C(5,3) = 10

```
Modal+Temporal+Epistemic,    Modal+Temporal+Deontic,
Modal+Temporal+Dynamic,      Modal+Epistemic+Deontic,
Modal+Epistemic+Dynamic,     Modal+Deontic+Dynamic,
Temporal+Epistemic+Deontic,  Temporal+Epistemic+Dynamic,
Temporal+Deontic+Dynamic,    Epistemic+Deontic+Dynamic
```

### Total Intersections

```
C(5,2) = 10  pairwise
C(5,3) = 10  triple
C(5,4) =  5  quadruple
C(5,5) =  1  quintuple
─────────────────────
Total  = 26  non-singleton subsets
```

### N-Logic Scaling Table

| N | Pairwise | Triple | Quad | Total Intersections |
|---|----------|--------|------|---------------------|
| 2 |        1 |      0 |    0 |                   1 |
| 3 |        3 |      1 |    0 |                   4 |
| 4 |        6 |      4 |    1 |                  11 |
| 5 |       10 |     10 |    5 |                  26 |
| 6 |       15 |     20 |   15 |                  57 |
| 7 |       21 |     35 |   35 |                 120 |

Growth is `2^N - N - 1`, which is **exponential** in the number of logic bundles. This is the core scaling concern.

**Important caveat**: In practice, only semantically meaningful intersections are formalized. The logically relevant pairwise combinations for CSLib are probably 5-8, not all 10. The exponential worst case is a theoretical bound.

---

## 2. `class abbrev` Scaling

### How It Works

`class abbrev` differs from `class ... extends` in one critical way: the constructor is **automatically registered as an instance**. This means any type that already has instances for all component classes automatically gains the bundled class for free.

The Mathlib precedent (`Mathlib/Algebra/AffineMonoid/Basic.lean`):
```lean
class abbrev IsAffineMonoid (M : Type*) [CommMonoid M] : Prop :=
  IsCancelMul M, Monoid.FG M, IsMulTorsionFree M
```

### Applied to CSLib

Under `class abbrev`, the hierarchy becomes:
```lean
-- Atomic classes (unchanged)
class HasBot (F : Type*) where bot : F
class HasImp (F : Type*) where imp : F → F → F
class HasBox (F : Type*) where box : F → F
class HasUntil (F : Type*) where untl : F → F → F
class HasSince (F : Type*) where snce : F → F → F
class HasKnowledge (F : Type*) (i : Agent) where know : F → F  -- future
class HasObligation (F : Type*) where obl : F → F              -- future

-- Bundled classes (class abbrev = automatic synthesis)
class abbrev PropositionalConnectives (F : Type*) := HasBot F, HasImp F
class abbrev ModalConnectives (F : Type*) := PropositionalConnectives F, HasBox F
class abbrev TemporalConnectives (F : Type*) := PropositionalConnectives F, HasUntil F, HasSince F
class abbrev FutureTemporalConnectives (F : Type*) := PropositionalConnectives F, HasUntil F
class abbrev BimodalConnectives (F : Type*) := ModalConnectives F, HasUntil F, HasSince F

-- Future extensions (no diamond analysis needed)
class abbrev EpistemicConnectives (F : Type*) := ModalConnectives F, HasKnowledge F
class abbrev EpistemicTemporalConnectives (F : Type*) := EpistemicConnectives F, HasUntil F, HasSince F
```

### Key N-Way Intersection Example

Under `class abbrev`, the triple intersection `EpistemicTemporalModal`:
```lean
class abbrev EpistemicTemporalConnectives (F : Type*) :=
  EpistemicConnectives F, HasUntil F, HasSince F
```

If `F` has instances for `HasBot`, `HasImp`, `HasBox`, `HasKnowledge`, `HasUntil`, `HasSince`, then ALL of the following are **automatically synthesized** without any explicit instance declarations:
- `PropositionalConnectives F`
- `ModalConnectives F`
- `EpistemicConnectives F`
- `TemporalConnectives F`
- `FutureTemporalConnectives F`
- `EpistemicTemporalConnectives F`

### Does It Scale Cleanly?

**Yes, for the no-new-methods case**. `class abbrev` has one hard constraint: **you cannot add new methods to the bundle**. It is purely a bundling mechanism for existing atomic classes. Since CSLib's connective bundles (`PropositionalConnectives`, `ModalConnectives`, etc.) currently add no new methods — they only bundle atomic `Has*` classes — `class abbrev` applies cleanly.

The limitation bites if future bundles need their own methods:
```lean
-- CANNOT do this with class abbrev:
class abbrev ModalConnectives (F : Type*) extends PropositionalConnectives F, HasBox F where
  diamond_def : ∀ (φ : F), ... -- cannot add methods to class abbrev
```

CSLib currently has no such bundled methods, but this is a design constraint to document.

### N-Way Bridge Instances Under `class abbrev`: Zero

The central scaling advantage: adding `EpistemicConnectives` to CSLib requires zero bridge instance declarations for intersections. Any formula type that provides the atomic `Has*` instances automatically participates in all intersection bundles.

---

## 3. True Diamond Scaling: `set_option` Count

### Per-Bundle Count

In the true diamond approach (`class ... extends BundleA F, BundleB F` where both share a grandparent), Lean 4 emits a `structureDiamondWarning`. The warning fires once per class definition.

For N=5 logics, if ALL possible intersection bundles are created:
- Each non-singleton subset (26 total) that extends 2+ parent bundles creates exactly 1 warning
- **Minimum `set_option` lines**: 26 (one per multi-parent bundle)
- **With file-level suppression**: `set_option structureDiamondWarning false` once per file, covering all classes in that file

**Practical count**: If all intersection bundles live in one `Connectives.lean` file, a single file-level `set_option structureDiamondWarning false` covers all 26. If bundles are split across files (e.g., one file per intersection logic), 26 separate lines are needed.

### Stacked Diamonds (3+ Parents Sharing Grandparent)

Triple intersections like `EpistemicTemporalModal extends EpistemicConn F, TemporalConn F, ModalConn F` create a **stacked diamond**: all three parents share `PropositionalConnectives` as a common ancestor. Lean 4 resolves this via first-parent-wins applied recursively.

**Verified pattern** (from Lean 4 test suite `tests/elab/diamond5.lean`):
```lean
class Semiring α extends AddMonoid α, Monoid α  -- both extend Numeric
class Monoid α extends Semigroup α, Numeric α    -- diamond
```
Lean handles these stacked diamonds correctly. The `structureDiamondWarning false` option suppresses warnings at each level.

**Definitional equality requirement for stacked diamonds**: All synthesis paths must produce definitionally equal fields. For CSLib's logic hierarchy, this holds as long as every formula type provides `HasBot.bot`, `HasImp.imp`, etc. via the same constructor. Since each formula type has exactly one constructor per operator (e.g., `Formula.bot`, `Formula.imp`), all paths through the diamond produce the same field values. No `rfl` proof of definitional equality is needed beyond compilation.

---

## 4. Bridge Instance Count: Flat + Bridge Approach

### Formula

Under the flat design (Option A), each intersection bundle extends ONE primary parent plus atomic mixins. The secondary parents are not available via implicit synthesis and require explicit bridge instances.

For pairwise bundles: 1 bridge instance per bundle
For triple bundles: 2 bridge instances per bundle (to each non-primary parent)
For quad bundles: 3 bridge instances per bundle
For quint bundles: 4 bridge instances per bundle

### N=5 Full Count (Theoretical Maximum)

| Bundle type | Count | Bridges each | Total bridges |
|-------------|-------|--------------|---------------|
| Pairwise    |    10 |            1 |            10 |
| Triple      |    10 |            2 |            20 |
| Quad        |     5 |            3 |            15 |
| Quint       |     1 |            4 |             4 |
| **Total**   |    26 |              |        **49** |

### Complexity Class

The total bridge count is `O(N * 2^N)`. This is **superexponential** growth: each new logic roughly doubles the number of intersection bundles AND each new bundle needs more bridges than before.

However, this is the theoretical worst case assuming all intersections are formalized. The **practical count** for CSLib is much smaller.

### Practical Estimate for CSLib (Next 3 Years)

Assuming 7 logics and only pairwise intersections formalized (semantically motivated ones):
- ~10-12 meaningful pairwise bundles
- 10-12 bridge instances total

This is very manageable. The superexponential blow-up only materializes if CSLib decides to formalize triple and higher-order intersection bundles systematically.

---

## 5. "Adding a New Logic" Story: Comparison

### Scenario: Adding `HybridConnectives` (7th Logic)

Hybrid logic adds nominals `i` and satisfaction operators `@_i`.

#### Under Flat Approach (current design + bridges):

Files that must change:
1. `Cslib/Foundations/Logic/Connectives.lean`:
   - Add `class HasNominal (F : Type*)` (or `HasAtNominal`, etc.)
   - Add `class HybridConnectives (F : Type*) extends ModalConnectives F, HasNominal F`
   - Add N bridge instances for each new pairwise bundle:
     - `instance [HybridConnectives F] : TemporalConnectives F`
     - `instance [HybridConnectives F] : EpistemicConnectives F` (if that exists)
     - etc. — one per existing logic that doesn't share `HasNominal`
   - Add N new intersection bundle classes (one per existing logic):
     - `class BimodalHybridConnectives (F : Type*) extends BimodalConnectives F, HasNominal F`
     - `class EpistemicHybridConnectives (F : Type*) extends EpistemicConnectives F, HasNominal F`
     - etc.
2. `Cslib/Logics/Hybrid/Syntax/Formula.lean`:
   - Define `Hybrid.Formula` inductive
   - Register `HasBot`, `HasImp`, `HasBox`, `HasNominal` instances
   - Register `HybridConnectives` instance

**Key burden**: Every existing logic now needs a new bridge instance for the hybrid case. If there are already 5 other logics, adding the 6th requires 5 new bridge instances plus 5 new intersection bundle declarations.

**Files changed**: 2 core files, plus potentially updating bimodal/other combination files.

#### Under `class abbrev` Approach:

Files that must change:
1. `Cslib/Foundations/Logic/Connectives.lean`:
   - Add `class HasNominal (F : Type*) where nominal : ...`
   - Add `class abbrev HybridConnectives (F : Type*) := ModalConnectives F, HasNominal F`
   - That's it — all N existing intersection bundles automatically gain hybrid variants when combined
2. `Cslib/Logics/Hybrid/Syntax/Formula.lean`:
   - Define `Hybrid.Formula` inductive
   - Register `HasBot`, `HasImp`, `HasBox`, `HasNominal` instances
   - `HybridConnectives`, `ModalConnectives`, `PropositionalConnectives` automatically synthesized

**Key advantage**: Zero bridge instances, zero new intersection bundle declarations. The `class abbrev` constructor registration means `Hybrid.Formula` automatically participates in ALL existing combination bundles that would logically include it.

**Files changed**: 2 files (same as flat approach), but dramatically less code in each.

#### Under True Diamond Approach:

Files that must change:
1. `Cslib/Foundations/Logic/Connectives.lean`:
   - Add `class HasNominal (F : Type*)`
   - Add `set_option structureDiamondWarning false in class HybridConnectives extends ModalConnectives F, HasNominal F`
   - Add N new diamond classes for each intersection:
     - `set_option structureDiamondWarning false in class BimodalHybridConn extends BimodalConnectives F, HybridConnectives F`
     - etc.
   - Similar declarative burden to flat approach, but using `set_option` instead of bridge instances
2. `Cslib/Logics/Hybrid/Syntax/Formula.lean`:
   - Same as other approaches

**Key difference from flat**: No bridge instances, but still need to declare intersection bundles explicitly. The `set_option` is mechanical but all intersection classes still need to be written.

### Verdict: `class abbrev` Wins the "New Logic" Story

| Approach | New atomic class | New bundle | New intersections declared | Bridge instances | Files changed |
|----------|-----------------|------------|--------------------------|-----------------|---------------|
| Flat+bridge | Yes | Yes, 1 | Yes, N new bundles | Yes, N bridges | 2 |
| `class abbrev` | Yes | Yes, 1 | **None** (automatic) | **None** | 2 |
| True diamond | Yes | Yes, 1 | Yes, N bundles + set_options | None | 2 |

The `class abbrev` approach is the only one where "adding a 7th logic" does not require updating any intersection bundle declarations. The contributor writes one atomic class and one bundle class — done.

---

## 6. How Mathlib Handles Growing Hierarchies

Mathlib's algebraic hierarchy (`Algebra/Group/Defs.lean`) provides a rich case study:

### Mathlib's Strategy: Extended + Bridge Instances at priority 100

Mathlib uses `class ... extends` (not `class abbrev`) for its main hierarchy. It manages diamonds through:

1. **Primary chain principle**: Each class has one main parent. `CommMonoid extends Monoid, CommSemigroup` (Monoid is primary).
2. **Bridge instances at priority 100**: When `CommGroup` (which has diamond paths) needs `CancelMonoid`, it adds:
   ```lean
   instance (priority := 100) CommGroup.toCancelCommMonoid : CancelCommMonoid G := ...
   instance (priority := 100) CommGroup.toDivisionCommMonoid : DivisionCommMonoid G := ...
   ```
3. **Lower cancel priority (75)**: `CancelCommMonoid.toCommMonoid` is registered at priority 75 to prevent eager synthesis loops.

### `class abbrev` in Mathlib: Currently Rare

Mathlib uses `class abbrev` in only **3 places** in the entire codebase:
- `IsAffineMonoid` (bundling `IsCancelMul`, `Monoid.FG`, `IsMulTorsionFree`)
- `IsAffineAddMonoid` (additive version)
- `CommGrpObj` (bundling `GrpObj`, `IsCommMonObj` in categorical context)

All three are **Prop-valued** or **predicate** bundles, not data-carrying class hierarchies. This suggests the Mathlib community uses `class abbrev` specifically for "property bundles" (conjunctions of propositions) rather than for structural class hierarchies that carry data.

**Critical insight for CSLib**: CSLib's connective bundles ARE data-carrying (they carry `bot`, `imp`, `box` field values). Mathlib's `class abbrev` examples are all Prop-valued. The behavior should be identical — `class abbrev` doesn't distinguish data vs. Prop — but the Mathlib precedent suggests the community may have concerns about `class abbrev` for data-carrying hierarchies that haven't yet surfaced.

### The "Lean Algebraic Hierarchy" Paper Perspective

From "Use and Abuse of Instance Parameters" (arXiv:2202.01629):
- Mathlib's diamond problem historically arose from propositionally equal but not definitionally equal fields
- The fix was careful instance ordering, not structural changes to the class system
- `class abbrev` was not the recommended fix for Mathlib's specific diamond issues

This suggests `class abbrev` is more appropriate for *predicate/property* bundles than for *structural/data* bundles in the algebraic hierarchy style.

---

## 7. Key Findings and Trade-offs

### Finding 1: Both Approaches Scale to N=5, But Differently

- **Flat + bridge**: Linear in practice (only meaningful intersections), but superexponential in theory. Manageable for CSLib's realistic scope of 5-8 intersection bundles.
- **`class abbrev`**: Constant overhead (0 bridge instances regardless of N). True O(N) scaling: N new logics = N new atomic classes + N new bundle abbrevs.
- **True diamond**: O(N^2) suppression lines (one per intersection class), but can collapse to O(1) with file-level `set_option`.

### Finding 2: `class abbrev` Has a Data-Carrying Class Caveat

Mathlib uses `class abbrev` only for Prop-valued bundles. CSLib's connective bundles carry data (`bot : F`, `imp : F → F → F`). While `class abbrev` should work identically for data and Prop, the absence of data-carrying `class abbrev` in Mathlib suggests potential unexplored edge cases with `instance` synthesis for data-heavy hierarchies. A branch test is warranted before committing.

### Finding 3: The Realistic Intersection Count Is Small

For logically coherent CSLib expansion over 5 years:
- Likely 5-8 pairwise intersections (not 10)
- At most 2-3 triple intersections (epistemic-temporal-modal, dynamic-epistemic-temporal)
- Bridge instances needed: 7-12 total

This makes the flat+bridge approach viable indefinitely if only practically relevant intersections are formalized.

### Finding 4: Stacked Diamonds Work in Lean 4

Lean 4's test suite (`diamond5.lean`) explicitly tests triple-shared-ancestor diamonds (`Semiring extends AddMonoid, Monoid` where both extend `Numeric`). Stacked diamonds compile correctly with `structureDiamondWarning false`. The definitional equality requirement holds for CSLib because each formula type uses exactly one constructor per operator.

### Finding 5: The "New Logic" Story Strongly Favors `class abbrev`

Under `class abbrev`, adding `EpistemicConnectives` requires:
- 1 new atomic class per new operator (`HasKnowledge`)
- 1 new bundle abbrev (`EpistemicConnectives`)
- 0 intersection declarations
- 0 bridge instances

Under flat+bridge, adding `EpistemicConnectives` requires:
- 1 new atomic class
- 1 new bundle class
- K new intersection declarations (one per existing logic)
- K new bridge instances (one per existing intersection)

Where K grows linearly with the number of existing logics. At N=7 logics, adding the 8th requires 7 new declarations and 7 bridge instances.

---

## Recommendations

### If `class abbrev` is Adopted (Recommended for Long-Term Scaling)

1. **Test first**: Create a branch with `class abbrev PropositionalConnectives`, `class abbrev ModalConnectives`, `class abbrev TemporalConnectives`, `class abbrev BimodalConnectives`. Run `lake test`. The automatic instance synthesis should preserve all existing behavior.

2. **Document the no-new-methods constraint**: The bundle classes cannot add new methods. Enforce by convention: connective bundles are purely bundling wrappers; operator-specific theorems live in the atomic `Has*` or formula-specific namespaces.

3. **Intersection classes become trivial**: `class abbrev EpistemicTemporalConnectives (F : Type*) := EpistemicConnectives F, HasUntil F, HasSince F` is a complete and correct definition.

### If Flat + Bridge is Maintained (Recommended for Conservatism)

1. **Add the missing bridge instances now** (before more proof-system classes accumulate):
   ```lean
   instance (priority := 100) instTemporalOfBimodal [BimodalConnectives F] :
       TemporalConnectives F where
     bot := HasBot.bot; imp := HasImp.imp; untl := HasUntil.untl; snce := HasSince.snce

   instance (priority := 100) instFutureTemporalOfBimodal [BimodalConnectives F] :
       FutureTemporalConnectives F where
     bot := HasBot.bot; imp := HasImp.imp; untl := HasUntil.untl
   ```

2. **Establish a policy for future logics**: Each new intersection bundle must immediately include bridge instances for all "missing" parent directions.

3. **At N=6 logics, revisit**: When CSLib has 6 or more logic bundles and the bridge instance count reaches 15+, switching to `class abbrev` will be clearly worthwhile.

---

## Confidence Assessment

| Claim | Confidence | Basis |
|-------|------------|-------|
| C(5,2)=10 pairwise diamonds with N=5 logics | **High** | Mathematical fact |
| `class abbrev` generates 0 bridge instances | **High** | Lean 4 docs; class abbrev registers constructor as instance |
| Bridge count is O(N * 2^N) in worst case | **High** | Combinatorial analysis |
| Stacked triples compile with structureDiamondWarning false | **High** | Lean 4 test suite diamond5.lean |
| Mathlib uses class abbrev only for Prop-valued bundles | **High** | Direct grep of mathlib/; 3 uses found |
| class abbrev works for data-carrying connective bundles | **Medium** | No direct precedent; theoretically sound |
| Realistic intersection count stays below 15 for 5 logics | **Medium** | Judgment about what CSLib actually needs; logic-dependent |
| N=7 is the threshold where flat+bridge becomes unwieldy | **Low** | Rule-of-thumb; depends on intersection count policy |
