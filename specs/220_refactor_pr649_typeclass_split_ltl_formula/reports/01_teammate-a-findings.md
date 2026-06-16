# Teammate A Findings: Primary Approach for PR #649 Refactor

## Key Findings

### 1. Connectives.lean Already Has the Right Foundation

The current `Cslib/Foundations/Logic/Connectives.lean` (from the PR) defines:
- `HasBot`, `HasImp`, `HasAnd`, `HasOr`, `HasBox`, `HasUntil`, `HasSince` — atomic typeclass per operator
- `PropositionalConnectives extends HasBot, HasImp`
- `ModalConnectives extends PropositionalConnectives, HasBox`
- `TemporalConnectives extends PropositionalConnectives, HasUntil, HasSince`
- `BimodalConnectives extends ModalConnectives, HasUntil, HasSince`

**Gap**: There is no `HasNext` typeclass and no `FutureTemporalConnectives` / `LTLConnectives` split. The refactor must add these without breaking the existing hierarchy.

### 2. Recommended Typeclass Hierarchy Changes

The hierarchy proposed in the task context maps cleanly to the existing code:

```
PropositionalConnectives  (HasBot + HasImp)   [UNCHANGED]
        |
FutureTemporalConnectives  (+ HasUntil)       [NEW]
       / \
LTLConnectives              TemporalConnectives
 (+ HasNext)                 (+ HasSince)     [MODIFIED: now extends FutureTemporalConnectives]
```

**Changes to Connectives.lean**:

1. Add `HasNext` typeclass:
```lean
/-- A type has a next-step (X) temporal operator. -/
class HasNext (F : Type*) where
  /-- The next-step operator: X(φ) = at the next time point φ holds. -/
  next : F → F
```

2. Add `FutureTemporalConnectives`:
```lean
/-- Future temporal connectives: propositional connectives plus until. -/
class FutureTemporalConnectives (F : Type*) extends PropositionalConnectives F, HasUntil F
```

3. Add `LTLConnectives`:
```lean
/-- LTL connectives: future temporal connectives plus next-step operator. -/
class LTLConnectives (F : Type*) extends FutureTemporalConnectives F, HasNext F
```

4. Modify `TemporalConnectives` to extend `FutureTemporalConnectives`:
```lean
/-- Temporal connectives: future temporal connectives plus since (past operator). -/
class TemporalConnectives (F : Type*) extends FutureTemporalConnectives F, HasSince F
```

5. Keep `BimodalConnectives` as-is but update to avoid diamond:
```lean
/-- Bimodal connectives: modal plus future temporal plus since. -/
class BimodalConnectives (F : Type*) extends ModalConnectives F, HasUntil F, HasSince F
```
Note: Diamond risk with ModalConnectives/FutureTemporalConnectives is avoided by NOT having `BimodalConnectives` extend `FutureTemporalConnectives` directly.

### 3. Formula.lean — What to Remove (ctchou's feedback)

Reviewers want to defer past-time operators to a later PR. The recommended removals from `Cslib/Logics/Temporal/Syntax/Formula.lean`:

**Must remove** (ctchou's explicit feedback):
- `public import Mathlib.Logic.Encodable.Basic`
- `public import Mathlib.Logic.Denumerable`  
- `public import Mathlib.Data.Finset.Basic`
- The entire `Countability` section (lines ~167–257): `encodeNat`, `encodeNat_injective`, `Countable`, `Infinite`, `Denumerable` instances
- `BEq` instances (lines ~259–333)
- `snce` constructor from `Formula` inductive
- `somePast`, `allPast`, `always`, `sometimes`, `weakPast`, `weakSince`, `strongTrigger`, `swapTemporal` (and related theorems), `atoms_swapTemporal`, `prev`, `trigger`
- Past-related notation: `S`, `𝐏`, `𝐇`, `△`, `▽`
- Update `TemporalConnectives` instance: remove `snce`

**Can keep**: `someFuture`, `allFuture`, `next`, `release`, `weakUntil`, `strongRelease`, `atoms`, `complexity`, `temporalDepth`, `countImplications`, `needsPositiveHypotheses`

**Update instance**: Change from `TemporalConnectives` to `FutureTemporalConnectives`:
```lean
instance : FutureTemporalConnectives (Formula Atom) where
  bot := .bot
  imp := .imp
  untl := .untl
```

### 4. New LTL.Formula File

Create `Cslib/Logics/LTL/Syntax/Formula.lean` (not in `Temporal/`):

```lean
namespace Cslib.Logic.LTL

/-- LTL formula type. Primitives: atoms, falsum, implication, next, until. -/
inductive Formula (Atom : Type u) : Type u where
  | atom (p : Atom)
  | bot
  | imp (φ₁ φ₂ : Formula Atom)
  | next (φ : Formula Atom)    -- X operator
  | untl (φ₁ φ₂ : Formula Atom)  -- U operator
deriving DecidableEq

instance : LTLConnectives (Formula Atom) where
  bot := .bot
  imp := .imp
  untl := .untl
  next := .next
```

Derived: `neg`, `top`, `or`, `and`, `iff`, `someFuture` (Fφ = ⊤ U φ), `allFuture` (Gφ = ¬F¬φ), `weakUntil`, `release`.

**Important**: `next` should NOT be derived from `untl` in `LTL.Formula` (as it is in the current `Temporal.Formula.next = φ U ⊥`). In the LTL formula type with the X constructor, `next` is primitive. The `HasNext` typeclass captures this.

### 5. Matthew's Abstraction: What It Means Concretely

Matthew's feedback is that MCS and DeductionTheorem for temporal/LTL can be abstracted using K, S, MP axioms. **This already exists in the codebase** — the key is `GenericMCS.lean` at `Cslib/Foundations/Logic/Metalogic/GenericMCS.lean`.

The `algebraicDerivationSystem` provides a free `DerivationSystem` from `MinimalHilbert`, and `algebraic_has_deduction_theorem` is the free deduction theorem. The `SetMaximalConsistent.closed_under_derivation`, `implication_property`, and `negation_complete` are all generic.

**Concrete implication**: A new LTL proof system only needs:
1. A tag type: `opaque LTL.HilbertLTL : Type := Empty`
2. A `DerivationTree` or equivalent inductive (with atom, bot, imp, next, until axioms + MP + structural rules)
3. `InferenceSystem`, `ClassicalHilbert`, and axiom instances
4. **The deduction theorem proof and Lindenbaum's lemma come for free from `GenericMCS`** if `MinimalHilbert` is instantiated

The current Temporal MCS (`MCS.lean`) manually proves `temporal_has_deduction_theorem` via explicit DerivationTree induction (DeductionTheorem.lean). This is NOT a consequence of GenericMCS — it IS the bridge to GenericMCS. Matthew's point is that this bridge approach (proving DeductionTheorem once, then getting everything else from the generic framework) should be used for all logics.

**The temporal `MCS.lean` is already following Matthew's pattern**: it uses `Metalogic.SetMaximalConsistent.closed_under_derivation` (from Consistency.lean) with `temporal_has_deduction_theorem`. The MCS witness proofs (`mcs_g_witness`, `mcs_h_witness`) are temporal-specific because they depend on G/H operators.

For a pure LTL logic (future-only), the MCS witness proof would only need `mcs_g_witness` (no `mcs_h_witness`). The deduction theorem proof would only handle 5 constructors (no `temporal_duality`, potentially no `temporal_necessitation` if next is primitive).

### 6. ProofSystem.lean Impact

Adding `FutureTemporalConnectives` and `HasNext` requires additions to `ProofSystem.lean`:

- New `TemporalNecessitation` for LTL (X-necessitation or just G-necessitation from K/S/MP + LTL axioms)
- New axiom typeclasses for LTL axioms (if a `LTLHilbert` proof system is defined in this PR)
- The `TemporalBXHilbert` class currently requires `[HasUntil F] [HasSince F]` — this should remain unchanged

The task description says the PR scope is `FutureTemporalConnectives` and `LTLConnectives` typeclasses + formula type; it does not require a complete LTL proof system in this PR.

### 7. Files Affected in the PR

**Minimal scope to address reviewer feedback**:

1. `Cslib/Foundations/Logic/Connectives.lean` — add `HasNext`, `FutureTemporalConnectives`, `LTLConnectives`; modify `TemporalConnectives` to extend `FutureTemporalConnectives`
2. `Cslib/Logics/Temporal/Syntax/Formula.lean` — remove past operators, Encodable/Countable/Infinite/Denumerable, BEq instances; update instance to `FutureTemporalConnectives`
3. `Cslib/Logics/LTL/Syntax/Formula.lean` — NEW FILE with LTL formula type + `LTLConnectives` instance

**Files that will need cascading updates** (due to `TemporalConnectives` becoming `extends FutureTemporalConnectives`):
- `Cslib/Logics/Temporal/ProofSystem/Instances.lean` — the instance chain may need review
- `Cslib/Foundations/Logic/ProofSystem.lean` — `TemporalBXHilbert` uses `[HasUntil F] [HasSince F]` explicitly; this should work unchanged since `TemporalConnectives` now extends `FutureTemporalConnectives` but the constraint is still `[HasUntil F] [HasSince F]`
- `Cslib/Logics/Bimodal/` — `BimodalConnectives` currently uses `TemporalConnectives`... need to verify no diamond

### 8. Diamond Risk Analysis

The diamond risk comes from `BimodalConnectives`. Current definition:
```lean
class BimodalConnectives extends ModalConnectives F, HasUntil F, HasSince F
```

If we introduce `FutureTemporalConnectives extends PropositionalConnectives, HasUntil`, then:
- `ModalConnectives extends PropositionalConnectives`
- `FutureTemporalConnectives extends PropositionalConnectives`

The existing `BimodalConnectives` does NOT extend `FutureTemporalConnectives` or `TemporalConnectives`. The comment in the code already says "to avoid a typeclass diamond". So the refactor should:
- NOT make `BimodalConnectives` extend `TemporalConnectives` or `FutureTemporalConnectives`
- Keep `BimodalConnectives` as `extends ModalConnectives F, HasUntil F, HasSince F`

This is safe because `HasUntil F` appears in both `BimodalConnectives` (directly) and `FutureTemporalConnectives` (via extends), but Lean 4's typeclass system handles this via `extends` diamond resolution: having `extends ... HasUntil F` twice resolves to one copy.

## Recommended Approach

**Phase 1**: Update `Connectives.lean`
- Add `HasNext` class after `HasSince`
- Add `FutureTemporalConnectives extends PropositionalConnectives F, HasUntil F`
- Add `LTLConnectives extends FutureTemporalConnectives F, HasNext F`
- Update `TemporalConnectives` to `extends FutureTemporalConnectives F, HasSince F`
- Keep `BimodalConnectives` as-is (already avoids diamond)
- Keep `ModalConnectives` as-is

**Phase 2**: Simplify `Temporal/Syntax/Formula.lean`
- Remove past-time operators (`snce`, `somePast`, `allPast`, `always`, `sometimes`, `weakPast`, `weakSince`, `swapTemporal`, `prev`, `trigger`, `strongTrigger`)
- Remove Countability/Enumerate/Infinite instances and imports
- Remove BEq manual proofs (keep `deriving DecidableEq`, which implies `BEq`)
- Update `TemporalConnectives` instance → `FutureTemporalConnectives` instance
- Keep `next` as a derived abbrev (since it's currently `φ U ⊥`)
- Update docstring to reflect future-only scope

**Phase 3**: Create `Cslib/Logics/LTL/Syntax/Formula.lean`
- Primitive `next` constructor (X operator)
- `LTLConnectives` instance
- Derived operators: `someFuture` (eventually), `allFuture` (globally), `neg`, `top`, `or`, `and`, `weakUntil`, `release`
- Notation scoped to `Cslib.Logic.LTL`
- New directory requires: `Cslib/Logics/LTL.lean` barrel, `lake exe mk_all` update

**Phase 4**: Cascading fixes
- Check `Temporal` metalogic and proof system files for references to `snce`/`TemporalConnectives` 
- The metalogic (`MCS.lean`, `DeductionTheorem.lean`) directly uses `Formula.snce` and `Formula.allPast` — these will break if `snce` is removed from `Temporal.Formula`
- Decision needed: either defer removing `snce` from `Temporal.Formula` (and only remove Encodable/BEq), OR split temporal formula into two files

## Evidence and Examples

### Precedent for minimal instance changes

`Cslib/Logics/Propositional/Defs.lean` shows the pattern:
```lean
instance : PropositionalConnectives (Proposition Atom) where
  bot := .bot
  imp := .imp
```
This is what `Temporal.Formula` should do for `FutureTemporalConnectives`.

### GenericMCS already abstracts Matthew's request

`GenericMCS.lean` line 47-61: `algebraicDerivationSystem` is fully generic over any `[MinimalHilbert S]`. Matthew's point is already implemented — the temporal MCS uses it via `temporal_has_deduction_theorem`.

### LTL formula next encoding

Current `Temporal.Formula.next` (abbrev, line ~413):
```lean
def next (φ : Formula Atom) : Formula Atom := .untl φ .bot
```
This encoding is valid for BX temporal logic semantics but NOT for LTL semantics on omega-executions where X is a primitive step. The new `LTL.Formula` should have a primitive `next` constructor to correctly capture LTL semantics.

## Critical Decision Point

The biggest implementation risk is whether to remove `snce` from `Temporal.Formula`. The metalogic files (`MCS.lean`, `DeductionTheorem.lean`, `GeneralizedNecessitation.lean`, `CompletenessHelpers.lean`, etc.) heavily use past operators. Removing `snce` from the formula type would require extensive changes to the existing `Temporal` metalogic.

**Recommended approach**: Keep `snce` in `Temporal.Formula` for now. Update the `TemporalConnectives` instance to still include `snce`. Only:
1. Remove the `Encodable/Countable/Infinite/Denumerable` instances and imports (unambiguous from ctchou's feedback)
2. Remove the manual `BEq` proofs (keep `deriving DecidableEq, BEq`)  
3. Add `FutureTemporalConnectives` + `LTLConnectives` + `HasNext` to `Connectives.lean`
4. Create a separate `LTL.Formula` with future-only primitives

The past operators in `Temporal.Formula` remain as-is (with the `TemporalConnectives` instance that includes `snce`), but the PR description explains they were NOT removed because the temporal metalogic depends on them. A follow-up PR can introduce a proper `Past.Formula` type.

## Confidence Level

**High confidence**:
- The typeclass hierarchy changes to `Connectives.lean` (adding `HasNext`, `FutureTemporalConnectives`, `LTLConnectives`, modifying `TemporalConnectives`)
- Removing Encodable/Countable/Infinite/Denumerable from Formula.lean
- The GenericMCS already handles Matthew's abstraction request
- The `BimodalConnectives` diamond analysis (keep as-is)

**Medium confidence**:
- Whether to remove `snce` from Temporal.Formula (depends on PR scope vs. preserving existing metalogic)
- Whether LTL.Formula should live at `Cslib/Logics/LTL/Syntax/Formula.lean` vs. somewhere else
- Whether the PR should include a `LTLHilbert` proof system tag type or just the formula type

**Low confidence**:
- Whether `HasNext` is the right name vs. `HasX` or `HasStep` (convention consistency check needed)
- Complete list of derived operators for LTL.Formula (depends on what ctchou means by "omega-executions")
