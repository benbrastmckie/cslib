# Research Report: Tableau Deduplication and Dead Code Cleanup

**Task**: 325
**Session**: sess_1782300192_f99803_325
**Date**: 2026-06-24

## Overview

This report analyzes six deduplication and dead-code-removal items across the propositional
tableau modules. All items are confirmed viable with no blockers.

---

## Part A: Deduplication

### Item (1): Delete `minBranchSatisfied` from Minimal/Soundness.lean

**Current location**: `Cslib/Logics/Propositional/Tableau/Minimal/Soundness.lean`, lines 71-78.

**Finding**: `minBranchSatisfied` is character-for-character identical to `intBranchSatisfied`
(Intuitionistic/Soundness.lean, lines 55-62). Both expand to:

```lean
∀ sf ∈ b,
  (sf.sign = .pos → IForces val botForces (worldOf sf.label) sf.formula) ∧
  (sf.sign = .neg → ¬ IForces val botForces (worldOf sf.label) sf.formula)
```

**Usage analysis**: `minBranchSatisfied` is **never used in any proof term**. The soundness
proof in Minimal/Soundness.lean (line 94, 142) already uses `intBranchSatisfied`. The only
references are:
- Its definition (line 71)
- Module docstring mentions (lines 19, 38, 69)

**Action**: Delete the definition and update the module docstring to remove mentions. No
proof terms need modification since no code references this symbol.

**Risk**: None. The definition is completely unused.

---

### Item (2): Delete `minExtractValuation` from Minimal/Completeness.lean

**Current location**: `Cslib/Logics/Propositional/Tableau/Minimal/Completeness.lean`, lines 72-73.

**Finding**: `minExtractValuation` is character-for-character identical to `intExtractValuation`
(Intuitionistic/Completeness.lean, lines 57-58). Both expand to:

```lean
b.any (fun sf => sf.sign == .pos && sf.formula == .atom p && sf.label == w)
```

**Usage analysis**: Unlike `minBranchSatisfied`, `minExtractValuation` IS used in proof terms:
- `minTruthLemma` type signature (lines 169, 171)
- `minOpenBranch_countermodel` type signature (line 182)

However, all three lemmas that use it are `sorry`-bodies, so the references appear only in
type signatures, not in proof terms that need to type-check against internal structure.

**Action**: Delete `minExtractValuation` and replace all references with `intExtractValuation`.
Since `intExtractValuation` is imported via the chain:
`Minimal.Completeness` -> `Minimal.Soundness` -> `Intuitionistic.Soundness` -> `Intuitionistic.Expansion`,
and `Intuitionistic.Completeness` is imported via `Intuitionistic.Soundness`... Actually,
let me trace the imports:

- `Minimal/Completeness.lean` imports `Minimal/Soundness.lean`
- `Minimal/Soundness.lean` imports `Intuitionistic/Soundness.lean`
- `Intuitionistic/Soundness.lean` imports `Intuitionistic/Expansion.lean`

But `intExtractValuation` is defined in `Intuitionistic/Completeness.lean`, which is NOT in
this import chain. So we need to verify the import path.

**Import resolution**: `Minimal/Completeness.lean` currently imports `Minimal/Soundness.lean`
(which gets us `Intuitionistic/Soundness.lean`), but NOT `Intuitionistic/Completeness.lean`.
To use `intExtractValuation`, we need to either:
1. Add `public import Cslib.Logics.Propositional.Tableau.Intuitionistic.Completeness` to
   Minimal/Completeness.lean, or
2. Move `intExtractValuation` to a shared location.

**Recommended approach**: Option 1 is simplest -- add the import. The dependency is logical:
minimal completeness depends on intuitionistic completeness infrastructure.

**Risk**: Low. Adding an import may slightly increase build times but establishes the
correct logical dependency.

---

### Item (3): Naming consistency check

After dedup, the remaining valuation extraction functions are:
- `extractValuation` (Classical/Completeness.lean) -- type `Branch (Proposition Atom) Unit → BoolValuation Atom`
- `intExtractValuation` (Intuitionistic/Completeness.lean) -- type `IBranch Atom → Nat → Atom → Prop`

These are fundamentally different types (Bool vs Prop, Unit-labeled vs Nat-labeled). The
naming convention (prefix-less for classical, `int` prefix for intuitionistic/Kripke) is
consistent and self-documenting. No further renaming needed.

---

## Part B: Dead Code Removal

### Item (4): Remove `MinimalClosure` instance from ClosureCondition.lean

**Current location**: `Cslib/Foundations/Logic/Tableau/ClosureCondition.lean`, lines 118-135
(namespace + instance).

**Finding**: `isMinimallyClosed` (Intuitionistic/Expansion.lean:89) uses `Branch.hasContradiction`
directly, NOT the `MinimalClosure` typeclass instance. The code comment at line 86-88 explicitly
documents why:

> NOTE: The weaker `MinimalClosure` instance (atom-only) was previously used, but this
> is insufficient for correctness -- for example, `⊥ → ⊥` is minimally valid but the
> atom-only closure fails to close the branch containing T(⊥)/F(⊥) at the created world.

**Usage analysis**: Zero code references to `MinimalClosure` outside of:
- Its own namespace/instance definition (ClosureCondition.lean:118-135)
- Documentation comments in 4 files

No code uses `MinimalClosure.inst...` or resolves `ClosureCondition` to the `MinimalClosure`
instance via typeclass inference.

**Action**: Delete lines 116-135 (the `/-! ## Minimal Closure -/` section header through
`end MinimalClosure`). Update the module docstring to remove `MinimalClosure` from the table.

**Risk**: None. The instance is provably unused.

---

### Item (5): Remove `IsAtomic` typeclass and `instIsAtomicProposition`

**`IsAtomic` location**: `Cslib/Foundations/Logic/Tableau/ClosureCondition.lean`, lines 70-78.
**`instIsAtomicProposition` location**: `Cslib/Logics/Propositional/Tableau/Defs.lean`, lines 106-117.

**Finding**: `IsAtomic` is used ONLY by the `MinimalClosure` instance (ClosureCondition.lean:124,127).
`instIsAtomicProposition` is used ONLY by typeclass inference for `MinimalClosure`.

Full grep results for `IsAtomic` (code references only):
1. Class definition (ClosureCondition.lean:76-78)
2. `MinimalClosure` instance requirement (ClosureCondition.lean:124)
3. `MinimalClosure` instance body (ClosureCondition.lean:127)
4. Instance definition (Defs.lean:113-117)
5. Documentation comments (5 locations)

Since `MinimalClosure` is dead code (item 4), both `IsAtomic` and `instIsAtomicProposition`
are transitively dead.

**Action**: Delete `IsAtomic` class (ClosureCondition.lean:70-78) and `instIsAtomicProposition`
(Defs.lean:106-117). Update module docstrings in both files.

**Risk**: None. No downstream consumers exist.

---

### Item (6): Remove `atomContradiction` constructor from `ClosureReason`

**Current location**: `Cslib/Foundations/Logic/Tableau/Closure.lean`, line 60.

**Finding**: `atomContradiction` is used ONLY by the `MinimalClosure` instance
(ClosureCondition.lean:130). No other code constructs or pattern-matches on this constructor.

The Bimodal module has its OWN `ClosureReason` type
(`Cslib/Logics/Bimodal/Metalogic/Decidability/TraceCertificate.lean:66`) which is completely
separate and unaffected by this change.

No code in `Cslib/Foundations/` or `Cslib/Logics/Propositional/` pattern-matches on
`ClosureReason` constructors beyond `ClosureCondition.isClosed` which uses `.isSome`
(type-agnostic).

**Action**: Remove the `atomContradiction` constructor from the `ClosureReason` inductive type.
Update the module docstring.

**Risk**: Low but non-zero. Removing a constructor from an inductive type is a breaking API
change for any downstream code that:
- Pattern-matches on `ClosureReason` exhaustively (none found in codebase)
- Constructs `.atomContradiction` values (only `MinimalClosure`, being removed)

The risk is theoretical since no such code exists, but a `lake build` verification is
essential after this change.

---

## Implementation Order

Recommended order to minimize risk and enable incremental verification:

1. **Phase 1 (Dedup - no risk)**:
   - Delete `minBranchSatisfied` from Minimal/Soundness.lean, update docstrings
   - Delete `minExtractValuation` from Minimal/Completeness.lean, replace with
     `intExtractValuation`, add import

2. **Phase 2 (Dead code removal - low risk)**:
   - Delete `MinimalClosure` namespace from ClosureCondition.lean
   - Delete `IsAtomic` class from ClosureCondition.lean
   - Delete `instIsAtomicProposition` from Defs.lean
   - Delete `atomContradiction` constructor from Closure.lean
   - Update all module docstrings

3. **Phase 3 (Verification)**:
   - `lake build` to verify no breakage
   - `lake exe checkInitImports` to verify imports
   - `lake test` for regression

---

## Files to Modify

| File | Changes |
|------|---------|
| `Cslib/Logics/Propositional/Tableau/Minimal/Soundness.lean` | Delete `minBranchSatisfied` def + update docstrings |
| `Cslib/Logics/Propositional/Tableau/Minimal/Completeness.lean` | Delete `minExtractValuation` def, replace uses with `intExtractValuation`, add import, update docstrings |
| `Cslib/Foundations/Logic/Tableau/ClosureCondition.lean` | Delete `MinimalClosure` namespace + `IsAtomic` class + update docstrings |
| `Cslib/Foundations/Logic/Tableau/Closure.lean` | Delete `atomContradiction` constructor + update docstrings |
| `Cslib/Logics/Propositional/Tableau/Defs.lean` | Delete `instIsAtomicProposition` + `IsAtomic` section + update docstrings |

---

## Blockers

None identified. All items are confirmed safe to implement.

## Dependencies

No external dependencies. The task is self-contained within the propositional tableau module
hierarchy.
