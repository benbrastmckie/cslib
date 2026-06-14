# Teammate A: Merge Feasibility and Import Graph

## 1. File Inventory and Line Counts

| Source File (to delete) | Lines | Target File (to absorb) | Lines | Merged Estimate |
|-------------------------|-------|--------------------------|-------|-----------------|
| `Completeness.lean` | 347 | `StrongCompleteness.lean` | 235 | ~530 |
| `IntCompleteness.lean` | 181 | `IntStrongCompleteness.lean` | 193 | ~330 |
| `MinCompleteness.lean` | 194 | `MinStrongCompleteness.lean` | 174 | ~320 |

All 6 files share the same namespace (`Cslib.Logic.PL`) and use identical `@[expose] public section` patterns. Merging requires no namespace changes.

## 2. Import Graph (Current State)

### Classical Chain

```
Semantics.Basic <-- Completeness.lean (public imports: Basic, MCS)
MCS <------------/
                      ^
                      |
StrongCompleteness.lean (public imports: SemanticConsequence, Completeness, Soundness)
```

### Intuitionistic Chain

```
Semantics.Kripke <-- IntCompleteness.lean (public imports: Kripke, IntLindenbaum)
IntLindenbaum <----/
                          ^
                          |
IntStrongCompleteness.lean (public imports: SemanticConsequence, IntSoundness, IntCompleteness)
```

### Minimal Chain

```
Semantics.Kripke <-- MinCompleteness.lean (public imports: Kripke, MinLindenbaum)
MinLindenbaum <----/
                          ^
                          |
MinStrongCompleteness.lean (public imports: SemanticConsequence, MinSoundness, MinCompleteness)
```

## 3. Consumer Analysis (Who Imports What)

### Source file consumers (files importing the 3 source files)

| Source File | Imported By |
|-------------|-------------|
| `Completeness.lean` | `StrongCompleteness.lean` (line 10), `Cslib.lean` (line 341) |
| `IntCompleteness.lean` | `IntStrongCompleteness.lean` (line 11), `Cslib.lean` (line 343) |
| `MinCompleteness.lean` | `MinStrongCompleteness.lean` (line 11), `Cslib.lean` (line 348) |

**Key finding**: The ONLY Lean file consumers of the source files are the corresponding target files. No other `.lean` file imports any of the three source files directly.

### Target file consumers (files importing the 3 target files)

| Target File | Imported By |
|-------------|-------------|
| `StrongCompleteness.lean` | `Cslib.lean` (line 353), `PropositionalConservativity.lean` (line 12), `Temporal/ConservativeExtension.lean` (line 12), `Modal/K/ConservativeExtension.lean` (line 11) |
| `IntStrongCompleteness.lean` | `Cslib.lean` (line 346) |
| `MinStrongCompleteness.lean` | `Cslib.lean` (line 351) |

### External declaration usage

The three external consumers of `StrongCompleteness.lean` all reference only `prop_completeness` (which already lives in `StrongCompleteness.lean`). No external file references any declaration from the source files:

- `canonicalValuation` -- 0 external references
- `prop_truth_lemma` (and sub-lemmas) -- 0 external references
- `IntCanonicalWorld`, `intCanonicalVal`, `int_truth_lemma` -- 0 external references
- `MinCanonicalWorld`, `minCanonicalVal`, `min_truth_lemma`, `minBotForces` -- 0 external references

## 4. Declarations to Move (Source -> Target)

### Completeness.lean -> StrongCompleteness.lean

| # | Declaration | Type | Lines |
|---|-------------|------|-------|
| 1 | `canonicalValuation` | def | 46-48 |
| 2 | `prop_truth_lemma_atom` | theorem | 54-59 |
| 3 | `prop_truth_lemma_bot` | theorem | 64-70 |
| 4 | `prop_truth_lemma_and` | theorem | 74-130 |
| 5 | `prop_truth_lemma_or` | theorem | 134-203 |
| 6 | `prop_truth_lemma_imp` | theorem | 207-320 |
| 7 | `prop_truth_lemma` | theorem | 330-345 |

**Name conflicts**: None. All 7 declarations have unique names not present in `StrongCompleteness.lean`.

### IntCompleteness.lean -> IntStrongCompleteness.lean

| # | Declaration | Type | Lines |
|---|-------------|------|-------|
| 1 | `IntCanonicalWorld` | def | 48-49 |
| 2 | `Preorder (IntCanonicalWorld Atom)` | instance | 52-55 |
| 3 | `intCanonicalVal` | def | 58-59 |
| 4 | `intCanonicalVal_upward_closed` | theorem | 62-65 |
| 5 | `int_truth_lemma` | theorem | 73-179 |

**Name conflicts**: None. All 5 declarations have unique names not present in `IntStrongCompleteness.lean`.

### MinCompleteness.lean -> MinStrongCompleteness.lean

| # | Declaration | Type | Lines |
|---|-------------|------|-------|
| 1 | `MinCanonicalWorld` | def | 54-55 |
| 2 | `Preorder (MinCanonicalWorld Atom)` | instance | 58-61 |
| 3 | `minCanonicalVal` | def | 64-65 |
| 4 | `minCanonicalVal_upward_closed` | theorem | 68-70 |
| 5 | `minBotForces` | def | 74-75 |
| 6 | `minBotForces_upward_closed` | theorem | 78-81 |
| 7 | `min_truth_lemma` | theorem | 90-192 |

**Name conflicts**: None. All 7 declarations have unique names not present in `MinStrongCompleteness.lean`.

## 5. Import Adjustments Required After Merge

### StrongCompleteness.lean (merged)

Current imports:
```lean
public import Cslib.Logics.Propositional.Semantics.SemanticConsequence
public import Cslib.Logics.Propositional.Metalogic.Completeness  -- DELETE
public import Cslib.Logics.Propositional.Metalogic.Soundness
```

After merge -- replace `Completeness` import with `Completeness.lean`'s own imports:
```lean
public import Cslib.Logics.Propositional.Semantics.SemanticConsequence  -- keeps Semantics.Basic transitively
public import Cslib.Logics.Propositional.Metalogic.MCS                 -- NEW (was via Completeness)
public import Cslib.Logics.Propositional.Metalogic.Soundness            -- unchanged
```

Note: `Semantics.Basic` is already transitively imported via `SemanticConsequence`, so no explicit import needed.

### IntStrongCompleteness.lean (merged)

Current imports:
```lean
public import Cslib.Logics.Propositional.Semantics.SemanticConsequence
public import Cslib.Logics.Propositional.Metalogic.IntSoundness
public import Cslib.Logics.Propositional.Metalogic.IntCompleteness  -- DELETE
```

After merge -- replace `IntCompleteness` import with `IntCompleteness.lean`'s own imports:
```lean
public import Cslib.Logics.Propositional.Semantics.SemanticConsequence  -- keeps Kripke transitively
public import Cslib.Logics.Propositional.Metalogic.IntSoundness         -- unchanged
public import Cslib.Logics.Propositional.Metalogic.IntLindenbaum        -- NEW (was via IntCompleteness)
```

Note: `Semantics.Kripke` is already transitively imported via `SemanticConsequence`, so no explicit import needed.

### MinStrongCompleteness.lean (merged)

Current imports:
```lean
public import Cslib.Logics.Propositional.Semantics.SemanticConsequence
public import Cslib.Logics.Propositional.Metalogic.MinSoundness
public import Cslib.Logics.Propositional.Metalogic.MinCompleteness  -- DELETE
```

After merge -- replace `MinCompleteness` import with `MinCompleteness.lean`'s own imports:
```lean
public import Cslib.Logics.Propositional.Semantics.SemanticConsequence  -- keeps Kripke transitively
public import Cslib.Logics.Propositional.Metalogic.MinSoundness         -- unchanged
public import Cslib.Logics.Propositional.Metalogic.MinLindenbaum        -- NEW (was via MinCompleteness)
```

### Cslib.lean (barrel file)

Remove the 3 deleted file imports:
```
Line 341: public import Cslib.Logics.Propositional.Metalogic.Completeness     -- DELETE
Line 343: public import Cslib.Logics.Propositional.Metalogic.IntCompleteness  -- DELETE
Line 348: public import Cslib.Logics.Propositional.Metalogic.MinCompleteness  -- DELETE
```

The Strong* files remain in the barrel and will export all declarations after merge.

## 6. Circular Import Risk Assessment

**Risk: NONE.**

After merging:
- `StrongCompleteness` will import `MCS` and `Soundness` (neither imports `StrongCompleteness`)
- `IntStrongCompleteness` will import `IntLindenbaum` and `IntSoundness` (neither imports `IntStrongCompleteness`)
- `MinStrongCompleteness` will import `MinLindenbaum` and `MinSoundness` (neither imports `MinStrongCompleteness`)

The import direction is strictly one-way: infrastructure files -> completeness files. No cycles.

## 7. `public import` Propagation Analysis

All 3 source files use `public import`, meaning their imports are re-exported to their consumers. This is important:

| Source File | Re-exports | Consumer | After Delete: Consumer Must... |
|-------------|------------|----------|-------------------------------|
| `Completeness.lean` | `Semantics.Basic`, `MCS` | `StrongCompleteness.lean` | Add `MCS` import (Basic already covered by SemanticConsequence) |
| `IntCompleteness.lean` | `Semantics.Kripke`, `IntLindenbaum` | `IntStrongCompleteness.lean` | Add `IntLindenbaum` import (Kripke already covered by SemanticConsequence) |
| `MinCompleteness.lean` | `Semantics.Kripke`, `MinLindenbaum` | `MinStrongCompleteness.lean` | Add `MinLindenbaum` import (Kripke already covered by SemanticConsequence) |

Since the Strong* files are the ONLY consumers (besides `Cslib.lean`), and since the Strong* files will absorb the content, this is cleanly handled.

For `Cslib.lean` (the barrel file): since all imports in `Cslib.lean` are `public import` and the barrel file also imports the Strong* variants, all declarations remain transitively accessible to anything importing `Cslib`. The only concern is whether removing lines 341, 343, 348 would cause any module that imports `Cslib` to lose transitive access -- but since the merged Strong* files will themselves `public import` the same dependencies (MCS, IntLindenbaum, MinLindenbaum), the transitive closure is preserved.

## 8. Merge Ordering Recommendation

For each source -> target merge, the canonical model infrastructure should be placed **before** the strong completeness content, because the strong completeness theorems use the canonical model definitions. Recommended section order in each merged file:

1. Imports (adjusted per Section 5)
2. `@[expose] public section` / `namespace Cslib.Logic.PL`
3. **[FROM SOURCE]** Canonical Model section (defs, instances, truth lemma helpers)
4. **[FROM SOURCE]** Truth Lemma
5. **[EXISTING TARGET]** Strong Soundness
6. **[EXISTING TARGET]** Helper lemmas
7. **[EXISTING TARGET]** Strong Completeness
8. **[EXISTING TARGET]** Biconditional / Compactness / Weak Completeness corollaries
9. `end Cslib.Logic.PL`

## 9. Summary of Required Changes

### Files to edit (3):
1. `StrongCompleteness.lean` -- replace Completeness import with MCS; insert canonical model content before existing
2. `IntStrongCompleteness.lean` -- replace IntCompleteness import with IntLindenbaum; insert canonical model content
3. `MinStrongCompleteness.lean` -- replace MinCompleteness import with MinLindenbaum; insert canonical model content

### Files to delete (3):
1. `Completeness.lean`
2. `IntCompleteness.lean`
3. `MinCompleteness.lean`

### Files to update (1):
1. `Cslib.lean` -- remove 3 import lines (341, 343, 348), then regenerate with `lake exe mk_all --module`

### Verification:
1. `lake build` must pass (all merged files compile, no missing imports)
2. `lake exe checkInitImports` (barrel file correct)
3. `lake exe lint-style` (style linting)
4. No external files need updating -- the 3 external consumers of `StrongCompleteness.lean` use only `prop_completeness`, which stays in `StrongCompleteness.lean`

## 10. Risk Assessment

| Risk | Level | Mitigation |
|------|-------|------------|
| Name conflicts | **None** | Verified: zero overlapping declaration names between source and target |
| Circular imports | **None** | Import direction strictly one-way after merge |
| Broken external consumers | **None** | External files only use `prop_completeness` from StrongCompleteness.lean |
| Missing transitive imports | **Low** | Solved by adding MCS / IntLindenbaum / MinLindenbaum imports explicitly |
| Merged file too large | **Low** | Largest merged file ~530 lines (classical), well within norms |

**Overall feasibility: FULLY FEASIBLE, no blockers identified.**
