# Teammate C Findings: Downstream Impact and CI Verification Strategy

## 1. Complete Downstream Consumer Map

### 1.1 Files Being Deleted (the "Legacy 3")

| File | Lines | Content |
|------|-------|---------|
| `Completeness.lean` | 347 | `canonicalValuation`, `prop_truth_lemma` (+ 5 helpers) |
| `IntCompleteness.lean` | 181 | `IntCanonicalWorld`, `intCanonicalVal`, `int_truth_lemma` (+ upward-closedness) |
| `MinCompleteness.lean` | 194 | `MinCanonicalWorld`, `minCanonicalVal`, `min_truth_lemma`, `minBotForces` (+ upward-closedness) |

### 1.2 Direct Import Consumers

Each legacy file has **exactly one** direct consumer:

| Legacy File | Direct Consumer | Import Line |
|-------------|----------------|-------------|
| `Completeness.lean` | `StrongCompleteness.lean` | Line 10: `public import Cslib.Logics.Propositional.Metalogic.Completeness` |
| `IntCompleteness.lean` | `IntStrongCompleteness.lean` | Line 11: `public import Cslib.Logics.Propositional.Metalogic.IntCompleteness` |
| `MinCompleteness.lean` | `MinStrongCompleteness.lean` | Line 11: `public import Cslib.Logics.Propositional.Metalogic.MinCompleteness` |

**No other file anywhere in the codebase directly imports any of the 3 legacy files.** This is the critical finding: the merge is a 1:1 collapse, not a fan-out refactor.

### 1.3 Declaration Usage Outside Source Files

**Completeness.lean declarations:**
- `canonicalValuation`: Used in `StrongCompleteness.lean` lines 178, 181, 182, 184 (4 uses, all in `prop_strong_completeness` proof)
- `prop_truth_lemma`: Used in `StrongCompleteness.lean` lines 179, 185 (2 uses, same proof)
- Helper lemmas (`prop_truth_lemma_atom`, `_bot`, `_and`, `_or`, `_imp`): **Used only internally** within `prop_truth_lemma` itself; no external consumers

**IntCompleteness.lean declarations:**
- `IntCanonicalWorld`: Used in `IntStrongCompleteness.lean` line 113
- `intCanonicalVal`: Used in `IntStrongCompleteness.lean` lines 115, 123, 127, 128
- `intCanonicalVal_upward_closed`: Used in `IntStrongCompleteness.lean` line 129
- `int_truth_lemma`: Used in `IntStrongCompleteness.lean` lines 117, 125

**MinCompleteness.lean declarations:**
- `MinCanonicalWorld`: Used in `MinStrongCompleteness.lean` line 95
- `minCanonicalVal`: Used in `MinStrongCompleteness.lean` lines 97, 105, 109, 110
- `minCanonicalVal_upward_closed`: Used in `MinStrongCompleteness.lean` line 111
- `minBotForces`: Used in `MinStrongCompleteness.lean` lines 97, 105, 109, 112
- `minBotForces_upward_closed`: Used in `MinStrongCompleteness.lean` line 112
- `min_truth_lemma`: Used in `MinStrongCompleteness.lean` lines 99, 107

### 1.4 Cslib.lean Barrel File Entries

Three entries must be removed from `Cslib.lean`:
- Line 341: `public import Cslib.Logics.Propositional.Metalogic.Completeness`
- Line 343: `public import Cslib.Logics.Propositional.Metalogic.IntCompleteness`
- Line 348: `public import Cslib.Logics.Propositional.Metalogic.MinCompleteness`

The corresponding `StrongCompleteness` entries already exist and will continue to serve.

## 2. Conservative Extension Files Analysis

### 2.1 Modal K Conservative Extension

**File**: `Cslib/Logics/Modal/Metalogic/Systems/K/ConservativeExtension.lean`
**Import**: Line 11: `public import Cslib.Logics.Propositional.Metalogic.StrongCompleteness`
**Usage**: Line 50: `prop_completeness (toModal_valid_implies_tautology ...)`

**STATUS: SAFE.** This file imports `StrongCompleteness`, not `Completeness`. The theorem `prop_completeness` is defined in `StrongCompleteness.lean` (line 221). No change needed.

### 2.2 Temporal BX Conservative Extension

**File**: `Cslib/Logics/Temporal/ConservativeExtension.lean`
**Import**: Line 12: `public import Cslib.Logics.Propositional.Metalogic.StrongCompleteness`
**Usage**: Line 90: `apply prop_completeness`

**STATUS: SAFE.** Same analysis as Modal K. No change needed.

### 2.3 Bimodal TM Conservative Extension

**File**: `Cslib/Logics/Bimodal/Metalogic/ConservativeExtension/PropositionalConservativity.lean`
**Import**: Line 12: `public import Cslib.Logics.Propositional.Metalogic.StrongCompleteness`
**Usage**: Line 119: `apply prop_completeness`

**STATUS: SAFE.** Same analysis. No change needed.

### 2.4 Summary: Zero Conservative Extension Impact

All three conservative extension files already import `StrongCompleteness.lean` directly, NOT the legacy `Completeness.lean`. They use `prop_completeness` which is defined in `StrongCompleteness.lean`. After the merge, these files will continue to work with zero changes.

## 3. Soundness Files Check

No soundness file imports any completeness file:
- `Soundness.lean` imports: `Semantics.Basic`, `ProofSystem.Derivation`, `ProofSystem.Axioms`
- `IntSoundness.lean` imports: `Semantics.Kripke`, `ProofSystem.Derivation`, `ProofSystem.Axioms`
- `MinSoundness.lean` imports: `Semantics.Kripke`, `ProofSystem.Derivation`, `ProofSystem.Axioms`

**STATUS: No circular dependency risk. No change needed.**

## 4. MCS and Lindenbaum Dependency Direction

### 4.1 Dependency Graph

```
MCS.lean
  <- DeductionTheorem.lean

Completeness.lean
  <- Semantics.Basic
  <- MCS.lean

IntLindenbaum.lean
  <- DeductionTheorem.lean
  <- MCS.lean
  <- Soundness.lean

IntCompleteness.lean
  <- Semantics.Kripke
  <- IntLindenbaum.lean

MinLindenbaum.lean
  <- DeductionTheorem.lean
  <- Soundness.lean

MinCompleteness.lean
  <- Semantics.Kripke
  <- MinLindenbaum.lean
```

### 4.2 Key Observation: One-Way Dependency

The completeness files import MCS/Lindenbaum. **Neither MCS nor any Lindenbaum file imports any completeness file.** The dependency is strictly downward:

```
MCS/Lindenbaum -> Completeness -> StrongCompleteness
                  ^^^^^^^^^^^^^
                  (being eliminated)
```

This means:
- MCS.lean and all Lindenbaum files are UNAFFECTED by the deletion
- The merged StrongCompleteness files just need to absorb the legacy imports

### 4.3 Merge Feasibility

After merging, each StrongCompleteness file will need these imports:

**StrongCompleteness.lean** (merged):
```lean
public import Cslib.Logics.Propositional.Semantics.Basic       -- from Completeness.lean
public import Cslib.Logics.Propositional.Metalogic.MCS          -- from Completeness.lean
public import Cslib.Logics.Propositional.Semantics.SemanticConsequence  -- already present
public import Cslib.Logics.Propositional.Metalogic.Soundness    -- already present
```

Note: `Semantics.Basic` is likely transitively available via `SemanticConsequence`, so only `MCS` may be genuinely new. This should be verified.

**IntStrongCompleteness.lean** (merged):
```lean
public import Cslib.Logics.Propositional.Semantics.Kripke       -- from IntCompleteness.lean
public import Cslib.Logics.Propositional.Metalogic.IntLindenbaum -- from IntCompleteness.lean
public import Cslib.Logics.Propositional.Semantics.SemanticConsequence  -- already present
public import Cslib.Logics.Propositional.Metalogic.IntSoundness  -- already present
```

Note: `IntLindenbaum` already imports `MCS` and `Soundness`. `Kripke` may come transitively via `SemanticConsequence`. Verify.

**MinStrongCompleteness.lean** (merged):
```lean
public import Cslib.Logics.Propositional.Semantics.Kripke        -- from MinCompleteness.lean
public import Cslib.Logics.Propositional.Metalogic.MinLindenbaum  -- from MinCompleteness.lean
public import Cslib.Logics.Propositional.Semantics.SemanticConsequence  -- already present
public import Cslib.Logics.Propositional.Metalogic.MinSoundness   -- already present
```

Same analysis as IntStrongCompleteness.

## 5. CI Verification Plan

### 5.1 Recommended Execution Order

**Phase 1: Merge content into strong completeness files**
1. For each pair (Completeness -> StrongCompleteness, Int*, Min*):
   a. Copy the legacy file's imports into the strong completeness file (add any not already present)
   b. Copy the legacy file's declarations (definitions, theorems) into the strong completeness file, inserting them BEFORE the first theorem that references them
   c. Remove the `import` of the legacy file from the strong completeness file
   d. Preserve the `@[expose] public section` and `namespace` structure

**Phase 2: Update Cslib.lean**
2. Run `lake exe mk_all --module` to regenerate `Cslib.lean` (this removes the 3 deleted files automatically)
   - Alternatively, manually remove lines 341, 343, 348 from `Cslib.lean`

**Phase 3: Delete legacy files**
3. Delete the 3 files:
   - `Cslib/Logics/Propositional/Metalogic/Completeness.lean`
   - `Cslib/Logics/Propositional/Metalogic/IntCompleteness.lean`
   - `Cslib/Logics/Propositional/Metalogic/MinCompleteness.lean`

**Phase 4: Verify**
4. Run verification in order:
   ```bash
   # Step 1: Build just the modified modules first (fast feedback)
   lake build Cslib.Logics.Propositional.Metalogic.StrongCompleteness
   lake build Cslib.Logics.Propositional.Metalogic.IntStrongCompleteness
   lake build Cslib.Logics.Propositional.Metalogic.MinStrongCompleteness

   # Step 2: Build downstream consumers (conservative extensions)
   lake build Cslib.Logics.Modal.Metalogic.Systems.K.ConservativeExtension
   lake build Cslib.Logics.Temporal.ConservativeExtension
   lake build Cslib.Logics.Bimodal.Metalogic.ConservativeExtension.PropositionalConservativity

   # Step 3: Full project build
   lake build

   # Step 4: Full CI pipeline
   lake exe checkInitImports
   lake exe lint-style
   lake test
   lake exe mk_all --module  # verify barrel is up to date
   ```

### 5.2 Why This Order Matters

- Phase 1 before Phase 3: The strong completeness files currently import the legacy files. If we delete first, the build breaks immediately. Merge first to make the deletion safe.
- `lake exe mk_all --module` after deletion: This regenerates `Cslib.lean` to remove the 3 deleted modules. Running it before deletion would be a no-op.
- Scoped builds before full build: Catches import errors in the modified files without waiting for the full 30+ minute build.

## 6. Risk Assessment

### 6.1 Low-Risk Areas (Confirmed Safe)

- **Conservative extension files**: All import `StrongCompleteness`, not `Completeness`. Zero changes needed.
- **Soundness files**: No completeness imports. Zero impact.
- **MCS/Lindenbaum files**: Upstream of completeness, not downstream. Zero impact.
- **Modal/Temporal/Bimodal completeness files**: These are separate completeness proofs for modal, temporal, and bimodal logics. They do NOT import the propositional completeness files.
- **Namespace collisions**: All 3 legacy files use namespace `Cslib.Logic.PL`, same as the strong completeness files. Since the declarations are being moved into the same namespace, no fully-qualified name changes are needed.

### 6.2 Medium-Risk Areas

- **Import transitivity**: When merging imports, some may be redundant due to transitive closure. For example, `SemanticConsequence` may already transitively import `Semantics.Basic`. Running `lake shake` after the merge will identify and clean up redundant imports. This is NOT a correctness risk, only a cleanliness issue.
- **Declaration order**: When inserting legacy content into the strong completeness file, the canonical valuation and truth lemma must appear BEFORE the strong completeness theorem that uses them. The natural insertion point is after the current imports section and before the "Strong Soundness" section.
- **File size**: The merged `StrongCompleteness.lean` will be ~582 lines (347 + 235). This is larger but not unreasonable for a single self-contained completeness proof.

### 6.3 Edge Cases

- **`@[expose] public section` scope**: Both legacy and strong completeness files use this pattern. When merging, only one `@[expose] public section` is needed at the top. The legacy file's `@[expose] public section` should be removed during merge, keeping only the strong completeness file's version.
- **`module` declaration**: Both files start with `module`. This is a per-file declaration and should be kept only once in the merged file.
- **Variable declarations**: Both `Completeness.lean` and `StrongCompleteness.lean` declare `variable {Atom : Type*}`. The merged file should have a single declaration. The IntStrong and MinStrong files use `variable {Atom : Type u}` with `universe u`, which the legacy Int and Min files also use -- consistent, no conflict.
- **`attribute [local instance] Classical.propDecidable`**: Present in `StrongCompleteness.lean` (line 55) but NOT in `Completeness.lean`. Since `Completeness.lean`'s proofs don't need it (they use constructive reasoning for the truth lemma), this is fine -- the attribute applies to the subsequent proofs.
- **`open Cslib.Logic.Helpers`**: Present in `StrongCompleteness.lean` (line 49) but NOT in `Completeness.lean`. The legacy content does not use `Helpers`, so no conflict.

### 6.4 Potential Gotchas

1. **mk_all vs manual barrel update**: If `lake exe mk_all --module` is run BEFORE deleting the files, it will re-add them. Delete first, then run `mk_all`, or manually edit `Cslib.lean`.
   - **Recommendation**: Delete files, then run `lake exe mk_all --module`.
   - **But wait**: We said merge first, delete second. The correct sequence is: merge -> delete -> mk_all -> build.

2. **Lean module caching**: After deleting files, old `.olean` files may linger. `lake build` should handle this, but if issues arise, `lake clean && lake build` resolves it.

3. **Git history**: After merging, the original file history is preserved in git for the strong completeness files (they're being edited, not recreated). The deleted files' history is preserved in git history.

## 7. Summary Dependency Table

| File to Delete | Only Consumer | Declarations to Move | Consumer Needs Changes |
|---------------|---------------|---------------------|----------------------|
| `Completeness.lean` (347 lines) | `StrongCompleteness.lean` | `canonicalValuation`, `prop_truth_lemma` + 5 helpers | Replace import, insert content |
| `IntCompleteness.lean` (181 lines) | `IntStrongCompleteness.lean` | `IntCanonicalWorld`, `intCanonicalVal`, `intCanonicalVal_upward_closed`, `int_truth_lemma` | Replace import, insert content |
| `MinCompleteness.lean` (194 lines) | `MinStrongCompleteness.lean` | `MinCanonicalWorld`, `minCanonicalVal`, `minCanonicalVal_upward_closed`, `minBotForces`, `minBotForces_upward_closed`, `min_truth_lemma` | Replace import, insert content |

**Total files needing changes**: 3 (the 3 strong completeness files) + `Cslib.lean` barrel
**Total files needing deletion**: 3 (the 3 legacy files)
**Total files unaffected**: Everything else (conservative extensions, soundness, MCS, Lindenbaum, modal/temporal/bimodal completeness)
