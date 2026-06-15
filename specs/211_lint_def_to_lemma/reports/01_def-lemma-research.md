# Research Report: Task 211 -- Change def to lemma/theorem for Prop-valued declarations

## Summary

The `defLemma` linter (via `lake lint`) identifies exactly **55 declarations** across 20 files where `def` is used for Prop-valued results that should be `lemma` or `theorem`. All 55 are safe to change with no downstream unfolding dependencies.

## Methodology

1. Ran `lake lint` to obtain the full linter report (837 total errors across 17 linters)
2. Extracted the 55 `defLemma` errors
3. Searched all 55 declaration names for `unfold`, `delta`, `simp [...]`, `rw [...]` usage -- found **zero** downstream unfolding
4. Read each flagged declaration to classify as `lemma` vs `theorem`
5. Identified special cases requiring annotation removal (`@[reducible]`, `abbrev`)

## Key Finding: Zero Downstream Unfolding Risk

When changing `def` to `lemma`/`theorem`, the body becomes opaque (cannot be unfolded by `simp`, `unfold`, `delta`, etc.). A codebase-wide search confirms that **none of the 55 flagged declarations are ever unfolded** -- they are all used via term-level application (e.g., `bxForwardWitness w ψ h_F`), which works identically for `def`, `lemma`, and `theorem`.

## Special Cases

### 1. `abbrev` declarations (3 declarations)

Three declarations use `abbrev` (which Lean stores as `@[reducible, inline] def`):
- `Cslib.Logic.Modal.completeness` (S5/Completeness.lean:92) -- `abbrev completeness := @s5_completeness`
- `Cslib.Logic.Bimodal.Theorems.Propositional.wrap'` (Connectives.lean:44) -- `abbrev wrap' ... := wrap d`
- `Cslib.Logic.Bimodal.Metalogic.Bundle.canonicalRTransitive` (CanonicalFrame.lean:247) -- `abbrev canonicalRTransitive := @existsTask_transitive`

**Fix**: Change `abbrev` to `theorem` (for `completeness`) or `lemma` (for `wrap'`, `canonicalRTransitive`), keeping the same body. The `abbrev` keyword is unnecessary since these are proofs and proof irrelevance makes reducibility meaningless.

### 2. `@[reducible]` annotated declarations (3 declarations)

Three declarations have `@[reducible]` which becomes meaningless on `lemma`/`theorem`:
- `DenseTemporalFrame.mk'` (FrameClass.lean:222) -- `@[reducible] def`
- `DiscreteTemporalFrame.mk'` (FrameClass.lean:230) -- `@[reducible] def`
- `chronicle_densely_ordered_dense` (DenseCompleteness.lean:196) -- `@[reducible] def`
- `derivesNegFromInconsistentExtension` (MaximalConsistent.lean:148) -- `@[reducible] noncomputable def`

**Fix**: Remove `@[reducible]` when changing to `lemma`. These are all used via term application, not unfolding.

### 3. `noncomputable` declarations (majority)

Most declarations (~45 of 55) use `noncomputable def` because they involve classical reasoning (Lindenbaum's lemma, propDecidable, etc.). The `noncomputable` keyword is compatible with `lemma`/`theorem` in Lean 4 -- change to `noncomputable lemma`.

## Complete Inventory by File

### Bimodal FrameConditions (3 declarations)

| File | Line | Declaration | Change to | Notes |
|------|------|-------------|-----------|-------|
| FrameConditions/FrameClass.lean | 218 | `DenseTemporalFrame.mk'` | `lemma` | Remove `@[reducible]` |
| FrameConditions/FrameClass.lean | 226 | `DiscreteTemporalFrame.mk'` | `lemma` | Remove `@[reducible]` |
| FrameConditions/Soundness.lean | 30 | `soundnessOver` | `theorem` | Parameterized soundness theorem |

### Bimodal Metalogic Core (9 declarations)

| File | Line | Declaration | Change to | Notes |
|------|------|-------------|-----------|-------|
| Core/MaximalConsistent.lean | 97 | `bimodalClosedUnderDerivation` | `lemma` | `noncomputable` |
| Core/MaximalConsistent.lean | 107 | `bimodalImplicationProperty` | `lemma` | `noncomputable` |
| Core/MaximalConsistent.lean | 117 | `bimodalNegationComplete` | `lemma` | `noncomputable` |
| Core/MaximalConsistent.lean | 142 | `derivesNegFromInconsistentExtension` | `lemma` | Remove `@[reducible]`, `noncomputable` |
| Core/MaximalConsistent.lean | 176 | `maximalConsistentClosed` | `lemma` | `noncomputable` |
| Core/MaximalConsistent.lean | 191 | `maximalNegationComplete` | `lemma` | `noncomputable` |
| Core/MaximalConsistent.lean | 208 | `theoremInMcs` | `lemma` | `noncomputable` |
| Core/MCSProperties.lean | 199 | `theoremInMcsFc` | `lemma` | `noncomputable` |
| Core/DeductionTheorem.lean | 219 | `bimodalHasDeductionTheorem` | `lemma` | Proves `HasDeductionTheorem` |

### Bimodal Metalogic Bundle (1 declaration)

| File | Line | Declaration | Change to | Notes |
|------|------|-------------|-----------|-------|
| Bundle/CanonicalFrame.lean | 246 | `canonicalRTransitive` | `lemma` | `abbrev` -> `lemma`, alias for `existsTask_transitive` |

### Bimodal BXCanonical (16 declarations)

| File | Line | Declaration | Change to | Notes |
|------|------|-------------|-----------|-------|
| BXCanonical/Frame.lean | 63 | `gContentClosedDerivation` | `lemma` | `noncomputable` |
| BXCanonical/Frame.lean | 78 | `hContentClosedDerivation` | `lemma` | `noncomputable` |
| BXCanonical/Frame.lean | 168 | `bxForwardWitness` | `lemma` | `noncomputable`, proves existential |
| BXCanonical/Frame.lean | 177 | `bxBackwardWitness` | `lemma` | `noncomputable`, proves existential |
| BXCanonical/Frame.lean | 195 | `bxGBackward` | `lemma` | `noncomputable`, proves existential |
| BXCanonical/Frame.lean | 245 | `bxHBackward` | `lemma` | `noncomputable`, proves existential |
| BXCanonical/Frame.lean | 305 | `bxModalWitness` | `lemma` | `noncomputable`, proves existential |
| BXCanonical/Frame.lean | 443 | `bxUntilEventualityResolution` | `lemma` | `noncomputable` |
| BXCanonical/Frame.lean | 454 | `bxSinceEventualityResolution` | `lemma` | `noncomputable` |
| BXCanonical/CanonicalModel.lean | 93 | `bxModalWitnessFc` | `lemma` | `noncomputable`, proves existential |
| BXCanonical/Chronicle/ChronicleToCountermodel.lean | 84 | `limitDomSubtypeIsSuccArchimedean` | `lemma` | Provides typeclass evidence |
| BXCanonical/Chronicle/ChronicleToCountermodelBasic.lean | 225 | `limitDomSubtypeDenselyOrderedFromF'T` | `lemma` | Provides typeclass evidence |
| BXCanonical/Chronicle/CounterexampleElimination.lean | 352 | `eliminateC5Counterexample` | `lemma` | `noncomputable` |
| BXCanonical/Chronicle/CounterexampleElimination.lean | 403 | `eliminateC5'Counterexample` | `lemma` | `noncomputable` |
| BXCanonical/Chronicle/CounterexampleElimination.lean | 458 | `eliminateGPropCounterexample` | `lemma` | `noncomputable` |
| BXCanonical/Chronicle/CounterexampleElimination.lean | 499 | `eliminateHPropCounterexample` | `lemma` | `noncomputable` |

### Bimodal BXCanonical Chronicle PointInsertion (5 declarations)

| File | Line | Declaration | Change to | Notes |
|------|------|-------------|-----------|-------|
| BXCanonical/Chronicle/PointInsertion.lean | 171 | `lemma_2_4` | `theorem` | `noncomputable`, Burgess 1982 named result |
| BXCanonical/Chronicle/PointInsertion.lean | 333 | `lemma_2_6` | `theorem` | `noncomputable`, Burgess 1982 named result |
| BXCanonical/Chronicle/PointInsertion.lean | 458 | `gPropagationWitness` | `lemma` | `noncomputable` |
| BXCanonical/Chronicle/PointInsertion.lean | 3363 | `lemma_2_4_with_guard` | `theorem` | `noncomputable`, strengthened Burgess Lemma 2.4 |
| BXCanonical/Chronicle/PointInsertion.lean | 3523 | `lemma_2_4_since_with_guard` | `theorem` | `noncomputable`, Since direction of Lemma 2.4 |

### Bimodal Theorems (2 declarations)

| File | Line | Declaration | Change to | Notes |
|------|------|-------------|-----------|-------|
| Theorems/Perpetuity/Helpers.lean | 55 | `wrap` | `lemma` | Trivial wrapper `⟨d⟩` |
| Theorems/Propositional/Connectives.lean | 44 | `wrap'` | `lemma` | `abbrev` -> `lemma`, alias for `wrap` |

### Modal (1 declaration)

| File | Line | Declaration | Change to | Notes |
|------|------|-------------|-----------|-------|
| Modal/Metalogic/Systems/S5/Completeness.lean | 91 | `completeness` | `theorem` | `abbrev` -> `theorem`, alias for `s5_completeness` |

### Temporal Metalogic Chronicle (14 declarations)

| File | Line | Declaration | Change to | Notes |
|------|------|-------------|-----------|-------|
| Chronicle/Frame.lean | 57 | `gContentClosedDerivation` | `lemma` | `noncomputable` |
| Chronicle/Frame.lean | 67 | `hContentClosedDerivation` | `lemma` | `noncomputable` |
| Chronicle/Frame.lean | 114 | `tForwardWitness` | `lemma` | `noncomputable` |
| Chronicle/Frame.lean | 123 | `tBackwardWitness` | `lemma` | `noncomputable` |
| Chronicle/Frame.lean | 141 | `tGBackward` | `lemma` | `noncomputable` |
| Chronicle/Frame.lean | 188 | `tHBackward` | `lemma` | `noncomputable` |
| Chronicle/Frame.lean | 231 | `tUntilEventualityResolution` | `lemma` | `noncomputable` |
| Chronicle/Frame.lean | 241 | `tSinceEventualityResolution` | `lemma` | `noncomputable` |
| Chronicle/CounterexampleElimination.lean | 288 | `eliminateC5Counterexample` | `lemma` | `noncomputable` |
| Chronicle/CounterexampleElimination.lean | 325 | `eliminateC5'Counterexample` | `lemma` | `noncomputable` |
| Chronicle/PointInsertion.lean | 148 | `lemma_2_4` | `theorem` | `noncomputable`, Burgess 1982 named result |
| Chronicle/PointInsertion.lean | 278 | `lemma_2_6` | `theorem` | `noncomputable`, Burgess 1982 named result |
| Chronicle/PointInsertion.lean | 2061 | `lemma_2_4_with_guard` | `theorem` | `noncomputable`, strengthened Burgess Lemma 2.4 |
| Chronicle/PointInsertion.lean | 2696 | `lemma_2_4_since_with_guard` | `theorem` | `noncomputable`, Since direction of Lemma 2.4 |

### Temporal Metalogic Other (4 declarations)

| File | Line | Declaration | Change to | Notes |
|------|------|-------------|-----------|-------|
| DenseCompleteness.lean | 191 | `chronicle_densely_ordered_dense` | `lemma` | Remove `@[reducible]` |
| DenseMCS.lean | 307 | `theoremInMcsFc` | `lemma` | `noncomputable` |
| MCS.lean | 84 | `theoremInMcs` | `lemma` | `noncomputable` |
| PropositionalHelpers.lean | 51 | `wrap` | `lemma` | Trivial wrapper `⟨d⟩` |

## File-Level Summary

| File | Count | Change Pattern |
|------|-------|----------------|
| Bimodal/Metalogic/BXCanonical/Frame.lean | 9 | `noncomputable def` -> `noncomputable lemma` |
| Bimodal/Metalogic/Core/MaximalConsistent.lean | 7 | `noncomputable def` -> `noncomputable lemma` (1 also needs `@[reducible]` removal) |
| Bimodal/Metalogic/BXCanonical/Chronicle/PointInsertion.lean | 5 | `noncomputable def` -> `noncomputable lemma` |
| Bimodal/Metalogic/BXCanonical/Chronicle/CounterexampleElimination.lean | 4 | `noncomputable def` -> `noncomputable lemma` |
| Temporal/Metalogic/Chronicle/Frame.lean | 8 | `noncomputable def` -> `noncomputable lemma` |
| Temporal/Metalogic/Chronicle/PointInsertion.lean | 4 | `noncomputable def` -> `noncomputable lemma` |
| Temporal/Metalogic/Chronicle/CounterexampleElimination.lean | 2 | `noncomputable def` -> `noncomputable lemma` |
| Bimodal/FrameConditions/FrameClass.lean | 2 | Remove `@[reducible]`, `def` -> `lemma` |
| Bimodal/FrameConditions/Soundness.lean | 1 | `def` -> `lemma` |
| Bimodal/Metalogic/BXCanonical/CanonicalModel.lean | 1 | `noncomputable def` -> `noncomputable lemma` |
| Bimodal/Metalogic/BXCanonical/Chronicle/ChronicleToCountermodel.lean | 1 | `def` -> `lemma` |
| Bimodal/Metalogic/BXCanonical/Chronicle/ChronicleToCountermodelBasic.lean | 1 | `def` -> `lemma` |
| Bimodal/Metalogic/Bundle/CanonicalFrame.lean | 1 | `abbrev` -> `lemma` |
| Bimodal/Metalogic/Core/DeductionTheorem.lean | 1 | `def` -> `lemma` |
| Bimodal/Metalogic/Core/MCSProperties.lean | 1 | `noncomputable def` -> `noncomputable lemma` |
| Bimodal/Theorems/Perpetuity/Helpers.lean | 1 | `def` -> `lemma` |
| Bimodal/Theorems/Propositional/Connectives.lean | 1 | `abbrev` -> `lemma` |
| Modal/Metalogic/Systems/S5/Completeness.lean | 1 | `abbrev` -> `theorem` |
| Temporal/Metalogic/DenseCompleteness.lean | 1 | Remove `@[reducible]`, `def` -> `lemma` |
| Temporal/Metalogic/DenseMCS.lean | 1 | `noncomputable def` -> `noncomputable lemma` |
| Temporal/Metalogic/MCS.lean | 1 | `noncomputable def` -> `noncomputable lemma` |
| Temporal/Metalogic/PropositionalHelpers.lean | 1 | `def` -> `lemma` |

**Total**: 55 declarations across 22 files (note: the task description said 20 files, actual count differs slightly due to the Modal/S5 file and additional Temporal files).

## Implementation Approach

### Change Patterns

There are exactly 4 change patterns needed:

1. **`noncomputable def` -> `noncomputable lemma`** (45 declarations): Simple keyword replacement
2. **`def` -> `lemma`** (4 declarations): Simple keyword replacement
3. **`abbrev` -> `lemma`/`theorem`** (3 declarations): Replace keyword, keep body
4. **`@[reducible] [noncomputable] def` -> `[noncomputable] lemma`** (3 declarations): Remove `@[reducible]`, replace `def` with `lemma`

### lemma vs theorem Convention

Classification uses `theorem` for major named results and `lemma` for supporting infrastructure:

- **`theorem`** (10 declarations): `completeness` (Modal S5), `soundnessOver` (parameterized soundness), and 8 Burgess 1982 named results (`lemma_2_4`, `lemma_2_6`, `lemma_2_4_with_guard`, `lemma_2_4_since_with_guard` -- each appearing in both Bimodal and Temporal)
- **`lemma`** (45 declarations): All supporting results (witness existentials, MCS closure properties, typeclass evidence, wrapper utilities)

### Verification

After making all changes:
1. `lake build` -- verify no compilation errors
2. `lake lint` -- verify the 55 `defLemma` errors are resolved
3. `lake test` -- verify tests pass (grind_lint should be unaffected since these are proof declarations)

## Risk Assessment

**Risk: LOW**. All changes are mechanical keyword replacements. The critical semantic difference between `def` and `lemma`/`theorem` (opacity of the proof body) has been verified to have zero downstream impact -- no code unfolds any of these 55 declarations.

## Blockers

None identified.
