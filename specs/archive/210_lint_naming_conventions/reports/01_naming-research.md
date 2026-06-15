# Research Report: Naming Convention Violations (Task 210)

## Summary

The `defsWithUnderscore` environment linter (from Mathlib's standard lint set) flags 105
declarations whose names contain underscores. The Mathlib convention requires `lowerCamelCase`
for definitions and `UpperCamelCase` for types. The linter only checks `def`/`abbrev`/`instance`
declarations and structure fields, NOT `theorem`/`lemma`.

All 105 violations are in two namespaces:
- **Bimodal** (87 violations across 21 files)
- **Temporal** (18 violations across 3 files)

## Linter Details

**Linter**: `defsWithUnderscore` (part of `mathlibStandardSet`)
**Location**: `Mathlib.Tactic.Linter.Style`
**Scope**: Only flags `def`/`abbrev`/`instance` and structure fields. Does NOT flag `theorem`/`lemma`.
**Exclusions**: Names ending in `_1`, `_2`, `_mathlib`, or names ending with trailing underscore.
**Command**: `lake lint` (environment linters, requires full build first)

## Violation Categories

### Category A: Letter-Prefix Underscore (38 violations)

Pattern: Single capital letter followed by underscore, e.g., `G_distribution`, `F_top`, `H_mono`.

These represent temporal operators (G = allFuture, H = allPast, F = someFuture, P = somePast)
followed by a description. The Foundations equivalents use `theorem` and are not flagged.

**Rename pattern**: `G_distribution` -> `gDistribution`, `F_top` -> `fTop`, `H_mono` -> `hMono`

| Current Name | Proposed Name | Refs | Files |
|---|---|---|---|
| `G_quot` | `gQuot` | 5 | 2 |
| `H_quot` | `hQuot` | 5 | 2 |
| `F_top` | `fTop` | 23 | 7 |
| `P_top` | `pTop` | 20 | 6 |
| `G_neg_neg_bot` | `gNegNegBot` | 8 | 1 |
| `H_neg_neg_bot` | `hNegNegBot` | 8 | 1 |
| `F_top_deferral` | `fTopDeferral` | 4 | 1 |
| `P_top_deferral` | `pTopDeferral` | 4 | 1 |
| `F_neg_contra_imp_F_neg` | `fNegContraImpFNeg` | 2 | 1 |
| `G_imp_to_G_contra` | `gImpToGContra` | 2 | 1 |
| `G_contra_to_GK` | `gContraToGK` | 2 | 1 |
| `FF_to_F_top_and` | `ffToFTopAnd` | 2 | 1 |
| `F_top_and_absorb` | `fTopAndAbsorb` | 2 | 1 |
| `G_distribution` | `gDistribution` | 11 | 2 |
| `H_distribution` | `hDistribution` | 11 | 2 |
| `G_transitivity` | `gTransitivity` | 1 | 1 |
| `H_transitivity` | `hTransitivity` | 1 | 1 |
| `G_implies_G_id` | `gImpliesGId` | 1 | 1 |
| `F_mono` | `fMono` | 4 | 2 |
| `P_mono` | `pMono` | 3 | 2 |
| `G_mono` | `gMono` | 1 | 1 |
| `H_mono` | `hMono` | 1 | 1 |
| `F_neg_G` | `fNegG` | 2 | 2 |
| `P_neg_H` | `pNegH` | 2 | 2 |
| `G_and_intro` | `gAndIntro` | 3 | 2 |
| `H_and_intro` | `hAndIntro` | 3 | 2 |
| `G_imp_trans` | `gImpTrans` | 3 | 2 |
| `H_imp_trans` | `hImpTrans` | 3 | 2 |
| `G_contrapose` | `gContrapose` | 3 | 2 |
| `H_contrapose` | `hContrapose` | 3 | 2 |
| `G_dne_theorem` | `gDneTheorem` | 1 | 1 |
| `H_dne_theorem` | `hDneTheorem` | 1 | 1 |
| `K_plus` | `kPlus` | 5 | 1 |
| `K_minus` | `kMinus` | 5 | 1 |
| `Q_Z` | `qZ` | 100 | 3 |
| `U_depth_under_S` | `uDepthUnderS` | 5 | 1 |
| `S_nesting_above_U` | `sNestingAboveU` | 4 | 2 |
| `U_nesting_depth` | `uNestingDepth` | 88 | 2 |

### Category B: Snake Case Definitions (13 violations)

Pattern: Multi-word lowercase with underscores, e.g., `eval_family`, `temporally_coherent`.

**Rename pattern**: Convert to lowerCamelCase.

| Current Name | Proposed Name | Refs | Files |
|---|---|---|---|
| `eval_family` | `evalFamily` | 9 | 4 |
| `temporally_coherent` | `temporallyCoherent` | 18 | 5 |
| `restricted_temporally_coherent` | `restrictedTemporallyCoherent` | 3 | 2 |
| `until_since_coherent` | `untilSinceCoherent` | 4 | 1 |
| `backward_until_since_coherent` | `backwardUntilSinceCoherent` | 12 | 4 |
| `forward_until_since_coherent` | `forwardUntilSinceCoherent` | 12 | 4 |
| `restricted_forward_until_since_coherent` | `restrictedForwardUntilSinceCoherent` | 6 | 3 |
| `restricted_backward_until_since_coherent` | `restrictedBackwardUntilSinceCoherent` | 6 | 3 |
| `modal_5_collapse_theorem` | `modal5CollapseTheorem` | 2 | 1 |
| `axiom_5_negative_introspection` | `axiom5NegativeIntrospection` | 3 | 2 |
| `chronicle_densely_ordered_dense` | `chronicleDenselyOrderedDense` | 3 | 1 |
| `subformulaClosure_fintype` | `subfomrulaClosureFintype` | 1 | 1 |
| `task_rel` | `taskRel` | 31 | 4 |

### Category C: Numeric Suffix with Underscore (17 violations)

Pattern: Name followed by `_N` where N >= 3. Names ending in `_1` or `_2` are auto-excluded.

**Rename pattern**: Remove underscore before number.

| Current Name | Proposed Name | Refs | Files |
|---|---|---|---|
| `temp_4_derived` (x2) | `temp4Derived` | 9 | 4 |
| `temp_4_past` | `temp4Past` | 2 | 1 |
| `combineImpConj_3` (x2) | `combineImpConj3` | 3+3 | 1+1 |
| `boxConjIntroImp_3` | `boxConjIntroImp3` | 3 | 1 |
| `perpetuity_3` | `perpetuity3` | 3 | 1 |
| `perpetuity_4` | `perpetuity4` | 3 | 1 |
| `perpetuity_5` | `perpetuity5` | 3 | 2 |
| `perpetuity_6` | `perpetuity6` | 2 | 1 |
| `modal_5` | `modal5` | 3 | 1 |
| `lemma_2_4` (x2) | `lemma24` | 29 | 4 |
| `lemma_2_6` (x2) | `lemma26` | 29 | 4 |
| `lemma_2_7_seed` (x2) | `lemma27Seed` | 48 | 2 |
| `lemma_2_7_since_seed` (x2) | `lemma27SinceSeed` | 30 | 2 |
| `lemma_2_4_with_guard` (x2) | `lemma24WithGuard` | 9 | 4 |
| `lemma_2_4_since_with_guard` (x2) | `lemma24SinceWithGuard` | 10 | 4 |

### Category D: Abbreviated Prefix with Underscore (13 violations)

Pattern: Short prefixes like `l27_`, `l27s_`, `c5_`, `d21_`, `case1_`, `case2_`, `case3_`.

**Rename pattern**: Remove underscore, use camelCase.

| Current Name | Proposed Name | Refs | Files |
|---|---|---|---|
| `c5_forward_walk` (x2) | `c5ForwardWalk` | 2+2 | 2+2 |
| `c5_backward_walk` (x2) | `c5BackwardWalk` | 2+2 | 2+2 |
| `l27_guard` (x2) | `l27Guard` | 12 | 2 |
| `l27_collect_guards` (x2) | `l27CollectGuards` | 22 | 2 |
| `l27_a_event_list` (x2) | `l27AEventList` | 18 | 2 |
| `l27s_c5_event_list` (x2) | `l27sC5EventList` | 16 | 2 |
| `l27s_b5_guard_list` (x2) | `l27sB5GuardList` | 16 | 2 |
| `d21_sep` | `d21Sep` | 24 | 2 |
| `case1_psi` | `case1Psi` | 44 | 3 |
| `case2_psi` | `case2Psi` | 11 | 2 |
| `case3_alpha` | `case3Alpha` | 31 | 3 |
| `case3_rhs` | `case3Rhs` | 18 | 3 |

### Category E: Structure Fields (9 violations)

Pattern: Structure fields with underscores.

**Rename pattern**: Convert to camelCase.

| Current Name | Proposed Name | Refs | Files | Struct |
|---|---|---|---|---|
| `h_impl` (x4) | `hImpl` | 16 | multi | EnrichedEvent, EnrichedEventSince (Bimodal+Temporal) |
| `h_snce` (x2) | `hSnce` | 12 | multi | EnrichedEvent (Bimodal+Temporal) |
| `h_untl` (x2) | `hUntl` | 12 | multi | EnrichedEventSince (Bimodal+Temporal) |
| `task_rel` | `taskRel` | 31 | 4 | TaskFrame |

### Category F: UpperCamelCase with Underscore (4 violations)

Pattern: UpperCamelCase prefix + underscore, e.g., `ExistsTask_past`, `Gamma_plus`.

| Current Name | Proposed Name | Refs | Files |
|---|---|---|---|
| `ExistsTask_past` | `ExistsTaskPast` | 14 | 1 |
| `Gamma_plus` | `gammaPlus` | 3 | 1 |
| `Gamma_minus` | `gammaMinus` | 3 | 1 |
| `S_nesting_above_U_inner` | `sNestingAboveUInner` | 1 | 1 |

## File-Level Impact Analysis

### Highest Impact Files (most violations to fix)

| File | Count | Categories |
|---|---|---|
| `Bimodal/Theorems/TemporalDerived.lean` | 23 | A, B, C |
| `Bimodal/Metalogic/BXCanonical/Chronicle/PointInsertion.lean` | 15 | C, D, E |
| `Temporal/Metalogic/Chronicle/PointInsertion.lean` | 15 | C, D, E |
| `Bimodal/Metalogic/Bundle/TemporalCoherence.lean` | 9 | A, B |
| `Bimodal/Metalogic/Separation/DedekindZ/QLemma.lean` | 7 | A, D |
| `Bimodal/Syntax/SubformulaClosure/TemporalFormulas.lean` | 6 | A |
| `Bimodal/Theorems/Perpetuity/Principles.lean` | 5 | C |

### Highest Impact Renames (most downstream references)

These renames require careful find-and-replace across multiple files:

| Name | Total Refs | Files Affected |
|---|---|---|
| `Q_Z` | 100 | 3 |
| `U_nesting_depth` | 88 | 2 |
| `lemma_2_7_seed` | 48 | 2 |
| `case1_psi` | 44 | 3 |
| `task_rel` | 31 | 4 |
| `case3_alpha` | 31 | 3 |
| `lemma_2_7_since_seed` | 30 | 2 |
| `lemma_2_4` | 29 | 4 |
| `lemma_2_6` | 29 | 4 |
| `d21_sep` | 24 | 2 |
| `F_top` | 23 | 7 |
| `l27_collect_guards` | 22 | 2 |
| `P_top` | 20 | 6 |
| `temporally_coherent` | 18 | 5 |

## Duplicate Violations (Bimodal + Temporal)

Several violations appear in BOTH `Bimodal` and `Temporal` namespaces because the Temporal
logic was ported from the Bimodal logic. These are exact copies with different namespaces:

- `c5_forward_walk` / `c5_backward_walk`
- `lemma_2_4` / `lemma_2_6`
- `lemma_2_7_seed` / `lemma_2_7_since_seed`
- `lemma_2_4_with_guard` / `lemma_2_4_since_with_guard`
- `l27_guard` / `l27_collect_guards` / `l27_a_event_list`
- `l27s_c5_event_list` / `l27s_b5_guard_list`
- `EnrichedEvent.h_impl` / `EnrichedEvent.h_snce`
- `EnrichedEventSince.h_impl` / `EnrichedEventSince.h_untl`

These 15 pairs account for 30 of the 105 violations.

## Approach Considerations

### Option 1: Rename to camelCase (Recommended)

Rename all 105 declarations to camelCase. This is the proper fix aligned with Mathlib conventions.

**Advantages**:
- Fully resolves all 105 lint errors
- Aligns with Mathlib naming convention
- No special annotations needed

**Challenges**:
- High-reference names like `Q_Z` (100 refs), `U_nesting_depth` (88 refs) need careful
  find-and-replace across multiple files
- Structure field renames affect dot-notation access patterns
- Must update both definition sites and all reference sites

### Option 2: Change `def` to `theorem` (Partial)

For Prop-valued declarations that should use `theorem` anyway (overlap with task 211 defLemma
fixes), changing the keyword would simultaneously fix both the `defLemma` and `defsWithUnderscore`
lint errors, without renaming.

**Overlap**: Only 9 declarations overlap between `defLemma` and `defsWithUnderscore`. This option
only resolves those 9, leaving 96 still needing renames.

### Option 3: Suppress with `@[nolint defsWithUnderscore]`

Add `nolint` annotations. NOT recommended -- CSLib aims for Mathlib-compatible conventions and
suppression should only be used for intentional deviations (e.g., Lean/Mathlib compatibility names).

### Recommended Approach: Option 1 (full rename)

Rename all 105 declarations. Execute in phases grouped by file cluster to minimize rebuild time:

1. **Phase 1**: TemporalDerived.lean (23 violations, mostly self-contained)
2. **Phase 2**: PointInsertion.lean pair (Bimodal + Temporal, 30 violations, high cross-refs)
3. **Phase 3**: Bundle files (TemporalCoherence, BFMCS, CanonicalFrame, ModalSaturation -- 13 violations)
4. **Phase 4**: Separation files (QLemma, Defs, Eliminations, HierarchyInduction, Cases -- 14 violations)
5. **Phase 5**: Remaining files (Perpetuity, Combinators, TemporalFormulas, TaskFrame, etc. -- 25 violations)

## Execution Notes

### Rename Procedure Per Declaration

1. Rename at definition site (change `def foo_bar` to `def fooBar`)
2. Find all references in the same file (grep for the local name)
3. Find all references in other files (grep for the qualified name and unqualified name)
4. Update all references
5. Build the affected module(s) to verify

### Special Cases

- **Structure fields**: Renaming `h_impl` to `hImpl` also requires updating `EnrichedEvent.h_impl`
  and `EnrichedEventSince.h_impl` at all use sites (dot notation access)
- **Bimodal/Temporal pairs**: Must rename in both namespaces simultaneously to maintain consistency
- **High-reference names**: `Q_Z`, `U_nesting_depth`, `case1_psi` need especially careful
  find-replace to avoid partial matches (e.g., `Q_Z` must not match `Q_Z_something`)
- **Comment references**: Doc comments referencing these names should also be updated

### Interaction with Task 211 (defLemma)

9 declarations overlap with task 211. If task 211 changes them to `theorem`, those 9 will
no longer trigger `defsWithUnderscore`. Coordinate to avoid duplicate work. The overlapping
declarations are:
- `lemma_2_4` (both Bimodal and Temporal)
- `lemma_2_6` (both Bimodal and Temporal)
- `lemma_2_4_with_guard` (both Bimodal and Temporal)
- `lemma_2_4_since_with_guard` (both Bimodal and Temporal)
- `chronicle_densely_ordered_dense` (Temporal only)

**Recommendation**: Rename these too, since even if they become `theorem`, the names should
follow conventions for consistency with the codebase.
