# Research Report: Propositional Deduction Theorem Naming Cleanup

## Task 191 | Session: sess_1781456783_f22155

---

## 1. Delete Unused `cl_prop_has_deduction_theorem`

### Current State

- **Location**: `Cslib/Logics/Propositional/Metalogic/DeductionTheorem.lean`, lines 213-217
- **Definition**: Wraps `prop_has_deduction_theorem` with `PropositionalAxiom`-specific constructor lambdas
- **Usage**: **Zero references** outside its own definition. No other file imports or calls it.

### Recommendation

**Delete it.** It is dead code. The generic `prop_has_deduction_theorem` is used directly everywhere, with explicit `prop_h_implyK`/`prop_h_implyS` witnesses (or `int_h_*`/`min_h_*` for other logics). There are no downstream breakage risks since it has zero call sites.

### Diff

Remove lines 210-217 from `DeductionTheorem.lean`:
```lean
-- DELETE:
/-! ## Classical backward-compatible wrapper -/

/-- Classical deduction theorem: the deduction theorem for the classical axiom set. -/
theorem cl_prop_has_deduction_theorem :
    Metalogic.HasDeductionTheorem (propDerivationSystem (@PropositionalAxiom Atom)) :=
  prop_has_deduction_theorem
    (fun φ ψ => .implyK φ ψ)
    (fun φ ψ χ => .implyS φ ψ χ)
```

---

## 2. Rename or Delete `_h_` Witness Theorems

### Current State

Six witness theorems in `Cslib/Logics/Propositional/ProofSystem/Axioms.lean`, lines 183-217:

| Name | Line | Body |
|------|------|------|
| `prop_h_implyK` | 184 | `fun φ ψ => .implyK φ ψ` |
| `prop_h_implyS` | 190 | `fun φ ψ χ => .implyS φ ψ χ` |
| `int_h_implyK` | 196 | `fun φ ψ => .implyK φ ψ` |
| `int_h_implyS` | 202 | `fun φ ψ χ => .implyS φ ψ χ` |
| `min_h_implyK` | 208 | `fun φ ψ => .implyK φ ψ` |
| `min_h_implyS` | 214 | `fun φ ψ χ => .implyS φ ψ χ` |

### Usage Sites

**`prop_h_implyK` / `prop_h_implyS`** (18 references each):
- `StrongCompleteness.lean`: 16 call sites (lines 112, 132, 145, 172, 185, 200, 202, 208, 243, 251, 281, 303, 334, 339, 345, 439, 465)
- All in the form `prop_closed_under_derivation prop_h_implyK prop_h_implyS h_mcs`, `prop_negation_complete prop_h_implyK prop_h_implyS h_mcs`, `deductionWithMem prop_h_implyK prop_h_implyS`, or `deductionTheorem prop_h_implyK prop_h_implyS`.

**`int_h_implyK` / `int_h_implyS`** (3 references each):
- `IntLindenbaum.lean`: lines 110, 145, 148

**`min_h_implyK` / `min_h_implyS`** (3 references each):
- `MinLindenbaum.lean`: lines 93, 128, 131

### Analysis

These witnesses are trivial eta-expansions of the axiom constructors. Their primary value is abbreviating the repeated pattern `(fun φ ψ => .implyK φ ψ)`. However, the naming convention `prop_h_implyK` is non-standard -- the `_h_` infix is a legacy artifact meaning "hypothesis" and doesn't follow Lean naming conventions.

### Recommendation: Move to Type Namespaces

Rename to use proper Lean namespacing on the axiom type:

| Old Name | New Name |
|----------|----------|
| `prop_h_implyK` | `PropositionalAxiom.mem_implyK` |
| `prop_h_implyS` | `PropositionalAxiom.mem_implyS` |
| `int_h_implyK` | `IntPropAxiom.mem_implyK` |
| `int_h_implyS` | `IntPropAxiom.mem_implyS` |
| `min_h_implyK` | `MinPropAxiom.mem_implyK` |
| `min_h_implyS` | `MinPropAxiom.mem_implyS` |

The `mem_` prefix follows the Lean/Mathlib convention for "this thing is a member of that set/predicate" (cf. `List.mem_cons`, `Set.mem_singleton`).

**Alternative considered**: Inlining `(fun φ ψ => .implyK φ ψ)` at all call sites. Rejected because:
- `StrongCompleteness.lean` has 16 call sites for the classical pair -- inlining would add significant noise
- The named witnesses provide self-documenting intent ("this axiom set includes implyK")

### Impact

- 24 total call sites need updating across 3 files
- No semantic change -- same proof terms
- Could be done incrementally (deprecate old names, alias to new)

---

## 3. Rename `prop_has_deduction_theorem`

### Current State

- **Location**: `DeductionTheorem.lean`, lines 198-208
- **Signature**: Takes `{Axioms}` + `h_implyK` + `h_implyS` and returns `Metalogic.HasDeductionTheorem (propDerivationSystem Axioms)`
- **Despite the name**, it is fully generic over any axiom set with implyK/implyS

### Usage Sites (5 references)

1. `DeductionTheorem.lean:215` -- called by `cl_prop_has_deduction_theorem` (dead code, to be deleted)
2. `MCS.lean:78` -- `prop_closed_under_derivation`
3. `MCS.lean:92` -- `prop_implication_property`
4. `MCS.lean:105` -- `prop_negation_complete`
5. `IntLindenbaum.lean:110` -- `int_deriv_from_closure_to_S`
6. `MinLindenbaum.lean:93` -- `min_deriv_from_closure_to_S`

### Recommendation

Rename to `hasDeductionTheorem` (or `propDerivationSystem_hasDeductionTheorem` for full qualification).

The name should reflect that it is the deduction theorem for `propDerivationSystem`, parameterized over an arbitrary axiom predicate -- not specific to classical propositional logic.

**Preferred**: `hasDeductionTheorem` within the `Cslib.Logic.PL` namespace. This mirrors the pattern used in the Bimodal and Modal logics where `deductionTheorem` is a `def` and the `HasDeductionTheorem` wrapper is a simple theorem.

| Old Name | New Name |
|----------|----------|
| `prop_has_deduction_theorem` | `hasDeductionTheorem` |

This is consistent with the pattern where `deductionTheorem` and `deductionWithMem` are already unadorned `def` names in the same namespace.

### Impact

- 5 active call sites (MCS.lean x3, IntLindenbaum.lean x1, MinLindenbaum.lean x1)
- 1 dead call site (cl_prop_has_deduction_theorem, to be deleted)
- No semantic change

---

## 4. Symmetric Wrappers vs Inline Pattern

### Current State

**IntLindenbaum.lean** (line 110):
```lean
have hd_dt := prop_has_deduction_theorem int_h_implyK int_h_implyS hd
```

**MinLindenbaum.lean** (line 93):
```lean
have hd_dt := prop_has_deduction_theorem min_h_implyK min_h_implyS hd
```

Neither file defines a wrapper like `int_has_deduction_theorem` or `min_has_deduction_theorem`. They call the generic `prop_has_deduction_theorem` directly with the appropriate witness theorems.

### Analysis

The current inline pattern is **preferred** over symmetric wrappers because:

1. **The generic theorem is already the right abstraction.** Adding `int_has_deduction_theorem` = `hasDeductionTheorem IntPropAxiom.mem_implyK IntPropAxiom.mem_implyS` would be trivial wrappers with no proof content.

2. **Usage count is low.** Each is used only once (IntLindenbaum) or once (MinLindenbaum). The classical witnesses are used many more times in StrongCompleteness, but that's because MCS properties are called there repeatedly.

3. **The deleted `cl_prop_has_deduction_theorem` was exactly this kind of trivial wrapper**, and it was unused -- confirming the pattern isn't needed.

### Recommendation

**Do not add symmetric wrappers.** Confirm the inline pattern is preferred. After renaming (items 2 and 3), the call sites will read:

```lean
-- IntLindenbaum.lean:
have hd_dt := hasDeductionTheorem IntPropAxiom.mem_implyK IntPropAxiom.mem_implyS hd

-- MinLindenbaum.lean:
have hd_dt := hasDeductionTheorem MinPropAxiom.mem_implyK MinPropAxiom.mem_implyS hd
```

This is clear and self-documenting without wrappers.

---

## 5. Broader Naming Inconsistencies Survey

### 5.1 Snake Case Prefix Pattern (Major Finding)

The entire Propositional Metalogic directory uses a consistent but non-standard `{prefix}_{name}` pattern where the prefix indicates the logic:

| Prefix | Logic | Files Using It |
|--------|-------|----------------|
| `prop_` | Classical (generic) | MCS.lean, StrongCompleteness.lean, Soundness.lean |
| `int_` | Intuitionistic | IntLindenbaum.lean, IntSoundness.lean, IntStrongCompleteness.lean |
| `min_` | Minimal | MinLindenbaum.lean, MinSoundness.lean, MinStrongCompleteness.lean |
| `cl_` | Classical (specific) | DeductionTheorem.lean (dead code only) |

**Examples** of the snake_case prefix pattern throughout the directory:

| File | Names |
|------|-------|
| MCS.lean | `prop_lindenbaum`, `prop_closed_under_derivation`, `prop_implication_property`, `prop_negation_complete`, `prop_mcs_bot_not_mem`, `prop_mcs_neg_of_not_mem`, `prop_mcs_not_mem_of_neg`, `prop_mcs_mem_iff_neg_not_mem` |
| Soundness.lean | `prop_axiom_sound`, `prop_soundness`, `prop_soundness_derivable`, `prop_soundness_tautology` |
| StrongCompleteness.lean | `prop_truth_lemma`, `prop_truth_lemma_atom`, `prop_truth_lemma_bot`, `prop_truth_lemma_and`, `prop_truth_lemma_or`, `prop_truth_lemma_imp`, `prop_strong_soundness`, `prop_strong_completeness`, `prop_strong_completeness_iff`, `prop_compactness`, `prop_completeness`, `prop_completeness_iff_tautology`, `prop_not_SetDerivable_union_neg_consistent` |
| IntSoundness.lean | `int_axiom_sound`, `int_soundness`, `int_soundness_derivable` |
| IntLindenbaum.lean | `int_dccs_bot_not_mem`, `int_dccs_imp_property`, `int_deriv_from_closure_to_S`, `int_deriv_imp_of_union`, `int_imp_witness`, `int_prime_exclusion`, `int_theorems_dccs`, `int_consistent` |
| IntStrongCompleteness.lean | `int_truth_lemma`, `int_strong_soundness`, `int_strong_completeness`, `int_strong_completeness_iff`, `int_compactness`, `int_completeness`, `int_soundness_completeness` |
| MinLindenbaum.lean | `min_theory_imp_property`, `min_deriv_from_closure_to_S`, `min_deriv_imp_of_union`, `min_imp_witness`, `min_prime_exclusion`, `min_consistent`, `min_theorems_theory` |
| MinSoundness.lean | `min_axiom_sound`, `min_soundness`, `min_soundness_derivable` |
| MinStrongCompleteness.lean | `min_truth_lemma`, `min_strong_soundness`, `min_strong_completeness`, `min_strong_completeness_iff`, `min_compactness`, `min_completeness` |

**Assessment**: This is a large-scale naming pattern (60+ declarations). Converting all of these to proper namespacing would be a significant refactor beyond the scope of task 191. However, the task description specifically asks about the `_h_` witnesses and `prop_has_deduction_theorem`.

### 5.2 Unused Declarations

| Declaration | Location | Status |
|-------------|----------|--------|
| `cl_prop_has_deduction_theorem` | DeductionTheorem.lean:213 | **Dead code** -- zero references |

No other unused declarations were found. All other `prop_*`, `int_*`, `min_*` names have active call sites.

### 5.3 Boilerplate Witnesses That Could Be Inlined

The 6 `_h_` theorems (item 2 above) are the primary boilerplate. The `MinimalAxioms` typeclass in `Equivalence.lean` provides an alternative bundling pattern, but it bundles 8 axioms (K, S, andI, andE1, andE2, orI1, orI2, orE) rather than just K+S. The deduction theorem only needs K+S, so `MinimalAxioms` is too heavy for this purpose.

**Possible future improvement**: A `HasImplyKS` typeclass bundling just K+S, which would eliminate the need for explicit witness passing. This would be a separate task and not part of the current cleanup.

### 5.4 Inconsistent Naming Patterns Across Files

**Consistency within the existing pattern**: The `prop_`/`int_`/`min_` prefixes are consistently applied within each file and across the directory. There are no mixed-pattern files.

**Interaction with the NaturalDeduction directory**: The `NaturalDeduction/` files use `CamelCase` naming (e.g., `hilbertToND`, `ndToHilbert`, `MinimalAxioms`), consistent with Lean 4 conventions. The `FromHilbert.lean` file uses `lowerCamelCase` def names (`impI`, `impE`, `botE`).

**Interaction with HilbertDerivedRules.lean**: Uses `lowerCamelCase` (e.g., `hilbertAndI`, `hilbertOrE`), consistent with the `NaturalDeduction/` convention.

**Conclusion**: The two subsystems (Metalogic/ and NaturalDeduction/) use different conventions. The Metalogic directory uses `snake_case` with logic-prefix; the NaturalDeduction directory uses `lowerCamelCase`. This is a deliberate architectural split (Metalogic = parameterized generic framework, NaturalDeduction = type-level ND system) and not a naming bug.

### 5.5 `PropSetConsistent` / `PropSetMaximalConsistent` Abbreviations

`MCS.lean` defines abbreviations `PropSetConsistent` and `PropSetMaximalConsistent` (lines 47-54) using `CamelCase`. These are correct and consistent with the Lean convention for type-level abbreviations.

### 5.6 `IntDCCS` / `MinTheory` / `IntPrimeDCCS` / `MinPrimeTheory` Definitions

These definition names in `IntLindenbaum.lean` and `MinLindenbaum.lean` use `CamelCase` and are well-named. No issues.

### 5.7 `intNegPhiImpPsi` (IntLindenbaum.lean:68)

This `lowerCamelCase` def name breaks from the surrounding `int_snake_case` theorem naming convention. However, it's a local helper `def` (not a `theorem`), so the different convention is acceptable.

---

## Summary of Recommended Changes

| # | Item | Action | Files Changed | Call Sites Affected |
|---|------|--------|---------------|---------------------|
| 1 | `cl_prop_has_deduction_theorem` | Delete | DeductionTheorem.lean | 0 |
| 2a | `prop_h_implyK` -> `PropositionalAxiom.mem_implyK` | Rename | Axioms.lean, StrongCompleteness.lean | 18 |
| 2b | `prop_h_implyS` -> `PropositionalAxiom.mem_implyS` | Rename | Axioms.lean, StrongCompleteness.lean | 18 |
| 2c | `int_h_implyK` -> `IntPropAxiom.mem_implyK` | Rename | Axioms.lean, IntLindenbaum.lean | 3 |
| 2d | `int_h_implyS` -> `IntPropAxiom.mem_implyS` | Rename | Axioms.lean, IntLindenbaum.lean | 3 |
| 2e | `min_h_implyK` -> `MinPropAxiom.mem_implyK` | Rename | Axioms.lean, MinLindenbaum.lean | 3 |
| 2f | `min_h_implyS` -> `MinPropAxiom.mem_implyS` | Rename | Axioms.lean, MinLindenbaum.lean | 3 |
| 3 | `prop_has_deduction_theorem` -> `hasDeductionTheorem` | Rename | DeductionTheorem.lean, MCS.lean, IntLindenbaum.lean, MinLindenbaum.lean | 5 (active) |
| 4 | Symmetric wrappers | No action needed | -- | -- |
| 5 | Broader `prop_`/`int_`/`min_` prefix pattern | Out of scope for this task | 60+ declarations | -- |

### Risk Assessment

- **Low risk**: All changes are mechanical renames or dead code deletion
- **No semantic changes**: Same proof terms, different names
- **No import changes**: All renamed declarations stay in the same files/modules
- **Build verification**: A full `lake build` after all renames will catch any missed call sites
- **Downstream impact**: Only the Propositional directory is affected. The Bimodal/Temporal/Modal logics have their own `deductionTheorem` defs (different namespaces) and are not affected.

### Recommended Implementation Order

1. Delete `cl_prop_has_deduction_theorem` (zero dependencies)
2. Rename `prop_has_deduction_theorem` to `hasDeductionTheorem` (5 call sites)
3. Rename the 6 `_h_` witnesses to namespace-qualified names (24 call sites)
4. Run `lake build` to verify
5. Run `lake exe lint-style` to check style compliance
