# Fix Verification Report: Task 187

- **Task**: 187 - Fix quality issues from task 185 audit
- **Date**: 2026-06-13
- **Scope**: Verify 14 audit items against current codebase state
- **Sources**: Task 185 team research report, current file state

---

## Executive Summary

Of the 14 fix items from the task 185 audit, **9 are already resolved**, **1 is partially resolved**, and **4 remain open**. The HIGH priority items are all resolved. The remaining items are MEDIUM and LOW priority refinements.

Additionally, `lake shake` reveals **30 files** in the target directories with import hygiene recommendations that were not part of the original audit scope but represent a significant new finding.

---

## Item-by-Item Verification

### HIGH Priority

#### Item 1: Remove unused `Std.Tactic.BVDecide.Normalize` imports
- **Status**: ALREADY FIXED
- **Evidence**: `grep -rn 'BVDecide\|bv_decide\|bv_omega\|Std.Tactic' Cslib/Logics/Propositional/` returns no matches. Neither `NaturalDeduction/DerivedRules.lean` nor `Semantics/SemanticConsequence.lean` contains this import.

#### Item 2: Replace bare "CZ" abbreviation with BibKey format
- **Status**: ALREADY FIXED
- **Evidence**: `grep -rn 'CZ' Cslib/Logics/Propositional/` returns no matches. All 14 files now use the full `[A. Chagrov, M. Zakharyaschev, *Modal Logic*][ChagrovZakharyaschev1997]` format. Verified in: Completeness.lean (line 29), StrongCompleteness.lean (line 40), Soundness.lean (line 28), IntCompleteness.lean (line 30), IntStrongCompleteness.lean (line 43), IntSoundness.lean (lines 27-28), MinCompleteness.lean (line 36), MinStrongCompleteness.lean (line 38), MinSoundness.lean (lines 28-29), IntLindenbaum.lean (lines 19, 425), MinLindenbaum.lean (line 31), DeductionTheorem.lean (line 129), MCS.lean (line 31), SemanticConsequence.lean (lines 36-37), Semantics/Basic.lean (line 23), Semantics/Kripke.lean (lines 42, 90), Defs.lean (line 67), ProofSystem/Axioms.lean (line 23), ProofSystem/Derivation.lean (line 42).

#### Item 3: Add literature citations to `set_lindenbaum` and `deductionTheorem`
- **Status**: ALREADY FIXED
- **Evidence**:
  - `set_lindenbaum` (Consistency.lean line 146): `See [A. Chagrov, M. Zakharyaschev, *Modal Logic*][ChagrovZakharyaschev1997], Section 5.1.`
  - `deductionTheorem` (DeductionTheorem.lean line 129): `See [A. Chagrov, M. Zakharyaschev, *Modal Logic*][ChagrovZakharyaschev1997], Theorem 1.4.3.`

#### Item 4: Fix lake shake import hygiene (IntSoundness/MinSoundness moves)
- **Status**: ALREADY FIXED (original specific items)
- **Evidence**: The specific audit items are resolved:
  - `IntCompleteness.lean`: Does NOT import IntSoundness (correct)
  - `IntStrongCompleteness.lean`: DOES import IntSoundness (line 10) (correct)
  - `MinCompleteness.lean`: Does NOT import MinSoundness (correct)
  - `MinStrongCompleteness.lean`: DOES import MinSoundness (line 10) (correct)
- **New finding**: `lake shake` now identifies **30 files** in target directories with further import recommendations (public->private conversions, missing explicit imports). See "New Findings" section below.

### MEDIUM Priority

#### Item 5: Decompose 241-line `prop_truth_lemma`
- **Status**: ALREADY FIXED
- **Evidence**: `prop_truth_lemma` (Completeness.lean line 330) is now a 16-line dispatcher that delegates to 5 helper lemmas:
  - `prop_truth_lemma_atom` (line 54)
  - `prop_truth_lemma_bot` (line 64)
  - `prop_truth_lemma_and` (line 74)
  - `prop_truth_lemma_or` (line 134)
  - `prop_truth_lemma_imp` (line 207)

#### Item 6: Add van Dalen 2013 and Fitting 1969 to references.bib
- **Status**: ALREADY FIXED
- **Evidence**: `references.bib` contains both entries:
  - `Fitting1969` at line 173
  - `vanDalen2013` at line 581

#### Item 7: Add References sections to 5 files
- **Status**: PARTIALLY FIXED (4 of 5)
- **Evidence**:
  - `Metalogic/MCS.lean`: HAS References (line 29)
  - `ProofSystem/Axioms.lean`: HAS References (line 21)
  - `ProofSystem/Derivation.lean`: HAS References (line 40)
  - `Foundations/Logic/Metalogic/DeductionHelpers.lean`: HAS References (line 38)
  - `Foundations/Logic/Metalogic/Consistency.lean`: **MISSING References** -- needs addition
- **Action needed**: Add a `## References` section to the module docstring in `Cslib/Foundations/Logic/Metalogic/Consistency.lean` citing [ChagrovZakharyaschev1997] Section 5.1 (Lindenbaum's lemma) and Zorn's lemma (standard).

#### Item 8: Fix naming (`soundness_tautology` and `completeness_iff_tautology`)
- **Status**: ALREADY FIXED
- **Evidence**:
  - `Soundness.lean` line 89: `theorem prop_soundness_tautology`
  - `StrongCompleteness.lean` line 231: `theorem prop_completeness_iff_tautology`

#### Item 9: Extract duplicated `h_implyK`/`h_implyS` helpers
- **Status**: ALREADY FIXED
- **Evidence**: All six helpers are centralized in `ProofSystem/Axioms.lean`:
  - `prop_h_implyK` (line 184)
  - `prop_h_implyS` (line 190)
  - `int_h_implyK` (line 196)
  - `int_h_implyS` (line 202)
  - `min_h_implyK` (line 208)
  - `min_h_implyS` (line 214)

#### Item 10: Change `public import Cslib.Init` to private `import` in Defs.lean
- **Status**: ALREADY FIXED
- **Evidence**: `Defs.lean` line 9: `import Cslib.Init` (no `public` prefix).

### LOW Priority

#### Item 11: Rename misleading `lem` theorem
- **Status**: STILL OPEN
- **Location**: `Cslib/Foundations/Logic/Theorems/Propositional/Core.lean` line 63
- **Current state**: `theorem lem` with docstring "Law of Excluded Middle: `⊢ φ ∨ ¬φ` where `φ ∨ ¬φ = (φ → ⊥) → (φ → ⊥)`."
- **Issue**: In the Minimal section, this proves `(φ → ⊥) → (φ → ⊥)` which is the identity on negation under Lukasiewicz encoding. While technically LEM under the encoding, the name is misleading because: (a) it's in the Minimal section where classical LEM is not a theorem, (b) the encoded formula is trivially an instance of `identity`.
- **Downstream consumers**: 
  - `Cslib/Logics/Bimodal/Theorems/Propositional/Core.lean` line 44-46 (defines `def lem` wrapping it)
  - `Cslib/Logics/Bimodal/Metalogic/Algebraic/BooleanStructure.lean` line 306 (uses `Theorems.Propositional.lem`)
- **Rename considerations**: Renaming to `neg_identity` or `encoded_lem` requires updating 2 downstream files. Also update docstring line 18 in the same file.

#### Item 12: Replace 3 instances of bare `simp` with `simp only`
- **Status**: ALREADY FIXED
- **Evidence**: `grep -rn '\bsimp\b' Cslib/Logics/Propositional/ | grep -v 'simp only\|simp_all\|simp \[\|@\[simp\]'` returns no bare simp calls. The only `simp` occurrence is an `@[simp]` attribute annotation.

#### Item 13: Add missing `@[simp]` attributes
- **Status**: STILL OPEN
- **Locations**:
  - `Cslib/Logics/Propositional/Semantics/Basic.lean` line 38: `def Evaluate` -- base cases (.atom, .bot) lack `@[simp]`
  - `Cslib/Logics/Propositional/Semantics/Kripke.lean` line 81: `def IForces` -- base cases (.atom, .bot) lack `@[simp]`
- **Consideration**: Adding `@[simp]` to recursive definitions requires care. These are structural recursions, so `@[simp]` on the individual match arms may not be directly applicable. The recommended approach would be to add simp lemmas for the base cases (e.g., `@[simp] theorem Evaluate_atom`, `@[simp] theorem Evaluate_bot`). Need to verify this does not break existing proofs.

#### Item 14: Fix stale docstring axiom count
- **Status**: ALREADY FIXED
- **Evidence**: `ProofSystem/Axioms.lean` line 17 reads "the 10 axiom schemata of classical" (correct count).

---

## New Findings

### Lake Shake Import Hygiene (30 files affected)

Running `lake shake` against the current codebase reveals extensive import recommendations across both target directories. The most significant patterns:

**Pattern 1: public -> private import conversions**
Many imports currently marked `public` should be `private` (plain `import`). This is the most common recommendation, affecting files like:
- `Metalogic/StrongCompleteness.lean`: Completeness, Soundness imports should be private
- `Metalogic/IntStrongCompleteness.lean`: IntSoundness, IntCompleteness imports should be private
- `Metalogic/MinStrongCompleteness.lean`: MinSoundness, MinCompleteness imports should be private
- `Metalogic/IntLindenbaum.lean`: DeductionTheorem, Soundness imports should be private
- `Metalogic/MinLindenbaum.lean`: DeductionTheorem, Soundness imports should be private
- `Metalogic/MCS.lean`: DeductionTheorem import should be private
- Multiple Foundations/Logic files: various public imports should be private

**Pattern 2: Missing explicit imports**
Several files rely on transitive imports and need explicit ones:
- `Metalogic/Completeness.lean`: needs explicit DeductionTheorem, Axioms, Init imports
- `Metalogic/DeductionTheorem.lean`: needs explicit Init import
- `Semantics/Basic.lean`: needs `Mathlib.Tactic.Finiteness.Attr`
- Various other files need explicit `Cslib.Init` imports

**Pattern 3: BVDecide imports recommended by shake**
`lake shake` recommends adding `Std.Tactic.BVDecide.Normalize.Prop` or `.BitVec` to several files (MCS.lean, Completeness.lean, IntLindenbaum.lean, MinLindenbaum.lean, IntCompleteness.lean, MinCompleteness.lean). This is likely a transitive dependency of omega/decide tactics used in these files.

**Recommendation**: A comprehensive `lake shake --fix` pass should be a separate phase from the targeted fixes, as it affects 30 files and may have complex interaction effects. Run `lake build` after each change to verify no regressions.

### DNE Helper Already Extracted

The audit recommended extracting a shared DNE helper from `StrongCompleteness.lean`. This is already done: `dne_from_neg_neg` (lines 73-102) is a private helper called from both branches of `prop_not_SetDerivable_union_neg_consistent`.

### int_prime_exclusion Citation Already Present

The audit recommended citing CZ Lemma 5.5 for `int_prime_exclusion`. This is already done at IntLindenbaum.lean line 425.

---

## Summary: Remaining Work

### Must Fix (3 items)

| # | Item | File | Line | Priority |
|---|------|------|------|----------|
| 7 | Add References section | `Cslib/Foundations/Logic/Metalogic/Consistency.lean` | docstring (line 13-31) | MEDIUM |
| 11 | Rename misleading `lem` theorem | `Cslib/Foundations/Logic/Theorems/Propositional/Core.lean` | 63 | LOW |
| 13 | Add `@[simp]` lemmas for base cases | `Semantics/Basic.lean` (line 38), `Semantics/Kripke.lean` (line 81) | LOW |

### Optional / Separate Task

| Finding | Scope | Recommendation |
|---------|-------|----------------|
| Lake shake (30 files) | Both directories | Separate task or additional phase; run `lake shake --fix` then verify with `lake build` |
| Axiom subsumption names | `ProofSystem/Axioms.lean` lines 155, 168 | Rename `toIntProp` -> `toIntPropAxiom`, `toProp` -> `toPropAxiom`; update 1 downstream reference in MinLindenbaum.lean line 373 |

### Dependencies / Ordering

1. Item 7 (add References section) is independent of all other items.
2. Item 11 (rename `lem`) requires updating 2 Bimodal files. Should be done as an atomic commit.
3. Item 13 (@[simp] lemmas) requires testing to verify no proof regressions. Should be done after items 7 and 11.
4. Lake shake fixes should be a separate phase after all targeted fixes, since they affect many files and can interact.

---

## Verification Method

Each item was verified by:
1. Reading the current file at the reported line number
2. Running grep searches across the target directories
3. Cross-checking with the task 185 audit report for exact issue descriptions
4. Running `lake shake` to verify import hygiene state
