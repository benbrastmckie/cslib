# Modal/ Compliance and Dead Code Audit

## Overview

Combined audit of all 57 `.lean` files under `Cslib/Logics/Modal/` for CSLib contribution standard compliance (per `CONTRIBUTING.md`) and dead/orphaned code.

**CI status**: All three CI checks pass clean (`checkInitImports`, `lint-style`, `lake lint`).

---

## Part 1: Compliance Issues

### Blockers (0)

None. All CI checks pass.

### Warnings (17)

All warnings are missing declaration docstrings (`docBlame` linter).

#### Basic.lean (4 missing docstrings)

| Line | Declaration |
|------|-------------|
| 106 | `instance : Bot (Proposition Atom)` |
| 187 | `instance : HasInferenceSystem (Judgement World Atom)` |
| 192 | `theorem derivation_def` |
| 234 | `theorem TheoryEq.ext_iff` |

#### Cube.lean (6 missing docstrings)

| Line | Declaration |
|------|-------------|
| 99 | `theorem k_subset_d` |
| 102 | `theorem k_subset_b` |
| 105 | `theorem k_subset_four` |
| 108 | `theorem k_subset_five` |
| 112 | `theorem d_subset_t` |
| 115 | `theorem k_subset_t` |

#### DerivationTree.lean (6 missing docstrings)

| Line | Declaration |
|------|-------------|
| 139 | `theorem height_modus_ponens_left` |
| 144 | `theorem height_modus_ponens_right` |
| 149 | `theorem height_weakening` |
| 172 | `theorem mp_deriv` |
| 178 | `theorem weakening_deriv` |
| 184 | `theorem assumption_deriv` |

#### K/Completeness.lean (1 inconsistency)

| Line | Declaration | Issue |
|------|-------------|-------|
| 332 | `@[simp] theorem k_strong_completeness_iff` | Only system with `@[simp]` on `_strong_completeness_iff`. Remove for consistency. |

### Notes (13)

#### Typo in Basic.lean

| Line | Issue |
|------|-------|
| 226 | "satifies" should be "satisfies" |

#### Blank line inconsistency (11 files)

The following Completeness files have an extra blank line (line 9) between `module` and the first `public import`. The other 4 (D, K, TB, T) do not:

B, D4, D5, D45, DB, K4, K5, K45, KB5, S4, S5

---

## Part 2: Dead Code

### Confirmed Dead Code (25 declarations + 1 param + 2 imports)

#### Category 1: S5 backward-compatibility aliases (4 items)

**File**: `Metalogic/DerivationTree.lean`

| Line | Declaration | Notes |
|------|-------------|-------|
| 206 | `S5DerivationTree` | 0 references. Alias for `@DerivationTree Atom ModalAxiom`. |
| 209 | `S5Deriv` | 0 references. Alias for `@Deriv Atom ModalAxiom`. |
| 212 | `S5Derivable` | 0 references. Alias for `@Derivable Atom ModalAxiom`. |
| 215 | `s5DerivationSystem` | 0 references. Instantiation at `ModalAxiom`. |

#### Category 2: Unused set-derivability lemmas (2 items)

**File**: `Metalogic/Completeness.lean`

| Line | Declaration | Notes |
|------|-------------|-------|
| 440 | `ModalSetDerivable_of_mem` | 0 references. Membership implies set-derivability. |
| 449 | `ModalSetDerivable_weakening` | 0 references. Monotonicity of set-derivability. |

Note: `ModalSetDerivable_of_Derivable` (line 457) appears unused externally but is used internally by `ModalSetDerivable_empty_iff` (line 477) -- do NOT remove.

#### Category 3: Dead per-system convenience wrappers (5 items)

**File**: `Systems/T/Completeness.lean`

| Line | Declaration | Notes |
|------|-------------|-------|
| 52 | `t_canonical_refl` | Wrapper for `canonical_refl` at `TAxiom`. Not used by `t_strong_completeness`. |
| 65 | `t_truth_lemma` | Wrapper for `truth_lemma` at `TAxiom`. Not used by `t_strong_completeness`. |

**File**: `Systems/TB/Completeness.lean`

| Line | Declaration | Notes |
|------|-------------|-------|
| 55 | `tb_canonical_refl` | Wrapper for `canonical_refl` at `TBAxiom`. Not used. |
| 66 | `tb_canonical_symm` | Wrapper for `canonical_symm` at `TBAxiom`. Not used. |
| 81 | `tb_truth_lemma` | Wrapper for `truth_lemma` at `TBAxiom`. Not used. |

#### Category 4: Dead `_soundness_derivable` wrappers (13 items)

Each per-system soundness file defines `X_soundness_derivable` which is never called. Exception: K's `k_soundness_derivable` IS used by `ConservativeExtension.lean` and must be kept.

| File | Declaration |
|------|-------------|
| B/Soundness.lean | `b_soundness_derivable` |
| D/Soundness.lean | `d_soundness_derivable` |
| D4/Soundness.lean | `d4_soundness_derivable` |
| D5/Soundness.lean | `d5_soundness_derivable` |
| D45/Soundness.lean | `d45_soundness_derivable` |
| DB/Soundness.lean | `db_soundness_derivable` |
| K4/Soundness.lean | `k4_soundness_derivable` |
| K5/Soundness.lean | `k5_soundness_derivable` |
| K45/Soundness.lean | `k45_soundness_derivable` |
| KB5/Soundness.lean | `kb5_soundness_derivable` |
| S4/Soundness.lean | `s4_soundness_derivable` |
| S5/Soundness.lean | `s5_soundness_derivable` |
| T/Soundness.lean | `t_soundness_derivable` |
| TB/Soundness.lean | `tb_soundness_derivable` |

#### Category 5: Dead global instance (1 item)

**File**: `Metalogic/DeductionTheorem.lean`

| Line | Declaration | Notes |
|------|-------------|-------|
| 47-53 | `instance : HasHilbertTree (Proposition Atom)` | Global instance for `ModalAxiom`. Shadowed by `letI` in `deductionWithMem` and `deductionTheorem`. |

#### Category 6: Unused parameter (1 item)

**File**: `Metalogic/Completeness.lean`

| Line | Parameter | Notes |
|------|-----------|-------|
| 148 | `_h_T` in `canonical_eucl` | Axiom T hypothesis passed but never used. Already marked with `_`. Only S5 calls this (which has axiom T), so harmless but imprecise. |

#### Category 7: Redundant imports (2 items)

**File**: `Systems/K/Completeness.lean`

Lines 10-11: `public import Cslib.Logics.Modal.Metalogic.MCS` and `public import Cslib.Logics.Modal.Metalogic.Soundness` are redundant -- both transitively imported via `Cslib.Logics.Modal.Metalogic.Completeness` (line 9). Confirm with `lake shake`.

**File**: `Systems/T/Completeness.lean`

Lines 10-11: Same pattern.

### Suspected Dead Code (judgment call)

#### Entire files with 0 external consumers

- **`LogicalEquivalence.lean`**: `LogicallyEquivalent` and `LogicallyEquivalent.congruence` have 0 references. Valid library API but currently unused.
- **`Denotation.lean`**: `Proposition.denotation` and associated lemmas have 0 external references. Valid library API.

These are legitimate public API and should be kept as library contributions.

#### Public API with implicit consumers

Theorems tagged `@[scoped grind]` in `Basic.lean` (`Satisfies.dual`, `Satisfies.t_refl`, etc.) and `@[simp]` lemmas in `FromPropositional.lean` have 0 grep hits but are consumed implicitly by tactics. Do NOT remove.

### Merge Artifacts (0)

No leftover artifacts from the StrongCompleteness merge. The only remaining "StrongCompleteness" import is `Cslib.Logics.Propositional.Metalogic.StrongCompleteness` in `K/ConservativeExtension.lean`, which is valid (propositional, not modal).

---

## Summary

| Category | Count |
|----------|-------|
| CI blockers | 0 |
| Missing docstrings | 16 |
| @[simp] inconsistency | 1 |
| Typo | 1 |
| Blank line inconsistency | 11 files |
| Dead declarations (confirmed) | 25 |
| Unused parameter | 1 |
| Redundant imports | 2 |
| Merge artifacts | 0 |
| Files audited | 57 |
