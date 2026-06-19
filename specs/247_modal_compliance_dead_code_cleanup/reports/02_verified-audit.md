# Verified Audit: Modal/ Compliance and Dead Code

## Verification Summary

All line numbers, declarations, and issues from the original audit report
(`01_compliance-dead-code-audit.md`) have been verified against the current
codebase state (post-task 246 StrongCompleteness merge, commit `9532b603`).

**Result**: All items are confirmed accurate. No line numbers have shifted.
One count discrepancy found in the original report (corrected below).

---

## Part 1: Compliance Issues -- VERIFIED

### Warnings (17 missing docstrings) -- ALL CONFIRMED

#### Basic.lean (4 missing docstrings)

| Line | Declaration | Status |
|------|-------------|--------|
| 106 | `instance : Bot (Proposition Atom)` | CONFIRMED |
| 187 | `instance : HasInferenceSystem (Judgement World Atom)` | CONFIRMED |
| 192 | `theorem derivation_def` | CONFIRMED |
| 234 | `theorem TheoryEq.ext_iff` | CONFIRMED |

#### Cube.lean (6 missing docstrings)

| Line | Declaration | Status |
|------|-------------|--------|
| 99 | `theorem k_subset_d` | CONFIRMED |
| 102 | `theorem k_subset_b` | CONFIRMED |
| 105 | `theorem k_subset_four` | CONFIRMED |
| 108 | `theorem k_subset_five` | CONFIRMED |
| 112 | `theorem d_subset_t` | CONFIRMED |
| 115 | `theorem k_subset_t` | CONFIRMED |

#### DerivationTree.lean (6 missing docstrings)

| Line | Declaration | Status |
|------|-------------|--------|
| 139 | `theorem height_modus_ponens_left` | CONFIRMED |
| 144 | `theorem height_modus_ponens_right` | CONFIRMED |
| 149 | `theorem height_weakening` | CONFIRMED |
| 172 | `theorem mp_deriv` | CONFIRMED |
| 178 | `theorem weakening_deriv` | CONFIRMED |
| 184 | `theorem assumption_deriv` | CONFIRMED |

#### K/Completeness.lean (1 `@[simp]` inconsistency)

| Line | Declaration | Issue | Status |
|------|-------------|-------|--------|
| 332 | `@[simp] theorem k_strong_completeness_iff` | Only system with `@[simp]` on `_strong_completeness_iff`. Remove for consistency. | CONFIRMED |

### Notes -- ALL CONFIRMED

#### Typo in Basic.lean

| Line | Issue | Status |
|------|-------|--------|
| 226 | "satifies" should be "satisfies" | CONFIRMED at line 226: `set of all propositions that it satifies.` |

#### Blank line inconsistency (11 files)

The following Completeness files have an extra blank line (line 9) between
`module` and the first `public import`. The other 4 (D, K, TB, T) do not:

B, D4, D5, D45, DB, K4, K5, K45, KB5, S4, S5

**CONFIRMED**: Line 9 is empty in all 11 files; line 9 is a `public import` in D, K, TB, T.

---

## Part 2: Dead Code -- VERIFIED

### Count Correction

The original audit report header says "Category 4: Dead `_soundness_derivable` wrappers (13 items)"
but the table lists **14 items** (B, D, D4, D5, D45, DB, K4, K5, K45, KB5, S4, S5, T, TB).
The corrected total for Category 4 is **14** dead wrappers (K's is the only one used, by
`ConservativeExtension.lean`).

Corrected total dead declarations: **26** (was 25 in original report).

### Category 1: S5 backward-compatibility aliases (4 items) -- CONFIRMED

**File**: `Metalogic/DerivationTree.lean`

| Line | Declaration | Status |
|------|-------------|--------|
| 206 | `S5DerivationTree` | CONFIRMED: 0 external references |
| 209 | `S5Deriv` | CONFIRMED: 0 external references |
| 212 | `S5Derivable` | CONFIRMED: 0 external references |
| 215 | `s5DerivationSystem` | CONFIRMED: 0 external references |

### Category 2: Unused set-derivability lemmas (2 items) -- CONFIRMED

**File**: `Metalogic/Completeness.lean`

| Line | Declaration | Status |
|------|-------------|--------|
| 440 | `ModalSetDerivable_of_mem` | CONFIRMED: 0 external references |
| 449 | `ModalSetDerivable_weakening` | CONFIRMED: 0 external references |

Note: `ModalSetDerivable_of_Derivable` (line 457) is used internally by
`ModalSetDerivable_empty_iff` (line 477) -- do NOT remove.

### Category 3: Dead per-system convenience wrappers (5 items) -- CONFIRMED

**File**: `Systems/T/Completeness.lean`

| Line | Declaration | Status |
|------|-------------|--------|
| 52 | `t_canonical_refl` | CONFIRMED: 0 external references |
| 65 | `t_truth_lemma` | CONFIRMED: 0 external references |

**File**: `Systems/TB/Completeness.lean`

| Line | Declaration | Status |
|------|-------------|--------|
| 55 | `tb_canonical_refl` | CONFIRMED: 0 external references |
| 66 | `tb_canonical_symm` | CONFIRMED: 0 external references |
| 81 | `tb_truth_lemma` | CONFIRMED: 0 external references |

### Category 4: Dead `_soundness_derivable` wrappers (14 items) -- CONFIRMED

Each per-system soundness file defines `X_soundness_derivable` which is never called.
**Exception**: K's `k_soundness_derivable` IS used by `ConservativeExtension.lean` (line 51)
and must be kept.

| File | Declaration | Decl Line | Status |
|------|-------------|-----------|--------|
| B/Soundness.lean | `b_soundness_derivable` | 78 | CONFIRMED dead |
| D/Soundness.lean | `d_soundness_derivable` | 79 | CONFIRMED dead |
| D4/Soundness.lean | `d4_soundness_derivable` | 90 | CONFIRMED dead |
| D5/Soundness.lean | `d5_soundness_derivable` | 91 | CONFIRMED dead |
| D45/Soundness.lean | `d45_soundness_derivable` | 99 | CONFIRMED dead |
| DB/Soundness.lean | `db_soundness_derivable` | 90 | CONFIRMED dead |
| K4/Soundness.lean | `k4_soundness_derivable` | 89 | CONFIRMED dead |
| K5/Soundness.lean | `k5_soundness_derivable` | 80 | CONFIRMED dead |
| K45/Soundness.lean | `k45_soundness_derivable` | 100 | CONFIRMED dead |
| KB5/Soundness.lean | `kb5_soundness_derivable` | 100 | CONFIRMED dead |
| S4/Soundness.lean | `s4_soundness_derivable` | 97 | CONFIRMED dead |
| S5/Soundness.lean | `s5_soundness_derivable` | 93 | CONFIRMED dead |
| T/Soundness.lean | `t_soundness_derivable` | 82 | CONFIRMED dead |
| TB/Soundness.lean | `tb_soundness_derivable` | 98 | CONFIRMED dead |

### Category 5: Dead global instance (1 item) -- CONFIRMED

**File**: `Metalogic/DeductionTheorem.lean`

| Line | Declaration | Status |
|------|-------------|--------|
| 47-53 | `instance : HasHilbertTree (Proposition Atom)` | CONFIRMED: Global instance for `ModalAxiom`. Shadowed by `letI` at lines 71 and 130 in `deductionWithMem` and `deductionTheorem`. |

### Category 6: Unused parameter (1 item) -- CONFIRMED

**File**: `Metalogic/Completeness.lean`

| Line | Parameter | Status |
|------|-----------|--------|
| 148 | `_h_T` in `canonical_eucl` | CONFIRMED: Axiom T hypothesis passed but never used. Already marked with `_`. |

### Category 7: Redundant imports (2 items) -- CONFIRMED

**File**: `Systems/K/Completeness.lean` (lines 10-11)

```
public import Cslib.Logics.Modal.Metalogic.MCS       -- redundant
public import Cslib.Logics.Modal.Metalogic.Soundness  -- redundant
```

Both are already transitively imported via `Cslib.Logics.Modal.Metalogic.Completeness` (line 9).
Confirmed: `Metalogic/Completeness.lean` does `public import` both `MCS` and `Soundness`.
No other system Completeness file has these redundant imports (only K and T).

**File**: `Systems/T/Completeness.lean` (lines 10-11)

Same pattern. Both `MCS` and `Soundness` are redundant.

Note: `lake shake` does not flag these because they are `public import`s with `--keep-implied`.
They are safe to remove since the parent (`Completeness.lean`) also uses `public import` for
both, so the re-export path is preserved.

---

## PR Description Line Numbers -- VERIFIED

All 45 GitHub line-number links in `specs/247_modal_compliance_dead_code_cleanup/pr-description.md`
have been verified against the current codebase. **All links are accurate; no updates needed.**

Verified links include:
- 15 ProofSystem/Instances links (axiom definitions)
- 15 strong_soundness links
- 15 strong_completeness links

---

## Corrected Summary

| Category | Count |
|----------|-------|
| CI blockers | 0 |
| Missing docstrings | 16 (plus 1 `@[simp]` inconsistency = 17 warnings total) |
| `@[simp]` inconsistency | 1 |
| Typo | 1 |
| Blank line inconsistency | 11 files |
| Dead declarations (confirmed) | **26** (corrected from 25) |
| Unused parameter | 1 |
| Redundant imports | 2 (in K and T Completeness files) |
| Merge artifacts | 0 |
| Files audited | 57 |
| Items already addressed | 0 |
| All items still actionable | Yes |

### Breakdown of 26 Dead Declarations

| Category | Count |
|----------|-------|
| S5 backward-compat aliases | 4 |
| Unused ModalSetDerivable lemmas | 2 |
| Dead per-system wrappers (T, TB) | 5 |
| Dead `_soundness_derivable` wrappers | **14** (corrected from 13) |
| Dead HasHilbertTree instance | 1 |
| **Total** | **26** |
