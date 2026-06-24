# Research Report: LawfulBEq for Proposition and SignedFormula

## Task Summary

Add `LawfulBEq` instances for `Proposition Atom` and `SignedFormula F L`, then remove
~60 lines of workaround lemmas (`prop_beq_eq`, `proposition_beq_eq`) that manually prove
`(a == b) = true -> a = b`.

## Root Cause Analysis

When Lean 4 processes `deriving DecidableEq, BEq` on an inductive type, it generates **two
independent instances**:

1. `instDecidableEqProposition` -- structural decidable equality
2. `instBEqProposition` -- structural pattern-matching BEq

The derived `BEq` uses its own structural matcher rather than `decide (a = b)`. This means the
standard `LawfulBEq` instance (`instLawfulBEq`, which requires `BEq` to come from
`instBEqOfDecidableEq`) does not apply. Consequently, `eq_of_beq` and `beq_iff_eq` are
unavailable, forcing manual workaround lemmas at every call site.

## Recommended Approach

**Remove `BEq` from the `deriving` clause** of both `Proposition` and `SignedFormula`. When only
`DecidableEq` is derived, Lean's instance resolution picks up `instBEqOfDecidableEq`, which
defines `(a == b) = decide (a = b)`. The standard library then provides `instLawfulBEq`
automatically, giving `eq_of_beq`, `beq_iff_eq`, and `beq_self_eq_true` for free.

This approach was verified via `lean_run_code` with a simulated `Proposition`-like inductive and
a simulated `SignedFormula`-like structure. Both `BEq` and `LawfulBEq` resolve correctly via
typeclass inference after removing `BEq` from deriving. Computational behavior (via `#eval`)
is preserved since `DecidableEq` for inductives is itself structural.

### Alternative Considered and Rejected

Keeping the derived `BEq` and proving `LawfulBEq` manually (as done for `Sign` in `Sign.lean`)
would require writing a ~30-line inductive proof for `Proposition.eq_of_beq` -- essentially
identical to the workaround lemmas we want to eliminate. The "remove from deriving" approach
achieves the same result with zero new proof code.

## Exact Changes Required

### Phase 1: Core Type Changes

**File: `Cslib/Logics/Propositional/Defs.lean`**
- Line 92: Change `deriving DecidableEq, BEq` to `deriving DecidableEq, Repr`
  - Adds `Repr` for debugging (optional, per task description)
  - Removes `BEq` so `instBEqOfDecidableEq` provides it
  - `LawfulBEq` becomes automatically available

**File: `Cslib/Foundations/Logic/Tableau/SignedFormula.lean`**
- Line 56: Change `deriving DecidableEq, BEq, Hashable` to `deriving DecidableEq, Hashable`
  - `BEq` will come from `instBEqOfDecidableEq` (conditional on `F` and `L` having `DecidableEq`)
  - `LawfulBEq` is then automatic when `F` and `L` have `DecidableEq`
  - `Hashable` derivation is independent of `BEq` and unaffected

### Phase 2: Delete Workaround Lemmas

**File: `Cslib/Logics/Propositional/Tableau/Classical/Soundness.lean`**
- Delete lines 128-157: `private lemma prop_beq_eq` (30 lines)

**File: `Cslib/Logics/Propositional/Tableau/Minimal/Soundness.lean`**
- Delete lines 80-116: section header + `lemma proposition_beq_eq` (~37 lines including docstring)

### Phase 3: Replace Call Sites

**Pattern A: `prop_beq_eq _ _ h` or `proposition_beq_eq _ _ h`**
Replace with: `eq_of_beq h`

| File | Line | Old | New |
|------|------|-----|-----|
| Classical/Soundness.lean | 461 | `prop_beq_eq _ _ hbot_eq` | `eq_of_beq hbot_eq` |
| Classical/Soundness.lean | 487 | `prop_beq_eq _ _ hformEq` | `eq_of_beq hformEq` |
| Minimal/Soundness.lean | 150 | `proposition_beq_eq _ _ hneg_form_b` | `eq_of_beq hneg_form_b` |
| Minimal/Completeness.lean | 111 | `Cslib.Logic.PL.proposition_beq_eq _ _ hpos_form_b` | `eq_of_beq hpos_form_b` |
| Minimal/Completeness.lean | 113 | `Cslib.Logic.PL.proposition_beq_eq _ _ hneg_form_b` | `eq_of_beq hneg_form_b` |
| Classical/Completeness.lean | 112 | `prop_beq_eq _ _ hsfpos_cond.2` | `eq_of_beq hsfpos_cond.2` |
| Classical/Completeness.lean | 113 | `prop_beq_eq _ _ hsfneg_cond.2` | `eq_of_beq hsfneg_cond.2` |
| Classical/Completeness.lean | 161 | `prop_beq_eq _ _ hsfcond.2` | `eq_of_beq hsfcond.2` |
| Classical/Completeness.lean | 255 | `prop_beq_eq _ _ hsfcond.2` | `eq_of_beq hsfcond.2` |
| Classical/Completeness.lean | 327 | `prop_beq_eq _ _ hsfcond.2` | `eq_of_beq hsfcond.2` |
| Classical/Completeness.lean | 344 | `prop_beq_eq _ _ hsfcond.2` | `eq_of_beq hsfcond.2` |
| Classical/Completeness.lean | 367 | `prop_beq_eq _ _ hsfcond.2` | `eq_of_beq hsfcond.2` |
| Classical/Completeness.lean | 388 | `prop_beq_eq _ _ hsfcond.2` | `eq_of_beq hsfcond.2` |

**Pattern B: `simp [hf, BEq.beq, instBEqProposition.beq] at hbot_form`**
Replace with: `simp [beq_iff_eq, hf] at hbot_form`

| File | Lines | Count |
|------|-------|-------|
| Intuitionistic/Soundness.lean | 296-299 | 4 lines |

**Pattern C: Comments referencing workaround**
- Minimal/Soundness.lean line 147: Update comment about `proposition_beq_eq`
- Minimal/Completeness.lean lines 108-109: Update comment about `instBEqProposition.beq`

### Phase 4: Optional Cleanup

- Remove stale comments referencing `instBEqProposition` in Minimal/Completeness.lean
- Minimal/Completeness.lean line 107 can now include formula BEq in the same `beq_iff_eq` simp:
  ```
  simp only [beq_iff_eq] at hpos_sign_b hneg_sign_b hpos_label_b hneg_label_b hpos_form_b hneg_form_b
  ```
  eliminating lines 110-113 entirely.

## Files NOT Affected

- `Sign.lean` -- already has explicit `LawfulBEq` instance; no change needed
- `Branch.lean` -- uses `[BEq (SignedFormula F L)]` constraint; will resolve via `instBEqOfDecidableEq`
- Bimodal `SignedFormula.lean` -- already follows the correct pattern (no `BEq` in deriving)
- Test files (`Test_Full.lean`, `Test_PersSimple.lean`, `Test_MainProof.lean`) -- scratch files,
  not in library build; they have their own copies of the workaround but are outside scope

## Risk Assessment

**Low risk.** The change is mechanical:
1. The `BEq` computational behavior is preserved (both paths ultimately do structural comparison).
2. All replacement patterns were verified via `lean_run_code`.
3. The bimodal codebase already uses this exact pattern successfully.
4. No sorry is introduced; this is purely a refactoring task.

**One subtlety:** The `change false = true at h` pattern inside the workaround lemma bodies
relies on the derived BEq reducing `(.atom x == .bot)` to `false` directly. But these lines
are inside the lemmas being deleted, so they are not a concern.

## Reuse Check

- `LawfulBEq` is a standard Lean 4 typeclass (in `Init.Core`).
- `instBEqOfDecidableEq` and `instLawfulBEq` are standard library instances.
- No new abstractions, typeclasses, or definitions are needed.
- The Bimodal module (`Cslib/Logics/Bimodal/Metalogic/Decidability/`) already follows this pattern.

## Line Count Impact

- Lines deleted: ~67 (prop_beq_eq: 30, proposition_beq_eq: 30, associated comments: ~7)
- Lines added: 0 (all replacements are shorter or equal length)
- Net: approximately -60 lines
