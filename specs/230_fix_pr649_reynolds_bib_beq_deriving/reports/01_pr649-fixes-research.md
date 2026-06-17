# Research Report: Fix PR #649 (Reynolds Bib Key + BEq Deriving)

**Task**: 230
**Session**: sess_1781724665_ae5019
**Branch**: feat/temporal-formula-propositional

## Issue 1: Reynolds1994 Bib Key Mismatch

**File**: `references.bib`, line 645
**Current key**: `Reynolds1994`
**Year field**: `1996`
**DOI**: `10.1093/logcom/6.5.679` (confirms 1996 publication)

The bib entry for Mark Reynolds, "Axiomatising First-Order Temporal Logic: Until and Since
over Linear Time" in *Journal of Logic and Computation* has key `Reynolds1994` but the year
field is `1996`. The DOI resolves to the 1996 publication. The key should be `Reynolds1996`.

**Scope of change**: Only `references.bib` line 645 needs updating. No Lean files, no
markdown files, and no doc-comments reference `Reynolds1994`. The key is not used in any
`[BibKey]` citation bracket in Lean source files.

**Fix**: Change `@article{Reynolds1994,` to `@article{Reynolds1996,` on line 645.

## Issue 2: Missing BEq in Temporal.Formula Deriving Clause

**File**: `Cslib/Logics/Temporal/Syntax/Formula.lean`

The `Temporal.Formula` inductive type derives only `DecidableEq`:

```lean
deriving DecidableEq
```

The `LTL.Formula` inductive type (in `Cslib/Logics/LTL/Syntax/Formula.lean`) derives both:

```lean
deriving DecidableEq, BEq
```

For consistency, `Temporal.Formula` should also derive `BEq`.

**Fix**: Change `deriving DecidableEq` to `deriving DecidableEq, BEq` in
`Cslib/Logics/Temporal/Syntax/Formula.lean`.

**Risk**: None. `BEq` is automatically derived from `DecidableEq` when explicitly requested
and adds a `BEq` instance that defers to `DecidableEq`. There is no behavioral change, only
an explicit instance registration for API consistency.

## Implementation Summary

Two single-line edits:

| File | Line | Change |
|------|------|--------|
| `references.bib` | 645 | `Reynolds1994` -> `Reynolds1996` |
| `Cslib/Logics/Temporal/Syntax/Formula.lean` | ~49 | `deriving DecidableEq` -> `deriving DecidableEq, BEq` |

No blockers. Both changes are cosmetic and safe.
