# Implementation Summary: Subformula Property for LK

- **Task**: 329 - Prove the subformula property as a corollary of cut elimination
- **Status**: [COMPLETED]
- **Session**: sess_1782300531_c471d6_329
- **Date**: 2026-06-24

## What Was Implemented

Created `Cslib/Logics/Propositional/SequentCalculus/LK/SubformulaProperty.lean` with:

1. **`Proposition.lkSubformulas`** (`def`): Recursive Finset-valued function computing all
   subformulas of a proposition, including itself. Defined locally to avoid an import conflict
   between `Normalization.lean` (which also defines `Proposition.complexity`) and
   `CutElimination.lean` (which transitively imports `Tableau.Defs`, which also defines
   `Proposition.complexity`).

2. **`Proposition.LKIsSubformula`** (`def`): Subformula predicate for LK.

3. **Supporting lemmas**: `refl`, `trans`, `and_left`, `and_right`, `or_left`, `or_right`,
   `imp_left`, `imp_right` for `LKIsSubformula`.

4. **`LKProof.formulas`** (`def`): Recursive Finset collector of all formulas from all
   sequents in an LK proof tree. Covers all 11 constructors (ax, botL, andL, andR, orL,
   orR, impL, impR, weakL, weakR, cut). Leaves collect antecedent ∪ succedent; unary rules
   propagate from the sub-proof; binary rules union both sub-proof collections.

5. **`CutFreeLKProof.subformula_property`** (`lemma`): Every formula in a cut-free LK proof
   of `Γ ⊢ₛ Δ` is a subformula of some formula in `Γ ∪ Δ`. Proved via a private helper
   `cutFreeSubformulaProp` that takes `(d : LKProof seq) (hcf : CutFree d)` separately,
   enabling `induction d with` to proceed (avoiding Finset-quotient index failures). The
   cut case is vacuously discharged since `CutFree` is `False` for cut steps.

6. **`LKProof.subformula_property`** (`theorem`): Every LK proof has a cut-free variant
   satisfying the subformula property. Uses `LKProof.cutElim` to obtain a cut-free proof
   and applies `cutFreeSubformulaProp`.

## Plan Deviations

1. **Normalization.lean import dropped**: The plan said to import `Normalization.lean` for
   `Proposition.subformulas` and `Proposition.IsSubformula`. This was impossible because
   `CutElimination.lean` transitively imports `Tableau.Defs` which defines
   `Proposition.complexity`, and `Normalization.lean` also defines `Proposition.complexity`,
   causing an "environment already contains" conflict. The definitions were instead created
   locally with names `Proposition.lkSubformulas` and `Proposition.LKIsSubformula`.

2. **Helper function pattern**: The core proof uses a private helper `cutFreeSubformulaProp`
   with signature `(d : LKProof seq) (hcf : CutFree d)` rather than a single tactic proof.
   This matches the pattern of `CutFree.mono` in `CutElimination.lean` and avoids the
   "Index in target's type is not a variable" error that occurs when the sequent index is
   fixed in `CutFreeLKProof`.

## Verification Results

- `lake build Cslib.Logics.Propositional.SequentCalculus.LK.SubformulaProperty`: PASSED
- `lake build Cslib.Logics.Propositional.SequentCalculus.LK`: PASSED
- `lake exe lint-style -- Cslib/Logics/Propositional/SequentCalculus/LK/SubformulaProperty.lean`: PASSED
- `lake shake --add-public --keep-implied --keep-prefix`: No issues for our file
- `lake lint` (grep for SubformulaProperty): No warnings
- `lake test`: FAILED (pre-existing `Tableau/Classical/Completeness.lean` error, unrelated)
- `lake exe checkInitImports`: FAILED (same pre-existing issue)
- Zero sorries, zero new axioms
- `import Cslib.Init` present on line 9

## Files Created/Modified

- `Cslib/Logics/Propositional/SequentCalculus/LK/SubformulaProperty.lean` (new, ~340 lines)
- `Cslib/Logics/Propositional/SequentCalculus/LK.lean` (added SubformulaProperty import)
- `Cslib.lean` (auto-updated by `lake exe mk_all --module`)
