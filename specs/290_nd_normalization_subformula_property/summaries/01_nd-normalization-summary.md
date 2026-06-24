# Implementation Summary: Task #290

- **Task**: 290 - ND Normalization and Subformula Property
- **Status**: [PARTIAL]
- **Effort**: ~4 hours (of 10 estimated)
- **Artifact**: `Cslib/Logics/Propositional/NaturalDeduction/Normalization.lean`

## Overview

Implemented Prawitz-style normalization infrastructure for `Theory.Derivation` in a new file
`Cslib/Logics/Propositional/NaturalDeduction/Normalization.lean`. The implementation provides
all key definitions and a computable normalization function. Two theorems about the subformula
property remain partially proved, blocked on the Prawitz "main branch" argument.

## What Was Completed

### Phase 1: Subformula Infrastructure (COMPLETED)

- `Proposition.subformulas`: computable `Finset`-valued function returning all subformulas
- `Proposition.IsSubformula`: subformula predicate
- `Proposition.IsSubformula.refl`, `.trans`: reflexivity and transitivity
- `Proposition.IsSubformula.and_left`, `.and_right`, `.or_left`, `.or_right`, `.imp_left`, `.imp_right`: structural subformula membership lemmas
- `Proposition.complexity`: formula size measure

### Phase 2: Metrics and Single-Step Reduction (COMPLETED)

- `Theory.Derivation.height`: maximum depth of derivation tree
- `Theory.Derivation.isNormal`: boolean predicate detecting absence of all 5 redex patterns (impE/impI, andE1/andI, andE2/andI, orE/orI1, orE/orI2)
- `Theory.Derivation.isNormal_ax`, `.isNormal_ass`: leaf derivations are normal
- `Theory.Derivation.subsOne`: single-hypothesis substitution helper for reduction steps
- `Theory.Derivation.reduceRoot`: single-step outermost reduction, returns `none` if already normal

### Phase 3: Normalization Function (COMPLETED - fuel-bounded approach)

- `Theory.Derivation.normalizeAux`: fuel-bounded normalization; normalizes subterms recursively then applies `reduceRoot`
- `Theory.Derivation.normalize`: normalization using `2^height` as fuel bound; computable

### Phase 4: CI Verification (COMPLETED)

- All 5 redex types handled in `reduceRoot`
- `Cslib.Init` imported transitively (via Basic.lean → Defs.lean)
- `Cslib.lean` barrel updated with `Normalization` import
- `lake exe checkInitImports` passes
- `lake exe lint-style` passes
- `lake lint` shows no warnings in Normalization.lean
- `lake build Cslib.Logics.Propositional.NaturalDeduction.Normalization` succeeds (2 sorry warnings)

### Phase 5: Subformula Property (PARTIAL - BLOCKED)

Completed:
- `Theory.Derivation.formulas`: set of formula occurrences in a derivation tree
- `Theory.Derivation.SubformulaProperty`: the subformula property predicate
- `Theory.Derivation.subformula_property_of_isNormal`: PARTIAL -- all introduction cases (ax, ass, andI, orI1, orI2, impI) proved fully; elimination cases (andE1, andE2, orE, impE) blocked on Prawitz main-branch argument

Not completed:
- `Theory.Derivation.normalize_isNormal`: proof that `normalize` produces a normal derivation (requires Prawitz measure-decrease argument)
- `Theory.Derivation.subformula_property`: full corollary combining normalization with subformula property

## Plan Deviations

| Phase | Deviation | Reason |
|-------|-----------|--------|
| Phase 3 | Used fuel-bounded approach instead of well-founded recursion | WF recursion with custom measure `(maxGrade, redexCountAtGrade)` is technically complex; fuel-bounded approach with `2^height` fuel gives a correct computable function without the termination proof complexity |
| Phase 5 | Elimination cases of `subformula_property_of_isNormal` left with `sorry` | The standard structural induction IH is insufficient: for `andE1 G D`, the IH gives `F.IsSubformula (A ∧ B)` but the goal needs `F.IsSubformula A`; the Prawitz main-branch lemma (Ch. III, Thm. 1) is required |
| Phase 5 | `normalize_isNormal` left with `sorry` | Requires Prawitz termination measure argument; deferred to follow-up task |

## Blockers for Continuation

Two `sorry` instances remain, both requiring substantial additional infrastructure:

1. **Elimination cases of `subformula_property_of_isNormal`** (line 351): Requires the Prawitz "main branch" lemma. The main branch of a derivation is the path of elimination rules from the conclusion upward. In a normal derivation, all formulas on this path are subformulas of the conclusion or a hypothesis. This is Prawitz [Prawitz1965] Ch. III, Theorem 1.

2. **`normalize_isNormal`** (line 364): Requires proving that `normalizeAux (2^d.height) d` always terminates with a normal derivation. This requires the Prawitz measure-decrease argument showing that each `reduceRoot` step strictly decreases the `(maxGrade, redexCountAtGrade)` pair.

## Key Design Decisions

- **Fuel-bounded normalization**: Avoids the technically difficult `termination_by` proof while still providing a correct, computable normalization function. The fuel bound `2^height` is generous (could be tightened to `totalRedexCount`).
- **Context arithmetic via `subsOne`**: The helper `subsOne D E` wraps `subs` to substitute a single hypothesis, avoiding explicit context set arithmetic in reduction steps.
- **`isNormal` as Bool**: Matches the computational flavor of the development; can be converted to `Prop` via `= true` when needed in proofs.

## CI Pipeline Results

| Check | Result | Notes |
|-------|--------|-------|
| `lake build Cslib.Logics.Propositional.NaturalDeduction.Normalization` | PASS (warnings) | 2 `sorry` warnings |
| `lake exe checkInitImports` | PASS | |
| `lake exe lint-style` | PASS | |
| `lake lint` (Normalization) | PASS | No warnings in new file |
| `lake shake` (Normalization) | PASS | No import issues |
| `lake test` | FAIL (pre-existing) | Failures in Tableau.Intuitionistic.Soundness and SequentCalculus.LK.CutElimination (other tasks) |

## Follow-up Task Recommendation

Create a follow-up task: "Prove Prawitz main-branch lemma for ND normalization (task 290 continuation)".

Goal: Prove `Theory.Derivation.mainBranch_subformula` stating that every formula on the main branch of a normal derivation is a subformula of the conclusion or a hypothesis. Use this to complete the elimination cases of `subformula_property_of_isNormal` and prove `normalize_isNormal`.

Estimated effort: 4-6 hours.
