# Implementation Plan: Task #290 (Revised)

- **Task**: 290 - ND Normalization and Subformula Property
- **Status**: [IMPLEMENTING]
- **Effort**: 14 hours (10 hours completed + 4 hours remaining)
- **Dependencies**: None (task 266 completed and archived; Derivation type and subs already in place)
- **Research Inputs**:
  - specs/290_nd_normalization_subformula_property/reports/01_nd-normalization-research.md
  - specs/290_nd_normalization_subformula_property/reports/02_blocker-hard-research.md
- **Artifacts**: plans/02_nd-normalization-plan-revised.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-formats.md, tasks.md
- **Type**: cslib
- **Lean Intent**: true

## Overview

This is a revised plan for ND normalization incorporating the critical finding from hard-mode
research (report 02): the theorem `subformula_property_of_isNormal` is **false as stated**. A
concrete Lean counterexample shows that `andE1(orE(ass, andI(ass,ass), andI(ass,ass)))` passes
`isNormal = true` but contains `r /\ r` which is not a subformula of the conclusion `r` or
any hypothesis.

The root cause: `isNormal` misses 4 commuting conversion (permutative reduction) patterns --
reductions that push elimination contexts inside `orE` branches. Phases 1-4 from the original
plan are completed and correct. Phase 5 (subformula property) is replaced with a multi-step
phase that addresses the false theorem by defining `isStronglyNormal`, extending `reduceRoot`
with commuting reductions, and proving the subformula property via a two-phase approach
(conclusion grounding lemma + structural induction).

### Research Integration

Reports integrated into this plan:
- `01_nd-normalization-research.md` (integrated in plan v1, preserved)
- `02_blocker-hard-research.md` (newly integrated -- provides counterexample, root cause
  analysis, and the two-phase proof strategy)

### Prior Plan Reference

`plans/01_nd-normalization-plan.md` -- original plan with 5 phases. Phases 1-4 completed
successfully. Phase 5 blocked due to false theorem statement (now understood via report 02).

## Goals & Non-Goals

**Goals**:
- Define `isStronglyNormal` predicate excluding both proper redexes AND commuting conversions
- Extend `reduceRoot` with commuting conversion cases (andE1/andE2/impE/orE of orE)
- Prove `conclusion_grounded_or_intro` lemma for elimination-headed strongly normal derivations
- Prove `subformula_property_of_isStronglyNormal` using the two-phase approach
- Prove `normalize` (with extended reductions) produces strongly normal derivations
- Replace the 2 remaining `sorry` instances with complete proofs

**Non-Goals**:
- Removing or refactoring Phases 1-4 code (completed and correct)
- Proving strong normalization (every reduction sequence terminates)
- Proving confluence (Church-Rosser property)
- Extending to classical logic (CPL) or modal logic
- Implementing the nested `orE(orE ...)` commuting conversion if simpler alternatives suffice

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Context arithmetic for commuting conversions (weakening minor premises into extended contexts) | M | M | `weakCtx` already exists in Basic.lean; use `subsOne`-style convenience wrappers |
| Termination measure for extended normalization may not account for commuting conversions | H | M | Commuting conversions reduce "elimination depth inside orE"; if needed, add permutation depth to the fuel bound |
| `conclusion_grounded_or_intro` induction may require careful case splits | M | L | The strongly normal condition ensures major premises of eliminations are never intro-headed or orE-headed, limiting cases |
| Nested `orE` commuting conversion is complex (3 sub-derivations + weakening) | M | M | Start with the 3 simpler cases (andE1/andE2/impE); add orE case only if needed for the proof |
| Fuel bound `2^height` may be insufficient with commuting conversions | L | M | Each commuting conversion strictly reduces elimination depth in orE; multiply fuel by node count if needed |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1, 2, 3, 4 | -- (completed) |
| 2 | 5 | 1-4 |

Phases within the same wave can execute in parallel.

---

### Phase 1: Subformula Infrastructure and isNormal Predicate [COMPLETED]

**Goal**: Define `Proposition.subformulas`, `Proposition.IsSubformula`, `Derivation.height`,
and `Derivation.isNormal` with basic lemmas.

**Completed**: All definitions and lemmas in place. `Proposition.subformulas`,
`Proposition.IsSubformula` with refl/trans/and_left/and_right/or_left/or_right/imp_left/imp_right,
`Proposition.complexity`, `Derivation.height`, `Derivation.isNormal` with 5 redex patterns.

**Files**: `Cslib/Logics/Propositional/NaturalDeduction/Normalization.lean`

---

### Phase 2: Derivation Metrics and Single-Step Reduction [COMPLETED]

**Goal**: Define `subsOne` convenience wrapper and `reduceRoot` for 5 proper redex types.

**Completed**: `subsOne` defined for single-formula substitution. `reduceRoot` handles all 5
proper redex patterns (impE/impI, andE1/andI, andE2/andI, orE/orI1, orE/orI2).

**Files**: `Cslib/Logics/Propositional/NaturalDeduction/Normalization.lean`

---

### Phase 3: Normalization Function with Fuel-Bounded Termination [COMPLETED]

**Goal**: Define `normalizeAux` (fuel-bounded) and `normalize` functions.

**Completed**: `normalizeAux` with fuel parameter and `normalize` defined as
`d.normalizeAux (2 ^ d.height)`. Fuel-bounded approach chosen over WF recursion.

**Files**: `Cslib/Logics/Propositional/NaturalDeduction/Normalization.lean`

---

### Phase 4: Full Connective Verification and Cleanup [COMPLETED]

**Goal**: Verify all 5 redex types handled, add docstrings, run CI.

**Completed**: All redex types covered. `formulas` and `SubformulaProperty` definitions added.
CI passes (lake build, checkInitImports, lint-style). 2 sorries remain in Phase 5 theorems.

**Files**: `Cslib/Logics/Propositional/NaturalDeduction/Normalization.lean`, `Cslib.lean`

---

### Phase 5: Strong Normalization and Subformula Property [IN PROGRESS]

**Goal**: Fix the false theorem by defining `isStronglyNormal`, extending `reduceRoot` with
commuting conversions, proving `conclusion_grounded_or_intro`, and completing the subformula
property proof. Remove all `sorry` instances.

**Rationale**: Report 02 proved `subformula_property_of_isNormal` is false via a concrete
counterexample: `andE1(orE(ass, andI(ass,ass), andI(ass,ass)))` passes `isNormal = true` but
violates SubformulaProperty. The root cause is 4 missing commuting conversion checks in
`isNormal`. The fix follows the two-phase proof strategy from Prawitz [Prawitz1965] Ch. V and
Troelstra-Schwichtenberg [TroelstraSchwichtenberg2000] Sec. 6.1.

**Tasks**:

*Step 5a: Define isStronglyNormal (~30-40 lines)*
- [ ] Define `Theory.Derivation.isStronglyNormal : T.Derivation G A -> Bool` adding 4 commuting conversion checks to the 5 proper redex checks from `isNormal`:
  - `andE1 _ (orE _ _ _ _) => false` (commuting)
  - `andE2 _ (orE _ _ _ _) => false` (commuting)
  - `impE (orE _ _ _ _) _ => false` (commuting)
  - `orE _ (orE _ _ _ _) _ _ => false` (commuting, optional -- may be covered transitively)
- [ ] Prove `isStronglyNormal_implies_isNormal : d.isStronglyNormal = true -> d.isNormal = true` (simple structural induction -- strong normality is strictly stronger)
- [ ] Define `Theory.Derivation.isIntroRoot : T.Derivation G A -> Bool` classifying whether a derivation is introduction-headed (andI, orI1, orI2, impI) vs elimination-headed (andE1, andE2, orE, impE) vs leaf (ax, ass)

*Step 5b: Extend reduceRoot with commuting reductions (~20-40 lines)*
- [ ] Add commuting conversion cases to `reduceRoot`:
  - `andE1 G (orE G' D DA DB) => some (orE G D (andE1 _ DA) (andE1 _ DB))`
  - `andE2 G (orE G' D DA DB) => some (orE G D (andE2 _ DA) (andE2 _ DB))`
  - `impE (orE G D DA DB) E => some (orE G D (impE DA (E.weakCtx ...)) (impE DB (E.weakCtx ...)))`
  - `orE G (orE G' D DA DB) EA EB => some (orE G D (orE _ DA (EA.weakCtx ...) (EB.weakCtx ...)) (orE _ DB (EA.weakCtx ...) (EB.weakCtx ...)))` (if needed)
- [ ] Verify `reduceRoot` compiles with the new cases (context types must align)
- [ ] If context arithmetic for impE/orE commuting conversions is complex, define helper lemmas for the required weakening operations

*Step 5c: Prove conclusion_grounded_or_intro (~60-100 lines)*
- [ ] Prove the key lemma:
  ```lean
  theorem conclusion_grounded_or_intro (d : T.Derivation G A)
      (hn : d.isStronglyNormal = true) :
      (exists C, C in G /\ A.IsSubformula C) \/
      (exists C, C in T /\ A.IsSubformula C) \/
      d.isIntroRoot = true
  ```
- [ ] Proof strategy by induction on `d`:
  - Leaves (ax, ass): `A` itself is in `T`/`G`, use `IsSubformula.refl`
  - Introduction rules (andI, orI1, orI2, impI): return the third disjunct
  - Elimination rules (andE1, andE2, impE, orE): by strong normality, major premise cannot be intro-headed or orE-headed. Apply IH to get major premise's conclusion grounded in `G`/`T`. Use `IsSubformula.trans` with `and_left`/`and_right`/`imp_right`/etc.
- [ ] The critical case: for `andE1 G d'` where `d'.isStronglyNormal = true`, the IH gives `(A /\ B).IsSubformula C` for some `C in G \/ T`. Then `A.IsSubformula (A /\ B)` by `and_left`, and `A.IsSubformula C` by `trans`.

*Step 5d: Prove subformula_property_of_isStronglyNormal (~40-60 lines)*
- [ ] Replace the existing `sorry`-containing `subformula_property_of_isNormal` with:
  ```lean
  theorem subformula_property_of_isStronglyNormal
      (d : T.Derivation G A) (hn : d.isStronglyNormal = true) :
      d.SubformulaProperty
  ```
- [ ] Proof by structural induction on `d`:
  - Introduction cases: unchanged from existing partial proof (already proved in v1)
  - Elimination cases: use `conclusion_grounded_or_intro` on the sub-derivation to establish that the major premise's conclusion is grounded in hypotheses/axioms. The IH on sub-derivations gives all formulas as subformulas of the major premise's conclusion or of hypotheses/axioms. Since the major premise's conclusion is grounded, everything is grounded via `IsSubformula.trans`.
- [ ] Verify the proof compiles without `sorry`

*Step 5e: Prove normalize produces strongly normal derivations (~50-80 lines)*
- [ ] Prove `Theory.Derivation.normalize_isStronglyNormal : (d.normalize).isStronglyNormal = true`
- [ ] This requires showing: (1) `reduceRoot` applied to a derivation with strongly normal sub-derivations produces a derivation with strongly normal sub-derivations, and (2) the fuel `2^height` is sufficient for the extended reduction (including commuting conversions)
- [ ] If the fuel bound is insufficient, increase to `2^height * d.nodeCount` or similar
- [ ] Alternatively, prove `normalizeAux_isStronglyNormal` by induction on fuel with the invariant that each iteration reduces at least one redex or commuting conversion

*Step 5f: Update main theorems and remove all sorry (~20-30 lines)*
- [ ] Update `subformula_property` corollary to use `isStronglyNormal`:
  ```lean
  theorem subformula_property (d : T.Derivation G A) :
      d.normalize.SubformulaProperty :=
    d.normalize.subformula_property_of_isStronglyNormal (normalize_isStronglyNormal d)
  ```
- [ ] Remove or deprecate `isNormal`-based theorem (or keep as documentation of the false statement)
- [ ] Verify zero `sorry` instances: `grep -c sorry Normalization.lean` returns 0
- [ ] Run full CI: `lake build`, `lake exe checkInitImports`, `lake exe lint-style`
- [ ] Add/update docstrings for new definitions

**Timing**: 3-4 hours

**Depends on**: 1, 2, 3, 4

**Files to modify**:
- `Cslib/Logics/Propositional/NaturalDeduction/Normalization.lean` -- all new/modified definitions and proofs

**Verification**:
- `subformula_property_of_isStronglyNormal` proof closes without `sorry`
- `normalize_isStronglyNormal` proof closes without `sorry`
- `subformula_property` corollary compiles
- `grep -c sorry Normalization.lean` returns 0
- `lake build` succeeds
- `lake exe checkInitImports` passes
- `lake exe lint-style` passes

## Testing & Validation

- [ ] `lake build Cslib.Logics.Propositional.NaturalDeduction.Normalization` succeeds at each step
- [ ] `lake build` (full project) succeeds after Phase 5
- [ ] `lake exe checkInitImports` passes
- [ ] `lake exe lint-style` passes
- [ ] `lake test` passes
- [ ] No `sorry` in any definition or proof (verify via `grep sorry`)
- [ ] `isStronglyNormal` correctly identifies all 5 proper redexes AND 4 commuting conversions as non-strongly-normal
- [ ] The counterexample `andE1(orE(ass, andI(ass,ass), andI(ass,ass)))` returns `isStronglyNormal = false`
- [ ] `normalize` is a computable function (not `noncomputable`)
- [ ] Subformula property statement is mathematically correct for MPL

## Artifacts & Outputs

- `Cslib/Logics/Propositional/NaturalDeduction/Normalization.lean` -- main implementation file (modified)
- `Cslib.lean` -- barrel import (already updated in Phase 4)
- `specs/290_nd_normalization_subformula_property/plans/02_nd-normalization-plan-revised.md` -- this plan
- `specs/290_nd_normalization_subformula_property/summaries/02_nd-normalization-summary.md` -- completion summary (after implementation)

## Rollback/Contingency

- Phase 5 changes are additive (new definitions alongside existing ones). If the `isStronglyNormal` approach fails, the existing `isNormal` infrastructure remains intact with documented `sorry` gaps.
- If the `conclusion_grounded_or_intro` induction is harder than expected in Lean, try mutual induction with a helper that tracks "all formulas in elimination chains are grounded."
- If the nested `orE(orE ...)` commuting conversion in `reduceRoot` causes excessive complexity, omit it and check whether the 3 simpler commuting conversions (andE1/andE2/impE of orE) suffice for the subformula property. The nested orE case can be handled by repeated application of the other reductions.
- If the fuel bound for `normalize` is insufficient with commuting conversions, switch to a product measure `(properRedexCount, commutingConversionCount)` with explicit decrease lemmas.
- If all else fails, mark the commuting conversion extension as a follow-up task and keep the existing Phases 1-4 work with `sorry` documented.
