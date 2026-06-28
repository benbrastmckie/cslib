# Implementation Plan: Task #290 (v3)

- **Task**: 290 - ND Normalization and Subformula Property
- **Status**: [COMPLETED]
- **Effort**: 16 hours (10 hours completed + 6 hours remaining)
- **Dependencies**: None (task 266 completed and archived; Derivation type and subs already in place)
- **Research Inputs**:
  - specs/290_nd_normalization_subformula_property/reports/01_nd-normalization-research.md
  - specs/290_nd_normalization_subformula_property/reports/02_blocker-hard-research.md
  - specs/290_nd_normalization_subformula_property/reports/03_termination-measure-research.md
- **Artifacts**: plans/04_nd-normalization-plan-v3.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-formats.md, tasks.md
- **Type**: cslib

## AS-BUILT RECONCILIATION (added at completion)

**Status: [COMPLETED] — fully discharged.** All deliverables exist sorry-free in
`Cslib/Logics/Propositional/NaturalDeduction/Normalization/`: `isNormal` (Basic.lean:169),
`isStronglyNormal` (Basic.lean:231), `normalize` (Reduction.lean:104), `SubformulaProperty`
(SubformulaProperty.lean:342), and `subformula_property` (SubformulaProperty.lean:292,
axiom-clean).

The two blockers this plan lists below were both resolved:
- The **3 sorries in `conclusion_grounded_or_intro`** (the `orE` intro-headed branches) were fixed
  during the Normalization refactor (3-way disjunction with `isOrERoot`, as report 03 §2 predicted).
- The **2 sorries in `subformula_property`** (termination — "`normalize` is strongly normal") were
  discharged by **task 332**, but via a *constructive* route, NOT the termination-measure route this
  plan's report 03 recommended (that Dershowitz–Manna measure was later proven **unsound** — see
  332 plans/06_termination-plan-v6-as-built.md §"Why v6"). `subformula_property` was re-pointed at
  `Theory.Derivation.exists_stronglyNormal_form` and the fuel theorem retired.

Nothing in 290's scope was skipped. The only outstanding items are inherited from 332: (a) the
full-project CI gates are blocked by pre-existing unrelated red modules, and (b) dead-code cleanup
of the abandoned termination-measure machinery. See 332 v6 plan "Skipped / Outstanding Items".

## Overview

This is the third revision of the ND normalization plan, incorporating findings from report 03
(termination measure research). The implementation file is 828 lines with 5 remaining sorry
instances. Phases 1-4 are complete. Phase 5 (steps 5a-5d) from plan v2 is substantially
complete: `isStronglyNormal`, `isIntroRoot`, extended `reduceRoot` with commuting conversions,
`conclusion_grounded_or_intro`, and `subformula_property_of_isStronglyNormal` are all
implemented. The 5 remaining sorry break down as:

- **3 sorry** (lines 519, 536, 557) in `conclusion_grounded_or_intro`: the `orE` case with
  intro-headed branches, where the theorem is false as stated. Report 03 Section 2 provides
  the root cause analysis and fix strategy (3-way disjunction with `isOrERoot`).
- **2 sorry** (lines 825-826) in `subformula_property`: the statement that `normalize`
  produces a strongly normal derivation. Report 03 Section 3 provides the termination measure
  analysis and recommended approaches.

This plan restructures the remaining work into two phases: Phase 5 (fix the false theorem
statement) and Phase 6 (prove normalization termination).

### Research Integration

Reports integrated into this plan:
- `01_nd-normalization-research.md` (integrated in plan v1, preserved)
- `02_blocker-hard-research.md` (integrated in plan v2, preserved)
- `03_termination-measure-research.md` (newly integrated -- provides root cause analysis for
  the 3 sorry in `conclusion_grounded_or_intro`, termination measure options for
  `normalize_isStronglyNormal`, and Mathlib API survey for well-founded recursion)

### Prior Plan References

- `plans/01_nd-normalization-plan.md` -- original plan with 5 phases. Phases 1-4 completed.
  Phase 5 blocked due to false theorem statement.
- `plans/02_nd-normalization-plan-revised.md` -- v2 plan. Phase 5 restructured with steps
  5a-5f. Steps 5a-5d substantially complete. Steps 5e-5f blocked on the 5 sorry.

## Goals & Non-Goals

**Goals**:
- Add `isOrERoot` predicate and fix `conclusion_grounded_or_intro` with a 3-way disjunction
  that admits the `orE` case. Eliminate 3 sorry.
- Update `subformula_property_of_isStronglyNormal` callsites to handle the third disjunct
  (minor changes to elimination cases).
- Prove `normalize_isStronglyNormal` via a termination argument. Eliminate 2 sorry.
- Achieve zero sorry in `Normalization.lean`.
- Pass full CI: `lake build`, `lake exe checkInitImports`, `lake exe lint-style`.

**Non-Goals**:
- Removing or refactoring Phases 1-4 code (completed and correct)
- Proving strong normalization (every reduction sequence terminates)
- Proving confluence (Church-Rosser property)
- Extending to classical logic (CPL) or modal logic
- Well-founded recursion refactor of `normalizeAux` (fuel-bounded approach is sufficient
  if termination is provable; WF refactor is a fallback only)

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| `subformula_property_of_isStronglyNormal` callsite updates are more involved than expected after 3-way disjunction change | M | L | In elimination cases, strong normality of the major premise excludes both `isIntroRoot` and `isOrERoot`; the third disjunct is discharged by `simp [isOrERoot]`. In the `orE` case, the existing code already handles intro-headed branches directly -- the `isOrERoot` disjunct is never reached on the major premise. |
| `subsOne` (substitution) in imp/or proper redexes increases derivation size, making fuel insufficiency hard to prove | H | M | Report 03 Section 3.6 identifies this as the hardest case. Fallback: use a two-phase normalizer (Phase 6 Strategy B) that separates proper-redex reduction from commuting-conversion normalization. |
| Commuting conversions create cascading new commuting conversions deeper in the tree | M | M | Report 03 Section 3.4 shows each level of `normalizeAux` handles one tree level. The fuel `2^height` gives enough for subterm normalization + root reduction + result normalization. |
| `redexWeight` measure is complex to define and verify strictly decreasing | M | H | Start with the simpler approach: prove `reduceRoot` on derivations with strongly normal subterms produces a result where the root is not a redex (no cascading at root level). Use strong induction on fuel for `normalizeAux`. |
| Full termination proof exceeds single-phase budget | M | M | Phase 6 has a pragmatic fallback: if the full proof is too complex, mark `normalize_isStronglyNormal` as a follow-up task with documented blockers and keep the subformula property for strongly normal derivations (0 sorry in that theorem). |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1, 2, 3, 4 | -- (completed) |
| 2 | 5 | 1-4 |
| 3 | 6 | 5 |

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
proper redex patterns (impE/impI, andE1/andI, andE2/andI, orE/orI1, orE/orI2) plus 4
commuting conversion patterns (andE1/orE, andE2/orE, impE/orE, orE/orE).

**Files**: `Cslib/Logics/Propositional/NaturalDeduction/Normalization.lean`

---

### Phase 3: Normalization Function with Fuel-Bounded Termination [COMPLETED]

**Goal**: Define `normalizeAux` (fuel-bounded) and `normalize` functions.

**Completed**: `normalizeAux` with fuel parameter and `normalize` defined as
`d.normalizeAux (2 ^ d.height)`. Fuel-bounded approach chosen over WF recursion.

**Files**: `Cslib/Logics/Propositional/NaturalDeduction/Normalization.lean`

---

### Phase 4: Full Connective Verification and Cleanup [COMPLETED]

**Goal**: Verify all redex types handled, add docstrings, run CI.

**Completed**: All proper redex types and commuting conversions covered. `isStronglyNormal`,
`isIntroRoot`, `formulas`, `SubformulaProperty`, `conclusionGrounded`,
`conclusion_grounded_or_intro`, and `subformula_property_of_isStronglyNormal` defined.
CI passes (`lake build`, `checkInitImports`, `lint-style`). 5 sorry remain.

**Files**: `Cslib/Logics/Propositional/NaturalDeduction/Normalization.lean`, `Cslib.lean`

---

### Phase 5: Fix conclusion_grounded_or_intro with 3-Way Disjunction [COMPLETED]

**Goal**: Eliminate the 3 sorry in `conclusion_grounded_or_intro` by adding `isOrERoot` and
changing the theorem to a 3-way disjunction. Update all callsites in
`subformula_property_of_isStronglyNormal`.

**Rationale**: Report 03 Section 2 proves the current theorem statement is false for `orE`
derivations with intro-headed branches. Concrete counterexample:
`orE {r} (ax h_pq) (andI (ass h_r) (ass h_r)) (andI (ass h_r) (ass h_r))` derives
`{r} |- r /\ r`, is strongly normal, but `r /\ r` is not a subformula of `r` or `p \/ q`,
and `orE` is not intro-headed. The fix is to add a third disjunct: `d.isOrERoot = true`.

**Tasks**:

*Step 5a: Add isOrERoot definition (~5 lines)*
- [ ] Define `Theory.Derivation.isOrERoot : T.Derivation G A -> Bool`:
  ```lean
  def Theory.Derivation.isOrERoot : T.Derivation G A -> Bool
    | orE _ _ _ _ => true
    | _ => false
  ```
- [ ] Place it near the existing `isIntroRoot` definition (around line 219)

*Step 5b: Change conclusion_grounded_or_intro to 3-way disjunction (~15 lines changed)*
- [ ] Update the theorem statement (around line 449) from:
  ```lean
  conclusionGrounded d \/ d.isIntroRoot = true
  ```
  to:
  ```lean
  conclusionGrounded d \/ d.isIntroRoot = true \/ d.isOrERoot = true
  ```
- [ ] Fix the 3 sorry locations (lines 519, 536, 557): in each case, the proof reaches
  a state where both branches DA, DB are intro-headed but the derivation is `orE`-headed.
  Replace `exact Or.inl sorry` with `exact Or.inr (Or.inr rfl)` (or the appropriate
  `simp [isOrERoot]` discharge)
- [ ] The `ax`, `ass`, `andE1/andE2/impE` sub-cases within the `orE` branch that currently
  succeed should continue to work -- they return the first disjunct (grounding) and the
  existing proof paths are unaffected by adding a third disjunct

*Step 5c: Update subformula_property_of_isStronglyNormal callsites (~20 lines changed)*
- [ ] In the elimination cases (`andE1`, `andE2`, `impE`): where `conclusion_grounded_or_intro`
  is called on the major premise, add handling for the third disjunct. Since strong normality
  of the major premise excludes `orE`-headed derivations (the `andE1(orE ...)`, `andE2(orE ...)`,
  `impE(orE ...) _` patterns are all false under `isStronglyNormal`), the third disjunct is
  discharged by contradiction: `simp [isOrERoot, isStronglyNormal] at *` or similar.
  Specifically:
  - For `andE1 G D`: strong normality gives `D` is not `orE`-headed, so `D.isOrERoot = false`
  - For `andE2 G D`: same reasoning
  - For `impE D E`: strong normality gives `D` is not `orE`-headed
- [ ] In the `orE` case: where `conclusion_grounded_or_intro` is called on branch derivations
  DA, DB, the existing handling for `isIntroRoot = true` already works. Add a case for
  `isOrERoot = true`. For `orE`-headed DA: DA is `orE(G', D', DA', DB')`. Since DA is
  strongly normal, we can recursively handle this, or note that the `orE` case in the
  subformula property proof already recurses on DA's subterms via `SubformulaProperty`
  induction. The simplest approach: when DA is `orE`-headed, use the IH on DA directly
  (DA is a sub-derivation).

*Step 5d: Verify 3 sorry eliminated*
- [ ] Run `grep -c sorry Normalization.lean` and confirm count drops from 5 to 2
- [ ] Run `lake build Cslib.Logics.Propositional.NaturalDeduction.Normalization` to confirm
  compilation succeeds
- [ ] The remaining 2 sorry should be only at lines 825-826 (the `normalize_isStronglyNormal`
  and its usage in `subformula_property`)

**Timing**: 1.5-2 hours

**Depends on**: 1, 2, 3, 4

**Files to modify**:
- `Cslib/Logics/Propositional/NaturalDeduction/Normalization.lean`

**Verification**:
- `conclusion_grounded_or_intro` compiles without sorry
- `subformula_property_of_isStronglyNormal` compiles without sorry
- `grep -c sorry Normalization.lean` returns 2 (only the termination-related sorry)
- `lake build Cslib.Logics.Propositional.NaturalDeduction.Normalization` succeeds

---

### Phase 6: Prove normalize_isStronglyNormal [IN PROGRESS]

**Goal**: Prove that `normalize` (equivalently `normalizeAux (2^height)`) produces a strongly
normal derivation. Eliminate the final 2 sorry and achieve zero sorry in the file.

**Rationale**: Report 03 Section 3 analyzes the termination measure problem. The key insight
(Section 3.4) is that after normalizing subterms, a single `reduceRoot` application at the
root either returns `none` (already strongly normal at root) or produces a result that may
have new commuting conversions deeper in the tree but NOT at the root. The recursive
`normalizeAux n` call handles the deeper commuting conversions. The main challenge is proving
fuel sufficiency: that `2^height` provides enough iterations for cascading commuting
conversions and substitution-enlarging proper redexes.

**Strategy A (preferred): Strong induction on fuel with root-redex elimination lemma**

The proof structure:
```
theorem normalizeAux_isStronglyNormal (n : Nat) (d : T.Derivation G A)
    (hfuel : n >= d.height) : (d.normalizeAux n).isStronglyNormal = true
```

By strong induction on `n`:
1. Base `n = 0`: `d.height <= 0` means `d` is a leaf (ax/ass), already strongly normal.
2. Step `n + 1`: Normalize subterms with fuel `n` (IH applies since subterms have smaller
   height). Let `d'` be the result with strongly normal subterms.
   - If `d'.reduceRoot = none`: prove `d'` is strongly normal (subterms are strongly normal
     and no root redex/commuting pattern means `isStronglyNormal d' = true`).
   - If `d'.reduceRoot = some d''`: need `(d''.normalizeAux n).isStronglyNormal = true`.
     This requires `d''.height <= n`, which is the hard sub-lemma.

Key sub-lemmas needed:
- `reduceRoot_none_isStronglyNormal`: if immediate subterms of `d` are strongly normal and
  `d.reduceRoot = none`, then `d.isStronglyNormal = true`
- `reduceRoot_height_bound`: if `d.reduceRoot = some d'` and the immediate subterms of `d`
  are strongly normal, then `d'.height <= max(heights of subterms of d)` (or some bound
  that allows IH application)

**Tasks**:

*Step 6a: Prove reduceRoot_none_isStronglyNormal (~30-50 lines)*
- [ ] Theorem: if all immediate subterms of `d` are strongly normal and `d.reduceRoot = none`,
  then `d.isStronglyNormal = true`
- [ ] Proof by cases on `d`: for each constructor, check that `reduceRoot` returning `none`
  means no redex or commuting pattern exists at the root, and strong normality of subterms
  gives the conjunction needed for `isStronglyNormal`

*Step 6b: Establish height/fuel bounds for reduceRoot results (~50-80 lines)*
- [ ] For commuting conversions: prove that `reduceRoot` does not increase the maximum height
  of the derivation tree. This is straightforward for commuting conversions (they rearrange
  structure without substitution).
- [ ] For proper redexes with substitution (`impE(impI body) arg -> body.subsOne arg` and
  `orE(orI1/orI2 d') DA DB -> DA.subsOne d'`): prove a bound on `(body.subsOne arg).height`.
  The bound is `body.height + arg.height` in the worst case. Combined with the fuel
  `2^d.height >= 2^(body.height) * 2^(arg.height)`, this should give enough fuel.
- [ ] If the height bound is too loose, define `nodeCount` and prove
  `(d.reduceRoot.get).nodeCount < d.nodeCount` for commuting conversions, or use a
  lexicographic `(cutrank, height)` measure.
- [ ] If Strategy A stalls on height bounds for substitution cases, pivot to Strategy B.

*Step 6c: Prove normalizeAux_isStronglyNormal (~60-100 lines)*
- [ ] Prove by strong induction on `n`:
  ```lean
  theorem normalizeAux_isStronglyNormal :
      forall (n : Nat) (d : T.Derivation G A),
      (d.normalizeAux n).isStronglyNormal = true
  ```
  Note: if fuel sufficiency for arbitrary `d` cannot be shown, restrict to `n >= d.height`
  hypothesis and prove `normalize_isStronglyNormal` using the fact that
  `normalize d = d.normalizeAux (2^d.height)` where `2^d.height >= d.height`.
- [ ] The induction applies the IH to:
  (a) Each subterm normalization `(sub.normalizeAux n)` where `n < n+1`
  (b) The result normalization `(d''.normalizeAux n)` after `reduceRoot`
- [ ] Use `reduceRoot_none_isStronglyNormal` for the `none` case
- [ ] Use the height/fuel bound from Step 6b for the `some d''` case

*Step 6d: Wire up normalize_isStronglyNormal and eliminate sorry (~10-20 lines)*
- [ ] Prove `normalize_isStronglyNormal`:
  ```lean
  theorem normalize_isStronglyNormal (d : T.Derivation G A) :
      (d.normalize).isStronglyNormal = true :=
    normalizeAux_isStronglyNormal (2 ^ d.height) d
  ```
- [ ] Update `subformula_property` to use the proof:
  ```lean
  theorem subformula_property (d : T.Derivation G A) :
      exists (d' : T.Derivation G A), d'.isStronglyNormal = true /\ d'.SubformulaProperty :=
    ⟨d.normalize,
     d.normalize_isStronglyNormal,
     d.normalize.subformula_property_of_isStronglyNormal d.normalize_isStronglyNormal⟩
  ```
- [ ] Remove sorry and any associated comments about deferred termination proofs

*Step 6e: Final verification (~10 min)*
- [ ] `grep -c sorry Normalization.lean` returns 0
- [ ] `lake build Cslib.Logics.Propositional.NaturalDeduction.Normalization` succeeds
- [ ] `lake build` (full project) succeeds
- [ ] `lake exe checkInitImports` passes
- [ ] `lake exe lint-style` passes

**Strategy B (fallback): Two-Phase Normalizer**

If Strategy A stalls on the `subsOne` height bound problem, restructure `normalizeAux` into
two passes:
1. A commuting-conversion normalizer that pushes all eliminations past `orE` (this always
   terminates because commuting conversions decrease "elimination nesting depth in orE")
2. A proper-redex normalizer that eliminates beta redexes

Each pass has a simpler termination argument. The commuting-conversion normalizer does not
involve substitution, so height bounds are straightforward. The proper-redex normalizer
operates on commuting-normal derivations where no `orE` appears under eliminations, so
substitution does not create new commuting conversions.

**Strategy C (pragmatic fallback): Partial completion**

If both Strategy A and B exceed the time budget, mark `normalize_isStronglyNormal` as a
follow-up task with:
- The `subformula_property_of_isStronglyNormal` theorem is fully proved (0 sorry)
- The `conclusion_grounded_or_intro` theorem is fully proved (0 sorry)
- Only 2 sorry remain: the termination of `normalize` producing `isStronglyNormal = true`
- Document exact blockers and partial progress for the follow-up task

**Timing**: 3-4 hours

**Depends on**: 5

**Files to modify**:
- `Cslib/Logics/Propositional/NaturalDeduction/Normalization.lean`

**Verification**:
- `grep -c sorry Normalization.lean` returns 0
- `lake build` succeeds
- `lake exe checkInitImports` passes
- `lake exe lint-style` passes
- `lean_verify` on `Theory.Derivation.subformula_property` reports no axiom violations

## Testing & Validation

- [ ] `lake build Cslib.Logics.Propositional.NaturalDeduction.Normalization` succeeds at each step
- [ ] `lake build` (full project) succeeds after Phase 6
- [ ] `lake exe checkInitImports` passes
- [ ] `lake exe lint-style` passes
- [ ] `lake test` passes
- [ ] No `sorry` in any definition or proof (verify via `grep sorry`)
- [ ] `isStronglyNormal` correctly identifies all 5 proper redexes AND 4 commuting conversions
- [ ] The counterexample `andE1(orE(ass, andI(ass,ass), andI(ass,ass)))` returns `isStronglyNormal = false`
- [ ] `normalize` is a computable function (not `noncomputable`)
- [ ] Subformula property statement is mathematically correct for MPL
- [ ] `conclusion_grounded_or_intro` is true as stated (3-way disjunction)

## Artifacts & Outputs

- `Cslib/Logics/Propositional/NaturalDeduction/Normalization.lean` -- main implementation file (modified)
- `Cslib.lean` -- barrel import (already updated in Phase 4)
- `specs/290_nd_normalization_subformula_property/plans/04_nd-normalization-plan-v3.md` -- this plan
- `specs/290_nd_normalization_subformula_property/summaries/04_nd-normalization-summary.md` -- completion summary (after implementation)

## Rollback/Contingency

- Phase 5 changes (3-way disjunction fix) are low-risk: the change makes the theorem true
  and the callsite updates are mechanical. If any callsite update fails, the original 2-way
  disjunction code can be restored.
- Phase 6 Strategy A (fuel/height bounds) is the primary approach. If height bounds for
  `subsOne` prove intractable, Strategy B (two-phase normalizer) separates the problem.
- If both strategies A and B exceed the time budget, Strategy C (partial completion) preserves
  all progress: the subformula property for strongly normal derivations is fully proved, and
  only the normalization termination theorem remains sorry.
- All Phase 1-4 work is preserved regardless of Phase 5-6 outcomes.
