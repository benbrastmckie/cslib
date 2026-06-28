# Implementation Plan: Task #332

- **Task**: 332 - Prove normalization termination theorem for CSLib Theory.Derivation
- **Status**: [IMPLEMENTING]
- **Effort**: 10 hours
- **Dependencies**: None (Task 290 is [PARTIAL] with this same sorry; this task directly resolves it)
- **Research Inputs**: specs/332_normalization_termination_proof/reports/01_termination-research.md
- **Artifacts**: plans/01_termination-plan.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: cslib
- **Lean Intent**: true

## Overview

The single remaining sorry in Normalization.lean (line 1083) requires proving that
`d.normalize.redexWeight = 0`, which is equivalent to showing that normalization
produces a strongly normal derivation. The research report demonstrates that the
existing `redexWeight` measure does not decrease monotonically under beta-reduction
(substitution can duplicate arguments, creating more redexes) and that the fuel
bound `2^height` is likely insufficient.

The plan follows Approach A from the research: define a new well-founded normalization
function `normalizeWF` using the Dershowitz-Manna multiset ordering on maximal formula
complexities, paired with a commuting conversion sum. Prove this function produces
strongly normal output, then bridge back to the existing `normalize` definition (either
by replacing its definition or proving equivalence).

### Research Integration

Key findings from the research report (01_termination-research.md):

- **Section 3**: Simple measures fail -- `redexWeight` not monotone under beta-reduction,
  `2^height` fuel insufficient, height does not decrease under commuting conversions.
- **Section 4**: Correct termination measure is `(maxFormulaMultiset, commutingSum)` ordered
  lexicographically via `Prod.Lex IsDershowitzMannaLT (<)`. Beta-reduction strictly decreases
  the first component; commuting conversions preserve the first and strictly decrease the second.
- **Section 5.1**: Approach A (well-founded normalization) recommended -- 250-350 lines, low risk.
- **Section 6**: `Mathlib.Data.Multiset.DershowitzManna` provides `wellFounded_isDershowitzMannaLT`.
- **Section 7**: Existing infrastructure (`redexWeight_zero_sn`, `normalizeAux_fixpoint`,
  `reduceRoot`, `subsOne`, `Proposition.complexity`) is directly reusable.

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

This task advances the Propositional Natural Deduction module within `Logics/Propositional/`.
Not directly listed in ROADMAP.md (which focuses on the BimodalLogic porting effort), but
represents foundational proof-theory infrastructure that supports the overall library goals.

## Goals & Non-Goals

**Goals**:
- Eliminate the sorry at Normalization.lean:1083
- Prove `normalize_isStronglyNormal` (and thereby `subformula_property`)
- Define the Dershowitz-Manna based termination measure for derivation normalization
- Prove that `reduceRoot` strictly decreases the combined measure
- Produce a sorry-free, axiom-clean Normalization.lean

**Non-Goals**:
- Optimizing the computational behavior of `normalize` (performance is not a concern)
- Proving tight fuel bounds for `normalizeAux` (the WF approach avoids fuel reasoning)
- Extending normalization to first-order or modal natural deduction
- Adding new normalization strategies beyond Prawitz-style

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| `Multiset.IsDershowitzMannaLT` API mismatch with proof needs | H | L | Verify API in Phase 1 before building on it; fall back to custom multiset ordering if needed |
| `subsOne` complexity lemma requires deep induction on 10 constructors | M | M | Use `cases`/structural recursion; break into helper lemmas per constructor group |
| Bridge from `normalizeWF` to `normalize` blocked by fuel insufficiency | H | M | If `2^height` is genuinely insufficient, replace `normalize` definition to use `normalizeWF` directly |
| Universe polymorphism issues with `Multiset` over `Nat` | L | L | `Multiset Nat` is universe-monomorphic; no issue expected |
| `WellFounded.fix` unfolding difficulties in proofs | M | M | Use `WellFounded.fix_eq` lemma; define `normalizeWF_unfold` helper early |
| Heartbeat/deterministic timeout on large case analyses | M | M | Split large proofs into private helper lemmas; use `set_option maxHeartbeats` locally if needed |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2 | 1 |
| 3 | 3 | 2 |
| 4 | 4 | 3 |
| 5 | 5 | 4 |

Phases within the same wave can execute in parallel.

---

### Phase 1: Termination Measure Infrastructure [COMPLETED]
<!-- Agent: cslib-implementation-agent, started 2026-06-24 -->
<!-- Started: 2026-06-24 -->

**Goal**: Define the two components of the termination measure (`maximalFormulas` and
`commutingSum`) and the combined well-founded relation. Verify the Mathlib
`Dershowitz-Manna` API is usable.

**Tasks**:
- [x] Add `import Mathlib.Data.Multiset.DershowitzManna` to the import block *(already present at line 11)*
- [x] Define `maximalFormulas : T.Derivation G A -> Multiset Nat` -- collects `complexity(F)` for
      each beta-redex (the 5 proper redex patterns in `reduceRoot`); recurses into subterms *(already defined at line 1032)*
- [x] Define `commutingSum : T.Derivation G A -> Nat` -- sum over commuting conversion sites of
      the node count of the sub-derivation rooted at each site *(already defined at line 1059)*
- [x] Define `nodeCount : T.Derivation G A -> Nat` -- total number of nodes (if not already present) *(already defined at line 1018)*
- [x] Define the combined measure type and well-founded relation:
      `normMeasure d := (maximalFormulas d, commutingSum d)` with
      `Prod.Lex IsDershowitzMannaLT (· < ·)` ordering *(already defined at line 1085)*
- [x] Prove `normMeasure_wf : WellFounded (InvImage (Prod.Lex ...) normMeasure)` using
      `Multiset.wellFounded_isDershowitzMannaLT` and `Nat.lt_wfRel.wf` *(already proved at line 1089)*
- [x] Run `lake build Cslib.Logics.Propositional.NaturalDeduction.Normalization` to verify
      definitions compile *(deviation: altered -- pre-existing errors in Phase 2+ proofs prevent clean build, but all Phase 1 definitions verified axiom-clean via lean_verify)*

**Timing**: 2 hours

**Depends on**: none

**Files to modify**:
- `Cslib/Logics/Propositional/NaturalDeduction/Normalization.lean` -- add definitions after the
  existing `redexWeight` section (around line 940-970)

**Verification**:
- All new definitions compile without errors
- `lean_verify` confirms no axioms or sorry in new definitions
- `maximalFormulas` correctly identifies beta-redex patterns (test via `lean_goal` on small examples)

---

### Phase 2: Measure Decrease Lemmas [PARTIAL]

**Goal**: Prove that `reduceRoot` strictly decreases the combined measure. This is the
mathematical heart of the termination argument.

**Tasks**:
- [ ] **Task 2.1**: Prove `subsOne_new_redex_complexity_lt`: when `subsOne` creates a new beta-redex, its
      maximal formula complexity is strictly less than the original cut formula's complexity.
      Key insight: new redexes involve proper subformulas of the cut formula.
      Requires induction on derivation structure, tracking where substituted terms land.
      *(deviation: deferred -- subsOne goes through subs which uses tactic blocks, making structural induction technically challenging)*
- [x] **Task 2.2**: Prove `reduceRoot_beta_maxFormulas_lt`: for the 2 conjunction beta-redex patterns, the
      `maximalFormulas` multiset strictly decreases in the Dershowitz-Manna ordering.
      *(deviation: altered -- split into `reduceRoot_andE_maxFormulas_lt` and `reduceRoot_andE2_maxFormulas_lt`; substitution beta cases (impE/orE) deferred pending Task 2.1)*
- [ ] **Task 2.3**: Prove `reduceRoot_commuting_commutingSum_lt`: for each of the 3 commuting conversion
      patterns, `maximalFormulas` is unchanged and `commutingSum` strictly decreases.
      *(deviation: deferred -- commuting conversions can increase maximalFormulas when subterms are not SN; requires strengthening h_allSubsSN hypothesis)*
- [ ] **Task 2.4**: Prove `reduceRoot_commuting_maxFormulas_eq`: commuting conversions do not create or
      destroy maximal formulas (they just rearrange sub-derivation structure).
      *(deviation: deferred -- only true when subterms are SN; requires isStronglyNormal hypotheses on DA/DB)*
- [x] **Task 2.5**: Combine into `reduceRoot_decreases_measure`: if `d.reduceRoot = some d'` and `d` has
      strongly normal subterms, then `normMeasure d' < normMeasure d` in the lex ordering.
      *(deviation: altered -- structure in place with conjunction cases proved; 6 of 8 cases remain as sorry pending Tasks 2.1, 2.3, 2.4)*
- [ ] **Task 2.6**: Run `lake build Cslib.Logics.Propositional.NaturalDeduction.Normalization` to verify
      *(deviation: skipped -- build blocked by remaining sorries)*

**BLOCKER** (Phase 2):
- **What failed**: 6 of 8 `reduceRoot` pattern cases in `reduceRoot_decreases_normMeasure`
- **What was tried**: Direct DM witness construction for conjunction cases (succeeded for h_2, h_3). Analysis of substitution cases (blocked on `subsOne` going through `subs` with tactic blocks). Analysis of commuting conversion cases (blocked on `maximalFormulas` not being preserved without SN hypotheses).
- **Why it's stuck**: Two root causes: (1) `subsOne` defined via `subs` with `by grind`/`weakCtx` rewrites makes induction on output infeasible. (2) Commuting conversions can create new maximal formulas when subterms are not SN, requiring `h_allSubsSN` to be non-vacuous.
- **What is needed**: (1) Either prove `subsOne_maximalFormulas_complexity_bound` by induction through `subs`, or refactor `subsOne` to use pattern matching. (2) Strengthen `h_allSubsSN` from `True` to actual SN predicate on immediate subterms, then show SN rules out introduction forms at redex positions.
- **Prohibited workarounds**: Do NOT use `sorry`, `def X := True`, or any vacuous placeholder

**Timing**: 3 hours

**Depends on**: 1

**Files to modify**:
- `Cslib/Logics/Propositional/NaturalDeduction/Normalization.lean` -- add lemmas after Phase 1
  definitions

**Verification**:
- All measure decrease lemmas compile without sorry
- `lean_verify` confirms no axioms on key theorems
- Case coverage: all 8 `reduceRoot` patterns (5 beta + 3 commuting) handled

---

### Phase 3: Well-Founded Normalization Function [NOT STARTED]

**Goal**: Define `normalizeWF` using `WellFounded.fix` on the combined measure. This
function has the same algorithm as `normalizeAux` but with a well-founded termination proof
instead of fuel.

**Tasks**:
- [ ] Define `normalizeSubterms : T.Derivation G A -> T.Derivation G A` -- normalize all
      immediate subterms structurally (same as the inner `let d' := ...` in `normalizeAux`)
- [ ] Define `normalizeWF : T.Derivation G A -> T.Derivation G A` using `WellFounded.fix`
      with the combined measure relation. The body: normalize subterms (structural recursion),
      then check `reduceRoot`; if `some d'`, recurse on `d'` (WF recursion on decreasing measure);
      if `none`, return.
- [ ] Handle the termination proof obligation inside `normalizeWF`: when `reduceRoot` returns
      `some d'`, apply `reduceRoot_decreases_measure` to show `normMeasure d' < normMeasure d`
- [ ] Prove `normalizeWF_unfold`: unfolding lemma for `normalizeWF` using `WellFounded.fix_eq`
- [ ] Run `lake build Cslib.Logics.Propositional.NaturalDeduction.Normalization` to verify

**Timing**: 2 hours

**Depends on**: 2

**Files to modify**:
- `Cslib/Logics/Propositional/NaturalDeduction/Normalization.lean` -- add `normalizeWF` after
  the measure decrease lemmas

**Verification**:
- `normalizeWF` compiles with no sorry, no axioms
- `normalizeWF_unfold` compiles (critical for later proofs)
- `lean_verify Cslib.Logic.PL.Theory.Derivation.normalizeWF` passes

---

### Phase 4: Main Termination Theorem [NOT STARTED]

**Goal**: Prove that `normalizeWF` produces strongly normal output, then bridge to the
existing `normalize` to eliminate the sorry.

**Tasks**:
- [ ] Prove `normalizeWF_isStronglyNormal`: the WF normalization produces strongly normal
      output. Proof by well-founded induction on the measure: if `reduceRoot` returns `none`
      and all subterms are SN, then the result is SN (no root redex + SN subterms = SN).
      If `reduceRoot` returns `some d'`, the IH applies (measure decreased).
- [ ] **Bridge strategy decision**: Determine whether to (a) replace `normalize`'s definition
      to use `normalizeWF`, or (b) prove `normalize d = normalizeWF d`. Option (a) is
      simpler but modifies an existing definition; option (b) requires showing `2^height`
      fuel suffices, which the research suggests may be false.
- [ ] If option (a): replace `normalize` definition at line 403 to use `normalizeWF` instead
      of `normalizeAux (2 ^ d.height)`. Update `normalizeAux`-based downstream lemmas.
- [ ] If option (b): prove fuel sufficiency and `normalize_eq_normalizeWF`.
- [ ] Replace the sorry at line 1083 with the actual proof term:
      `(normalizeWF_isStronglyNormal d).symm ▸ sn_redexWeight_zero _ (by rfl)` or equivalent.
- [ ] Verify `subformula_property` (line 1092) still compiles (it depends on
      `normalize_isStronglyNormal` but not on the definition of `normalize` itself).
- [ ] Run `lake build Cslib.Logics.Propositional.NaturalDeduction.Normalization`

**Timing**: 2 hours

**Depends on**: 3

**Files to modify**:
- `Cslib/Logics/Propositional/NaturalDeduction/Normalization.lean` -- modify `normalize` and/or
  `normalize_isStronglyNormal`, eliminate sorry

**Verification**:
- Zero sorry in Normalization.lean
- `lean_verify` on `normalize_isStronglyNormal` and `subformula_property` -- no axioms, no sorry
- `lake build Cslib.Logics.Propositional.NaturalDeduction.Normalization` passes

---

### Phase 5: CI Verification and Cleanup [NOT STARTED]

**Goal**: Run the full CSLib CI pipeline, clean up any style/lint issues, verify the
complete build.

**Tasks**:
- [ ] Run `lake build` (full project build) to verify no regressions
- [ ] Run `lake exe checkInitImports` to verify import structure
- [ ] Run `lake exe lint-style` to check style compliance
- [ ] Run `lake test` to run CslibTests suite
- [ ] Fix any lint or style issues in the new code
- [ ] Verify docstrings on all new public definitions (`maximalFormulas`, `commutingSum`,
      `normalizeWF`, `normalizeWF_isStronglyNormal`)
- [ ] Review final file structure: ensure new code is placed in logical sections with
      appropriate `/-! ## Section Headers -/`

**Timing**: 1 hour

**Depends on**: 4

**Files to modify**:
- `Cslib/Logics/Propositional/NaturalDeduction/Normalization.lean` -- style/lint fixes, docstrings

**Verification**:
- All 4 CI commands pass without warnings
- `lake build` succeeds with no errors
- Zero sorry across entire project (`grep -r "sorry" Cslib/ --include="*.lean" | grep -v "^--"`)

## Testing & Validation

- [ ] `lean_verify` on `normalize_isStronglyNormal` confirms no sorry, no axioms
- [ ] `lean_verify` on `subformula_property` confirms no sorry, no axioms
- [ ] `lake build Cslib.Logics.Propositional.NaturalDeduction.Normalization` succeeds
- [ ] `lake build` (full project) succeeds
- [ ] `lake exe checkInitImports` passes
- [ ] `lake exe lint-style` passes
- [ ] `lake test` passes
- [ ] `grep -rn "sorry" Cslib/Logics/Propositional/NaturalDeduction/Normalization.lean` returns empty

## Artifacts & Outputs

- `specs/332_normalization_termination_proof/plans/01_termination-plan.md` (this file)
- `specs/332_normalization_termination_proof/reports/01_termination-research.md` (research input)
- `Cslib/Logics/Propositional/NaturalDeduction/Normalization.lean` (modified -- sorry eliminated)

## Rollback/Contingency

If the well-founded approach encounters insurmountable difficulties (e.g., `WellFounded.fix`
unfolding issues, universe problems with `Multiset`):

1. **Rollback**: `git checkout -- Cslib/Logics/Propositional/NaturalDeduction/Normalization.lean`
   restores the file to the 1-sorry state.
2. **Alternative**: Switch to Approach B (change fuel bound to a provably sufficient value).
   This requires modifying the `normalize` definition but avoids `WellFounded.fix` entirely.
3. **Minimal fallback**: If neither approach works within the effort budget, document the
   blocking issue and keep the sorry with an improved docstring explaining what is needed.
