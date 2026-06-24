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

### Phase 1: Termination Measure Infrastructure [IN PROGRESS]
<!-- Started: 2026-06-24 -->

**Goal**: Define the two components of the termination measure (`maximalFormulas` and
`commutingSum`) and the combined well-founded relation. Verify the Mathlib
`Dershowitz-Manna` API is usable.

**Tasks**:
- [ ] Add `import Mathlib.Data.Multiset.DershowitzManna` to the import block
- [ ] Define `maximalFormulas : T.Derivation G A -> Multiset Nat` -- collects `complexity(F)` for
      each beta-redex (the 5 proper redex patterns in `reduceRoot`); recurses into subterms
- [ ] Define `commutingSum : T.Derivation G A -> Nat` -- sum over commuting conversion sites of
      the node count of the sub-derivation rooted at each site
- [ ] Define `nodeCount : T.Derivation G A -> Nat` -- total number of nodes (if not already present)
- [ ] Define the combined measure type and well-founded relation:
      `normMeasure d := (maximalFormulas d, commutingSum d)` with
      `Prod.Lex IsDershowitzMannaLT (· < ·)` ordering
- [ ] Prove `normMeasure_wf : WellFounded (InvImage (Prod.Lex ...) normMeasure)` using
      `Multiset.wellFounded_isDershowitzMannaLT` and `Nat.lt_wfRel.wf`
- [ ] Run `lake build Cslib.Logics.Propositional.NaturalDeduction.Normalization` to verify
      definitions compile

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

### Phase 2: Measure Decrease Lemmas [NOT STARTED]

**Goal**: Prove that `reduceRoot` strictly decreases the combined measure. This is the
mathematical heart of the termination argument.

**Tasks**:
- [ ] Prove `subsOne_new_redex_complexity_lt`: when `subsOne` creates a new beta-redex, its
      maximal formula complexity is strictly less than the original cut formula's complexity.
      Key insight: new redexes involve proper subformulas of the cut formula.
      Requires induction on derivation structure, tracking where substituted terms land.
- [ ] Prove `reduceRoot_beta_maxFormulas_lt`: for each of the 5 beta-redex patterns, the
      `maximalFormulas` multiset strictly decreases in the Dershowitz-Manna ordering.
      One element of rank `k` is removed; zero or more elements of rank `< k` may be added.
- [ ] Prove `reduceRoot_commuting_commutingSum_lt`: for each of the 3 commuting conversion
      patterns, `maximalFormulas` is unchanged and `commutingSum` strictly decreases.
      Key: the original site contributes `|D| + |DA| + |DB| + 2`, new sites contribute at
      most `|DA| + |DB| + 2`, and `|D| >= 1`.
- [ ] Prove `reduceRoot_commuting_maxFormulas_eq`: commuting conversions do not create or
      destroy maximal formulas (they just rearrange sub-derivation structure).
- [ ] Combine into `reduceRoot_decreases_measure`: if `d.reduceRoot = some d'` and `d` has
      strongly normal subterms, then `normMeasure d' < normMeasure d` in the lex ordering.
- [ ] Run `lake build Cslib.Logics.Propositional.NaturalDeduction.Normalization` to verify

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
