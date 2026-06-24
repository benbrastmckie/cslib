# Research Report: Normalization Termination Proof (Task 332)

- **Task**: 332 -- Prove normalization termination theorem for CSLib Theory.Derivation
- **Date**: 2026-06-24
- **Session**: sess_1782302542_261dfa_332
- **Status**: Research findings ready for planning
- **Focus**: Proving `d.normalize.redexWeight = 0` (the 1 sorry at Normalization.lean:1083)

## 1. Executive Summary

The sorry at line 1083 requires proving `d.normalize.redexWeight = 0`, which is equivalent to
showing that `normalizeAux (2^d.height) d` produces a strongly normal derivation. After extensive
analysis, I find that:

1. **The existing `redexWeight` measure is NOT monotonically decreasing under beta-reduction.**
   Substitution (`subsOne`) can duplicate the argument, creating multiple new redexes whose
   combined weight exceeds the original.

2. **The fuel bound `2^height` is likely insufficient for the general case.** Beta-reduction via
   `subsOne` can increase derivation height from `h` to approximately `2h`, causing cascading
   height growth that exceeds `2^h` fuel.

3. **The correct termination measure is the Dershowitz-Manna multiset ordering** on the multiset
   of maximal formula complexities, paired with a commuting-conversion depth measure.
   Mathlib provides the necessary infrastructure (`Multiset.IsDershowitzMannaLT` and its
   well-foundedness proof).

4. **Two viable implementation approaches exist** (detailed in Section 5), both requiring
   modification to the `normalize` definition or addition of a well-founded normalization
   function.

## 2. Analysis of the Sorry

### 2.1 Goal State

At line 1083, the proof goal is:

```
Atom : Type u
inst : DecidableEq Atom
T : Theory Atom
G : Ctx Atom
A : Proposition Atom
d : Derivation G A
-- d.normalize.redexWeight = 0
```

Where `normalize d = normalizeAux (2^d.height) d`.

### 2.2 What redexWeight = 0 Means

By the existing lemma `redexWeight_zero_sn` (line 1017), `redexWeight d = 0` is equivalent to
`d.isStronglyNormal = true`. So the goal is equivalent to proving the output of `normalize` is
strongly normal.

### 2.3 Why the Existing Infrastructure Is Insufficient

The existing lemmas provide:
- `sn_redexWeight_zero`: strongly normal implies redexWeight 0 (line 974)
- `redexWeight_zero_sn`: redexWeight 0 implies strongly normal (line 1017)
- `normalizeAux_fixpoint`: strongly normal derivation is a fixpoint of normalizeAux (line 922)

What is MISSING is the proof that `normalizeAux` with sufficient fuel reaches a strongly normal
fixpoint. The gap cannot be closed by simple induction on fuel, derivation structure, or
redexWeight alone.

## 3. Why Simple Measures Fail

### 3.1 redexWeight Does Not Decrease Under Beta-Reduction

**Counterexample construction:** Consider `d = impE (impI G body) arg` where:
- `body` uses hypothesis `A = p -> q` three times under `impE`
- `arg` is `impI`-headed (intro-headed for type `A`)
- Both `body` and `arg` are strongly normal (from subterm normalization)

Before reduction: `d.redexWeight = A.complexity + 1 = 2` (one root redex)

After reduction (`body.subsOne arg`): Three new `impE/impI` redexes are created (one per
hypothesis occurrence). Each has weight `p.complexity + 1 = 1`. Total new weight = 3 > 2.

**Root cause:** `subsOne` replaces each hypothesis occurrence with a copy of `arg`. If `arg` is
introduction-headed, each copy placed under a matching elimination creates a new redex. Multiple
copies means the total weight can exceed the original.

### 3.2 Fuel Bound 2^height Is Likely Insufficient

**Mechanism:** When `impE (impI G body) arg` reduces to `body.subsOne arg`:
- `height(body) <= height(d) - 2`
- `height(arg) <= height(d) - 1`
- `height(body.subsOne arg) <= height(body) + height(arg) <= 2*height(d) - 3`

For `height(d) = h >= 3`, the result's height can be approximately `2h`, which exceeds `h`.
After the result is recursively normalized, cascading beta-reductions can further increase height.
After `k` cascade steps, `height_k ~ 2^k * h`. The total cascade depth is bounded by the sum
of formula complexities (polynomial in the derivation size), so the required fuel is
approximately `2^(2^poly(h) * h)`, which is doubly exponential -- far exceeding `2^h`.

**Caveat:** I have not constructed an explicit Lean derivation demonstrating fuel exhaustion.
It is possible that the specific recursive structure of `normalizeAux` (which normalizes
subterms first) prevents the worst case. However, the burden of proof lies with showing
sufficiency, and I see no path to proving `2^height` bounds the convergence fuel.

### 3.3 Height Does Not Decrease Under Commuting Conversions

For `andE1 G (orE G' D DA DB) -> orE G D (andE1 _ DA) (andE1 _ DB)`:
- Before: `height = 2 + max(h(D), max(h(DA), h(DB)))`
- After: `height = 1 + max(h(D), 1 + max(h(DA), h(DB)))`
- Height can stay the same or increase.

Additionally, if `DA` is `orE`-headed (which is compatible with `DA` being strongly normal),
then `andE1 DA` creates a NEW commuting conversion, so the count of commuting conversions
can increase.

## 4. The Correct Termination Measure

### 4.1 Dershowitz-Manna Multiset Ordering (for Beta-Redexes)

**Definition:** For a derivation `d`, define the **maximal formula multiset**:
```
maxFormulaMultiset(d) : Multiset Nat
```
as the multiset of `complexity(F)` for each maximal formula `F` in `d`. A maximal formula is
one that is both the conclusion of an introduction rule and the major premise of an immediately
following elimination rule (the five beta-redex patterns in `reduceRoot`).

**Key property (Prawitz Ch. IV):** When a beta-redex of cut formula complexity `k` is reduced:
- One element `k` is REMOVED from the multiset
- Zero or more elements of value `< k` may be ADDED (from new redexes created by substitution)
- New redexes involve formulas that are proper subformulas of the cut formula, so their
  complexity is strictly less than `k`

This is exactly a strict decrease in the Dershowitz-Manna ordering:
```
IsDershowitzMannaLT M N := exists X Y Z, Z != {} /\ M = X + Y /\ N = X + Z
                           /\ forall y in Y, exists z in Z, y < z
```
With `Z = {k}` and `Y = {c_1, ..., c_m}` where each `c_i < k`.

**Well-foundedness:** `Multiset.wellFounded_isDershowitzMannaLT` in
`Mathlib.Data.Multiset.DershowitzManna` provides well-foundedness for `Multiset Nat`.

### 4.2 Commuting Conversion Measure (commutingSum)

**Definition:** For a derivation `d`, define:
```
commutingSum(d) : Nat
```
as the sum, over all commuting conversion sites `c` in `d`, of the node count of the
sub-derivation rooted at `c`.

**Key property:** When a commuting conversion `andE1(orE G D DA DB)` is reduced to
`orE G D (andE1 DA) (andE1 DB)`:
- The original root commuting conversion contributed `2 + |D| + |DA| + |DB|`
- New commuting conversions (if `DA` or `DB` are `orE`-headed) contribute at most
  `(1 + |DA|) + (1 + |DB|) = 2 + |DA| + |DB|`
- The difference is `|D| >= 1` (D has at least one node)
- So `commutingSum` strictly decreases by at least `|D|`

This handles the fact that commuting conversions can create new commuting conversions.

### 4.3 Combined Measure

The full termination measure is:
```
measure(d) = (maxFormulaMultiset(d), commutingSum(d))
```
ordered lexicographically: `Prod.Lex IsDershowitzMannaLT (<)`.

**Strict decrease:**
- Beta-reduction: first component strictly decreases (DM ordering). Second may increase.
  Lexicographic ordering only examines first component. Strict decrease overall.
- Commuting conversion: first component unchanged (no maximal formulas created or destroyed).
  Second component strictly decreases. Strict decrease overall.

**Well-foundedness:** `Prod.Lex` of two well-founded relations is well-founded. Both
`IsDershowitzMannaLT` on `Multiset Nat` and `<` on `Nat` are well-founded.

### 4.4 Key Sub-Lemma: Beta-Reduction Cannot Create Same-Rank Maximal Formulas

When `impE (impI G body) arg` reduces to `body.subsOne arg` (where body and arg are sn):
- The cut formula is `A -> B` with complexity `1 + complexity(A) + complexity(B)`
- `subsOne` replaces `ass h` (type `A`) in `body` with copies of `arg`
- If `body` has `impE (ass h) E'` and `arg = impI _ D` (intro-headed for `A`), then
  `impE (impI _ D) E'` is a new maximal formula
- The new cut formula is `A` with complexity `complexity(A)`
- Since `complexity(A) < 1 + complexity(A) + complexity(B)`, the new formula has strictly
  lower complexity

Similarly for other beta-redex types (and/or). The general principle: any new maximal formula
created by substitution involves a proper subformula of the original cut formula.

## 5. Recommended Implementation Approaches

### 5.1 Approach A: Well-Founded Normalization Function (Recommended)

**Summary:** Define a new normalization function `normalizeWF` using well-founded recursion on
the combined measure. Prove it produces strongly normal output. Then prove `normalize = normalizeWF`
(or change `normalize` to use `normalizeWF`).

**Components (~250-350 lines):**

1. **Maximal formula extraction** (~30 lines):
   - `maximalFormulas : T.Derivation G A -> Multiset Nat`
   - Collects complexity of each beta-redex pattern in the derivation

2. **Commuting conversion sum** (~20 lines):
   - `commutingSum : T.Derivation G A -> Nat`
   - Sums node counts at commuting conversion sites

3. **normalizeWF definition** (~40 lines):
   - Uses `WellFounded.fix` with the combined measure
   - Same algorithm as `normalizeAux` but with WF termination proof
   - Requires: normalize subterms (structural recursion), then reduceRoot,
     then recurse (WF recursion on decreasing measure)

4. **Measure decrease lemma** (~80 lines):
   - `reduceRoot_decreases_measure`: If `d` has sn subterms and `d.reduceRoot = some d'`,
     then `measure(d') < measure(d)` in the lex ordering
   - Requires case analysis on all 8 reduceRoot patterns
   - Beta-redex cases need the sub-lemma about subsOne not creating same-rank formulas

5. **subsOne complexity lemma** (~50 lines):
   - `subsOne_maxFormula_complexity_lt`: New maximal formulas created by subsOne have
     strictly lower complexity than the original cut formula
   - Requires induction on the derivation structure, tracking where substitutions land

6. **Main theorem** (~30 lines):
   - `normalizeWF_isStronglyNormal`: the WF normalization produces sn output
   - Direct from the WF construction: each recursive call has smaller measure,
     and the base case (no root redex + sn subterms) is sn

7. **Bridge to normalize** (~30 lines):
   - Either change `normalize` to use `normalizeWF`, or prove `normalize d = normalizeWF d`
   - The latter requires showing `2^height` fuel is sufficient for `normalizeWF`'s behavior
   - **If 2^height is genuinely insufficient**: must change `normalize`'s definition

**Pros:** Cleanest separation of concerns. Termination argument is self-contained.
**Cons:** Requires either modifying `normalize` or proving fuel equivalence.

### 5.2 Approach B: Fuel Bound Change + Direct Proof

**Summary:** Change `normalize`'s fuel from `2^height` to a provably sufficient bound, then
prove the direct theorem by induction.

**New fuel bound:** `totalComplexityWeight(d)` defined as:
```
totalComplexityWeight(d) = (sum of complexity(F) + 1 for all formulas F in d) * nodeCount(d)
```
This bounds the total number of reduction steps (each step removes weight from the measure,
and each unit of weight corresponds to at most one reduction).

Alternatively, use a simpler exponential: `height^(maxComplexity + 1)` or `nodeCount^2`.

**Components (~200-300 lines):**

1. **New fuel function** (~10 lines):
   - `sufficientFuel : T.Derivation G A -> Nat`
   - `normalize d := normalizeAux (sufficientFuel d) d`

2. **Fuel sufficiency proof** (~100 lines):
   - Show `normalizeAux (sufficientFuel d) d` converges to sn form
   - By induction on the combined measure, show each recursive call
     consumes at most a bounded amount of fuel

3. **Main theorem** (~30 lines):
   - Direct proof that `normalize` produces sn output

4. **Existing infrastructure adaptation** (~50 lines):
   - Update downstream uses of `normalize` for new definition
   - May need to reprove `normalizeAux_fixpoint` variants

**Pros:** More direct. Avoids defining a second normalization function.
**Cons:** Requires modifying the `normalize` definition, which affects downstream code.
Need to carefully choose and justify the fuel bound.

### 5.3 Approach C: Monotonicity + Existence (Most Conservative)

**Summary:** Prove that `normalizeAux` is monotone (more fuel never undoes normalization) and
that normalization terminates (some fuel suffices). Then show `2^height` exceeds the required
fuel.

**Components:**

1. **Monotonicity lemma**: For all `d`, `n`, if `normalizeAux n d` is sn, then
   `normalizeAux (n+k) d = normalizeAux n d` for all `k`.

2. **Existence**: For all `d`, there exists `N` such that `normalizeAux N d` is sn.
   (By WF induction on the combined measure.)

3. **Bound**: `N <= 2^height(d)`.

**Risk:** Step 3 may be FALSE, as analyzed in Section 3.2. If `2^height` is genuinely
insufficient, this approach fails and falls back to Approach B.

**Recommendation:** Only pursue this if there's strong evidence that `2^height` IS sufficient.

## 6. Dependency Analysis

### 6.1 New Mathlib Imports Required

```lean
import Mathlib.Data.Multiset.DershowitzManna  -- Dershowitz-Manna ordering
```

The current file already imports Mathlib transitively through `Cslib.Logics.Propositional.NaturalDeduction.Basic`.

### 6.2 Impact on Existing Code

| Change | Scope | Risk |
|--------|-------|------|
| New definitions (maximalFormulas, commutingSum) | Local to Normalization.lean | Low |
| normalizeWF definition (Approach A) | New function, no existing code changed | Low |
| Change normalize's fuel (Approach B) | Modifies normalize definition | Medium |
| Downstream theorems | `subformula_property` uses `normalize` | Low if normalize type unchanged |

The downstream `subformula_property` theorem (line 1092) depends on `normalize_isStronglyNormal`
but not on the specific definition of `normalize`. Changing the fuel bound does not affect its
type signature.

### 6.3 Dependency on Task 290

Task 290 is [PARTIAL] with 1 sorry (this same sorry). The current file (1099 lines) has all
other infrastructure complete. This task directly addresses the remaining sorry.

## 7. Reuse Check

### 7.1 CSLib Foundations

No existing normalization infrastructure in `Cslib.Foundations.*`. The normalization code is
specific to propositional natural deduction.

### 7.2 Mathlib

| Mathlib Resource | Location | Relevance |
|-----------------|----------|-----------|
| `Multiset.IsDershowitzMannaLT` | `Mathlib.Data.Multiset.DershowitzManna` | Core termination measure |
| `Multiset.wellFounded_isDershowitzMannaLT` | Same | Well-foundedness proof |
| `Prod.Lex` | `Init.Prelude` | Lexicographic product |
| `Prod.instWellFoundedRelation` | `Init.WFSimpLemmas` | WF for product |
| `WellFounded.fix` | `Init.WF` | Well-founded recursion |
| `Nat.strongRecOn` | `Init.WF` | Strong induction on Nat |

### 7.3 Existing Normalization.lean Infrastructure

The following existing definitions/lemmas are directly usable:

| Name | Line | Purpose |
|------|------|---------|
| `redexWeight` | 945 | Current weight measure (useful for characterization) |
| `sn_redexWeight_zero` | 974 | sn implies redexWeight 0 |
| `redexWeight_zero_sn` | 1017 | redexWeight 0 implies sn |
| `normalizeAux_fixpoint` | 922 | sn is a fixpoint of normalizeAux |
| `isStronglyNormal` | 244 | Boolean predicate for strong normality |
| `reduceRoot` | 365 | Single-step root reduction |
| `subsOne` | 344 | Single-hypothesis substitution |
| `Proposition.complexity` | 148 | Formula complexity measure |

## 8. Tactic Survey Results

| Tactic | Applicability |
|--------|--------------|
| `cases`/`rcases` | Essential for constructor case analysis (10 Derivation constructors) |
| `induction` | Structural induction on Derivation |
| `omega` | Nat arithmetic in measure bounds |
| `simp` | Boolean normality checks, multiset simplification |
| `WellFounded.fix` | Core tool for WF recursion definition |
| `Nat.strongRecOn` | Alternative strong induction |
| `decide` | Decidable propositions (Bool equality) |

## 9. Estimated Effort and Risk

| Approach | Lines | Difficulty | Risk |
|----------|-------|------------|------|
| A (WF normalization) | 250-350 | High | Low (self-contained) |
| B (Fuel bound change) | 200-300 | High | Medium (modifies definition) |
| C (Monotonicity) | 200-250 | High | High (fuel bound may fail) |

**Recommended:** Approach A (well-founded normalization). It cleanly separates the termination
argument from the computational definition. The existing `normalize` can remain as-is, with
the theorem proved by showing `normalizeWF d = normalize d` or by replacing `normalize`'s
definition.

If the `2^height` bound turns out to be sufficient after all (which would require a deeper
analysis I haven't completed), then Approach C is cleaner.

## 10. Key Open Question

**Is `2^height` actually sufficient?** My analysis suggests it is not for the worst case, but I
have not constructed an explicit Lean derivation that demonstrates fuel exhaustion. If someone
can prove `2^height` is sufficient (perhaps through a more refined height analysis of
`subsOne` on strongly-normal derivations), then the proof becomes significantly simpler.

The key property to investigate: after normalizing subterms (making them sn), does `subsOne`
on strongly-normal arguments produce a result whose "effective height" (accounting for the
fact that new redexes will be quickly reduced) is bounded by a function of the original height?
