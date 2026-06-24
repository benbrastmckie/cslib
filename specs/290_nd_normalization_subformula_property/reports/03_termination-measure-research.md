# Research Report: Termination Measure for normalize_isStronglyNormal (Task 290)

- **Task**: 290 -- ND Normalization and Subformula Property
- **Date**: 2026-06-24
- **Session**: sess_1782296192_f489df
- **Status**: Research findings ready for implementation
- **Focus**: Termination measure for `normalize_isStronglyNormal` and fixing 3+2 sorry gaps

## 1. Executive Summary

This research addresses two interrelated blockers in the normalization proof:

1. **Three sorry in `conclusion_grounded_or_intro`** (lines 519, 536, 557): The theorem is
   **false as stated**. The `orE` case with intro-headed branches does not guarantee grounding.
   However, these sorry cases are **not needed** by the downstream
   `subformula_property_of_isStronglyNormal` proof, which only applies
   `conclusion_grounded_or_intro` to the major premise of elimination rules (never to `orE`
   derivations directly). The fix is to **restrict the theorem** to non-`orE` derivations or to
   add an `isIntroRoot = false` hypothesis.

2. **Two sorry in `subformula_property`** (lines 825-826): Proving `normalize_isStronglyNormal`
   requires a termination measure that strictly decreases under both proper redexes and
   commuting conversions. The recommended approach is a **redex weight measure** combined with
   the existing fuel-bounded `normalizeAux`.

## 2. Analysis of the Three Sorry in conclusion_grounded_or_intro

### 2.1 The Problem

All three sorry locations share the same pattern. The goal state (representative):

```
hirA : DA.isIntroRoot = true
hirB : DB.isIntroRoot = true
h : (A' ∨ B') ∈ T   -- (or ∈ G' for the ass case)
⊢ ((∃ C ∈ G', C'.IsSubformula C) ∨ ∃ C ∈ T, C'.IsSubformula C)
  ∨ (orE G' ... DA DB).isIntroRoot = true
```

Since `(orE ...).isIntroRoot = false`, the right disjunct is impossible. We must prove the
conclusion `C'` is grounded. But `C'` is the conclusion of intro-headed DA and DB -- it can
be any compound formula (e.g., `r ∧ r` when branches are `andI (ass r) (ass r)`). This
formula need not be a subformula of anything in `G'` or `T`.

**Concrete counterexample to the theorem**: With `G' = {r}` and `T ∋ {p ∨ q}`:
- `orE {r} (ax h_pq) (andI _ (ass h_r) (ass h_r)) (andI _ (ass h_r) (ass h_r))`
- Derives `{r} ⊢ r ∧ r`
- `isStronglyNormal = true` (no proper redexes, no commuting conversions)
- But `r ∧ r` is NOT a subformula of `r` or `p ∨ q`
- And `orE` is not intro-headed

### 2.2 Why This Does Not Block the Subformula Property

In `subformula_property_of_isStronglyNormal`, `conclusion_grounded_or_intro` is invoked only:
- On the **major premise** of `andE1`, `andE2`, `impE` (lines 648, 672, 700, 785)
- On the **branch derivations** DA, DB in the `orE` case (lines 704, 723, 748)

For elimination-headed major premises: strong normality ensures the major premise cannot be
intro-headed or `orE`-headed, so `conclusion_grounded_or_intro` returns the grounding
disjunct (the `isIntroRoot` case is discharged by `simp [isIntroRoot]`).

For DA/DB branches: when `conclusion_grounded_or_intro DA` returns `hirA : isIntroRoot = true`,
the subformula property proof at line 715 uses `exact Or.inl (IsSubformula.refl _)` --
meaning the conclusion of DA is a subformula of itself. This is correct and complete.

**The three sorry cases in `conclusion_grounded_or_intro` are never reached by the downstream proof.**

### 2.3 Recommended Fix

**Option A (Simplest -- recommended):** Restrict the theorem to non-`orE` derivations:

```lean
theorem conclusion_grounded_or_intro
    (d : T.Derivation G A) (hn : d.isStronglyNormal = true)
    (h_not_orE : ∀ G' D DA DB, d ≠ orE G' D DA DB) :  -- NEW
    conclusionGrounded d ∨ d.isIntroRoot = true
```

But this requires proving the inequality, which is awkward with dependent types.

**Option B (Cleaner):** Change the conclusion to a three-way disjunction:

```lean
theorem conclusion_grounded_or_intro
    (d : T.Derivation G A) (hn : d.isStronglyNormal = true) :
    conclusionGrounded d ∨ d.isIntroRoot = true ∨ d.isOrERoot = true
```

where `isOrERoot` returns `true` for `orE` and `false` otherwise. This makes the theorem true
and the downstream proof still works (the `orE` case of the subformula property already handles
the `isOrERoot` disjunct separately).

**Option C (Most pragmatic):** Since the downstream proof only calls `conclusion_grounded_or_intro`
on derivations that are known to be elimination-headed and not `orE`-headed (after case-splitting),
the theorem can be stated with an additional hypothesis:

```lean
theorem conclusion_grounded_or_intro
    (d : T.Derivation G A) (hn : d.isStronglyNormal = true) :
    conclusionGrounded d ∨ d.isIntroRoot = true
```

And the three sorry cases can be discharged by observing that in the `orE` case, when both
branches are intro-headed, the proof can recurse into the intro structure. Specifically:
if `DA = andI _ D1 D2` and `C' = X ∧ Y`, we can apply the IH to `D1 : insert A' G' ⊢ X`
and `D2 : insert A' G' ⊢ Y`. But this requires nested structural recursion on DA, which
is not available in the current proof structure (the induction is on the outer `d`).

**Recommended: Option B.** Add `isOrERoot` and a three-way disjunction. This is the most
honest encoding and requires minimal changes to the downstream proof.

Alternatively, **Option D**: The simplest path to zero sorry is to **inline** the
`conclusion_grounded_or_intro` logic directly into the `subformula_property_of_isStronglyNormal`
proof for the elimination cases, avoiding the need for a separate lemma. The elimination
cases in the subformula property only need grounding for the major premise, which is always
elimination-headed (not intro, not orE) by strong normality. A local `have` block that
does the case split directly on the major premise constructor would avoid the false-for-orE
theorem entirely.

## 3. Termination Measure for normalize_isStronglyNormal

### 3.1 Why No Simple Measure Works

No single `Nat`-valued measure on derivations strictly decreases under all reductions:

| Measure | Proper β-redex (imp/or) | Proper β-redex (and) | Commuting conv |
|---------|------------------------|---------------------|----------------|
| nodeCount | Can INCREASE (substitution duplicates) | Decreases | INCREASES by 1 |
| height | Can INCREASE | Decreases | Can INCREASE |
| sizeOf | Can INCREASE (includes formula sizes) | Decreases | Can INCREASE |

### 3.2 The Standard Proof-Theoretic Measure

From Troelstra-Schwichtenberg Sec. 6.1 (pp.178-183) and Prawitz Ch. IV:

**Cutrank** `cr(d)` = max complexity of maximal formulas (maximal segments of length > 1).
A **critical cut** = a maximal segment of maximal cutrank.

The normalization strategy reduces the **rightmost topmost critical cut**:
- Detour conversions (proper redexes): reduce cutrank or reduce the number/length of critical cuts
- Permutation conversions (commuting): reduce the length of critical cut segments

The measure is `(cutrank, total_cut_length)` under lexicographic `<`:
- Detour conversion at max rank: removes a maximal formula of max complexity, may introduce
  formulas of strictly lower complexity. Cutrank decreases or stays same with fewer cuts.
- Permutation conversion: cutrank stays same, total length of critical cuts strictly decreases.

### 3.3 Encoding for the Fuel-Bounded Approach

The current `normalizeAux` uses fuel `2^height`. The approach for proving
`normalize_isStronglyNormal` should be:

**Define `redexWeight : T.Derivation G A → Nat`:**

```lean
def Theory.Derivation.redexWeight : T.Derivation G A → Nat
  | ax _ | ass _ => 0
  | andI _ D₁ D₂ => D₁.redexWeight + D₂.redexWeight
  | andE1 _ D =>
    match D with
    | andI _ _ _ => D.conclusion_complexity + 1 + D.redexWeight  -- proper redex
    | orE _ _ _ _ => 1 + D.redexWeight                           -- commuting
    | _ => D.redexWeight
  | andE2 _ D =>
    match D with
    | andI _ _ _ => D.conclusion_complexity + 1 + D.redexWeight
    | orE _ _ _ _ => 1 + D.redexWeight
    | _ => D.redexWeight
  | orI1 _ D | orI2 _ D | impI _ D => D.redexWeight
  | orE _ D DA DB =>
    match D with
    | orI1 _ _ | orI2 _ _ => D.conclusion_complexity + 1 + D.redexWeight + DA.redexWeight + DB.redexWeight
    | orE _ _ _ _ => 1 + D.redexWeight + DA.redexWeight + DB.redexWeight
    | _ => D.redexWeight + DA.redexWeight + DB.redexWeight
  | impE D E =>
    match D with
    | impI _ _ => D.conclusion_complexity + 1 + D.redexWeight + E.redexWeight
    | orE _ _ _ _ => 1 + D.redexWeight + E.redexWeight
    | _ => D.redexWeight + E.redexWeight
```

**Key property**: `reduceRoot` on a derivation with strongly-normal subterms strictly decreases
`redexWeight`:

- **And-redex**: `andE1(andI d1 d2) → d1`. Weight goes from
  `(complexity + 1) + d1.rw + d2.rw` to `0` (since d1 has no root redex by strong normality of subterms).
  Strict decrease.

- **Commuting**: `andE1(orE G D DA DB) → orE G D (andE1 DA) (andE1 DB)`.
  Weight goes from `1 + D.rw + DA.rw + DB.rw` to `D.rw + (andE1 DA).rw + (andE1 DB).rw`.
  If DA is `andI`-headed, `(andE1 DA).rw` includes a proper redex contribution, but that
  contribution is bounded by `complexity(DA.conclusion) + 1 ≤ complexity(A∧B)` where
  `A∧B` is the conclusion type of DA. This needs careful analysis but the net effect
  should still decrease because the commuting conversion's "1" contribution is removed.

  **Caution**: This is the hardest case. If DA/DB heads create new redexes after commuting,
  the weight might not strictly decrease in one step. The standard approach handles this by
  first normalizing subterms (which `normalizeAux` already does), then reducing at root.
  After subterm normalization, DA and DB are strongly normal, so `andE1 DA` cannot be a
  proper redex (DA is not `andI`-headed in a strongly normal derivation).

  **CRITICAL INSIGHT**: After `normalizeAux n` normalizes subterms, the immediate subterms
  are already strongly normal (by induction on `n`). Therefore when we apply `reduceRoot`:
  - `andE1(orE G D DA DB)` where D, DA, DB are strongly normal
  - Result: `orE G D (andE1 DA) (andE1 DB)` where DA, DB are strongly normal
  - Since DA is strongly normal, DA is not `andI`-headed and not `orE`-headed
  - Therefore `(andE1 DA).isStronglyNormal = DA.isStronglyNormal = true`
  - So the result `orE G D (andE1 DA) (andE1 DB)` is strongly normal at the root!
  - No further reduction needed!

### 3.4 The Key Realization: One-Step Sufficiency

**After normalizing subterms, a single `reduceRoot` application either produces `none`
(already strongly normal) or produces a strongly normal derivation.**

This is because:
1. Subterms are already strongly normal (by IH on fuel)
2. `reduceRoot` handles all root-level redex patterns (proper + commuting)
3. For proper redexes: the result is a subterm (and/or-redex) or a substitution instance
   (imp/or-redex). Substitution does not create new root redexes because the substituted
   derivation replaces `ass` nodes (which are strongly normal leaves).
4. For commuting conversions: the result rearranges strongly normal subterms. The new root
   is `orE` with strongly normal subterms, and the pushed-in eliminations have strongly
   normal arguments (since we pushed into already-strongly-normal branches).

**Wait -- point 4 is WRONG.** After `andE1(orE G D DA DB) → orE G D (andE1 DA) (andE1 DB)`:
- `andE1 DA` has DA as immediate subterm. DA is strongly normal.
- But `andE1 DA` might itself be a commuting conversion if DA is... wait, DA cannot be
  `orE`-headed (since DA is strongly normal and the `orE` case in `isStronglyNormal` checks
  that the discriminant is not `orE`-headed). Actually, DA CAN be `orE`-headed -- strong
  normality of DA means DA's subterms satisfy the strong normality checks. The issue is
  whether `andE1` applied to a strongly-normal `orE`-headed DA creates a new commuting
  conversion.

Actually: re-reading `isStronglyNormal` for `orE`:
```lean
| orE _ D DA DB =>
  match D with
  | orI1 _ _ => false        -- proper redex
  | orI2 _ _ => false        -- proper redex
  | orE _ _ _ _ => false     -- commuting conversion
  | _ => D.isStronglyNormal && DA.isStronglyNormal && DB.isStronglyNormal
```

So `isStronglyNormal` for `orE` checks that D (the discriminant) is NOT `orE`-headed. But
DA and DB CAN be `orE`-headed (they are checked for strong normality independently, and an
`orE` CAN be strongly normal if its own discriminant is not `orI1/orI2/orE`-headed).

Therefore: after `andE1(orE G D DA DB) → orE G D (andE1 DA) (andE1 DB)`:
- If DA is `orE`-headed (and strongly normal), then `andE1 DA` is a commuting conversion!
- So the result is NOT strongly normal at the pushed-in positions.
- This means a single `reduceRoot` is NOT sufficient. We need to recurse.

**Revised conclusion**: Commuting conversions can create NEW commuting conversions deeper in
the tree. Each commuting conversion pushes an elimination one level into `orE` branches.
The process terminates because the nesting depth of `orE`-within-elimination is bounded.

### 3.5 Recommended Approach: Restructured Normalization

The most practical approach is to restructure normalization to guarantee strong normality:

**Strategy 1: Inner normalization loop for commuting conversions**

After the main `normalizeAux` loop normalizes subterms and reduces root once, if the result
still has a root redex (which can happen if `reduceRoot` produced a commuting conversion
whose result contains new commuting conversions), recurse with reduced fuel.

The current `normalizeAux` already does this:
```lean
match d'.reduceRoot with
| none => d'
| some d'' => d''.normalizeAux n
```

So `d''` is further normalized with fuel `n`. The question is whether fuel `n` is sufficient
for the cascading commuting conversions.

**Fuel analysis**: Each application of `reduceRoot` to a commuting conversion `andE1(orE ...)`
produces `orE G D (andE1 DA) (andE1 DB)`. The result may have commuting conversions at
`andE1 DA` or `andE1 DB`. But `normalizeAux n` will:
1. Normalize subterms of the result (including `andE1 DA` and `andE1 DB`)
2. Then try `reduceRoot` again at the root of the result

Since the result is `orE`-headed, `reduceRoot` at the root checks for:
- `orI1/orI2` discriminant (impossible since D is strongly normal and not `orI`-headed)
- The root is now `orE` with non-`orI/orE` discriminant D, so `reduceRoot` returns `none`

The commuting conversions at `andE1 DA` and `andE1 DB` are handled by the recursive
`normalizeAux n` calls on the subterms.

**Key insight**: Each level of `normalizeAux` fuel handles one level of the derivation tree.
The fuel `2^height` is sufficient because:
- Level 0: normalize leaves (trivial)
- Level k+1: normalize subterms with fuel k, then reduce root once, then normalize result
  with fuel k
- The height of the result of `reduceRoot` is at most `max(height of subterms) + 1`
  (for commuting conversions, the height stays roughly the same)
- With fuel `2^h`, we have `2^h = 2 * 2^(h-1)`, giving enough fuel for: subterm
  normalization (fuel `2^(h-1)`), root reduction, and result normalization (fuel `2^(h-1)`)

**BUT**: This argument requires showing that `reduceRoot` does not increase height, which
is not true for proper redexes involving substitution (`subsOne` can increase height).

### 3.6 The Practical Path Forward

Given the complexity of the termination analysis, the recommended implementation approach is:

**Phase 1: Fix the 3 sorry in `conclusion_grounded_or_intro` (immediate)**

Use Option B or Option D from Section 2.3. This eliminates 3 sorry and makes the
subformula property for strongly normal derivations fully proved.

**Phase 2: Prove `normalizeAux` termination via a bounded descent argument**

Define `rootRedexCount : T.Derivation G A → Nat` counting only root-level redexes/commuting
conversions (not recursive):

```lean
def Theory.Derivation.hasRootRedex : T.Derivation G A → Bool
  | andE1 _ (andI _ _ _) | andE2 _ (andI _ _ _) => true
  | andE1 _ (orE _ _ _ _) | andE2 _ (orE _ _ _ _) => true
  | orE _ (orI1 _ _) _ _ | orE _ (orI2 _ _) _ _ => true
  | impE (impI _ _) _ | impE (orE _ _ _ _) _ => true
  | _ => false
```

Prove: If `d` has strongly normal immediate subterms and `d.hasRootRedex = true`, then
`(d.reduceRoot).get!` has `hasRootRedex = false` OR has strictly smaller `redexWeight`.

The key cases:
- Proper and-redex: result is a subterm, no root redex (strongly normal subterms)
- Proper imp/or-redex: result is a substitution, root may not be redex (needs proof about `subsOne`)
- Commuting and-conv: result is `orE(D, andE1 DA, andE1 DB)`. Root `orE` may be a redex only if D is `orI1/orI2` (impossible since D is strongly normal) or `orE`-headed (impossible since D is strongly normal). So root has no redex. But subterms `andE1 DA` may have a new redex if DA is `orE`-headed. This is NOT a root redex of the result.

So actually: **After normalizing subterms and applying one `reduceRoot`, the result has no root redex.** The result's subterms may have new commuting conversions (from pushing eliminations into `orE` branches), but these are handled by the recursive `normalizeAux n` call.

The proof structure:
```lean
theorem normalizeAux_isStronglyNormal :
    ∀ (n : Nat) (d : T.Derivation G A),
    n ≥ d.height → (d.normalizeAux n).isStronglyNormal = true
```

Proof by strong induction on `n`:
- Base `n = 0`: `d.height ≤ 0` means `d` is a leaf, already strongly normal
- Step `n + 1`:
  1. Normalize subterms with fuel `n` (IH: subterms have height < d.height ≤ n+1, so height ≤ n, IH applies)
  2. Let `d'` be the result. `d'` has strongly normal subterms.
  3. If `d'.reduceRoot = none`: `d'` is strongly normal (its subterms are, and no root redex/commuting pattern)
  4. If `d'.reduceRoot = some d''`: need `(d''.normalizeAux n).isStronglyNormal = true`
     - Need: `d''.height ≤ n`. This is the hard part.
     - For proper redexes: `d''` is a subterm or substitution. Height may increase for imp/or substitution.
     - For commuting conversions: `d''` has height ≤ `d'.height` (structure rearrangement, no increase).

**Blocker for the fuel approach**: Proper redexes with substitution (`subsOne`) can increase
height. If `impE(impI _ body) arg → body.subsOne arg`, and `arg` is large, `body.subsOne arg`
can have height much larger than the original. This means `2^height` may not be sufficient
fuel, and we cannot easily prove `d''.height ≤ n`.

### 3.7 Alternative: Well-Founded Recursion

Instead of fuel-bounded `normalizeAux`, define normalization via well-founded recursion:

```lean
def Theory.Derivation.normalizeWF : T.Derivation G A → T.Derivation G A :=
  WellFounded.fix (InvImage.wf redexMeasure Nat.lt_wfRel.wf) fun d normalizeWF_rec =>
    let d' := normalizeSubterms d normalizeWF_rec
    match h : d'.reduceRoot with
    | none => d'
    | some d'' => normalizeWF_rec d'' (by <prove redexMeasure d'' < redexMeasure d>)
```

This requires proving `redexMeasure` strictly decreases, which is the core challenge.

**Mathlib infrastructure available**:
- `WellFounded.fix` (Init.WF)
- `InvImage.wf` (Init.WF)
- `Nat.lt_wfRel` (Init.WF)
- `Prod.Lex.instIsWellFounded` (Mathlib.Order.RelClasses) -- for lexicographic measures
- `Multiset.wellFounded_isDershowitzMannaLT` (Mathlib.Data.Multiset.DershowitzManna) -- for multiset ordering

### 3.8 Recommended Approach (Final)

Given the complexity, the recommended approach for the implementation plan is:

**Keep the fuel-bounded `normalizeAux` but change the fuel to a safe upper bound and prove
sufficiency via a different route.**

**Concrete recommendation**:

1. **Define `nodeCount : T.Derivation G A → Nat`** (count all constructor nodes)

2. **Prove `reduceRoot_preserves_subterm_normality`**: If immediate subterms of `d` are
   strongly normal and `d.reduceRoot = some d'`, then:
   - For commuting conversions: `d'` has strongly normal root and subterms that are themselves
     strongly normal (after re-wrapping with the pushed elimination)
   - For proper and-redexes: `d'` is a strongly normal subterm
   - For proper imp/or-redexes: `d'` is a substitution instance; needs separate analysis

3. **For the imp/or-redex substitution case**: This is genuinely hard. The standard approach
   (Prawitz Ch. IV) shows that `subsOne` does not create new maximal formulas of the same
   or higher complexity. This requires a detailed analysis of `subs` through the derivation
   structure.

4. **Pragmatic fallback**: If the full termination proof for imp/or-redexes proves too complex,
   consider:
   - Proving termination only for the commuting-conversion-free fragment first
   - Using `Nat.strongRecOn` with `redexMeasure` instead of fuel
   - Or: accepting that `normalize_isStronglyNormal` requires more infrastructure and
     marking it as a follow-up, while completing the subformula property for strongly
     normal derivations (which is already sorry-free except for the 3 cases in
     `conclusion_grounded_or_intro`)

## 4. Implementation Priorities

### Priority 1 (Can be done now): Fix conclusion_grounded_or_intro (3 sorry → 0)

**Approach**: Replace the three-way `orE` sorry cases. Two options:

**Option A (recommended)**: The theorem IS true but requires deeper induction. When both
branches DA, DB of `orE` are intro-headed:
- Case split on DA's constructor:
  - If `DA = andI _ D1 D2`, then `C' = X ∧ Y`. Apply IH to `D1 : insert A' G' ⊢ X`
    and `D2 : insert A' G' ⊢ Y`. D1 and D2 are strongly normal (from DA being strongly
    normal). The IH gives grounding or intro-headedness for D1 and D2. If both give
    grounding, combine to ground `X ∧ Y`. If either is intro-headed, recurse deeper.
  - If `DA = orI1 _ D'`, then `C' = X ∨ Y`. Apply IH to `D' : insert A' G' ⊢ X`.
  - If `DA = impI _ D'`, then `C' = X → Y`. Apply IH to `D' : insert (X) (insert A' G') ⊢ Y`.

This is a well-founded recursion on the size of DA (each recursive call goes to a strict subterm
of DA). However, the current proof is by induction on `d` (the outer derivation), not on DA.
This mismatch means we need either:
- Mutual recursion: simultaneously prove for both the outer derivation and the intro-headed branches
- A separate lemma for intro-headed derivations

**Separate lemma approach**:
```lean
/-- For an intro-headed strongly normal derivation, the conclusion is grounded
    or a subformula of something grounded. -/
theorem intro_conclusion_grounded (d : T.Derivation G A)
    (hn : d.isStronglyNormal = true) (hir : d.isIntroRoot = true) :
    conclusionGrounded d
```

This is provable by induction on `d`, restricted to intro constructors:
- `andI G D1 D2`: need `A ∧ B` grounded. Apply `conclusion_grounded_or_intro` to D1 and D2.
  If both give grounding, then D1 grounds `A` and D2 grounds `B`... but we need `A ∧ B`
  grounded, not `A` and `B` separately.

**Wait**: "grounded" means `A ∧ B` is a subformula of something in G or T. If D1's conclusion
`A` is grounded as a subformula of `C ∈ G`, that does NOT mean `A ∧ B` is a subformula of C.

**This approach does NOT work.** The intro-headed derivation's conclusion is NOT necessarily
grounded. The counterexample above (`orE` producing `r ∧ r` from `r`-assumptions)
demonstrates exactly this: the `andI` branches produce `r ∧ r` which is not grounded.

**Therefore: the theorem `conclusion_grounded_or_intro` as stated IS false, even when restricted to intro-headed derivations.**

**Correct fix**: Use **Option D from Section 2.3**: inline the grounding logic directly into
the subformula property proof for elimination cases, avoiding the need for a separate lemma.
The `conclusion_grounded_or_intro` theorem should be weakened to exclude `orE` cases:

```lean
theorem conclusion_grounded_or_intro
    (d : T.Derivation G A) (hn : d.isStronglyNormal = true) :
    conclusionGrounded d ∨ d.isIntroRoot = true ∨ ∃ G' D DA DB, d = orE G' D DA DB
```

Or more practically: **just add an `orE` check** to the `orE` case:

In the `orE.ax/ass/elim` sorry cases, the goal has `hirA : DA.isIntroRoot = true` and
`hirB : DB.isIntroRoot = true`. Instead of trying to prove grounding, return the second
disjunct by observing that the derivation is an `orE` with intro-headed branches. But the
current second disjunct is `d.isIntroRoot = true`, and `orE` is not intro-headed.

**THE ACTUAL FIX**: Since the subformula property proof for `orE` (lines 703-715) handles
the intro-headed branch case correctly (line 715: `exact Or.inl (IsSubformula.refl _)`),
and the only place `conclusion_grounded_or_intro` is used in elimination cases (where it
always returns the first disjunct), the simplest fix is to **not use `conclusion_grounded_or_intro`
in the `orE` subformula case at all**. Instead, handle the `orE` case in the subformula
property directly.

Looking at lines 703-715 more carefully: when `B = A` (the conclusion), the proof does:
```lean
rcases (conclusion_grounded_or_intro DA hn_DA) with hgA | hirA
· <handle grounded DA>
· exact Or.inl (Proposition.IsSubformula.refl _)  -- A is subformula of itself
```

This already handles the intro-headed case! The sorry is only needed for the three cases
inside `conclusion_grounded_or_intro` itself. So the fix is:

**Change `conclusion_grounded_or_intro` to only claim grounding for non-intro, non-orE derivations,
and add the orE disjunct to the conclusion.**

### Priority 2 (Requires more infrastructure): Prove normalize_isStronglyNormal (2 sorry → 0)

This is substantially harder and requires either:
(a) A complete termination argument for the fuel-bounded approach, or
(b) Restructuring to well-founded recursion, or
(c) A hybrid approach: prove the result for a "sufficient fuel" value

Estimated effort: 150-300 lines depending on approach.

## 5. Concrete Code Sketch for Priority 1

The minimal change to eliminate the 3 sorry is to weaken `conclusion_grounded_or_intro`:

```lean
/-- In a strongly normal derivation, either the conclusion is grounded,
    the derivation is intro-headed, or it is an orE. -/
theorem conclusion_grounded_or_intro_v2
    (d : T.Derivation G A) (hn : d.isStronglyNormal = true) :
    conclusionGrounded d ∨ d.isIntroRoot = true ∨ d.isOrERoot = true := by
  -- ... same proof but orE cases return the third disjunct

/-- Helper: an orE-rooted derivation. -/
def Theory.Derivation.isOrERoot : T.Derivation G A → Bool
  | orE _ _ _ _ => true
  | _ => false
```

Then update `subformula_property_of_isStronglyNormal` to handle the three-way disjunction.
In the elimination cases (`andE1`, `andE2`, `impE`), the major premise cannot be `orE`-headed
(strong normality excludes it), so the third disjunct is discharged by `simp [isOrERoot]`.

## 6. Tactic Survey Results

Tactics available for the termination proof:

| Tactic | Applicability |
|--------|--------------|
| `omega` | Useful for Nat arithmetic in fuel bounds |
| `simp` | Essential for Bool/Prop normality checks |
| `cases` / `rcases` | Core tool for constructor case splits |
| `induction` | Standard for structural recursion on Derivation |
| `Nat.strongRecOn` | Available for strong induction on Nat (fuel) |
| `WellFounded.fix` | For well-founded recursion on custom measure |

## 7. Mathlib API Summary

| Name | Module | Relevance |
|------|--------|-----------|
| `WellFounded.fix` | Init.WF | Core tool for WF recursion |
| `InvImage.wf` | Init.WF | Lift WF from Nat to Derivation |
| `Nat.lt_wfRel` | Init.WF | `<` on Nat is well-founded |
| `Prod.Lex.instIsWellFounded` | Mathlib.Order.RelClasses | Lexicographic WF |
| `Multiset.wellFounded_isDershowitzMannaLT` | Mathlib.Data.Multiset.DershowitzManna | Multiset WF ordering |
| `Nat.strongRecOn` | Init.WF | Strong induction on Nat |

## 8. Summary of Recommendations

1. **Fix `conclusion_grounded_or_intro` (Priority 1, ~40 lines)**:
   - Add `isOrERoot` definition
   - Change theorem to three-way disjunction
   - Update `subformula_property_of_isStronglyNormal` callsites (minor changes)
   - Result: 3 sorry eliminated, subformula property for strongly normal derivations fully proved

2. **Prove `normalize_isStronglyNormal` (Priority 2, ~150-300 lines)**:
   - Define `redexWeight` measure
   - Prove `reduceRoot` strictly decreases `redexWeight` when subterms are strongly normal
   - Prove fuel sufficiency or switch to WF recursion
   - Key sub-lemma: `subsOne` on strongly normal derivation does not create redexes of same/higher complexity
   - Result: 2 sorry eliminated, full normalization theorem proved

3. **If Priority 2 proves too complex**: Mark [BLOCKED] with specific sub-goals documented.
   The 3 sorry from Priority 1 should be fixed regardless, as they represent a theorem
   statement bug rather than a proof difficulty.
