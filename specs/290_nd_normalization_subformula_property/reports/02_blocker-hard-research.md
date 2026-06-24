# Hard-Mode Research Report: Blockers for ND Normalization Subformula Property (Task 290)

- **Task**: 290 -- ND Normalization and Subformula Property
- **Date**: 2026-06-23
- **Agent**: cslib-research-hard-agent
- **Reference Grounding Tier**: 1 (literature-backed)
- **BibKey Verification**: Prawitz1965 (verified), TroelstraSchwichtenberg2000 (verified), NegriVonPlato2001 (NOT in references.bib -- needs addition)

## Source-to-Implementation Mapping

| Source | Prop/Location | Lean Identifier | Type Signature | Status |
|--------|---------------|-----------------|----------------|--------|
| [Prawitz1965] | Ch. III, Thm. 1 | -- (not yet defined) | Main branch structure of normal derivations | pending |
| [Prawitz1965] | Ch. IV, Sec. 3 | `Derivation.normalizeAux` | Fuel-bounded normalization | transcribed (fuel bound unproved) |
| [Prawitz1965] | Ch. V | -- (not yet defined) | Commuting conversions for VE | pending |
| [TroelstraSchwichtenberg2000] | Thm. 6.2.7, p.188 | `Derivation.subformula_property_of_isNormal` | Normal derivations satisfy subformula property | **FALSE as stated** (see Section 2) |
| [TroelstraSchwichtenberg2000] | Def. 6.2.2, p.186 | -- (not yet defined) | Track definition for derivations | pending |
| [TroelstraSchwichtenberg2000] | Sec. 6.1, p.183 | -- (not yet defined) | Commuting conversions (permutative reductions) | pending |
| [Prawitz1965] | Ch. IV-V | `Derivation.normalize` | `d.normalizeAux (2 ^ d.height)` | transcribed (isNormal unproved) |

## 1. Executive Summary

**CRITICAL FINDING**: The current theorem `subformula_property_of_isNormal` is **false as stated**. The predicate `isNormal` (which detects only proper intro-elim redexes) is insufficient for the subformula property. A concrete counterexample exists: `andE1 G (orE G (ass h) (andI _ e1 e2) (andI _ f1 f2))` passes `isNormal = true` but contains `r /\ r` in its formulas, which is not a subformula of the conclusion `r` or any hypothesis.

The root cause: `isNormal` misses **commuting conversions** (also called permutative reductions), which are reductions that push elimination contexts inside `orE` branches. Without reducing these, introduction rules can appear inside elimination sub-derivations, introducing formulas that are not subformulas of the conclusion or hypotheses.

This finding changes the nature of both blockers:

- **Blocker 1** is not a proof gap -- it is a **false theorem**. The fix requires either (a) strengthening `isNormal` to `isStronglyNormal` (also excluding commuting conversion patterns), or (b) adding commuting reductions to `normalizeAux` so that `normalize` produces strongly normal derivations.

- **Blocker 2** (`normalize_isNormal`) is also affected: the normalization function must also reduce commuting conversions to produce derivations for which the subformula property holds.

**Recommended path**: Define `isStronglyNormal` (adding 4 commuting conversion patterns to the 5 proper redex patterns), add commuting reductions to `reduceRoot`, and prove the subformula property for `isStronglyNormal` derivations. The proof for strongly normal derivations goes through by standard structural induction without tracks.

## 2. The Counterexample: isNormal Is Insufficient

### 2.1 Construction

Consider `G = {p \/ q, r}` with `T = MPL = emptyset` (minimal propositional logic, no axioms):

```lean
-- The derivation:
-- andE1 G (orE G (ass h_pq) (andI _ (ass h_r) (ass h_r)) (andI _ (ass h_r) (ass h_r)))
-- derives: G ⊢ r
-- Shape:
--
--   [p]    r  r       [q]    r  r
--   ---  -------       ---  -------
--   p∨q   r ∧ r        p∨q   r ∧ r
--   ----  -----  -----
--        r ∧ r
--        -----
--          r
```

### 2.2 Verification

**isNormal check**: `andE1 G d` checks if `d` matches `andI` -- it does not (it's `orE`). So the check falls through to `d.isNormal`. For `orE G d' da db`, the check verifies `d'` is not `orI1` or `orI2` -- it's `ass`, so it passes. Then `d'.isNormal && da.isNormal && db.isNormal` where all sub-derivations are `ass` or `andI` of `ass` nodes, all normal. Result: `isNormal = true`.

**SubformulaProperty violation**: The formula `r /\ r` appears in `d_full.formulas` (from the `andI` nodes inside the `orE` branches). But:
- `(r /\ r).IsSubformula r = false` (verified by `decide`: `r.subformulas = {r}`)
- `(r /\ r).IsSubformula (p \/ q) = false` (verified by `decide`)
- `(r /\ r).IsSubformula r = false` (the other hypothesis is `r` again)
- `T = emptyset`, so no axioms

Therefore `SubformulaProperty` fails.

### 2.3 Root Cause: Missing Commuting Conversions

The derivation `andE1(orE(...))` is a **commuting conversion** (permutative redex). Prawitz ([Prawitz1965] Ch. V) and Troelstra-Schwichtenberg ([TroelstraSchwichtenberg2000] Sec. 6.1, p.183) define these as additional reduction steps beyond proper redexes:

The commuting conversion pushes the elimination context inside the `orE` branches:

```
andE1(orE G d da db) → orE G d (andE1 (insert A G) da) (andE1 (insert B G) db)
```

After this reduction, the `andI` nodes would create proper redexes with the now-adjacent `andE1`, which would then be reduced by standard normalization. The four commuting conversion patterns are:

| Pattern | Reduction |
|---------|-----------|
| `andE1(orE G d da db)` | `orE G d (andE1 _ da) (andE1 _ db)` |
| `andE2(orE G d da db)` | `orE G d (andE2 _ da) (andE2 _ db)` |
| `impE(orE G d da db, e)` | `orE G d (impE da (weak e)) (impE db (weak e))` |
| `orE(orE G d da db, ea, eb)` | `orE G d (orE _ da (weak ea) (weak eb)) (orE _ db (weak ea) (weak eb))` |

Note: The `impE` and nested `orE` commuting conversions require weakening the minor premise(s) into the extended context.

## 3. Revised Blocker Analysis

### 3.1 Blocker 1 (Revised): False Theorem Statement

**Original diagnosis**: "Elimination cases require Prawitz main-branch lemma."
**Revised diagnosis**: "The theorem is false. `isNormal` does not exclude commuting conversions."

**Fix**: Replace `isNormal` with `isStronglyNormal` that also detects commuting conversion patterns:

```lean
def Theory.Derivation.isStronglyNormal : T.Derivation G A → Bool
  | ax _ => true
  | ass _ => true
  | andI _ D₁ D₂ => D₁.isStronglyNormal && D₂.isStronglyNormal
  | andE1 _ D =>
    match D with
    | andI _ _ _ => false      -- proper redex
    | orE _ _ _ _ => false     -- commuting conversion
    | _ => D.isStronglyNormal
  | andE2 _ D =>
    match D with
    | andI _ _ _ => false      -- proper redex
    | orE _ _ _ _ => false     -- commuting conversion
    | _ => D.isStronglyNormal
  | orI1 _ D => D.isStronglyNormal
  | orI2 _ D => D.isStronglyNormal
  | orE _ D DA DB =>
    match D with
    | orI1 _ _ => false        -- proper redex
    | orI2 _ _ => false        -- proper redex
    | _ => D.isStronglyNormal && DA.isStronglyNormal && DB.isStronglyNormal
  | impI _ D => D.isStronglyNormal
  | impE D E =>
    match D with
    | impI _ _ => false        -- proper redex
    | orE _ _ _ _ => false     -- commuting conversion
    | _ => D.isStronglyNormal && E.isStronglyNormal
```

**Why this fixes Blocker 1**: In a strongly normal derivation, the major premise of `andE1` cannot be `orE`-headed. It must be one of: `ax`, `ass`, `andE1`, `andE2`, or `impE`. All of these derive `A /\ B` either from a hypothesis/axiom directly (leaf case) or via elimination from another hypothesis/axiom (elimination case). In either case, all formulas in the sub-derivation are subformulas of `A /\ B` or of hypotheses/axioms -- and since these are elimination-headed, the strengthened induction gives `IsSubformula C` for `C in G union T`, from which `IsSubformula A` follows by `trans` with `and_left`.

The key insight: once commuting conversions are excluded, the major premise of every elimination rule in a strongly normal derivation is itself an elimination or a leaf. This means every formula flows through a chain of eliminations from a hypothesis/axiom, and the subformula relationship is monotonically decreasing along this chain.

### 3.2 Blocker 2 (Revised): Normalization Must Include Commuting Reductions

**Original diagnosis**: "Need to prove 2^height fuel suffices for proper redex reduction."
**Revised diagnosis**: "normalizeAux must also reduce commuting conversions, and the termination measure must account for them."

**Fix**: Extend `reduceRoot` with commuting conversion cases:

```lean
def Theory.Derivation.reduceRoot : T.Derivation G A → Option (T.Derivation G A)
  -- Proper redexes (existing)
  | impE (impI _ D) E => some (D.subsOne E)
  | andE1 _ (andI _ D₁ _) => some D₁
  | andE2 _ (andI _ _ D₂) => some D₂
  | orE _ (orI1 _ D) DA _ => some (DA.subsOne D)
  | orE _ (orI2 _ D) _ DB => some (DB.subsOne D)
  -- Commuting conversions (new)
  | andE1 G (orE G' D DA DB) => some (orE G D (andE1 _ DA) (andE1 _ DB))
  | andE2 G (orE G' D DA DB) => some (orE G D (andE2 _ DA) (andE2 _ DB))
  | impE (orE G D DA DB) E =>
      some (orE G D (impE DA (E.weakCtx ...)) (impE DB (E.weakCtx ...)))
  | _ => none
```

Note: The `orE(orE ...)` commuting conversion is the most complex to encode because it requires three sub-derivations to be rearranged with weakening. It may be simpler to handle this case by repeated application of the other commuting conversions, since `orE` as major premise of `andE1`/`andE2`/`impE` covers most cases, and `orE` as major premise of another `orE` is handled by transitively reducing the inner `orE` first.

**Termination**: Commuting conversions do not change the grade (max complexity of maximal formulas) but do change the structure. The standard measure for strong normalization with commuting conversions adds a "rank" component: the number of rule instances below the highest commuting conversion. Alternatively, a simpler fuel-bounded approach works: the total number of nodes in the derivation provides a bound on the number of commuting conversion steps (each commuting conversion strictly reduces the "depth" of `orE` within elimination contexts).

### 3.3 The Proof Path for Strongly Normal Derivations

Once `isStronglyNormal` is defined and commuting reductions are added, the subformula property proof proceeds by standard structural induction WITHOUT tracks:

**For `andE1 G d` where `d.isStronglyNormal = true`**:
- `d` cannot be `andI` (proper redex) or `orE` (commuting conversion)
- `d` must be `ax`, `ass`, `andE1`, `andE2`, or `impE`
- If `d = ax h`: then `A /\ B in T`, and all formulas are subformulas of `A /\ B` which is in `T`. Since `A` is a subformula of `A /\ B`, we get `IsSubformula A` by transitivity, or directly `IsSubformula C` for `C in T`.
- If `d = ass h`: similar, with `A /\ B in G`
- If `d` is elimination-headed: by IH on the strongly normal sub-derivation, all formulas are subformulas of `A /\ B` or of hypotheses/axioms. For the first disjunct, `IsSubformula (A /\ B)` and `and_left : A.IsSubformula (A /\ B)` give `IsSubformula A` by transitivity. For the other disjuncts, they pass through unchanged.

Wait -- this still has the same problem. The IH gives `IsSubformula (A /\ B)` but we need `IsSubformula A`. The formula `B` is a subformula of `A /\ B` but not of `A`, so we cannot get `IsSubformula A` from `IsSubformula (A /\ B)` by transitivity (transitivity goes the wrong direction: we'd need `(A /\ B).IsSubformula A`, but the actual fact is `A.IsSubformula (A /\ B)`).

**This means the strengthened `isStronglyNormal` is necessary but NOT sufficient** on its own to make the standard induction work. We still need one more ingredient.

### 3.4 The Actual Fix: Strengthened Induction for Elimination Chains

The key insight from Prawitz's track analysis, adapted for strongly normal derivations:

In a strongly normal derivation, the major premise of every elimination rule is either a leaf (ax/ass) or another elimination. This means the formulas flow through a chain:

```
ax/ass(F) → elim₁(F₁) → elim₂(F₂) → ... → elimₙ(Fₙ)
```

where each `Fᵢ` is a subformula of `Fᵢ₋₁` (since elimination extracts subformulas). Therefore `Fₙ` is a subformula of `F`, and `F` is a hypothesis or axiom.

To capture this in the induction, we prove a **stronger statement**:

```lean
theorem subformula_property_of_isStronglyNormal_strong
    (d : T.Derivation G A) (hn : d.isStronglyNormal = true) :
    ∀ B ∈ d.formulas,
      (∃ C ∈ G, B.IsSubformula C) ∨ (∃ C ∈ T, B.IsSubformula C)
      ∨ B.IsSubformula A
```

Note the ORDER of disjuncts is reversed compared to the original: the hypothesis/axiom case comes FIRST. This is semantically the same but makes the proof easier because the elimination cases primarily produce the first two disjuncts.

For the `andE1` case: the IH gives `(∃ C ∈ G, B.IsSubformula C) ∨ (∃ C ∈ T, B.IsSubformula C) ∨ B.IsSubformula (A /\ B)`. The first two disjuncts pass through directly. For the third: `B.IsSubformula (A /\ B)` means `B` is in `(A /\ B).subformulas = {A /\ B} ∪ A.subformulas ∪ B.subformulas`. If `B ∈ A.subformulas`, we're done (`B.IsSubformula A`). If `B = A /\ B` or `B ∈ B✝.subformulas`, we need to show these are subformulas of some hypothesis or axiom.

This is STILL not enough with standard induction. The problem remains that `B ∈ B✝.subformulas` does not give `B.IsSubformula A`.

### 3.5 The Definitive Solution: Two-Phase Proof

After thorough adversarial analysis, the cleanest solution is a **two-phase approach**:

**Phase A**: Prove that in a strongly normal derivation, the major premise of every elimination rule has its conclusion formula as a subformula of some hypothesis or axiom. This is a simple induction on the "elimination depth" (chain of eliminations from a leaf).

```lean
/-- In a strongly normal derivation, the conclusion formula A is either:
    (1) a subformula of some hypothesis C ∈ G, or
    (2) a subformula of some axiom C ∈ T, or
    (3) the derivation is introduction-headed. -/
theorem conclusion_grounded_or_intro (d : T.Derivation G A)
    (hn : d.isStronglyNormal = true) :
    (∃ C ∈ G, A.IsSubformula C) ∨ (∃ C ∈ T, A.IsSubformula C)
    ∨ d.isIntroRoot = true
```

For elimination-headed strongly normal `d`:
- If leaf (ax/ass): `A` itself is in `T`/`G`, use `refl`
- If `andE1 G d'` where `d'` is strongly normal: by IH on `d'`, `A /\ B` is grounded in `G`/`T` (since `d'` is not intro-headed -- `d'` can't be `andI` or `orE`). Then `A.IsSubformula (A /\ B)` by `and_left`, and `A /\ B` is a subformula of some `C ∈ G ∪ T`, giving `A.IsSubformula C` by transitivity.

**Phase B**: With `conclusion_grounded_or_intro` in hand, the subformula property follows:

For elimination-headed normal `d : Derivation G A`:
- By Phase A, `A` is a subformula of some `C ∈ G ∪ T`
- By IH, all formulas in sub-derivations are subformulas of the major premise's conclusion or of hypotheses/axioms
- Since the major premise's conclusion is a compound of `A` and other subformulas, and all of these are subformulas of `C ∈ G ∪ T`, everything is grounded

For introduction-headed normal `d`:
- The IH gives subformulas of the introduced components, which are subformulas of `A`
- This is the already-proved case

**This two-phase approach avoids explicit track definitions and works with standard structural induction.** Estimated effort: 60-100 lines for Phase A, 40-60 lines for Phase B modifications.

## 4. Reuse Check Results

### 4.1 CSLib Reuse (All 5 Steps Exhausted)

| Step | Query | Result |
|------|-------|--------|
| 1. Foundations | `lean_local_search "Track"`, `lean_local_search "mainBranch"` | No track/main-branch infrastructure exists |
| 2. Typeclass hierarchy | `lean_local_search "IsSubformula"` | 9 lemmas exist (refl, trans, and_left/right, or_left/right, imp_left/right) |
| 3. Notation | N/A for this task | N/A |
| 4. Mathlib | `lean_leansearch "subformula property of normal natural deduction"` | No relevant results |
| 5. Logics/Languages | `grep mainBranch/topSegment/endPiece` across Cslib/ | No matches |

### 4.2 Adjacent Infrastructure

| Component | File | Relevance |
|-----------|------|-----------|
| `LJProof.cutElim` | `SequentCalculus/LJ/CutElimination.lean` | Has sorry (line 103); would enable Negri-von Plato approach if completed |
| `LKProof.cutElim` | `SequentCalculus/LK/CutElimination.lean` | Exists but LK import is commented out due to build errors |
| `Derivation.subs` | `NaturalDeduction/Basic.lean` | Critical for reduction steps; used in `reduceRoot` via `subsOne` |
| `Derivation.weak` / `weakCtx` | `NaturalDeduction/Basic.lean` | Needed for commuting conversion reductions (weakening minor premises) |
| `Proposition.IsSubformula.*` | `Normalization.lean` | 9 lemmas provide the subformula lattice; sufficient for the two-phase proof |

## 5. Concrete Implementation Recommendations

### 5.1 Step 1: Define isStronglyNormal (Replace isNormal)

Add a new predicate that excludes both proper redexes AND commuting conversions. The 4 additional checks (over the existing 5) are:
- `andE1 _ (orE _ _ _ _) => false`
- `andE2 _ (orE _ _ _ _) => false`
- `impE (orE _ _ _ _) _ => false`
- `orE _ (orE _ _ _ _) _ _ => false` (optional: this may be handled by transitively reducing inner `orE` first)

### 5.2 Step 2: Extend reduceRoot with Commuting Reductions

Add 3-4 cases to `reduceRoot` for the commuting conversions. The `andE1`/`andE2` cases are straightforward. The `impE` case requires weakening. The nested `orE` case is most complex but may be omitted if covered by other reductions.

### 5.3 Step 3: Prove conclusion_grounded_or_intro (Phase A)

By induction on `d`:
- Leaves: direct from ax/ass
- Introduction rules: return the third disjunct (`isIntroRoot = true`)
- Elimination rules: use IH on the sub-derivation (which is not intro-headed in a strongly normal derivation due to proper redex exclusion, and not orE-headed due to commuting conversion exclusion), getting the conclusion of the sub-derivation grounded. Then use subformula transitivity.

### 5.4 Step 4: Prove subformula_property_of_isStronglyNormal (Phase B)

Modify the existing proof:
- Introduction cases: unchanged (already proved)
- Elimination cases: use `conclusion_grounded_or_intro` on the sub-derivation to establish that the major premise's conclusion is grounded. Then the IH on the sub-derivation gives all formulas subformula of the major premise's conclusion or hypotheses/axioms. Since the major premise's conclusion is grounded, everything is grounded.

### 5.5 Step 5: Update normalize and prove normalize_isStronglyNormal

The existing `normalizeAux` already normalizes sub-derivations before reducing at root. Adding commuting conversion cases to `reduceRoot` means the loop will now also reduce commuting conversions. The termination argument needs to account for this: commuting conversions do not decrease the grade but do decrease a "permutation depth" measure.

### 5.6 Effort Estimate (Revised)

| Component | Lines | Difficulty | Depends On |
|-----------|-------|------------|------------|
| `isStronglyNormal` definition | 30-40 | Low | Existing `isNormal` as template |
| Commuting conversion cases in `reduceRoot` | 20-40 | Medium | `weakCtx` for context manipulation |
| `conclusion_grounded_or_intro` (Phase A) | 60-100 | Medium | `isStronglyNormal`, `IsSubformula.trans` |
| Revised `subformula_property` proof (Phase B) | 40-60 | Medium | Phase A result |
| `normalize_isStronglyNormal` termination | 50-80 | Medium-High | Extended `reduceRoot` |
| Total | 200-320 | | |

## 6. Adversarial Self-Verification

### 6.1 Challenged Claims

| Claim | Challenge | Verdict |
|-------|-----------|---------|
| "The theorem subformula_property_of_isNormal is false" | Is the counterexample valid? Could there be a subtle error in the isNormal check? | **Confirmed by Lean**: `isNormal` checks `andE1 G d` by matching `d` against `andI`; `d = orE(...)` does not match, so the check passes. Independently verified `r /\ r ∉ r.subformulas` and `r /\ r ∉ (p \/ q).subformulas` using `by decide`. |
| "Commuting conversions are the root cause" | Could the issue be something else, e.g., a bug in the `formulas` definition? | **Confirmed**: `formulas` collects conclusions at every node. The `andI` nodes inside `orE` contribute `r /\ r`. This is correct behavior -- `formulas` faithfully reports what the derivation contains. The issue is purely that `isNormal` does not exclude the commuting conversion pattern. |
| "isStronglyNormal suffices for the subformula property" | After adding commuting conversion exclusions, does standard induction now work? | **Partially confirmed (high confidence)**: The two-phase approach (Phase A + Phase B) handles the elimination cases. Phase A is the key enabler: it proves the conclusion of elimination-headed strongly normal derivations is grounded in hypotheses/axioms. Phase B then uses this to close the IH gap. The argument is sound proof-theoretically; Lean encoding feasibility is medium-high confidence. |
| "Strengthened mutual induction avoids tracks entirely" | Even with strong normality, do we need tracks? | **Revised**: Tracks are NOT needed. The two-phase approach (conclusion_grounded_or_intro + revised subformula property) is simpler and sufficient. The conclusion_grounded_or_intro lemma is effectively a "mini-track" that only tracks the CONCLUSION formula through the elimination chain, rather than tracking all formulas through a full track structure. |
| "2^height fuel is sufficient for normalization" | With commuting conversions added, is the fuel bound still reasonable? | **Medium confidence**: Commuting conversions change the structure but do not duplicate sub-derivations (unlike proper imp/or reductions). Each commuting conversion step pushes one elimination down into orE branches, strictly reducing the "distance" between elimination and introduction rules. The number of such steps is bounded by the product of the number of elimination rules and the number of orE nodes. The `2^height` bound may or may not cover this. |

### 6.2 BibKey Verification Status

| BibKey | Status | Location in references.bib |
|--------|--------|---------------------------|
| `Prawitz1965` | Verified | Line 418 |
| `TroelstraSchwichtenberg2000` | Verified | Line 811 |
| Negri & von Plato 2001 | **NOT in references.bib** | Needs to be added as `NegriVonPlato2001` |

### 6.3 Recommendations Modified After Verification

| Original Recommendation | Revised Recommendation | Reason |
|------------------------|------------------------|--------|
| "Use track machinery from T&S Sec. 6.2" | "Use two-phase proof without tracks" | Tracks are unnecessary given isStronglyNormal |
| "Fix Blocker 1 with strengthened mutual induction" | "Fix Blocker 1 by correcting the theorem (false as stated)" | The theorem is false, not merely hard to prove |
| "Blocker 2 is about fuel sufficiency" | "Blocker 2 now also requires commuting conversion support in reduceRoot" | normalizeAux must produce strongly normal derivations |
| "150-230 lines total" | "200-320 lines total" | Additional work for commuting conversions |

### 6.4 Confidence Assessment

| Claim | Confidence | Rationale |
|-------|------------|-----------|
| `isNormal` is insufficient (counterexample exists) | Very High (99%) | Verified independently via `lean_run_code` and `by decide` |
| `isStronglyNormal` + two-phase proof resolves Blocker 1 | High (85%) | Sound proof-theoretically; Lean encoding has medium-high feasibility |
| Commuting conversions in `reduceRoot` resolve Blocker 2 | Medium-High (75%) | Standard proof theory; `weakCtx` is available; nested `orE` case is complex |
| Total effort 200-320 lines | Medium (65%) | Commuting conversion cases may be larger than estimated due to context arithmetic |

## 7. Zero-Debt Compliance

No `sorry` deferral is recommended. The core issue is a false theorem statement, not a hard proof. The fix is well-understood proof-theoretically and has concrete Lean implementation paths:

1. Replace `isNormal` with `isStronglyNormal` (or rename and strengthen)
2. Extend `reduceRoot` with commuting conversion cases
3. Prove `conclusion_grounded_or_intro` (Phase A)
4. Complete the subformula property proof (Phase B)
5. Prove `normalize_isStronglyNormal` for the extended normalization

If implementation proves intractable (particularly the nested `orE` commuting conversion), the task should be marked [BLOCKED] with the specific Lean goal state rather than introducing sorry.
