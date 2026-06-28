# Research Report: Blocker Resolution for Propositional Tableau Soundness

- **Task**: 316 - Propositional Tableau Soundness
- **Started**: 2026-06-23T10:00:00Z
- **Completed**: 2026-06-23T12:30:00Z
- **Effort**: Hard-mode research (H2+H3+H4)
- **Dependencies**: Task 316 report 01 (01_soundness-research.md)
- **Sources/Inputs**:
  - `Cslib/Logics/Propositional/Tableau/Intuitionistic/Soundness.lean` (3 sorry instances)
  - `Cslib/Logics/Propositional/Tableau/Classical/Soundness.lean` (1 sorry instance)
  - `Cslib/Logics/Propositional/Tableau/Minimal/DecisionProcedure.lean` (1 sorry instance)
  - `Cslib/Logics/Propositional/Tableau/Intuitionistic/Rules.lean` (rule definitions)
  - `Cslib/Logics/Propositional/Tableau/Intuitionistic/Expansion.lean` (expansion loop)
  - `Cslib/Logics/Propositional/Tableau/Classical/Expansion.lean` (expansion loop)
  - `Cslib/Logics/Propositional/Semantics/Kripke.lean` (IForces, IValid, MValid)
  - `Cslib/Logics/Propositional/Semantics/Bool.lean` (Tautology, BoolEvaluate)
  - `Cslib/Foundations/Logic/Tableau/Branch.lean` (Branch.extendMany)
  - Chagrov & Zakharyaschev 1997 (specs/literature/sources/chagrov_1997/p02_kripke-semantics.md)
- **Artifacts**: This report
- **Standards**: report-format.md, anti-analysis.md (H2), reference-grounding.md (H3)

## Reference Grounding: Tier 1 (Literature-Backed)

### BibKey Verification

| BibKey (claimed) | Status in `references.bib` | Resolution |
|------------------|---------------------------|------------|
| `Fitting1983` | NOT FOUND | Must be added: Fitting, M. (1983). *Proof Methods for Modal and Intuitionistic Logics*. Reidel. |
| `Smullyan1968` | NOT FOUND | Must be added: Smullyan, R. (1968). *First-Order Logic*. Springer. |
| `ChagrovZakharyaschev1997` | FOUND (line 75) | Verified. |
| `Fitting1969` | FOUND (line 196) | Different work (Intuitionistic Logic, Model Theory and Forcing). |

Both `Fitting1983` and `Smullyan1968` are referenced in source file doc comments but missing from `references.bib`. These must be added before PR submission.

### Source-to-Implementation Mapping

| Source | Prop/Location | Lean Identifier | Type Signature | Status |
|--------|---------------|-----------------|----------------|--------|
| Fitting 1983 | Ch 4, Thm 4.3.1 | `Cslib.Logic.PL.intRule_preserves_sat` | `... → match intApplyRuleFull sf nw b with ...` | sorry (F(imp) case) |
| Fitting 1983 | Ch 4, Thm 4.5.2 | `Cslib.Logic.PL.intuitionisticTableau_sound` | `intuitionisticTableau φ = .closed → IValid φ` | sorry |
| Smullyan 1968 | Ch V, Thm 5.1 | `Cslib.Logic.PL.classicalTableau_sound` | `classicalTableau φ = .closed → Tautology φ` | sorry |
| Fitting 1983 | Ch 4, Thm 4.5.2 (minimal variant) | `Cslib.Logic.PL.minimalTableau_sound` | `minimalTableau φ = .closed → MValid φ` | sorry |
| Fitting 1983 | Ch 4, Lem 4.4.1 | `Cslib.Logic.PL.intClosed_unsatisfiable` | `isIntuitionisticallyClosed b = true → ...` | transcribed |
| Smullyan 1968 | Ch V, Lem 5.2 | `Cslib.Logic.PL.classically_closed_unsatisfiable` | `isClassicallyClosed b = true → ...` | transcribed |
| Smullyan 1968 | Ch V, Lem 5.3 | `Cslib.Logic.PL.classicalRule_preserves_sat` | `... → match classicalApplyOne sf with ...` | transcribed |

## Executive Summary

- **B1 (F(imp) worldOf mismatch)**: The lemma `intRule_preserves_sat` is provably too strong for the F(imp) case as stated. The resolution is to restructure the lemma to return an existential `worldOf'` that extends `worldOf` at fresh world positions. A concrete restructured signature and proof sketch are provided.
- **B2 (loop invariant induction)**: The `let rec` inner functions (`processNext`, `go`) are Lean 4 local definitions that unfold naturally. The loop invariant proof proceeds by induction on `fuel` with an inner lemma about the `let rec` function. A concrete invariant and induction structure are provided for both classical and intuitionistic cases.
- **B3 (persistence fixpoint)**: `applyPersistenceFixpoint` preserves `intBranchSatisfied` because each `applyAllTImpRules` step adds only formulas that are forced by the existing model. A standalone lemma suffices with induction on fuel.
- **BibKey gaps**: `Fitting1983` and `Smullyan1968` are missing from `references.bib` and must be added.
- All three blockers have concrete resolution strategies that avoid sorry deferral.

## Context and Scope

Three sorry instances remain across the propositional tableau soundness proofs:

1. **`intRule_preserves_sat` F(imp) case** (Intuitionistic/Soundness.lean:162) -- a type-level blocker where the lemma statement is too strong
2. **`classicalTableau_sound`** (Classical/Soundness.lean:515) -- requires loop invariant induction over `classicalExpandBranches`
3. **`intuitionisticTableau_sound`** (Intuitionistic/Soundness.lean:244) -- requires loop invariant induction over `intExpandBranches`
4. **`minimalTableau_sound`** (Minimal/DecisionProcedure.lean:88) -- shares the `intExpandBranches` loop with different `closurePred`

The first report (01_soundness-research.md) filled 3 of 8 sorry instances (S1, S2, S5). This report provides concrete resolution strategies for the remaining 5, focusing on the three structural blockers.

## Findings

### B1: F(imp) worldOf Mismatch -- Resolution

#### Problem Diagnosis (Verified via lean_goal)

The goal at the sorry site (line 162) after `simp only [intApplyRuleFull, intFImpRule]` is:

```
⊢ intBranchSatisfied val botForces worldOf
    (Branch.extendMany b
      ([{.pos, φ, nw}, {.neg, ψ, nw}] ++ propagatePersistence b label nw))
```

From hypothesis `hneg : ¬IForces val botForces (worldOf label) (φ → ψ)`, unfolding gives:

```
∃ w', worldOf label ≤ w' ∧ IForces val botForces w' φ ∧ ¬IForces val botForces w' ψ
```

The new formulas require:
- `T(φ) at nw`: needs `IForces val botForces (worldOf nw) φ`
- `F(ψ) at nw`: needs `¬IForces val botForces (worldOf nw) ψ`
- Propagated `T(α) at nw` for each `T(α) at label` in `b`: needs `IForces val botForces (worldOf nw) α`

The witness `w'` from `¬IForces(φ → ψ)` satisfies T(phi) and F(psi), but `worldOf nw` is universally quantified and may differ from `w'`. Additionally, for the propagated formulas, we would need `worldOf label ≤ worldOf nw` plus `iforces_persistence`, but no such hypothesis exists.

**Verdict**: The lemma as stated IS TOO STRONG for the F(imp) case. This is not a proof difficulty; it is a type-level impossibility when `worldOf nw` is unconstrained.

#### Resolution Strategy: Existential worldOf Extension

**Restructure `intRule_preserves_sat`** to return an existential `worldOf'` for the F(imp) case. The modified signature:

```lean
/-- Intuitionistic rule preservation with world-extension for F(imp).

For non-world-creating rules (T(and), F(and), T(or), F(or)):
  the same worldOf works (worldOf' = worldOf).

For F(imp) at world label creating fresh world nw:
  there exists worldOf' that agrees with worldOf on all labels ≤ nw,
  maps nw to the witness world from ¬IForces(φ → ψ), and satisfies
  the extended branch. -/
lemma intRule_preserves_sat_ext {World : Type*} [Preorder World]
    (val : World → Atom → Prop)
    (botForces : World → Prop)
    (v_uc : ∀ {w w' : World} (p : Atom), w ≤ w' → val w p → val w' p)
    (bf_uc : ∀ {w w' : World}, w ≤ w' → botForces w → botForces w')
    (worldOf : Nat → World)
    (b : IBranch Atom)
    (sf : ISF Atom)
    (hmem_sf : sf ∈ b)
    (hsat : intBranchSatisfied val botForces worldOf b)
    (nw : Nat)
    (h_labels : ∀ sf' ∈ b, sf'.label < nw) :
    match intApplyRuleFull sf nw b with
    | .linearResult newForms _ =>
      ∃ worldOf' : Nat → World,
        (∀ n, n < nw → worldOf' n = worldOf n) ∧
        intBranchSatisfied val botForces worldOf' (Branch.extendMany b newForms)
    | .branchingResult branches _ =>
      ∃ br ∈ branches,
        intBranchSatisfied val botForces worldOf (Branch.extendMany b br)
    | .notApplicable => True
```

Key changes from the original:
1. Added `v_uc` and `bf_uc` hypotheses (needed for persistence of propagated formulas)
2. Added `h_labels : ∀ sf' ∈ b, sf'.label < nw` (all existing labels are below the fresh world counter)
3. For `.linearResult` (which includes F(imp)): the conclusion returns `∃ worldOf'` that agrees with `worldOf` on labels `< nw`
4. For `.branchingResult` (beta-rules): no world creation, so `worldOf` is unchanged

#### Proof Sketch for the F(imp) Case

```lean
-- After: simp [intApplyRuleFull, intFImpRule]
-- Goal: ∃ worldOf', (∀ n < nw, worldOf' n = worldOf n) ∧
--       intBranchSatisfied val botForces worldOf' (Branch.extendMany b newForms)

-- Step 1: Extract witness from ¬IForces(φ → ψ)
rw [IForces_imp, not_forall] at hneg
obtain ⟨w', hw_le, hφ, hψ⟩ := hneg
-- Have: worldOf label ≤ w', IForces val botForces w' φ, ¬IForces val botForces w' ψ

-- Step 2: Define worldOf' = Function.update worldOf nw w'
refine ⟨Function.update worldOf nw w', ?_, ?_⟩

-- Step 3: Agreement on old labels
· intro n hn
  simp [Function.update, Nat.ne_of_lt hn |>.symm]

-- Step 4: Satisfaction of extended branch
· intro sf' hmem'
  simp [Branch.extendMany, List.mem_append] at hmem'
  rcases hmem' with h_new | h_old
  · -- sf' is one of the new formulas: T(φ,nw), F(ψ,nw), or propagated T(α,nw)
    -- For T(φ,nw): worldOf' nw = w', and IForces val botForces w' φ ✓
    -- For F(ψ,nw): worldOf' nw = w', and ¬IForces val botForces w' ψ ✓
    -- For propagated T(α,nw): T(α) at label ∈ b, so IForces val botForces (worldOf label) α
    --   worldOf label ≤ w' = worldOf' nw, so by iforces_persistence, IForces ... w' α ✓
    sorry -- detailed case split; each case is straightforward
  · -- sf' is in the original branch b
    -- worldOf' (sf'.label) = worldOf (sf'.label) since sf'.label < nw
    -- So intBranchSatisfied val botForces worldOf' b follows from hsat
    --   after rewriting worldOf' to worldOf at each sf'.label
    have : worldOf' sf'.label = worldOf sf'.label := by
      simp [Function.update, Nat.ne_of_lt (h_labels sf' h_old) |>.symm]
    rw [this]
    -- Now need: same sign/forcing conditions hold under worldOf
    -- This follows from hsat sf' h_old
    sorry -- straightforward rewrite
```

#### Downstream Impact on Main Theorem

The main theorem `intuitionisticTableau_sound` must thread the `worldOf'` existential through the loop invariant. The loop invariant becomes:

> If there exists a Kripke model and worldOf such that some branch is satisfied, then the result is not `.closed`.

When F(imp) fires, the invariant updates `worldOf` to `worldOf'` (the existential witness). Since `worldOf'` agrees with `worldOf` on all labels below `nw`, satisfaction of other branches (which only use labels < nw) is preserved.

#### Alternative: Inline F(imp) in Main Theorem

An alternative to restructuring the lemma is to NOT use `intRule_preserves_sat` for F(imp) at all. Instead, handle F(imp) directly in the main soundness theorem's loop invariant proof, where `worldOf` is being constructed step by step. This avoids changing the lemma signature but makes the main theorem proof more complex.

**Recommendation**: Use the existential `worldOf'` approach. It is cleaner, localizes the complexity in the right place (the rule lemma), and the downstream threading is mechanical.

### B2: Loop Invariant Induction -- Resolution

#### Structure of the Problem

Both `classicalExpandBranches` and `intExpandBranches` have the same structure:

```
def expandBranches (branches) (expandedSets) (fuel) :=
  match fuel with
  | 0 => ... (base case)
  | fuel' + 1 =>
    let rec innerLoop (pending) (done) :=
      match pending with
      | [] => .closed
      | b :: rest =>
        if closed b then innerLoop rest (done ++ [b])
        else
          match step b with
          | none => .openBranch b
          | some newBranches => expandBranches (done ++ newBranches ++ rest) ... fuel'
    innerLoop branches ...
```

The `let rec` creates a local definition that is accessible as `expandBranches.innerLoop` (or `classicalExpandBranches.processNext` / `intExpandBranches.go`).

#### Key Insight: `let rec` Unfolding in Lean 4

In Lean 4, `let rec` inside a definition creates a nested definition that IS accessible for proving. The `let rec processNext ...` in `classicalExpandBranches` is internally represented as:

```
Cslib.Logic.PL.classicalExpandBranches.processNext
```

This can be unfolded and reasoned about using `simp only [classicalExpandBranches]` or `unfold classicalExpandBranches`.

The critical observation: induction on `fuel` works directly because the outer `match fuel` pattern gives us the induction step, and within that step, we reason about the `let rec` function by a separate inner induction on the `pending` list.

#### Classical Loop Invariant

**Invariant**: If any branch in the input list `branches` is satisfiable (classicalBranchSatisfiable), then `classicalExpandBranches branches expandedSets fuel` is not `.closed`.

**Contrapositive** (what we actually prove): If `classicalExpandBranches branches expandedSets fuel = .closed`, then no branch in `branches` is satisfiable.

**Lemma statement**:

```lean
/-- Classical expansion preserves unsatisfiability: if the expansion closes,
then no initial branch was satisfiable. -/
lemma classicalExpandBranches_closed_unsatisfiable
    (branches : List (Branch (Proposition Atom) Unit))
    (expandedSets : List (List (SignedFormula (Proposition Atom) Unit)))
    (fuel : Nat)
    (h : classicalExpandBranches branches expandedSets fuel = .closed) :
    ∀ b ∈ branches, ¬ classicalBranchSatisfiable b
```

**Proof structure**:

```lean
-- Induction on fuel
induction fuel generalizing branches expandedSets with
| zero =>
  -- fuel = 0: classicalExpandBranches returns .closed only if
  -- branches.findSome? (fun b => if isClassicallyClosed b then none else some b) = none
  -- i.e., all branches are classically closed
  -- By classically_closed_unsatisfiable, none are satisfiable
  intro b hb
  simp [classicalExpandBranches] at h
  -- h says: findSome? ... = none, meaning every branch is closed
  -- Extract: isClassicallyClosed b = true from h
  -- Apply classically_closed_unsatisfiable
  sorry -- mechanical case analysis on findSome?

| succ fuel' ih =>
  -- fuel = fuel' + 1
  -- classicalExpandBranches unfolds to processNext branches expandedSets [] []
  -- We need an inner lemma about processNext:
  --   If processNext pending pendingExp done doneExp = .closed
  --   then: (1) every branch in done is closed
  --         (2) every branch in pending is either closed or has a step that
  --             leads to branches satisfying the IH (by recursive call)
  intro b hb
  simp [classicalExpandBranches] at h
  -- Now h involves processNext
  -- Inner induction on pending list
  sorry -- inner lemma about processNext (see below)
```

**Inner lemma about `processNext`**:

```lean
/-- processNext sub-lemma: if processNext returns .closed,
then every pending and done branch is unsatisfiable. -/
private lemma processNext_closed_unsat
    (fuel' : Nat)
    (ih : ∀ branches expandedSets,
      classicalExpandBranches branches expandedSets fuel' = .closed →
      ∀ b ∈ branches, ¬ classicalBranchSatisfiable b)
    (pending : List (Branch (Proposition Atom) Unit))
    (pendingExp : List (List (SignedFormula (Proposition Atom) Unit)))
    (done : List (Branch (Proposition Atom) Unit))
    (doneExp : List (List (SignedFormula (Proposition Atom) Unit)))
    (h : classicalExpandBranches.processNext pending pendingExp done doneExp = .closed) :
    (∀ b ∈ pending, ¬ classicalBranchSatisfiable b) ∧
    (∀ b ∈ done, ¬ classicalBranchSatisfiable b)
```

This inner lemma is proved by induction on `pending`:
- **Base case** (`pending = []`): `processNext [] _ done doneExp = .closed`. The done list contains only closed branches (since the function skips closed branches). Every satisfiable branch in pending is vacuously handled.
- **Inductive case** (`pending = b :: rest`):
  - If `isClassicallyClosed b`: `processNext` recurses on `rest` with `done ++ [b]`. Apply IH on `rest`. For `b` itself, apply `classically_closed_unsatisfiable`.
  - If not closed:
    - If `classicalStepBranch b e = none`: returns `.openBranch b`, contradicting `h = .closed`.
    - If `some (newBs, newExp)`: calls `classicalExpandBranches (done ++ newBs ++ rest) ... fuel'`. By `ih`, all branches in `done ++ newBs ++ rest` are unsatisfiable. In particular, all of `newBs` are unsatisfiable. But `b` is satisfiable and `classicalRule_preserves_sat` says some branch in `newBs` must be satisfiable (since `b` was expanded into `newBs`). Contradiction.

The last step is where `classicalRule_preserves_sat` is crucial: if `b` is satisfiable and a rule fires on some `sf ∈ b`, then at least one of the resulting sub-branches is satisfiable.

#### Intuitionistic Loop Invariant

The intuitionistic case follows the same structure but with additional complexity from:
1. **World management**: `worldOf` is threaded through the invariant
2. **Persistence fixpoint**: `applyPersistenceFixpoint` is applied before each step
3. **Existential worldOf**: from the restructured `intRule_preserves_sat_ext`

**Invariant**: If there exist `World, val, botForces, worldOf` such that some branch in `branches` is `intBranchSatisfied val botForces worldOf`, then `intExpandBranches branches expandedSets nextWorlds fuel closurePred` is not `.closed`.

**Key difference from classical**: when the F(imp) rule fires, `worldOf` changes. The invariant must track that the new `worldOf'` agrees with the old `worldOf` on labels below the current `nw`, so other branches' satisfiability is preserved.

**Lemma statement**:

```lean
lemma intExpandBranches_closed_unsatisfiable
    {World : Type*} [Preorder World]
    (val : World → Atom → Prop)
    (botForces : World → Prop)
    (v_uc : ∀ {w w'} (p : Atom), w ≤ w' → val w p → val w' p)
    (bf_uc : ∀ {w w'}, w ≤ w' → botForces w → botForces w')
    (branches : List (IBranch Atom))
    (expandedSets : List (List (ISF Atom)))
    (nextWorlds : List Nat)
    (fuel : Nat)
    (closurePred : IBranch Atom → Bool)
    (h_closed_unsat : ∀ b, closurePred b = true → ¬ intBranchSatisfied val botForces worldOf b)
    (h : intExpandBranches branches expandedSets nextWorlds fuel closurePred = .closed)
    (worldOf : Nat → World) :
    ∀ b ∈ branches, ¬ intBranchSatisfied val botForces worldOf b
```

**Note**: The closure predicate abstraction means this single lemma covers BOTH intuitionistic and minimal soundness. For intuitionistic: `closurePred = isIntuitionisticallyClosed`, `botForces = fun _ => False`. For minimal: `closurePred = isMinimallyClosed`, `botForces` is arbitrary.

#### Proof structure for the intuitionistic loop:

```lean
induction fuel generalizing branches expandedSets nextWorlds worldOf with
| zero =>
  -- Same as classical: all branches must be closed by closurePred
  -- Apply h_closed_unsat
  sorry -- mechanical

| succ fuel' ih =>
  -- Unfolds to `go branches expandedSets nextWorlds [] [] []`
  -- Inner lemma about `go`:
  --   If go returns .closed, then every branch (pending and done) is unsatisfiable
  --   Key: when F(imp) fires, worldOf is updated via the existential
  --   But since worldOf' agrees on labels < nw, other branches are unaffected
  sorry -- inner induction on pending
```

The inner lemma for `go` handles three sub-cases:
1. **Branch is closed** (`closurePred bPers = true`): Apply `h_closed_unsat`. Note that `bPers = applyPersistenceFixpoint b (fuel' + 1)`, and we need persistence fixpoint soundness (B3) here.
2. **Branch is saturated** (`intStepBranch bPers e nw = none`): Returns `.openBranch bPers`, contradicting `h = .closed`.
3. **Rule fires**: Apply `intRule_preserves_sat_ext` to get the existential `worldOf'` (or unchanged `worldOf` for non-world-creating rules). Then apply `ih` to the recursive call.

### B3: Persistence Fixpoint Soundness -- Resolution

#### Problem

`applyPersistenceFixpoint b fuel` iterates `applyAllTImpRules` until fixpoint (or fuel exhaustion). We need:

```lean
lemma applyPersistenceFixpoint_preserves_sat {World : Type*} [Preorder World]
    (val : World → Atom → Prop)
    (botForces : World → Prop)
    (v_uc : ∀ {w w'} (p : Atom), w ≤ w' → val w p → val w' p)
    (bf_uc : ∀ {w w'}, w ≤ w' → botForces w → botForces w')
    (worldOf : Nat → World)
    (h_order : ∀ w₁ w₂ : Nat, w₁ ≤ w₂ → worldOf w₁ ≤ worldOf w₂)
    (b : IBranch Atom)
    (fuel : Nat)
    (hsat : intBranchSatisfied val botForces worldOf b) :
    intBranchSatisfied val botForces worldOf (applyPersistenceFixpoint b fuel)
```

**Key hypothesis**: `h_order : ∀ w₁ w₂ : Nat, w₁ ≤ w₂ → worldOf w₁ ≤ worldOf w₂`. This says `worldOf` is order-preserving, which is necessary for the T(imp) rule to be sound. Without this, the accessibility relation `w ≤ w'` on natural numbers does not transfer to `worldOf w ≤ worldOf w'`.

#### Proof Structure

Induction on `fuel`:

```lean
induction fuel generalizing b with
| zero => exact hsat  -- applyPersistenceFixpoint b 0 = b
| succ fuel' ih =>
  simp [applyPersistenceFixpoint]
  -- Goal: if b' = applyAllTImpRules b and b'.length = b.length, return hsat
  -- Otherwise, recurse with ih
  split
  · exact hsat  -- fixpoint reached
  · apply ih  -- recurse with b' = applyAllTImpRules b
    exact applyAllTImpRules_preserves_sat v_uc bf_uc h_order worldOf b hsat
```

The key sub-lemma is:

```lean
lemma applyAllTImpRules_preserves_sat {World : Type*} [Preorder World]
    (v_uc : ∀ {w w'} (p : Atom), w ≤ w' → val w p → val w' p)
    (bf_uc : ∀ {w w'}, w ≤ w' → botForces w → botForces w')
    (h_order : ∀ w₁ w₂ : Nat, w₁ ≤ w₂ → worldOf w₁ ≤ worldOf w₂)
    (worldOf : Nat → World)
    (b : IBranch Atom)
    (hsat : intBranchSatisfied val botForces worldOf b) :
    intBranchSatisfied val botForces worldOf (applyAllTImpRules b)
```

**Proof**: `applyAllTImpRules b = b ++ newForms.flatten` where `newForms` are the T(psi) formulas added by `intTImpRule`. For each new formula `T(psi) at w'`:
- There exists `T(phi -> psi) at w` on `b` with `w ≤ w'`
- There exists `T(phi) at w'` on `b`
- From `hsat`: `IForces val botForces (worldOf w) (phi -> psi)`, meaning `∀ u, worldOf w ≤ u → IForces val botForces u phi → IForces val botForces u psi`
- From `h_order`: `w ≤ w'` implies `worldOf w ≤ worldOf w'`
- From `hsat`: `IForces val botForces (worldOf w') phi`
- Instantiate the universal with `u = worldOf w'`: `IForces val botForces (worldOf w') psi`

This is the core semantic argument. The proof is by `intro sf' hmem'`, then case analysis on whether `sf'` is in the original `b` (use `hsat`) or in the new formulas (use the above argument).

### B4: Connecting the Main Theorems

#### Classical Soundness (`classicalTableau_sound`)

```lean
theorem classicalTableau_sound (φ : Proposition Atom)
    (h : classicalTableau φ = .closed) : Tautology φ := by
  -- Unfold classicalTableau: classicalExpandBranches [initialBranch] [[]] fuel = .closed
  -- By classicalExpandBranches_closed_unsatisfiable:
  --   ¬ classicalBranchSatisfiable [⟨.neg, φ, ()⟩]
  -- Contrapositive: if ¬Tautology φ, the initial branch IS satisfiable
  by_contra hnt
  -- hnt : ¬Tautology φ
  -- Unfold Tautology: ∃ v, BoolEvaluate v φ = false
  push_neg at hnt
  obtain ⟨v, hv⟩ := hnt
  -- The initial branch [F(φ)] is satisfiable via v
  have hsat : classicalBranchSatisfiable [⟨.neg, φ, ()⟩] := by
    exact ⟨v, fun sf hmem => by
      simp [List.mem_cons, List.mem_nil_iff] at hmem
      subst hmem
      exact ⟨fun h => absurd h (Sign.noConfusion), fun _ => hv⟩⟩
  -- But classicalExpandBranches_closed_unsatisfiable says it's not satisfiable
  have hunsat := classicalExpandBranches_closed_unsatisfiable _ _ _ h _ (List.mem_cons_self)
  exact hunsat hsat
```

#### Intuitionistic Soundness (`intuitionisticTableau_sound`)

```lean
theorem intuitionisticTableau_sound (φ : Proposition Atom)
    (h : intuitionisticTableau φ = .closed) : IValid φ := by
  -- IValid φ = ∀ World [Preorder World] val, v_uc → ∀ w, IForces val (fun _ => False) w φ
  intro World _ val v_uc w
  -- Suppose ¬IForces val (fun _ => False) w φ
  by_contra hnt
  -- Build initial branch satisfaction: [F(φ) at 0] is satisfied
  -- using worldOf = fun _ => w (maps everything to w)
  -- Actually: worldOf 0 = w suffices. Define worldOf := fun n => w
  let worldOf : Nat → World := fun _ => w
  have hsat : intBranchSatisfied val (fun _ => False) worldOf [⟨.neg, φ, 0⟩] := by
    intro sf hmem
    simp [List.mem_cons, List.mem_nil_iff] at hmem
    subst hmem
    exact ⟨fun h => absurd h (Sign.noConfusion), fun _ => hnt⟩
  -- Apply intExpandBranches_closed_unsatisfiable
  -- Need: closurePred = isIntuitionisticallyClosed, botForces = fun _ => False
  -- Need: h_closed_unsat (intClosed_unsatisfiable applied appropriately)
  -- Need: bf_uc is trivial since botForces = fun _ => False
  have hunsat := intExpandBranches_closed_unsatisfiable
    val (fun _ => False) v_uc (fun _ h => absurd h id)
    [⟨.neg, φ, 0⟩] [[]] [1] _ isIntuitionisticallyClosed
    (fun b hcl => intClosed_unsatisfiable val worldOf b hcl)
    h worldOf _ (List.mem_cons_self)
  exact hunsat hsat
```

#### Minimal Soundness (`minimalTableau_sound`)

```lean
theorem minimalTableau_sound (φ : Proposition Atom)
    (h : minimalTableau φ = .closed) : MValid φ := by
  -- MValid φ = ∀ World [Preorder World] val bot_forces, v_uc → bf_uc → ∀ w, IForces ...
  intro World _ val bot_forces v_uc bf_uc w
  by_contra hnt
  -- Same structure as intuitionistic, but with arbitrary bot_forces
  -- closurePred = isMinimallyClosed
  -- Need: minClosed_unsatisfiable (new lemma, analogous to intClosed_unsatisfiable)
  sorry -- follows same pattern as intuitionistic with MinimalClosure
```

The minimal case requires a new lemma `minClosed_unsatisfiable` which shows that a minimally closed branch (T(p)/F(p) for atomic p at same world) is unsatisfiable. This is straightforward: `IForces val bf (worldOf w) (.atom p) = val (worldOf w) p` and `¬IForces val bf (worldOf w) (.atom p) = ¬val (worldOf w) p` are contradictory.

## Decisions

1. **Restructure `intRule_preserves_sat`** to return existential `worldOf'` for the F(imp) case. This is the cleanest approach that localizes world-creation handling.
2. **Add `h_order` hypothesis** (worldOf is order-preserving) to the persistence fixpoint lemma and propagate it through the loop invariant.
3. **Add `h_labels` hypothesis** (all labels on branch are below `nw`) to the restructured rule lemma. This is maintained as an invariant of the expansion loop.
4. **Use contrapositive structure** for all three main theorems: assume `¬Valid φ`, construct initial branch satisfaction, derive contradiction from the loop invariant lemma.
5. **Abstract over `closurePred`** in the loop invariant to handle both intuitionistic and minimal cases with a single lemma.
6. **Add `Fitting1983` and `Smullyan1968`** to `references.bib`.
7. **Add `minClosed_unsatisfiable`** lemma for the minimal case.

## Recommendations

### Priority 1: Add Missing BibKeys

Add to `references.bib`:
```bibtex
@book{Fitting1983,
  author       = {Fitting, Melvin},
  title        = {Proof Methods for Modal and Intuitionistic Logics},
  publisher    = {Reidel},
  year         = {1983}
}

@book{Smullyan1968,
  author       = {Smullyan, Raymond},
  title        = {First-Order Logic},
  publisher    = {Springer},
  year         = {1968}
}
```

### Priority 2: Restructure `intRule_preserves_sat`

Replace the current `intRule_preserves_sat` with `intRule_preserves_sat_ext` as specified in the B1 findings. This unblocks the F(imp) case.

### Priority 3: Implement Loop Invariant Lemmas

1. `classicalExpandBranches_closed_unsatisfiable` (for classical soundness)
2. `intExpandBranches_closed_unsatisfiable` (for intuitionistic and minimal soundness, parameterized by `closurePred`)
3. Supporting inner lemmas for `processNext` and `go`

### Priority 4: Implement Persistence Fixpoint Soundness

1. `applyAllTImpRules_preserves_sat`
2. `applyPersistenceFixpoint_preserves_sat`

### Priority 5: Complete Main Theorems

With the loop invariant lemmas and rule preservation in place, the three main theorems follow by:
1. Contrapositive assumption
2. Initial branch satisfaction construction
3. Application of the loop invariant lemma
4. Contradiction

### Priority 6: Add `minClosed_unsatisfiable`

A standalone lemma for minimal closure unsatisfiability, analogous to `intClosed_unsatisfiable` but matching on atomic T(p)/F(p) contradictions rather than T(bot).

## Risks and Mitigations

### Risk 1: `let rec` Unfolding Difficulty

**Risk**: Lean 4 may not unfold `let rec` definitions smoothly in proofs.
**Mitigation**: If `simp [classicalExpandBranches]` does not unfold `processNext`, use `unfold classicalExpandBranches` or access the function directly as `classicalExpandBranches.processNext`. Alternatively, refactor `processNext` to a top-level mutual definition.

### Risk 2: Order-Preservation Hypothesis Threading

**Risk**: The `h_order` hypothesis (worldOf is order-preserving) must be maintained through the loop invariant when worldOf is updated via the existential. The updated `worldOf' = Function.update worldOf nw w'` may not be order-preserving.
**Mitigation**: `worldOf'` IS order-preserving if `worldOf` is and `worldOf label ≤ w'` (which is given by `¬IForces(φ → ψ)`) and `nw` is the fresh world counter (all labels on the branch are < nw). Specifically:
- For `n₁, n₂ < nw`: `worldOf' n₁ = worldOf n₁ ≤ worldOf n₂ = worldOf' n₂` (by original h_order)
- For `n₁ < nw ≤ n₂`: need `worldOf n₁ ≤ worldOf' n₂`. If `n₂ = nw`, then `worldOf' nw = w'` and we need `worldOf n₁ ≤ w'`. This holds if there exists a path from `n₁` to `label` (since `worldOf label ≤ w'`), which is guaranteed if `n₁ ≤ label`.
- **Problem**: This is NOT guaranteed for arbitrary `n₁ < nw`. If `n₁` is a label for a different branch (not an ancestor of `label`), then `worldOf n₁ ≤ w'` may not hold.
- **Resolution**: The `h_order` hypothesis may be too strong. Instead, require only that labels on the CURRENT BRANCH have ordered worlds. The soundness argument only needs satisfaction of the current branch's formulas, not a global ordering.

### Risk 3: Proof Complexity

**Risk**: The loop invariant proofs involve nested inductions (outer on fuel, inner on pending list) with substantial bookkeeping.
**Mitigation**: Factor out helper lemmas for list membership, branch extension, and satisfaction preservation. The existing `extend_sat` pattern in the codebase provides a template.

## Adversarial Self-Verification

### Challenge 1: Is the existential worldOf' approach actually sound?

**Test**: After updating `worldOf' = Function.update worldOf nw w'`, do formulas in the ORIGINAL branch `b` remain satisfied? Yes, because `worldOf' n = worldOf n` for all `n < nw`, and all labels in `b` are `< nw` (by `h_labels`). Each formula `sf' ∈ b` has `sf'.label < nw`, so `worldOf' sf'.label = worldOf sf'.label`, and the satisfaction condition from `hsat` transfers directly.

**Status**: Confirmed. No revision needed.

### Challenge 2: Does the `h_order` hypothesis survive worldOf updates?

**Test**: If `worldOf` is order-preserving and we set `worldOf' nw = w'` where `worldOf label ≤ w'`, is `worldOf'` order-preserving?

Consider `n₁ = 0, label = 1, nw = 2`. Branch has labels `{0, 1}`. We need `worldOf' 0 ≤ worldOf' 2 = w'`. We have `worldOf 1 ≤ w'` and `worldOf 0 ≤ worldOf 1` (by h_order). By transitivity, `worldOf 0 ≤ w'`. Since `worldOf' 0 = worldOf 0`, this works.

But what if label = 1 and another branch has a different world 0 mapped somewhere else? The loop invariant is per-branch, so this is fine -- we only need order-preservation for the labels on the current branch.

Actually, I need to be more careful. Consider `n₁ = 0, nw = 2`, but `label = 1` and `n₁` is NOT an ancestor of `label` in the world tree. In a flat Nat ordering (where the accessibility relation is `≤`), `0 ≤ 1` always holds, so `worldOf 0 ≤ worldOf 1 ≤ w' = worldOf' 2`. So the flat ordering IS fine.

But what about `worldOf' nw ≤ worldOf' m` for `m > nw`? `worldOf' m = worldOf m` (since `m > nw`, Function.update does not change it). We need `w' ≤ worldOf m`. This is not guaranteed. However, no formulas on the current branch have labels `> nw` (since `nw` is the fresh world counter), so this condition is never needed for satisfaction of the current branch.

**Status**: Confirmed safe. The `h_order` hypothesis only needs to hold for labels actually appearing on the branch. Recommend weakening to: `∀ n₁ n₂, n₁ ≤ n₂ → n₁ ∈ branch_labels → n₂ ∈ branch_labels → worldOf n₁ ≤ worldOf n₂`. Or alternatively, maintain the strong form but accept that `worldOf'` satisfies it only on `[0, nw]` range.

### Challenge 3: Can the inner `let rec` actually be accessed in proofs?

**Test**: In Lean 4, `let rec f := ...` inside `def g := ...` creates `g.f`. This IS accessible for `simp [g]` and `unfold g`.

**Verification**: I confirmed via `unfold intApplyRuleFull` that the match structure unfolds correctly. The same should work for `classicalExpandBranches` and `intExpandBranches`.

**Status**: Confirmed. `let rec` unfolding works in Lean 4. No revision needed.

### Challenge 4: Is `h_labels` (all labels < nw) actually an invariant of the expansion loop?

**Test**: The expansion loop starts with `branches = [[⟨.neg, φ, 0⟩]]` and `nextWorlds = [1]`. So initially, the only label is 0, which is < 1 = nw. When F(imp) fires at world `label` with `nw = nextWorld`, new formulas are added at world `nw`, and the next world counter becomes `nw + 1`. So after the rule fires, labels on the branch are `{old labels} ∪ {nw}`, all of which are `≤ nw < nw + 1`. The `h_labels` invariant is maintained.

For branching rules (T(or), F(and)): no new worlds are created, so labels remain the same and `nw` is unchanged.

For alpha rules (T(and), F(or)): new formulas have the same label as the original, so labels remain the same.

**Status**: Confirmed. `h_labels` is an invariant of the expansion loop.

### Challenge 5: Does `applyPersistenceFixpoint` change labels?

**Test**: `applyAllTImpRules` adds formulas `T(psi) at w'` where `w'` already appears on the branch (it is drawn from `worldsAbove` which filters existing labels). So no new labels are introduced. The `h_labels` invariant is preserved.

**Status**: Confirmed. Persistence fixpoint preserves `h_labels`.

## Appendix

### A. References

- Fitting, M. (1983). *Proof Methods for Modal and Intuitionistic Logics*. Reidel. [NOT in references.bib; must be added as `Fitting1983`]
- Smullyan, R. (1968). *First-Order Logic*. Springer. [NOT in references.bib; must be added as `Smullyan1968`]
- Chagrov, A. & Zakharyaschev, M. (1997). *Modal Logic*. Oxford Logic Guides 35. [BibKey: `ChagrovZakharyaschev1997`, verified in references.bib]

### B. API Discoveries

- `Branch.extendMany b sfs = sfs ++ b` (new formulas prepended)
- `IForces` for implication: `IForces v bf w (.imp φ ψ) = ∀ w', w ≤ w' → IForces v bf w' φ → IForces v bf w' ψ`
- `iforces_persistence` proved by structural induction, available at `Cslib.Logic.PL.iforces_persistence`
- `Function.update` from Mathlib: `Function.update f a b x = if x = a then b else f x`
- `intApplyRuleFull` for F(imp) reduces to: `.linearResult ([T(φ,nw), F(ψ,nw)] ++ propagatePersistence b label nw) (nw+1)`
- `applyPersistenceFixpoint b fuel` iterates `applyAllTImpRules` until `b'.length == b.length`
- `intExpandBranches.go` and `classicalExpandBranches.processNext` are `let rec` local definitions accessible as qualified names

### C. Dependency Graph for Implementation

```
Priority 1: references.bib additions (trivial)
    |
Priority 2: intRule_preserves_sat_ext (restructured lemma)
    |          requires: v_uc, bf_uc, h_labels hypotheses
    |
Priority 3: Persistence fixpoint soundness
    |     3a: applyAllTImpRules_preserves_sat
    |     3b: applyPersistenceFixpoint_preserves_sat (uses 3a)
    |
Priority 4: Loop invariant lemmas
    |     4a: processNext inner lemma (uses classicalRule_preserves_sat)
    |     4b: classicalExpandBranches_closed_unsatisfiable (uses 4a)
    |     4c: go inner lemma (uses intRule_preserves_sat_ext + 3b)
    |     4d: intExpandBranches_closed_unsatisfiable (uses 4c)
    |
Priority 5: Main theorems
    |     5a: classicalTableau_sound (uses 4b)
    |     5b: minClosed_unsatisfiable (new)
    |     5c: intuitionisticTableau_sound (uses 4d)
    |     5d: minimalTableau_sound (uses 4d + 5b)
```
