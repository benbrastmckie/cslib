# Research Report: Propositional Tableau Soundness (Task 316)

## Summary

This report documents the sorry instances across three propositional tableau soundness files and provides proof strategies for filling each. There are **8 total sorry instances** (not 6 as initially estimated): 3 in classical soundness, 3 in intuitionistic soundness, and 2 in minimal decision procedure. The task description says 6, which likely excludes the two completeness-direction sorries (`minimalTableau_complete` in the minimal file). The 6 soundness-direction sorries are the primary targets.

## Sorry Inventory

### File 1: `Cslib/Logics/Propositional/Tableau/Classical/Soundness.lean`

| # | Declaration | Line | Goal |
|---|-------------|------|------|
| S1 | `classicalRule_preserves_sat` | 92 | Show each classical rule preserves `classicalBranchSatisfiable` |
| S2 | `classically_closed_unsatisfiable` | 101 | Show `isClassicallyClosed b = true` implies no Boolean valuation is consistent with `b` |
| S3 | `classicalTableau_sound` | 118 | Show `classicalTableau phi = closed` implies `Tautology phi` |

### File 2: `Cslib/Logics/Propositional/Tableau/Intuitionistic/Soundness.lean`

| # | Declaration | Line | Goal |
|---|-------------|------|------|
| S4 | `intRule_preserves_sat` | 99 | Show each intuitionistic rule preserves `intBranchSatisfied` under Kripke semantics |
| S5 | `intClosed_unsatisfiable` | 112 | Show `isIntuitionisticallyClosed b = true` implies no Kripke model satisfies `b` with `botForces = fun _ => False` |
| S6 | `intuitionisticTableau_sound` | 130 | Show `intuitionisticTableau phi = closed` implies `IValid phi` |

### File 3: `Cslib/Logics/Propositional/Tableau/Minimal/DecisionProcedure.lean`

| # | Declaration | Line | Goal |
|---|-------------|------|------|
| S7 | `minimalTableau_sound` | 88 | Show `minimalTableau phi = closed` implies `MValid phi` |
| S8 | `minimalTableau_complete` | 105 | Show `MValid phi` implies `minimalTableau phi = closed` |

**Note**: S8 (`minimalTableau_complete`) is a completeness lemma, not a soundness lemma. The task description says "6 sorry instances" suggesting S8 may be out of scope. However, the `Decidable` instances at lines 119-131 depend on both S7 and S8 via `minimalTableau_decides`.

## Type Signatures and Goal States

### S1: `classicalRule_preserves_sat`

```
Atom : Type u_1, DecidableEq Atom, Hashable Atom
b : Branch (Proposition Atom) Unit
sf : SignedFormula (Proposition Atom) Unit
hmem : sf ∈ b
hsat : classicalBranchSatisfiable b
⊢ match classicalApplyOne sf with
  | RuleResult.linear newForms => classicalBranchSatisfiable (b.extendMany newForms)
  | RuleResult.branching branches => ∃ br ∈ branches, classicalBranchSatisfiable (b.extendMany br)
  | RuleResult.persistent newForms => classicalBranchSatisfiable (b.extendMany newForms)
  | RuleResult.notApplicable => True
```

### S2: `classically_closed_unsatisfiable`

```
b : Branch (Proposition Atom) Unit
hclosed : isClassicallyClosed b = true
⊢ ¬classicalBranchSatisfiable b
```

### S3: `classicalTableau_sound`

```
φ : Proposition Atom
h : classicalTableau φ = ClassicalTableauResult.closed
⊢ Tautology φ
```

### S4: `intRule_preserves_sat`

```
World : Type u_2, Preorder World
val : World → Atom → Prop, botForces : World → Prop, worldOf : ℕ → World
b : IBranch Atom, sf : ISF Atom
x✝ : sf ∈ b
hsat : intBranchSatisfied val botForces worldOf b
nw : ℕ
⊢ match intApplyRuleFull sf nw b with
  | IntRuleResult.linearResult newForms a => intBranchSatisfied val botForces worldOf (Branch.extendMany b newForms)
  | IntRuleResult.branchingResult branches a =>
    ∃ br, br ∈ branches ∧ intBranchSatisfied val botForces worldOf (Branch.extendMany b br)
  | IntRuleResult.notApplicable => True
```

### S5: `intClosed_unsatisfiable`

```
World : Type u_2, Preorder World
val : World → Atom → Prop, worldOf : ℕ → World
b : IBranch Atom
hclosed : isIntuitionisticallyClosed b = true
⊢ ¬intBranchSatisfied val (fun x => False) worldOf b
```

### S6: `intuitionisticTableau_sound`

```
φ : Proposition Atom
h : intuitionisticTableau φ = IntTableauResult.closed
⊢ IValid φ
```

### S7: `minimalTableau_sound`

```
φ : Proposition Atom
h : minimalTableau φ = IntTableauResult.closed
⊢ MValid φ
```

### S8: `minimalTableau_complete`

```
φ : Proposition Atom
h : MValid φ
⊢ minimalTableau φ = IntTableauResult.closed
```

## Key Definitions and Their Unfoldings

### Branch and Satisfiability

- `Branch F L := List (SignedFormula F L)` (abbreviation)
- `Branch.extendMany b sfs := sfs ++ b` (prepend list to branch)
- `branchConsistent v b := ∀ sf ∈ b, (sf.sign = .pos → BoolEvaluate v sf.formula = true) ∧ (sf.sign = .neg → BoolEvaluate v sf.formula = false)`
- `classicalBranchSatisfiable b := ∃ v, branchConsistent v b`

### Classical Closure

`isClassicallyClosed b` unfolds (via `ClassicalClosure` instance) to checking:
1. `b.find? (fun sf => sf.isPos && sf.formula == HasBot.bot)` returns `some` -- T(bot) present
2. OR `b.findContradiction` returns `some (phi, l)` -- T(phi)/F(phi) pair found

### Classical Rule Application

`classicalApplyOne sf := tryAllPropRules propAndOf? propOrOf? propImpOf? propNegOf? sf`

This tries all 8 rules in order: andPos, andNeg, orPos, orNeg, impPos, impNeg, negPos, negNeg. Returns the first applicable result.

### Intuitionistic Types

- `ISF Atom := SignedFormula (Proposition Atom) Nat` (world-labeled)
- `IBranch Atom := List (ISF Atom)`
- `intBranchSatisfied val botForces worldOf b := ∀ sf ∈ b, (sf.sign = .pos → IForces val botForces (worldOf sf.label) sf.formula) ∧ (sf.sign = .neg → ¬ IForces val botForces (worldOf sf.label) sf.formula)`

### Intuitionistic Rule Application

`intApplyRuleFull sf nw b` matches on `(sf.sign, sf.formula)`:
- `(.pos, .and phi psi)` -> `.linearResult [T(phi), T(psi)] nw`
- `(.neg, .and phi psi)` -> `.branchingResult [[F(phi)], [F(psi)]] nw`
- `(.pos, .or phi psi)` -> `.branchingResult [[T(phi)], [T(psi)]] nw`
- `(.neg, .or phi psi)` -> `.linearResult [F(phi), F(psi)] nw`
- `(.neg, .imp phi psi)` -> world-creating: `.linearResult (intFImpRule results) nw'`
- Everything else -> `.notApplicable`

### IForces Definition

```
IForces v bf w (.atom p) = v w p
IForces v bf w .bot = bf w
IForces v bf w (.imp phi psi) = ∀ w', w ≤ w' → IForces v bf w' phi → IForces v bf w' psi
IForces v bf w (.and phi psi) = IForces v bf w phi ∧ IForces v bf w psi
IForces v bf w (.or phi psi) = IForces v bf w phi ∨ IForces v bf w psi
```

### Minimal Closure

`isMinimallyClosed b` checks for T(p)/F(p) where `isAtom p = true` at the same label. Uses `MinimalClosure` instance: looks for positive atomic formulas that have a negative counterpart at the same label.

## Proof Strategies

### S2: `classically_closed_unsatisfiable` (SIMPLEST -- start here)

**Strategy**: Unfold `isClassicallyClosed` and case-split on closure reason.

1. Unfold `isClassicallyClosed` -> `ClosureCondition.isClosed` -> `Option.isSome (findClosure b)`
2. The `findClosure` implementation checks two conditions:
   - `b.find? (sf.isPos && sf.formula == HasBot.bot)` returns `some sf`
   - OR `b.findContradiction` returns `some (phi, l)`
3. Case 1 (T(bot) present): Extract `sf` from the `find?` result. Since `sf.isPos && sf.formula == HasBot.bot`, we have `sf.sign = .pos` and `sf.formula = .bot`. Any consistent valuation requires `BoolEvaluate v .bot = true`, but `BoolEvaluate v .bot = false` by definition. Contradiction.
4. Case 2 (T(phi)/F(phi)): Extract the contradiction pair. The consistent valuation must have `BoolEvaluate v phi = true` (from T(phi)) and `BoolEvaluate v phi = false` (from F(phi)). These are contradictory.

**Key lemmas needed**:
- `List.any_eq_true` to extract membership from `Bool` predicates
- `List.find?_some` or manual case analysis on the `find?` result
- `BoolEvaluate_bot` (already `@[simp]`)
- `Bool` decidability: `true ≠ false`

**Difficulty**: Low. Pure unfolding and case analysis on closure conditions.

### S1: `classicalRule_preserves_sat` (MODERATE)

**Strategy**: Unfold `classicalApplyOne` and case-split on the formula structure and sign.

1. `classicalApplyOne sf = tryAllPropRules propAndOf? propOrOf? propImpOf? propNegOf? sf`
2. Need to case-split on `sf.sign` and `sf.formula`:
   - `(.pos, .and a b)` -> `.linear [T(a), T(b)]` -- alpha rule
   - `(.neg, .and a b)` -> `.branching [[F(a)], [F(b)]]` -- beta rule
   - ... (8 cases total)
   - `(.pos, .atom x)`, `(.neg, .atom x)`, `(.pos, .bot)`, `(.neg, .bot)` -> `.notApplicable` (goal becomes `True`)

3. For each applicable case, use `hsat` (existence of consistent valuation `v`) and show the extended branch is also satisfiable:

**Alpha-rule cases** (linear): The same valuation `v` works. Show that if `v` is consistent with `b` containing `T(phi and psi)`, then `v` is also consistent with `b ++ [T(phi), T(psi)]`. This follows from `BoolEvaluate_and` and the definition of `branchConsistent`.

**Beta-rule cases** (branching): If `v` is consistent with `b` containing `F(phi and psi)`, then `BoolEvaluate v (phi and psi) = false`, meaning `BoolEvaluate v phi = false` or `BoolEvaluate v psi = false`. Pick the branch accordingly. The same `v` works for that branch.

**Key challenge**: Unfolding `tryAllPropRules` is a chain of `List.find?` on 8 rules. May need to unfold `applyPropRule` for each case. The match on `classicalApplyOne sf` needs to reduce after the case split.

**Suggested approach**: First case-split on `sf.sign` (2 cases: `.pos`, `.neg`), then case-split on `sf.formula` (5 cases: `.atom`, `.bot`, `.imp`, `.and`, `.or`). This gives 10 subcases. For each, `classicalApplyOne sf` should reduce to a specific `RuleResult`, and the match target becomes concrete.

**Key lemmas**:
- `BoolEvaluate_and`, `BoolEvaluate_or`, `BoolEvaluate_imp`, `BoolEvaluate_bot` (all `@[simp]`)
- `List.mem_append` for membership in extended branches
- `Bool.and_eq_true`, `Bool.or_eq_true` for Boolean reasoning
- `Branch.extendMany` unfolds to `sfs ++ b`

**Difficulty**: Moderate. 10 subcases but each is mechanical.

### S3: `classicalTableau_sound` (HARDEST in classical)

**Strategy**: This is the hardest proof because it requires reasoning about the fuel-based expansion loop `classicalExpandBranches`.

**Approach A (direct induction on fuel)**: Show by induction on fuel that if `classicalExpandBranches branches ... fuel = .closed` and at least one branch is satisfiable, we reach a contradiction. The inductive step uses S1 and S2.

**Approach B (contrapositive)**: Assume `¬ Tautology phi`. Then there exists `v` with `BoolEvaluate v phi = false`. Show the initial branch `[F(phi)]` is satisfiable via `v`. By S1, satisfiability is preserved at each expansion step. By S2, no satisfiable branch can close. Therefore the tableau cannot return `.closed`.

Approach B is cleaner but still requires induction on the expansion loop:

1. Unfold `classicalTableau phi` = `classicalExpandBranches [initialBranch] [[]] fuel`
2. Need an invariant: "if some branch in the list is satisfiable, the result is not `.closed`"
3. Prove by induction on `fuel`:
   - Base case (`fuel = 0`): If some branch is satisfiable, it's not closed (by S2), so `findSome?` finds it and returns `.openBranch`.
   - Inductive step (`fuel + 1`): The inner `processNext` loop processes each branch. If a branch is satisfiable and closed -> contradiction with S2. If satisfiable and has an applicable step -> by S1, at least one sub-branch is satisfiable. By IH, the recursive call to `classicalExpandBranches` cannot return `.closed`.

**Key challenge**: The `processNext` auxiliary function is defined via `let rec`, making induction awkward. May need a separate lemma about `processNext`.

**Alternative approach (simpler)**: Instead of directly inducting on the expansion loop, use the existing completeness theorem. Note that `classicalTableau_complete` is in the completeness file and also uses sorry. However, looking at `Bool.lean`, there is already a sorry-free `instDecidableTautology` using Boolean enumeration. The soundness theorem could potentially be proved differently:

If `classicalTableau phi = .closed`, we need `Tautology phi`. By `instDecidableTautology`, `Tautology phi` is decidable. If `Tautology phi` holds, done. If not, then `classicalTableau_complete phi` would give `classicalTableau phi = .closed` -- wait, this requires completeness which also has sorry.

The direct approach is necessary. The main structural challenge is proving a loop invariant for `classicalExpandBranches`.

**Difficulty**: High. Requires loop invariant induction over the fuel-based expansion.

### S5: `intClosed_unsatisfiable` (SIMPLE)

**Strategy**: Similar to S2 but simpler. The intuitionistic closure condition only checks for T(bot).

1. Unfold `isIntuitionisticallyClosed` -> checks `b.find? (sf.isPos && sf.formula == HasBot.bot)`.
2. If `some sf` is found, then `sf.sign = .pos` and `sf.formula = .bot`.
3. From `intBranchSatisfied val (fun _ => False) worldOf b`, at `sf`, the `.pos` case gives `IForces val (fun _ => False) (worldOf sf.label) .bot`.
4. But `IForces val (fun _ => False) w .bot = (fun _ => False) w = False`. Contradiction.

**Key lemmas**:
- `IForces_bot` (`@[simp]`)
- `List.any_eq_true` or direct analysis of `find?`

**Difficulty**: Low.

### S4: `intRule_preserves_sat` (MODERATE-HIGH)

**Strategy**: Case-split on `sf.sign` and `sf.formula`, then for each applicable rule show the extended branch is satisfied.

Cases from `intApplyRuleFull`:
1. `(.pos, .and phi psi)` -> linear: T(phi), T(psi). From `IForces val bf w (.and phi psi)` = `IForces ... phi ∧ IForces ... psi`. Both conjuncts give the result.
2. `(.neg, .and phi psi)` -> branching: F(phi) or F(psi). From `¬IForces ... (.and phi psi)` = `¬(IForces phi ∧ IForces psi)`. Push negation to get `¬IForces phi ∨ ¬IForces psi`. Pick the branch.
3. `(.pos, .or phi psi)` -> branching: T(phi) or T(psi). From `IForces ... (.or phi psi)` = `IForces phi ∨ IForces psi`. Pick the branch.
4. `(.neg, .or phi psi)` -> linear: F(phi), F(psi). From `¬IForces ... (.or phi psi)` = `¬(IForces phi ∨ IForces psi)`. Push negation to get both.
5. `(.neg, .imp phi psi)` -> world-creating: Adds T(phi) at w', F(psi) at w', plus propagation.
   From `¬IForces val bf w (.imp phi psi)` = `¬(∀ w', w ≤ w' → IForces phi w' → IForces psi w')`.
   Push negation: `∃ w', w ≤ w' ∧ IForces phi w' ∧ ¬IForces psi w'`.
   The new world `w'` witnesses both T(phi) and F(psi). The propagated T-formulas from world `w` persist by `iforces_persistence`.

   **Subtlety**: The `worldOf` function maps Nat labels to World elements. The new world label `nw` needs `worldOf nw` to be the witness `w'`. But `worldOf` is fixed in the hypothesis. This is a fundamental issue: the proof must show that *if there exists a model satisfying the old branch, then there exists a (possibly different) model satisfying the new branch*.

   Actually, looking at the statement more carefully: `worldOf` is universally quantified in the goal via the `∀ sf ∈ b` in `intBranchSatisfied`. The key insight is that the F(imp) rule creates a new world label `nw` and adds formulas at that label. The existing model's `worldOf nw` must map to some world that satisfies these formulas.

   The `hsat` hypothesis says the model satisfies all formulas on the old branch `b`. The F(phi -> psi) at label `l` tells us `¬IForces val bf (worldOf l) (.imp phi psi)`, which gives us a world `w'` with `worldOf l ≤ w'` where `phi` is forced and `psi` is not. We need `worldOf nw = w'`, but `worldOf` is fixed.

   **Resolution**: The lemma statement needs `worldOf` to be quantified *outside* or we need to construct a *new* `worldOf'` that maps `nw` to `w'` while agreeing with `worldOf` on existing labels. Looking at the lemma signature again:

   ```
   intBranchSatisfied val botForces worldOf (Branch.extendMany b newForms)
   ```

   This requires the *same* `worldOf` to work for the extended branch. This is problematic for world-creating rules because `worldOf nw` is already determined by the fixed function.

   **This means the lemma as stated may be too strong for the F(imp) case.** The proof needs to show: for the *same* `val`, `botForces`, and `worldOf`, the extended branch is satisfied. But the F(imp) rule creates a new world, and we need `worldOf nw` to be the specific witness world.

   **Possible resolutions**:
   a. The lemma should quantify over all possible `worldOf` extensions (needs re-statement)
   b. The proof should construct a new `worldOf'` and show satisfaction under it (needs existential in the conclusion about worldOf)
   c. The proof uses the fact that `worldOf nw` is *some* world, and shows that the model can be "adjusted" -- but val and botForces are fixed too

   This is a genuine difficulty. The current lemma statement may need revision for the F(imp) case. The resolution depends on how the main soundness theorem (S6) uses this lemma.

6. Everything else -> `.notApplicable`, goal becomes `True`.

**Difficulty**: Moderate for standard cases, potentially requires lemma re-statement for the F(imp) world-creating case.

### S6: `intuitionisticTableau_sound` (HARDEST in intuitionistic)

Same structural challenge as S3: requires loop invariant induction over `intExpandBranches`.

**Strategy**: Contrapositive. If `¬IValid phi`, there exists a Kripke model where phi fails at some world. The initial branch `[F(phi) at 0]` is satisfied by this model (with appropriate worldOf). By S4, each expansion preserves satisfiability. By S5, no satisfiable branch closes. Therefore the tableau cannot return `.closed`.

**Difficulty**: High. Same loop induction challenge as S3, compounded by world management.

### S7: `minimalTableau_sound` (HARD)

**Strategy**: Same as S6 but with `MValid` instead of `IValid` and `MinimalClosure` instead of `IntuitionisticClosure`.

For `MValid`, the `botForces` predicate is universally quantified (not fixed to `fun _ => False`). The minimal closure condition checks for T(p)/F(p) for atomic p at the same world. The unsatisfiability argument: if `T(atom p)` and `F(atom p)` at world w are both on the branch, then `IForces val bf (worldOf w) (.atom p) = val (worldOf w) p` must be both true and false.

**Note**: A helper lemma `minClosed_unsatisfiable` is needed (analogous to S2 and S5) but is not currently stated in the file. This would need to be added.

**Difficulty**: High. Requires adding the missing helper lemma plus the loop invariant.

### S8: `minimalTableau_complete` (COMPLETENESS -- possibly out of scope)

This is a completeness proof requiring countermodel construction from open branches, which is a separate direction from soundness. If it's out of scope for task 316, it should remain sorry.

## Recommended Implementation Order

1. **S2** (`classically_closed_unsatisfiable`) -- simplest, pure case analysis on closure conditions
2. **S5** (`intClosed_unsatisfiable`) -- analogous to S2, even simpler (only T(bot) case)
3. **S1** (`classicalRule_preserves_sat`) -- 10 subcases, each mechanical
4. **S4** (`intRule_preserves_sat`) -- similar to S1 but with worldOf complications for F(imp)
5. **S3** (`classicalTableau_sound`) -- requires loop invariant lemma
6. **S6** (`intuitionisticTableau_sound`) -- same loop challenge as S3 with worlds
7. **S7** (`minimalTableau_sound`) -- needs new helper lemma + loop invariant
8. **S8** (`minimalTableau_complete`) -- out of scope (completeness direction)

## Potential Blockers

### Blocker 1: World-Creating Rule Preservation (S4, F(imp) case)

The `intRule_preserves_sat` lemma as currently stated may be too strong: it requires the *same* `worldOf` function to work for the extended branch after a world-creating rule. The F(imp) rule creates a new world label `nw`, and the existing `worldOf nw` maps to some arbitrary world that may not be the witness needed.

**Resolution options**:
a. **Re-state the lemma** to return an existential: "there exist val', bf', worldOf' such that the extended branch is satisfied" -- but this changes the API
b. **Weaken the conclusion** to allow worldOf modification
c. **Observe that the main theorem (S6) doesn't use this lemma directly** in this form -- the contrapositive proof constructs the model from the assumption `¬IValid phi` and has control over `worldOf`

The recommended approach is to bypass S4 for the F(imp) case and instead fold the argument directly into S6, where the model construction gives us control over `worldOf`.

### Blocker 2: Loop Invariant for Expansion Functions (S3, S6, S7)

The `classicalExpandBranches` and `intExpandBranches` functions use `let rec` internal helpers (`processNext`, `go`) that complicate induction. Separate invariant lemmas about these helpers may be needed.

**Resolution**: Define the invariant as a separate lemma:
```
lemma expandBranches_preserves_sat (branches : List (Branch ...)) ... (fuel : Nat) :
    (∃ b ∈ branches, classicalBranchSatisfiable b) →
    classicalExpandBranches branches ... fuel ≠ .closed
```
Then prove by induction on `fuel`, with the inner loop handled by a nested induction on the branch list.

### Blocker 3: tryAllPropRules Reduction (S1)

`tryAllPropRules` is defined as `results.find? (·.isApplicable) |>.getD .notApplicable` where `results` is a list of 8 rule applications. After case-splitting on sign and formula, this should reduce, but the `find?` on a concrete list may require unfolding through all 8 elements.

**Resolution**: The `simp` lemma for `List.find?` on concrete lists, or `native_decide`/`decide` for the concrete `Option` checks. Alternatively, prove separate `@[simp]` lemmas like:
```
@[simp] lemma classicalApplyOne_pos_and (a b : Proposition Atom) :
    classicalApplyOne ⟨.pos, .and a b, ()⟩ = .linear [⟨.pos, a, ()⟩, ⟨.pos, b, ()⟩]
```

## Relevant API

### Core Lean/Mathlib Lemmas

| Lemma | Type | Use |
|-------|------|-----|
| `List.mem_append` | `a ∈ s ++ t ↔ a ∈ s ∨ a ∈ t` | Membership in extended branches |
| `List.any_eq_true` | `l.any p = true ↔ ∃ x ∈ l, p x = true` | Extracting witnesses from Bool predicates |
| `List.any_of_mem` | `a ∈ l → p a = true → l.any p = true` | Constructing Bool predicates from membership |
| `BoolEvaluate_bot` | `BoolEvaluate v .bot = false` | `@[simp]`, bot evaluates to false |
| `BoolEvaluate_and` | `BoolEvaluate v (.and a b) = (BoolEvaluate v a && BoolEvaluate v b)` | `@[simp]` |
| `BoolEvaluate_or` | `BoolEvaluate v (.or a b) = (BoolEvaluate v a \|\| BoolEvaluate v b)` | `@[simp]` |
| `BoolEvaluate_imp` | `BoolEvaluate v (.imp a b) = (!BoolEvaluate v a \|\| BoolEvaluate v b)` | `@[simp]` |
| `IForces_bot` | `IForces v bf w .bot = bf w` | `@[simp]` |
| `IForces_and` | `IForces v bf w (.and phi psi) = (IForces ... phi ∧ IForces ... psi)` | `@[simp]` |
| `IForces_or` | `IForces v bf w (.or phi psi) = (IForces ... phi ∨ IForces ... psi)` | `@[simp]` |
| `IForces_imp` | `IForces v bf w (.imp phi psi) = ∀ w', w ≤ w' → ...` | `@[simp]` |
| `iforces_persistence` | persistence under preorder | World-creating rule preservation |

### CSLib-Specific Definitions

| Definition | Location | Notes |
|-----------|----------|-------|
| `Branch.extendMany` | `Foundations/Logic/Tableau/Branch.lean` | `sfs ++ b` (prepend) |
| `isClassicallyClosed` | `Classical/Expansion.lean` | `ClassicalClosure` instance |
| `isIntuitionisticallyClosed` | `Intuitionistic/Expansion.lean` | `IntuitionisticClosure` instance |
| `isMinimallyClosed` | `Intuitionistic/Expansion.lean` | `MinimalClosure` instance |
| `classicalApplyOne` | `Classical/Expansion.lean` | `tryAllPropRules` with prop decomposition |
| `intApplyRuleFull` | `Intuitionistic/Rules.lean` | Direct pattern match on sign/formula |
| `intFImpRule` | `Intuitionistic/Rules.lean` | World-creating F(imp) rule |

## Tactic Survey

For S2 and S5 (closure unsatisfiability):
- `intro ⟨v, hv⟩` to destructure the existential
- `simp [isClassicallyClosed, ClosureCondition.isClosed]` to unfold closure
- `cases` on `Sign` and `Option` results
- `simp [BoolEvaluate]` or `simp [IForces]` for the contradiction

For S1 and S4 (rule preservation):
- `cases sf.sign <;> cases sf.formula` to split into subcases
- `simp [classicalApplyOne, tryAllPropRules, applyPropRule]` to reduce rule application
- `obtain ⟨v, hv⟩ := hsat` to extract the witness
- `exact ⟨v, fun sf' hsf' => ...⟩` to provide the same witness

For S3, S6, S7 (main theorems):
- Induction on `fuel` with a custom invariant
- May need `Nat.recOn` or `match` induction
- The inner `let rec` functions may need extraction to top-level for induction
