# Task 319: Minimal Tableau Soundness/Completeness -- Research Report

## 1. Current State of Minimal Tableau Code

### Existing file: `Cslib/Logics/Propositional/Tableau/Minimal/DecisionProcedure.lean` (135 lines)

The file contains:
- **`minBranchSatisfied`** (lines 66-73): Defines branch satisfiability for minimal logic. Definition is identical to `intBranchSatisfied` from the intuitionistic module -- both quantify over `∀ sf ∈ b` and check `IForces val botForces (worldOf sf.label) sf.formula` for positive/negative signs.
- **`minimalTableau_sound`** (lines 86-88): Sorry'd. Statement: `minimalTableau φ = .closed → MValid φ`.
- **`minimalTableau_complete`** (lines 103-105): Sorry'd. Statement: `MValid φ → minimalTableau φ = .closed`.
- **`minimalTableau_decides`** (lines 111-113): Combines sound + complete. Not sorry'd itself but depends on sorry'd theorems.
- **`instDecidableMValid`** (lines 119-125): `Decidable (MValid φ)` via tableau. Structurally sorry-free.
- **`instDecidableDerivableMinPropAxiom`** (lines 129-131): Uses `min_soundness_completeness` from `MinStrongCompleteness.lean`.

### Shared infrastructure (already exists, no changes needed):
- `Cslib/Logics/Propositional/Tableau/Intuitionistic/Rules.lean` -- `intApplyRuleFull`, `intFImpRule`, `propagatePersistence`, `posFormulasAt`, etc.
- `Cslib/Logics/Propositional/Tableau/Intuitionistic/Expansion.lean` -- `intExpandBranches`, `minimalTableau`, `isMinimallyClosed`, `isIntuitionisticallyClosed`, `IntTableauResult`.
- `Cslib/Logics/Propositional/Semantics/Kripke.lean` -- `IForces`, `IValid`, `MValid`, `iforces_persistence`, `KripkeModel`.

## 2. Analysis of Classical Tableau Proof Structure

### Classical Soundness (`Classical/Soundness.lean`, ~653 lines)
1. **`branchConsistent`**: Boolean valuation agrees with signed branch.
2. **`classicalBranchSatisfiable`**: Existential over `BoolValuation`.
3. **Simp lemmas** for `classicalApplyOne` (lines 72-127): Reduction lemmas for each rule case.
4. **`classicalRule_preserves_sat`** (~260 lines): Case analysis on all formula/sign combinations. For each rule, shows that if the branch is satisfiable, at least one result branch is satisfiable.
5. **`classically_closed_unsatisfiable`**: T(bot) or T(phi)/F(phi) forces contradiction.
6. **`classicalExpandBranches_closed_unsat`** (~80 lines): Induction on fuel with inner induction on pending list. Uses `classicalStepBranch_preserves_sat` helper.
7. **`classicalTableau_sound`**: Contrapositive -- initial branch `[F(phi)]` is satisfiable, expansion preserves satisfiability, so if tableau closes, contradiction.

### Classical Completeness (`Classical/Completeness.lean`, ~518 lines)
1. **`extractValuation`**: `v p = b.any (fun sf => sf.sign == .pos && sf.formula == .atom p)`.
2. **`classicalHintikkaSet`**: Branch is open AND every formula's rule outputs are present.
3. **`classicalTruthLemma`** (~310 lines): By induction on formula. For each sign/formula case, the Hintikka condition guarantees rule outputs are on branch, and IH gives the semantic consequence.
4. **`classicalExpandBranches_hintikka`**: Sorry'd -- proves open branch is Hintikka set.
5. **`classicalOpenBranch_countermodel`**: Applies truth lemma to show F(phi) on branch means phi is falsified.
6. **`classicalTableau_complete`**: Contrapositive via countermodel.

## 3. Analysis of Intuitionistic Tableau Proof Structure

### Intuitionistic Soundness (`Intuitionistic/Soundness.lean`, ~365 lines)
1. **`intBranchSatisfied`** (lines 55-62): Identical definition to `minBranchSatisfied`.
2. **`intRule_preserves_sat`** (~165 lines): Case analysis on sign/formula. Key case: F(imp) world-creating rule uses `Function.update worldOf nw w'` where `w'` is the witness world for `¬ IForces_w (phi -> psi)`. Returns existential `worldOf'` for linear results.
3. **`intClosed_unsatisfiable`**: T(bot) on branch contradicts `botForces = fun _ => False`.
4. **`intExpandBranches_closed_unsat`** (sorry'd): **CRITICAL -- already parameterized by `closurePred` and `closed_unsat`**. Takes arbitrary closure predicate.
5. **`intuitionisticTableau_sound`**: Instantiates `intExpandBranches_closed_unsat` with `isIntuitionisticallyClosed` and `intClosed_unsatisfiable`.

### Intuitionistic Completeness (`Intuitionistic/Completeness.lean`, ~117 lines)
1. **`intExtractValuation`**: `v w p = b.any (... sign==.pos && formula==.atom p && label==w)`.
2. **`intBotForces`**: `fun _ => False`.
3. **`intTruthLemma`** (sorry'd): By formula induction, extracted model satisfies branch.
4. **`intuitionisticOpenBranch_countermodel`** (sorry'd): Applies truth lemma.
5. **`intuitionisticTableau_complete`** (sorry'd): Contrapositive.

## 4. Reusability Analysis: Intuitionistic to Minimal

### Directly Reusable (no modification needed)

| Lemma | Why reusable |
|-------|-------------|
| `intRule_preserves_sat` | Already parameterized by arbitrary `botForces`. Works for both intuitionistic and minimal models. |
| `intExpandBranches_closed_unsat` | Already parameterized by `closurePred` and `closed_unsat`. Minimal soundness only needs to instantiate differently. |
| `intApplyRuleFull` | Same rules for both logics. |
| `intExpandBranches` | Same expansion loop, already takes `closurePred` as parameter. |
| `iforces_persistence` | Works for any upward-closed `botForces`. |
| `IForces` | Already parameterized by `botForces`. |
| `minimalTableau` | Already defined in Expansion.lean. |

### Need New Versions (minimal-specific)

| Component | Intuitionistic version | Minimal adaptation needed |
|-----------|----------------------|--------------------------|
| Closure unsatisfiability | `intClosed_unsatisfiable`: T(bot) implies `False` since `botForces = fun _ => False` | `minClosed_unsatisfiable`: T(p) and F(p) at same world for atomic p implies `val w p` and `¬ val w p` -- contradiction regardless of `botForces` |
| Countermodel valuation | `intExtractValuation`: `v w p = T(atom p) at w on b` | Same definition works |
| Bot forcing predicate | `intBotForces = fun _ => False` | `minBotForces w = T(bot) at w on b` (upward-closed by persistence) |
| Truth lemma | `intTruthLemma`: T(bot) cannot appear (branch is open by intuitionistic closure) | `minTruthLemma`: T(bot) CAN appear (minimal closure does not check for T(bot)). Bot case: `IForces v minBotForces w .bot = minBotForces w = (T(bot) at w on b)`, which is exactly the branch content. |
| Countermodel construction | Implicit in completeness | Same world structure (Nat with ≤), same valuation, different `botForces` |

### Key insight: `minBranchSatisfied` = `intBranchSatisfied`

Both definitions are identical (`∀ sf ∈ b, ...`). The difference is only in how `botForces` is instantiated:
- Intuitionistic: `botForces = fun _ => False`
- Minimal: `botForces` is arbitrary (for soundness) or `botForces w = T(bot) at w on b` (for completeness countermodel)

This means all lemmas about `intBranchSatisfied` apply to `minBranchSatisfied` with zero adaptation.

## 5. Key Differences for Minimal Logic

### 5.1 Closure Predicate

**Intuitionistic** (`isIntuitionisticallyClosed`): Branch closes when T(bot) appears at any label.
```
findClosure b := match b.find? (fun sf => sf.isPos && sf.formula == bot) with
  | some sf => some (.botPos sf.label)
  | none => none
```

**Minimal** (`isMinimallyClosed`): Branch closes when T(p) and F(p) appear at the same label for atomic p.
```
findClosure b := b.findSome? fun sf =>
  if sf.isPos && IsAtomic.isAtom sf.formula then
    if b.any (fun sf' => sf'.sign == .neg && sf'.formula == sf.formula && sf'.label == sf.label)
    then some (.atomContradiction sf.formula sf.label)
    else none
  else none
```

### 5.2 Soundness: `minClosed_unsatisfiable`

For minimal closure, the unsatisfiability argument is:
- Branch has T(p) at world w and F(p) at world w, where p is atomic.
- T(p) at w means `IForces val botForces (worldOf w) (.atom p) = val (worldOf w) p` holds.
- F(p) at w means `¬ IForces val botForces (worldOf w) (.atom p) = ¬ val (worldOf w) p` holds.
- These contradict each other regardless of what `botForces` is.

This proof is simpler than the intuitionistic case (which required `botForces = fun _ => False` specifically).

### 5.3 Completeness: Countermodel `botForces`

For the intuitionistic countermodel, `botForces = fun _ => False` (trivially upward-closed).

For the minimal countermodel from an open branch b:
- `minBotForces w = b.any (fun sf => sf.sign == .pos && sf.formula == .bot && sf.label == w)`
- Upward-closure: If T(bot) at w on b, then by persistence propagation, T(bot) at w' for w' >= w should also be on b. This needs to follow from the saturation/persistence fixpoint property of the open branch.

### 5.4 Truth Lemma: Bot Case

**Intuitionistic**: T(bot) on branch implies branch is closed (by `isIntuitionisticallyClosed`). But branch is open (hypothesis), contradiction. So T(bot) case is vacuously true.

**Minimal**: T(bot) on branch does NOT imply closure. The bot case of the truth lemma is:
- Forward: `T(bot) at w on b → IForces v minBotForces w .bot = minBotForces w = (T(bot) at w on b)`. This is just identity (Iff.rfl essentially).
- Backward: `F(bot) at w on b → ¬ minBotForces w = ¬ (T(bot) at w on b)`. This holds because if both T(bot) and F(bot) were at w, then since `.bot` is not atomic, minimal closure would NOT fire. Wait -- actually F(bot) is not useful since there's no rule for it. Let me reconsider.

Actually, F(bot) at w on the branch means `¬ IForces v minBotForces w .bot = ¬ minBotForces w`. So we need `¬ (T(bot) at w on b)`. If F(bot) at w AND T(bot) at w were both on b, then... `.bot` is NOT atomic (`isAtom .bot = false`), so minimal closure does NOT fire. This is a potential issue.

**Resolution**: F(bot) never appears on the branch in practice. The tableau starts with F(phi) at world 0. The only rule that produces F-signed formulas is:
- F(phi and psi) -> F(phi) or F(psi)
- F(phi or psi) -> F(phi) and F(psi)
- F(phi -> psi) -> T(phi) at new world, F(psi) at new world

None of these produce F(bot) directly. F(bot) could only appear if the initial formula decomposes to produce it (e.g., F(bot -> bot) produces T(bot) and F(bot) at a new world). So F(bot) CAN appear.

If F(bot) at w and T(bot) at w coexist, minimal closure does not fire. The truth lemma needs:
- `F(bot) at w → ¬ minBotForces w` i.e., `F(bot) at w → ¬ (T(bot) at w on b)`.
- Contrapositive: if T(bot) at w on b, then F(bot) at w should not be on b.

This is NOT guaranteed by minimal closure. However, it IS guaranteed by the Hintikka/saturation property. If both T(bot) and F(bot) are at the same world w, then the persistence rule for T(bot -> psi) combined with T(bot) would fire. But bot is not an implication.

Actually, let me reconsider the structure. The truth lemma for minimal completeness should work as follows:

For the bot case, the key insight is that `minBotForces w` is defined as `T(bot) at w on b` (a decidable `Bool` lifted to `Prop`). Then:
- T(bot) at w → `IForces v minBotForces w .bot = minBotForces w = True` (by definition of `minBotForces`). Holds trivially.
- F(bot) at w → `¬ IForces v minBotForces w .bot = ¬ minBotForces w = ¬ (T(bot) at w on b)`.

The second direction requires showing that T(bot) and F(bot) cannot coexist at the same world on an open saturated branch. Since `.bot` is not atomic, minimal closure won't fire. So we need a separate argument.

**Key observation**: F(bot) has no rule that applies to it (`intApplyRuleFull` returns `.notApplicable` for `(.neg, .bot, _)`). So F(bot) is never expanded. But is it consistent to have both T(bot) and F(bot) at the same world? In terms of the branch being consistent as a Kripke interpretation, no -- it would mean `botForces w` and `¬ botForces w`. The truth lemma proof must show this cannot happen on a saturated branch.

Wait -- can both T(bot) and F(bot) appear at the same world on a minimal open branch? Let's trace:
1. F(bot -> bot) at w -> creates new world w' with T(bot) at w' and F(bot) at w'.
2. Both are at w'. Minimal closure checks for atomic contradictions only -- `.bot` is not atomic. So the branch stays open.
3. The branch has T(bot) and F(bot) at w'. This is a genuine consistency issue for the countermodel.

**This is the fundamental challenge of minimal completeness**: The naive countermodel construction with `minBotForces w = T(bot) at w on b` fails if both T(bot) and F(bot) coexist.

**Resolution approaches**:
1. **Show it cannot happen**: If F(bot -> bot) is never generated. But `bot -> bot` is `True` in minimal logic, so F(True) should always close somehow... Actually `bot -> bot` is provable in minimal logic (`fun x => x`), so it's MValid. The tableau on `bot -> bot` would close. But it could appear as a subformula.
2. **Strengthen closure**: Define a modified closure that also closes on T(bot)/F(bot) pairs. But this changes the decision procedure.
3. **Use the Hintikka property differently**: Show that the saturation ensures consistency without relying on closure.

Actually, re-examining: the F(bot -> bot) case at world w creates T(bot) at w' and F(bot) at w'. But this is the world-creating rule for F(phi -> psi). The persistence propagation also fires, copying all T-formulas from w to w'. Now, there's no rule for F(bot) (it's `.notApplicable`), and T(bot) is also `.notApplicable` (it's not an implication, conjunction, or disjunction). So both sit on the branch.

For the truth lemma to work, we need `¬ minBotForces w'` from `F(bot) at w'`. But `minBotForces w' = T(bot) at w'`, and T(bot) IS at w'. So the truth lemma fails.

**This means the minimal tableau with `isMinimallyClosed` is NOT complete for minimal logic as currently defined** -- at least not with the naive countermodel construction.

**Correct approach**: The minimal closure should ALSO close on T(p)/F(p) pairs where p is ANY formula, not just atomic p -- OR the countermodel construction needs to be more sophisticated.

Wait, let me re-read the task description more carefully: "closure is on complementary atoms only". And the `MinimalClosure` instance indeed only checks atomic formulas. But this is correct for minimal logic tableaux -- the Fitting reference confirms that minimal tableaux close only on atomic contradictions (and classical additionally on T(bot) and all contradictions).

The fix is in the truth lemma argument. Looking at the literature (Fitting 1983, Chapter 4), the truth lemma for minimal logic works because:
- The saturated open branch defines a Hintikka set.
- The Hintikka property ensures: if F(phi -> psi) at w, then there exists w' >= w with T(phi) at w' and F(psi) at w'.
- For the bot case: T(bot) at w gives `minBotForces w` by definition. F(bot) at w gives... F(bot) is NOT a compound formula, so no rule fires. It sits on the branch. The truth lemma says we need `¬ minBotForces w`. But `minBotForces w = T(bot) at w`.

The resolution is that **the countermodel should use the canonical Kripke model approach** (as in MinStrongCompleteness.lean) rather than the direct branch extraction. Alternatively, the definition of `minBotForces` needs to be more careful.

**Actually, the correct definition**: In Fitting's treatment, the countermodel for minimal tableaux uses:
- `botForces w = T(bot) at w on b`
- The truth lemma works because: if both T(bot) and F(bot) are at w, then T(bot) and F(bot) coexist. Since `.bot` is not atomic, this is allowed by minimal closure. But the truth lemma for F(bot) at w requires `¬ botForces w`. This seems contradictory.

Let me reconsider. The issue is specific to `F(bot)`. In the Fitting treatment, I believe the key is that F(bot) CAN coexist with T(bot), and the truth lemma handles this by not claiming F(bot) implies `¬ botForces w` -- instead, the truth lemma only needs to handle formulas that actually appear on the branch in a way that's consistent.

**Alternative resolution**: The truth lemma for minimal logic should be: for formulas phi that appear POSITIVELY on the branch, `IForces v minBotForces w phi`, and for formulas that appear NEGATIVELY, `¬ IForces v minBotForces w phi`. The issue only arises when BOTH T(bot) and F(bot) appear. In that case, we cannot simultaneously have `botForces w` and `¬ botForces w`.

This means the countermodel construction must handle this case differently. The standard approach in the literature uses:
1. `botForces w = T(bot) at w on b AND F(bot) is NOT at w on b`
2. OR `botForces w = {w | T(bot) at w on b} ∩ {w | F(bot) NOT at w on b}`

But this breaks upward-closure unless persistence guarantees F(bot) propagates upward too. F-signed formulas do NOT propagate upward in intuitionistic/minimal tableaux (only T-formulas do).

**Simplest correct approach**: Since F(bot) has no applicable rule and cannot generate new formulas, and since `.bot` is not atomic so no closure fires, the branches where T(bot) and F(bot) coexist at the same world are NOT closed by minimal closure. The tableau would return such a branch as open. But the formula `bot -> bot` IS minimally valid, so `minimalTableau (bot -> bot)` should return `.closed`. Let's trace:
- Start: F(bot -> bot) at w=0.
- Rule: F(imp) world-creating: creates w=1 with T(bot) at 1, F(bot) at 1.
- Persistence: copies all T-formulas from w=0 to w=1 (none at w=0).
- isMinimallyClosed: checks for T(p)/F(p) at same world for atomic p. `.bot` is not atomic. Not closed.
- No more rules to apply (T(bot) and F(bot) are not applicable).
- Branch is open and saturated -> returns openBranch.

But `bot -> bot` IS minimally valid (the identity function). So the tableau returns the wrong answer.

**This is a bug in the current `isMinimallyClosed` definition, or the decision procedure is incomplete with this closure.**

Wait -- let me re-read the MinimalClosure more carefully. Looking at line 124-134 of ClosureCondition.lean:

```lean
instance [BEq F] [BEq L] [IsAtomic F] : ClosureCondition F L where
  findClosure b :=
    b.findSome? fun sf =>
      if sf.isPos && IsAtomic.isAtom sf.formula then
        if b.any fun sf' =>
          sf'.sign == .neg && sf'.formula == sf.formula && sf'.label == sf.label
        then some (.atomContradiction sf.formula sf.label)
        else none
      else
        none
```

This closes on T(p)/F(p) for atomic p ONLY. Since `.bot` is not atomic, T(bot)/F(bot) does not close. This means `minimalTableau (bot -> bot)` returns `openBranch` even though `bot -> bot` is minimally valid.

**However**, looking at this from the logic perspective: `bot -> bot` is indeed valid in minimal logic (the identity function works). So either:
1. The closure condition needs to include T(bot)/F(bot) pairs (i.e., also close on non-atomic contradictions), OR
2. There's something wrong with my analysis.

Let me check: is minimal closure supposed to close on ALL complementary pairs T(phi)/F(phi), not just atomic ones? Looking at Fitting 1983:

In Fitting's treatment, the minimal tableau closes a branch when it contains a SIGNED ATOMIC formula and its complement. The key: in propositional logic, atoms are the only formulas that are "elementary" for closure. But `.bot` is not a standard propositional atom.

Actually, in Fitting's formulation, bot is not part of the language for minimal logic -- negation is treated as a primitive connective (not as `phi -> bot`). In CSLib, negation IS `phi -> bot`, and `.bot` is a separate constructor. This creates the discrepancy.

**The correct fix for CSLib**: The minimal closure should close on T(phi)/F(phi) for ANY formula phi at the same world. This makes it equivalent to classical closure minus the T(bot) rule. Actually, re-reading the task description: "MinimalClosure T(p)/F(p) contradiction is unsatisfiable since val w p <-> not val w p" -- but if closure is only on atoms, then the countermodel MUST handle the bot case differently.

**Alternatively**, looking at the task description again: "closure is on complementary atoms only, and botForces is unconstrained" -- this suggests the task description intends atom-only closure. But then the truth lemma needs a different approach for bot.

Let me reconsider the truth lemma. If both T(bot) and F(bot) at world w exist on the branch, then the countermodel needs `IForces v bf w .bot` (from T(bot)) and `¬ IForces v bf w .bot` (from F(bot)). These are contradictory regardless of bf. So such a branch IS semantically inconsistent, even though it's not caught by minimal closure.

This means the COMPLETENESS proof would need to show that the returned open branch never has both T(bot) and F(bot) at the same world -- even though the closure predicate doesn't check for it. This would follow from showing that the tableau's expansion always produces branches where non-atomic contradictions are impossible, perhaps because the only way to get both T(phi) and F(phi) is through rules that also produce atomic contradictions.

**Actually, the real issue is simpler**: The branch with T(bot) at w=1 and F(bot) at w=1 DOES have a semantic contradiction. The completeness proof by contrapositive says: if the tableau returns openBranch, then the formula is not MValid. So we need to construct a countermodel from the open branch. If the branch has T(bot) and F(bot) at the same world, we can't build a consistent countermodel, meaning we can't prove ¬MValid, meaning the contrapositive doesn't work.

BUT: the formula IS MValid, so the tableau should return .closed. If it returns openBranch, the decision procedure is wrong. This means the current `isMinimallyClosed` definition may be TOO WEAK for correctness. The decision procedure `minimalTableau` may not correctly decide MValid with the current closure.

**CRITICAL FINDING**: The task description says "no separate Rules.lean or Expansion.lean is needed" and the expansion reuses `intExpandBranches` with `isMinimallyClosed`. But `isMinimallyClosed` may be insufficient. The completeness proof needs to address this.

Let me think about what the correct minimal closure should be. Standard references:
- Minimal logic tableau (Fitting): negation is primitive, no bot in language.
- CSLib encoding: negation is `phi -> bot`, bot is a constructor.

In CSLib's encoding, the correct minimal closure should close on:
1. T(p)/F(p) for atomic p at the same world (same as current), AND
2. T(bot)/F(bot) at the same world (needed because bot is now in the language).

Wait, but actually T(bot)/F(bot) at the same world is just a specific case of complementary pairs for non-atomic formulas. If we close on ALL complementary pairs (not just atomic), we get classical closure minus the T(bot) rule.

**Let me check**: Does classical closure = T(bot) OR any T(phi)/F(phi)? Yes, from the code:
```
ClassicalClosure: T(bot) at any label, OR T(phi)/F(phi) at same label
IntuitionisticClosure: T(bot) at any label only
MinimalClosure: T(p)/F(p) for atomic p at same label
```

For minimal logic, the correct closure should be: T(phi)/F(phi) for ANY formula phi at the same label (but NOT T(bot) alone). This is "classical minus T(bot)". But the current MinimalClosure is weaker -- it only checks atoms.

**HOWEVER**: For the SOUNDNESS proof, the current atom-only closure is fine because atom contradictions ARE unsatisfiable. The issue is only with COMPLETENESS -- if the closure is too weak, the tableau may return openBranch for valid formulas.

**My recommendation**: The implementation plan should either:
1. **Fix `isMinimallyClosed`** to close on ALL complementary T(phi)/F(phi) pairs (not just atomic). This is the cleanest fix.
2. **Prove that non-atomic contradictions cannot arise** on open saturated branches -- which seems false given the `bot -> bot` counterexample.

Actually wait, let me re-examine the `bot -> bot` example more carefully. The expansion loop also applies persistence:

1. Start: F(bot -> bot) at w=0, nextWorld=1.
2. Rule for F(imp bot bot) at w=0: creates w=1 with T(bot) at 1, F(bot) at 1. Also propagates T-formulas from w=0 to w=1 (none).
3. Persistence fixpoint: apply T(imp) rules. There are no T(imp) formulas on the branch. Fixpoint reached.
4. isMinimallyClosed: T(bot) is not atomic, F(bot) is not atomic. Not closed.
5. No more unexpanded formulas. Branch is saturated and open.

So yes, `minimalTableau (bot -> bot)` returns `openBranch` with the current implementation. This IS a bug since `bot -> bot` is minimally valid.

**RECOMMENDATION**: Strengthen `isMinimallyClosed` to close on ALL complementary pairs T(phi)/F(phi) at the same world. This makes it equivalent to `hasContradiction` from Branch.lean (without the T(bot) clause). The soundness proof is then straightforward (any complementary pair is unsatisfiable), and the completeness proof for the countermodel works because the open branch has no complementary pairs at all.

This change is NECESSARY for correctness and should be part of the implementation plan.

## 6. Concrete Proof Strategy

### Phase 1: Fix `isMinimallyClosed` (in Expansion.lean)

Change from atom-only contradictions to all complementary pairs:
```lean
def isMinimallyClosed (b : IBranch Atom) : Bool :=
  b.hasContradiction  -- T(phi)/F(phi) at same label, for any phi
```

Or create a new `MinimalContradictionClosure` instance:
```lean
namespace MinimalContradictionClosure
instance [BEq F] [BEq L] : ClosureCondition F L where
  findClosure b :=
    match b.findContradiction with
    | some (phi, l) => some (.contradiction phi l)
    | none => none
end MinimalContradictionClosure
```

The key distinction from classical: T(bot) alone does NOT close. Only complementary pairs close.

### Phase 2: Minimal/Soundness.lean

**Target theorems**:

1. **`minClosed_unsatisfiable`**: If `isMinimallyClosed b = true`, then the branch is unsatisfiable in any Kripke model.
   - Proof: Extract T(phi) at w and F(phi) at w from the complementary pair. By `intBranchSatisfied`, get `IForces v bf (worldOf w) phi` and `¬ IForces v bf (worldOf w) phi`. Contradiction.
   - This is SIMPLER than both the classical and intuitionistic cases.
   - Works for any `botForces` (no constraint needed).

2. **`minimalTableau_sound`**: If `minimalTableau phi = .closed`, then `MValid phi`.
   - Proof: Instantiate `intExpandBranches_closed_unsat` with:
     - `botForces` = arbitrary (from MValid quantifier)
     - `closurePred` = `isMinimallyClosed`
     - `closed_unsat` = `minClosed_unsatisfiable`
   - Structure mirrors `intuitionisticTableau_sound` exactly.

**Dependencies**: Imports `Intuitionistic.Soundness` (for `intRule_preserves_sat`, `intExpandBranches_closed_unsat`, `intBranchSatisfied`).

**Estimated size**: ~80-120 lines.

### Phase 3: Minimal/Completeness.lean

**Target definitions and theorems**:

1. **`minExtractValuation`**: Same as `intExtractValuation` -- `v w p = T(atom p) at w on b`.

2. **`minBotForces`**: `w ↦ T(bot) at w on b` -- upward-closed by persistence.

3. **`minHintikkaSet`**: Branch is open AND every formula's intuitionistic rule outputs are on the branch. Same structure as `classicalHintikkaSet` but using `intApplyRuleFull`.

4. **`minTruthLemma`**: By induction on formula.
   - **atom p**: Same as intuitionistic.
   - **bot**: T(bot) at w → `minBotForces w` = `T(bot) at w on b` = True by definition. F(bot) at w → `¬ minBotForces w` → by openness (no T(phi)/F(phi) contradiction for any phi, including bot), T(bot) is not at w.
   - **imp, and, or**: Same structure as intuitionistic, using saturation.

5. **`minBotForces_upward_closed`**: If T(bot) at w on b and w <= w', then T(bot) at w' on b. Follows from persistence propagation in the saturated branch.

6. **`minExtractValuation_upward_closed`**: Same argument as intuitionistic.

7. **`minOpenBranch_countermodel`**: From open saturated branch, construct countermodel using `minExtractValuation` and `minBotForces`. Truth lemma shows F(phi) at 0 means `¬ IForces ... phi`.

8. **`minimalTableau_complete`**: Contrapositive via countermodel.

**Dependencies**: Imports `Minimal.Soundness`, `Intuitionistic.Expansion`.

**Estimated size**: ~200-300 lines. The truth lemma is the largest component, with induction on formula structure and case analysis on sign.

### Phase 4: Refactor DecisionProcedure.lean

- Remove `minBranchSatisfied` (now in Soundness.lean or shared).
- Remove sorry'd `minimalTableau_sound` and `minimalTableau_complete` (now proved in Soundness/Completeness).
- Keep `minimalTableau_decides`, `instDecidableMValid`, `instDecidableDerivableMinPropAxiom`.
- Update imports to include new modules.

**Estimated size**: ~45 lines (reduced from 135).

### Phase 5: Update barrel imports

- Update `Cslib/Logics/Propositional/Tableau/Minimal.lean` to import Soundness and Completeness.
- Run `lake exe mk_all --module`.

## 7. Dependencies and Import Structure

```
Intuitionistic/Rules.lean
    ↓
Intuitionistic/Expansion.lean   (defines minimalTableau, isMinimallyClosed)
    ↓
Intuitionistic/Soundness.lean   (defines intRule_preserves_sat, intExpandBranches_closed_unsat)
    ↓
Minimal/Soundness.lean [NEW]    (defines minClosed_unsatisfiable, proves minimalTableau_sound)
    ↓
Minimal/Completeness.lean [NEW] (defines countermodel, truth lemma, proves minimalTableau_complete)
    ↓
Minimal/DecisionProcedure.lean  [REFACTORED] (keeps Decidable instances only)
```

Plus:
- `Semantics/Kripke.lean` (IForces, MValid, iforces_persistence)
- `Metalogic/MinStrongCompleteness.lean` (min_soundness_completeness, for DecisionProcedure)

## 8. Risk Assessment

### Blocking risk: `intExpandBranches_closed_unsat` is sorry'd

The intuitionistic loop invariant lemma `intExpandBranches_closed_unsat` is sorry'd in `Intuitionistic/Soundness.lean`. The minimal soundness proof depends on it. Options:
1. **Accept sorry**: The minimal soundness proof will have the same sorry as intuitionistic. Both can be filled independently.
2. **Prove it first**: This is a substantial effort (the classical version is ~80 lines with intricate induction). Not required for the current task structure.

**Recommendation**: Accept the sorry dependency. Document it. The minimal soundness module will be structurally correct and will become sorry-free when the intuitionistic loop invariant is proved.

### Closure fix risk

The proposed change to `isMinimallyClosed` is necessary for correctness but touches shared code in `Expansion.lean`. The change should be backward-compatible since:
- `isMinimallyClosed` is only used by `minimalTableau` (in Expansion.lean).
- Strengthening closure (more branches close) cannot break soundness (fewer open branches).
- It may affect the fuel bound (more closures = faster termination).

### Sorry inventory

After implementation, expected sorries:
- `intExpandBranches_closed_unsat` (inherited from intuitionistic, needed by soundness)
- Possibly `minTruthLemma` induction cases (if time-constrained)
- `classicalExpandBranches_hintikka` (pre-existing in classical, not touched)

## 9. Empirical Verification of Closure Fix

The closure bug was verified empirically with `lean_run_code`. Key test results:

### Bug demonstration (current `isMinimallyClosed` -- atom-only):
| Formula | Expected | Actual | Correct? |
|---------|----------|--------|----------|
| `bot -> bot` | closed (MValid) | open | **BUG** |
| `p -> p` | closed (MValid) | closed | Yes |

### Fix verification (`hasContradiction` -- all complementary pairs):
| Formula | Expected | Result | Correct? |
|---------|----------|--------|----------|
| `bot -> bot` | closed (MValid) | closed | Yes |
| `p -> p` | closed (MValid) | closed | Yes |
| `p ∨ ¬p` (excluded middle) | open (not MValid) | open | Yes |
| `¬¬p → p` (DNE) | open (not MValid) | open | Yes |
| `⊥ → p` (ex falso) | open (not MValid) | open | Yes |
| Peirce's law | open (not MValid) | open | Yes |
| Modus ponens scheme | closed (MValid) | closed | Yes |
| Weakening `p → q → p` | closed (MValid) | closed | Yes |
| Conj intro `p → q → p ∧ q` | closed (MValid) | closed | Yes |
| Disj intro `p → p ∨ q` | closed (MValid) | closed | Yes |

All 10 test cases pass with the corrected closure. The fix is:
```lean
def isMinimallyClosed (b : IBranch Atom) : Bool :=
  Branch.hasContradiction b
```

This replaces the current atom-only `MinimalClosure` instance with full complementary-pair checking (same as classical minus the T(bot) standalone rule).
