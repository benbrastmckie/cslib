# Research Report: Task 317 -- Propositional Tableau Completeness

- **Task**: 317 -- Fill sorry instances in propositional tableau completeness proofs
- **Started**: TBD
- **Completed**: TBD
- **Effort**: TBD
- **Dependencies**: TBD
- **Sources/Inputs**: TBD
- **Artifacts**: TBD
- **Standards**: TBD
- **Date**: 2026-06-24
- **Type**: cslib research
- **Session**: sess_1750723200_orchestrate_batch_317
- **Sources**:
  - `Cslib/Logics/Propositional/Tableau/Classical/Completeness.lean`
  - `Cslib/Logics/Propositional/Tableau/Intuitionistic/Completeness.lean`
  - `Cslib/Logics/Propositional/Tableau/Minimal/DecisionProcedure.lean`
  - `Cslib/Logics/Propositional/Tableau/Classical/Expansion.lean`
  - `Cslib/Logics/Propositional/Tableau/Intuitionistic/Expansion.lean`
  - `Cslib/Logics/Propositional/Tableau/Classical/Soundness.lean`
  - `Cslib/Logics/Propositional/Tableau/Intuitionistic/Soundness.lean`
  - `Cslib/Logics/Propositional/Semantics/Bool.lean`
  - `Cslib/Logics/Propositional/Semantics/Kripke.lean`

## Executive Summary

Task 317 requires filling 8 sorry instances across 3 files to prove completeness of
propositional tableau systems for classical, intuitionistic, and minimal logic. The core
technique throughout is the Hintikka-set argument: a saturated open branch satisfies
conditions from which a countermodel is extracted, showing the initial formula is not valid.

The 8 sorry sites decompose into three logical groups:
1. **Truth lemmas** (3 sorries): Induction on formula structure showing the extracted
   valuation/model matches the signed formulas on the branch.
2. **Countermodel extraction** (3 sorries): Using the truth lemma to show an open branch
   yields a model refuting the formula.
3. **Main completeness theorems** (2 sorries): Contrapositive argument connecting the
   tableau result to validity.

The classical case (3 sorries) is self-contained and straightforward. The intuitionistic
case (3 sorries) has a dependency on task 316's resolution of Blocker B2 (the `worldOf`
mismatch in the F(imp) soundness case). The minimal case (2 sorries, but only 1 is in
scope for completeness) adapts the intuitionistic proof with `botForces` changed.

## Sorry Inventory

| ID | File | Line | Declaration | Goal |
|----|------|------|-------------|------|
| C1 | Classical/Completeness.lean | 79 | `classicalTruthLemma` | Induction on formula: `extractValuation b` satisfies every T(phi) and falsifies every F(phi) on branch `b` |
| C2 | Classical/Completeness.lean | 88 | `classicalOpenBranch_countermodel` | Open branch from `classicalTableau` yields `BoolEvaluate (extractValuation b) phi = false` |
| C3 | Classical/Completeness.lean | 102 | `classicalTableau_complete` | `Tautology phi -> classicalTableau phi = .closed` |
| I1 | Intuitionistic/Completeness.lean | 89 | `intTruthLemma` | Induction on formula: `intExtractValuation b` satisfies forcing relation at each world |
| I2 | Intuitionistic/Completeness.lean | 98 | `intuitionisticOpenBranch_countermodel` | Open branch yields `not IForces (intExtractValuation b) intBotForces 0 phi` |
| I3 | Intuitionistic/Completeness.lean | 112 | `intuitionisticTableau_complete` | `IValid phi -> intuitionisticTableau phi = .closed` |
| M1 | Minimal/DecisionProcedure.lean | 88 | `minimalTableau_sound` | `minimalTableau phi = .closed -> MValid phi` (soundness, not completeness) |
| M2 | Minimal/DecisionProcedure.lean | 105 | `minimalTableau_complete` | `MValid phi -> minimalTableau phi = .closed` |

**Scope clarification**: M1 (`minimalTableau_sound`) is a soundness theorem, not
completeness. The task description says "8 sorry instances in completeness proofs across
all three logics," but M1 is soundness. Likely in scope since it is in the same file and
the `Decidable` instances depend on both sound + complete being sorry-free.

## Dependency Analysis

### Intra-file Dependencies

```
Classical:
  C1 (truth lemma) <- C2 (countermodel) <- C3 (completeness)

Intuitionistic:
  I1 (truth lemma) <- I2 (countermodel) <- I3 (completeness)

Minimal:
  M1 (soundness) -- independent
  M2 (completeness) -- adapts I1+I2+I3 pattern
```

### Cross-file Dependencies

- C1-C3 depend on: `extractValuation`, `classicalStepBranch`, `isClassicallyClosed`,
  `BoolEvaluate`, `Tautology`, `ClassicalTableauResult`, `classicalTableau` -- all
  already defined and available.
- I1-I3 depend on: `intExtractValuation`, `intBotForces`, `IForces`, `IValid`,
  `intStepBranch`, `isIntuitionisticallyClosed`, `IntTableauResult`, `intuitionisticTableau`
  -- all already defined.
- M1 depends on: `intExpandBranches`, `isMinimallyClosed`, `MValid` -- all defined.
  Also needs the same loop invariant pattern as task 316's `intExpandBranches_closed_unsat`.
- M2 depends on: same infrastructure as I1-I3 but with `isMinimallyClosed` and
  `botForces w = b.any (...)` instead of `fun _ => False`.

### Task 316 Dependencies

Task 316 is [PARTIAL] and addresses soundness proofs. Key interactions:

1. **Classical soundness** (task 316): `classicalTableau_sound` is already proved
   (sorry-free in Soundness.lean lines 633-647). Classical completeness (C1-C3) does
   NOT depend on classical soundness for its proofs.

2. **Intuitionistic soundness** (task 316): Has 2 sorry sites in Soundness.lean
   (lines 162 and 244). The completeness proofs (I1-I3) do NOT depend on soundness.
   However, the `Decidable (IValid phi)` instance in DecisionProcedure.lean uses
   both soundness and completeness.

3. **Minimal soundness** (task 316 scope overlap): M1 (`minimalTableau_sound`) at
   line 88 of DecisionProcedure.lean is a soundness proof. If task 316 fills it, we
   should not duplicate the work. If it remains sorry after 316, this task fills it.

**Verdict**: Tasks 316 and 317 are **independent** for the core proofs. Completeness
does not invoke soundness, and soundness does not invoke completeness. They share the
`Decidable` instance as a downstream consumer, but each direction is self-contained.

## Proof Strategy by Logic

### Classical Completeness (C1, C2, C3)

#### C1: `classicalTruthLemma` -- Truth Lemma by Formula Induction

**Goal state** (reconstructed from types):
```
b : Branch (Proposition Atom) Unit
hopen : isClassicallyClosed b = false
hsat : classicalStepBranch b [] = none  -- branch is saturated
phi : Proposition Atom
|- (b.any (fun sf => sf.sign == .pos && sf.formula == phi) ->
     BoolEvaluate (extractValuation b) phi = true) /\
   (b.any (fun sf => sf.sign == .neg && sf.formula == phi) ->
     BoolEvaluate (extractValuation b) phi = false)
```

**Proof approach**: Induction on `phi`:

- **atom p**: T-direction: `extractValuation b p = b.any (fun sf => ...)` by definition,
  so `BoolEvaluate (extractValuation b) (atom p) = extractValuation b p = true`.
  F-direction: If F(atom p) is on the branch and T(atom p) were also on it, we'd have
  a classical contradiction (T(p)/F(p) at same label `()`), contradicting `hopen`. So
  `extractValuation b p = false`, giving `BoolEvaluate v (atom p) = false`.

- **bot**: T-direction: If T(bot) were on the branch, `isClassicallyClosed b = true`
  (because ClassicalClosure detects T(bot)). But `hopen` says it's false. Contradiction,
  so the hypothesis `b.any (...)` is vacuously false.
  F-direction: `BoolEvaluate v bot = false` by definition. Trivially true.

- **and phi psi**: T-direction: If T(phi /\ psi) is on branch and the branch is saturated
  (`hsat`), then `classicalStepBranch b [] = none` means every applicable rule has been
  applied. But T(phi /\ psi) has an applicable alpha-rule adding T(phi) and T(psi). If
  T(phi /\ psi) is on the branch and it's saturated, then T(phi) and T(psi) must already
  be on the branch. By IH, `BoolEvaluate v phi = true` and `BoolEvaluate v psi = true`,
  so `BoolEvaluate v (phi /\ psi) = true`.
  F-direction: Similar -- saturation means F(phi /\ psi) has been expanded (beta-rule
  to F(phi) or F(psi)). Since saturation means the formula was already expanded, one of
  F(phi) or F(psi) must be on the branch. Wait -- this is wrong for beta-rules. A beta-
  rule creates two sub-branches, and the expansion loop picks one. Actually, the
  saturation condition `classicalStepBranch b [] = none` means NO unexpanded formula
  with an applicable rule exists. For F(phi /\ psi), the applicable rule is beta
  (branching), but `classicalStepBranch` returns the branching result, not `none`. So
  if F(phi /\ psi) is unexpanded and on the branch, `classicalStepBranch` would return
  `some (...)`, contradicting `hsat`. This means F(phi /\ psi) was already expanded, so
  its expansion result (branching to F(phi) and F(psi)) was processed earlier.

  **Critical subtlety**: The saturation condition `classicalStepBranch b [] = none`
  does NOT directly tell us that the branch contains the results of all applicable rules.
  It tells us that no formula on the branch (with `expanded = []`) triggers a rule.
  But wait -- the `expanded` argument is `[]`, meaning nothing is marked as expanded.
  So if ANY formula on the branch has an applicable rule, `classicalStepBranch` returns
  `some`. The only way it returns `none` is if EVERY formula on the branch is either
  an atom or bot (for which `classicalApplyOne` returns `.notApplicable`).

  This is a stronger condition than saturation: it means the branch contains ONLY atoms
  and bot. But that can't be right for a meaningful branch -- the initial F(phi) was
  placed on the branch, and expansion decomposes it, but complex subformulas can remain.

  **Re-examination**: Looking at `classicalStepBranch` more carefully:
  ```lean
  def classicalStepBranch (b : Branch ...) (expanded : List ...) :=
    b.findSome? fun sf =>
      if expanded.any (. == sf) then none  -- skip already-expanded
      else match classicalApplyOne sf with
        | .linear newForms => some ([Branch.extendMany b newForms], expanded ++ [sf])
        | .branching branches => some (..., expanded ++ [sf])
        | .persistent newForms => some (..., expanded ++ [sf])
        | .notApplicable => none
  ```

  The `expanded` list grows as formulas are processed. In the truth lemma, the hypothesis
  is `classicalStepBranch b [] = none`, which means with `expanded = []` (nothing
  previously expanded), every formula on the branch yields `.notApplicable` from
  `classicalApplyOne`. This is indeed the strongest saturation: no formula has an
  applicable rule.

  For `classicalApplyOne`, the only formulas yielding `.notApplicable` are atoms (pos
  or neg) and bot (pos or neg). So saturation with `expanded = []` means the branch
  contains only signed atoms and signed bot. This is consistent: the expansion loop
  decomposes all complex formulas, and when only atoms/bot remain, it's saturated.

  **But**: The actual branch returned by `classicalExpandBranches` when it returns
  `openBranch b` has gone through the expansion loop which accumulates an `expanded`
  list. The actual saturation condition in the expansion loop is:
  ```lean
  match classicalStepBranch b e with
  | none => .openBranch b  -- Saturated and open: countermodel
  ```
  where `e` is the current expanded list, not `[]`.

  **Problem with current formulation**: The truth lemma states
  `hsat : classicalStepBranch b [] = none`, but the actual branch returned by the
  expansion loop has saturation with respect to a non-empty `expanded` list. The truth
  lemma's hypothesis is STRONGER than what's actually available from the expansion loop.

  This means either:
  (a) The truth lemma should have `hsat : classicalStepBranch b expanded = none` for
      some `expanded`, and the proof must work for any `expanded` (which it can, since
      `expanded` only adds to what's already been processed).
  (b) The expanded list at saturation time contains exactly the formulas that have been
      expanded, meaning every formula on the branch with an applicable rule is in
      `expanded`. In this case, `classicalStepBranch b expanded = none` means every
      formula on the branch is either in `expanded` or has `.notApplicable`.

  For the truth lemma, what we actually need is: for every compound formula on the
  branch, its decomposition results are also on the branch. This is the Hintikka
  condition. The saturation condition `classicalStepBranch b expanded = none` (with
  appropriate `expanded`) provides exactly this.

  **Resolution**: The truth lemma hypothesis should be weakened to express the Hintikka
  conditions directly, or the saturation argument should be connected to the Hintikka
  conditions. The cleanest approach is:

  **Option A** (Hintikka conditions directly): Define `classicalHintikka b` as:
  - If T(phi /\ psi) in b, then T(phi) in b and T(psi) in b
  - If F(phi /\ psi) in b, then F(phi) in b or F(psi) in b
  - If T(phi \/ psi) in b, then T(phi) in b or T(psi) in b
  - If F(phi \/ psi) in b, then F(phi) in b and F(psi) in b
  - If T(phi -> psi) in b, then F(phi) in b or T(psi) in b
  - If F(phi -> psi) in b, then T(phi) in b and F(psi) in b
  - If T(neg phi) in b, then F(phi) in b
  - If F(neg phi) in b, then T(phi) in b

  Then prove: (1) saturation implies Hintikka, (2) Hintikka + open implies truth lemma.

  **Option B** (Direct proof with saturation): Use the saturation condition as stated
  but carefully extract the Hintikka conditions from it. For each compound formula T(phi)
  on the branch, if its rule were applicable and it weren't already expanded, then
  `classicalStepBranch` wouldn't return `none`. So either it's in `expanded` (meaning
  its results were added to the branch during expansion) or its rule is not applicable.

  **Recommended approach**: Option A (explicit Hintikka conditions) is cleaner for the
  formal proof and separates concerns. The truth lemma becomes a standard textbook proof
  by formula induction over Hintikka sets.

  **However**: The current code uses `classicalStepBranch b [] = none` as the hypothesis.
  Changing this requires modifying the lemma signature, which is acceptable since the file
  is being implemented from scratch (all proofs are sorry).

#### C2: `classicalOpenBranch_countermodel`

**Goal state**:
```
phi : Proposition Atom
h : classicalTableau phi = .openBranch b
|- BoolEvaluate (extractValuation b) phi = false
```

**Proof approach**:
1. Unfold `classicalTableau` to get the expansion loop result.
2. From `classicalTableau phi = .openBranch b`, the branch `b` was returned by
   `classicalExpandBranches` as a saturated open branch.
3. The initial branch contains `F(phi)` at `()`.
4. By the expansion loop invariant: the formulas on `b` are a superset of the initial
   branch (expansion only adds, never removes).
5. So `F(phi)` is on `b`.
6. The branch is open (`isClassicallyClosed b = false`) and saturated.
7. By C1 (truth lemma), `F(phi)` on `b` implies `BoolEvaluate (extractValuation b) phi = false`.

**Key challenge**: Extracting from `classicalTableau phi = .openBranch b` that:
- `isClassicallyClosed b = false`
- `classicalStepBranch b expanded = none` (for the appropriate `expanded`)
- `F(phi)` is in `b` (initial formula persists through expansion)

The first two follow from how `classicalExpandBranches` works: it only returns
`.openBranch b` when `isClassicallyClosed b = false` (line 136-137 of Expansion.lean)
and `classicalStepBranch b e = none` (line 137).

The third requires showing that expansion is monotone (formulas are added, never removed).
This is visible from `Branch.extendMany b newForms = newForms ++ b`, which prepends to `b`.
So every formula in the original branch remains.

**Practical approach**: Rather than proving a complex loop invariant about the expansion,
we can observe that `classicalExpandBranches` returns `.openBranch b` only at two sites:
- Fuel exhaustion (line 120): finds a non-closed branch
- Saturated and open (line 137): `classicalStepBranch b e = none`

For the truth lemma to apply, we need the Hintikka conditions. The fuel-exhaustion case
is problematic: we'd need to show that even with fuel exhaustion, the branch has Hintikka
properties. In practice, the fuel bound is designed to be sufficient, so fuel exhaustion
shouldn't happen for the initial formula. But proving this formally requires showing
the fuel bound is adequate.

**Alternative approach**: State C2 with an explicit hypothesis about the branch's
Hintikka conditions, and prove separately that the expansion loop produces Hintikka
branches. Or, restructure to use the contrapositive: if phi is a tautology, the tableau
must close (for C3), using soundness from task 316 for one direction and completeness
from the expansion loop for the other.

**Simplest approach for C2+C3 combined**: Use `by_contra` in C3. Assume
`classicalTableau phi != .closed`. Then `classicalTableau phi = .openBranch b` for some
`b`. Show `b` is open and saturated (from the expansion loop). Apply truth lemma to get
`BoolEvaluate (extractValuation b) phi = false`. This contradicts `Tautology phi`.

#### C3: `classicalTableau_complete`

**Goal state**:
```
phi : Proposition Atom
h : Tautology phi
|- classicalTableau phi = .closed
```

**Proof approach**: By contradiction (cases on `classicalTableau phi`):
- If `classicalTableau phi = .closed`, done.
- If `classicalTableau phi = .openBranch b`, apply C2 to get
  `BoolEvaluate (extractValuation b) phi = false`. But `Tautology phi` means
  `forall v, BoolEvaluate v phi = true` (by `tautology_iff_boolEvaluate_true`).
  Instantiate with `v = extractValuation b` to get `BoolEvaluate (extractValuation b) phi = true`.
  Contradiction.

This proof is simple, assuming C2 is available.

### Intuitionistic Completeness (I1, I2, I3)

#### I1: `intTruthLemma` -- Kripke Truth Lemma

**Goal state** (from LSP):
```
b : IBranch Atom
hopen : isIntuitionisticallyClosed b = false
hsat : forall sf in b, intStepBranch b [] 0 = none
phi : Proposition Atom
w : Nat
|- ((b.any (fun sf => sf.sign == .pos && sf.formula == phi && sf.label == w)) = true ->
     IForces (intExtractValuation b) intBotForces w phi) /\
   ((b.any (fun sf => sf.sign == .neg && sf.formula == phi && sf.label == w)) = true ->
     not (IForces (intExtractValuation b) intBotForces w phi))
```

**Proof approach**: Induction on `phi`:

- **atom p**: T-direction: `intExtractValuation b w p` is defined as
  `b.any (fun sf => sf.sign == .pos && sf.formula == .atom p && sf.label == w)`.
  So `IForces (intExtractValuation b) intBotForces w (atom p) = intExtractValuation b w p`,
  which equals the hypothesis directly.
  F-direction: If F(atom p) at w is on the branch and T(atom p) at w were also on it,
  we'd need to check whether this triggers closure. Intuitionistic closure only checks
  for T(bot), NOT for complementary pairs. So T(p)/F(p) does NOT close an intuitionistic
  branch. This means the F-direction for atoms cannot use closure.

  **Key insight for intuitionistic F-atom**: We need a separate argument. If both T(p)
  at w and F(p) at w are on the branch, then `intExtractValuation b w p = true` (from
  T(p)), so `IForces ... w (atom p) = true`, but we need `not (IForces ... w (atom p))`,
  which is `False`. This is a contradiction only if the branch is "Hintikka-consistent"
  in the sense that T(p) and F(p) at the same world don't coexist.

  But in the intuitionistic tableau, branches CAN have both T(p) and F(p) at different
  worlds. At the same world, they can coexist because intuitionistic closure doesn't
  close on complementary pairs. So how does the intuitionistic truth lemma work?

  The answer is in the saturation conditions for the intuitionistic tableau. The
  persistence propagation ensures that if T(p) is at world w and the branch is
  saturated, then there's no F(phi -> psi) decomposition that would create a world
  w' >= w with F(p). Actually, the intuitionistic T(imp) persistent rule handles this.

  Actually, re-reading Fitting Chapter 4: the intuitionistic truth lemma works because:
  - The model is constructed from the branch
  - Positive formulas define what's forced
  - Negative formulas are shown to be not-forced by induction
  - The key is: if F(p) at w is on the branch, then T(p) at w is NOT on the branch
    (this is maintained as an invariant of the expansion, NOT by closure).

  Wait -- is this guaranteed? Looking at the expansion: the initial branch has F(phi) at
  world 0. Rules add new signed formulas. Can T(p) and F(p) at the same world both appear?

  Yes, they can: consider F(p -> p) at world 0. The F(imp) rule creates a new world 1
  with T(p) at 1 and F(p) at 1. This branch would not close under intuitionistic closure
  (no T(bot)). But persistence propagation and further expansion might add more formulas.

  So the intuitionistic truth lemma for F-atom at world w requires: if F(atom p) at w is
  on the branch, then T(atom p) at w is NOT on the branch. This needs to be an invariant
  or a consequence of openness.

  Actually, this is NOT an invariant. The intuitionistic tableau can have T(p) and F(p)
  at the same world, and the branch stays open (no T(bot)). The truth lemma says:
  if T(p) at w is on branch -> IForces v bf w (atom p), and if F(p) at w is on branch
  -> not (IForces v bf w (atom p)). If both T(p) and F(p) at w are on the branch, this
  would require `IForces v bf w (atom p)` AND `not (IForces v bf w (atom p))`, which is
  a contradiction. So the truth lemma implicitly requires that this doesn't happen.

  **Critical observation**: The truth lemma as currently stated cannot be proved as-is
  for the intuitionistic case if T(p)/F(p) at the same world can coexist on an open
  saturated branch. We need to either:
  (a) Show this can't happen (an invariant of the expansion), or
  (b) Strengthen the closure condition, or
  (c) Restructure the countermodel construction.

  Looking at Fitting's approach more carefully: the worlds in the countermodel are not
  the world labels on the branch. Instead, each world in the countermodel corresponds to
  a "complete" set of formulas at a world label that satisfies the Hintikka conditions.
  The key is that the Hintikka conditions for a world include: if T(p) at w and F(p) at
  w, then the world is "inconsistent" and should be excluded. But in intuitionistic
  tableaux without the complementary closure rule, this situation can arise.

  **Resolution**: In Fitting's system, the intuitionistic tableau DOES close on
  complementary pairs at the same world for atoms. Looking at `MinimalClosure` in the
  CSLib code: `MinimalClosure` closes when T(p) and F(p) coexist at the same world for
  atomic p. And `IntuitionisticClosure` closes only on T(bot).

  The difference: Fitting's intuitionistic tableau uses classical-style closure (T(p)/F(p)
  closes) while CSLib's `IntuitionisticClosure` only closes on T(bot). This means CSLib's
  intuitionistic tableau is actually closer to the MINIMAL tableau.

  For the truth lemma to work with `IntuitionisticClosure`, we need the additional property
  that `botForces = fun _ => False` makes T(bot) closure equivalent to the relevant
  Hintikka condition. The F-atom case works because: if F(p) at w is on the open branch,
  and T(p) at w were also present, then... we need to show this leads to T(bot), which
  it doesn't directly.

  **Alternative resolution**: The truth lemma for intuitionistic logic may need to be
  stated differently. Instead of: "T(p) on branch implies IForces, F(p) on branch implies
  not IForces", we can use: "the forcing relation at world w agrees with the positive
  formulas, and the negation of the forcing relation agrees with the negative formulas --
  provided the branch is Hintikka-consistent."

  Or, more practically: the `intExtractValuation b w p` is defined as
  `b.any (fun sf => sf.sign == .pos && sf.formula == .atom p && sf.label == w)`.
  So `IForces v bf w (atom p) = intExtractValuation b w p`. For the F-direction: if
  F(atom p) at w is on the branch, we need `not (intExtractValuation b w p)`, i.e.,
  T(atom p) at w is NOT on the branch.

  For the intuitionistic case with `IntuitionisticClosure` (only T(bot) closes): we need
  to ensure that no open saturated branch has both T(p) and F(p) at the same world. This
  IS actually guaranteed by the expansion loop's construction:

  Looking at the expansion: the initial branch has `F(phi)` at world 0. The F(imp) rule
  creates new worlds. The T(imp) persistent rule propagates positive formulas. Atoms are
  never decomposed (they are `.notApplicable`). So T(p) at w can appear only from
  propagation of T(p) from an earlier world, or from decomposition of a conjunction/
  disjunction at world w. Similarly, F(p) at w appears from decomposition of a formula
  at world w.

  In fact, for the branch to be saturated and open with T(p) at w and F(p) at w: this is
  POSSIBLE. Consider `F(p /\ (p -> bot))` at world 0. The F(and) beta-rule branches to
  F(p) at 0 or F(p -> bot) at 0. Taking the F(p -> bot) branch: F(imp) creates world 1
  with T(p) at 1 and F(bot) at 1... wait, F(bot) is never decomposed. T(p) at 1 is
  propagated. But we need T(p) and F(p) at the SAME world.

  After more careful analysis, it appears that for a properly saturated branch with
  only intuitionistic closure (T(bot)), we CAN have T(p) and F(p) at the same world.
  This means the truth lemma as stated IS UNPROVABLE with `IntuitionisticClosure` alone.

  **Conclusion for I1**: The intuitionistic truth lemma needs `MinimalClosure` (which
  closes on atomic complementary pairs at the same world) rather than
  `IntuitionisticClosure`. OR, the lemma hypothesis needs strengthening to exclude
  atomic contradictions. OR, the countermodel construction needs adjustment.

  Actually, there's a simpler way to see this: in Fitting's system, the intuitionistic
  closure IS the same as classical closure (both T/F pairs and T(bot)). The reason is
  that bot is FALSE in all intuitionistic worlds (`botForces = fun _ => False`), so T(bot)
  is automatically a contradiction. And for atoms, T(p)/F(p) at the same world is also a
  contradiction. The ONLY difference between classical and intuitionistic tableau is the
  RULES (world-creating F(imp) vs. non-world-creating), not the closure condition.

  So the issue is: CSLib's `IntuitionisticClosure` (only T(bot) closes) is WEAKER than
  what Fitting uses. With CSLib's current design, the intuitionistic truth lemma would
  need to work with MinimalClosure, or the code needs to use ClassicalClosure for
  intuitionistic tableau (which seems wrong but is what Fitting does -- the closure
  condition is the same; the difference is in the rules).

  **Pragmatic resolution**: Since `IntuitionisticClosure` only closes on T(bot), but we
  also need no atomic contradictions for the truth lemma, we should either:
  1. Change `isIntuitionisticallyClosed` to also close on atomic contradictions (same as
     MinimalClosure), or
  2. Accept that the current `IntuitionisticClosure` cannot support the truth lemma and
     restructure the completeness proof to avoid it, or
  3. Prove that atomic contradictions at the same world DON'T arise in saturated
     intuitionistic branches (by a structural argument about the expansion loop).

  Option 3 is the most interesting but hardest. Option 1 is cleanest for the math but
  requires modifying the Foundations infrastructure. Option 2 may not be possible.

  **Actually**: Looking more carefully at Fitting, the intuitionistic closure in signed
  tableaux DOES use both T(bot) and complementary pairs. The difference between classical
  and intuitionistic tableaux is solely in the rules. So CSLib's `IntuitionisticClosure`
  (bot-only) appears to be a design error for completeness purposes. The correct closure
  for intuitionistic tableau should include complementary pairs.

  **For this research report**: Flag this as a potential blocker. The implementation plan
  should address whether to modify `IntuitionisticClosure` or prove the structural
  invariant.

  **Update after re-reading the code**: The `intuitionisticTableau` function passes
  `isIntuitionisticallyClosed` to `intExpandBranches`. And `isIntuitionisticallyClosed`
  only checks for T(bot). But the `minimalTableau` function passes `isMinimallyClosed`
  which checks for T(p)/F(p) at same world for atomic p. Since atoms are the only
  "ground" formulas, MinimalClosure is the right completeness closure for both minimal
  AND intuitionistic logic. IntuitionisticClosure is weaker and makes completeness harder.

  The key question: does the expansion loop with `isIntuitionisticallyClosed` actually
  terminate correctly and produce open branches that support countermodels? If the
  branch has T(p)/F(p) at the same world but no T(bot), the expansion doesn't close
  it, so it may return it as an "open" branch. But then the truth lemma fails.

  **Tentative conclusion**: The intuitionistic completeness proof may require changing the
  closure predicate passed to `intExpandBranches` from `isIntuitionisticallyClosed` to
  something that also closes on atomic contradictions. This would be a code change, not
  just a proof fill. Alternatively, we can prove that for `botForces = fun _ => False`,
  having T(p)/F(p) at the same world on the branch means the branch is "semantically
  inconsistent" even though it's not closed, and build the countermodel from a branch
  that avoids such pairs.

  **Most practical resolution**: For the completeness direction, the countermodel is built
  from the positive formulas only. The F-direction of the truth lemma for atoms works if
  we can show: if F(p) at w is on the saturated branch, then T(p) at w is not. This IS
  provable for the intuitionistic expansion: the expansion never creates both T(p) and
  F(p) at the same world from the intuitionistic rules. The F(imp) rule creates T(phi)
  and F(psi) at a NEW world (not T and F of the same formula). Propagation only adds
  T formulas. So the only way to get T(p) and F(p) at the same world is:
  - T(p) propagated from an earlier world to w, AND F(p) placed at w by decomposition.
  This CAN happen. But can it happen with p atomic? Let's trace: F(p) at w can only
  arise from F(phi \/ psi) decomposition (giving F(phi) and F(psi)) where phi or psi = p,
  or from F(imp) creating F(psi) at a new world where psi = p, or from the initial F(phi).
  T(p) at w can arise from T(phi /\ psi) decomposition, T(phi \/ psi) decomposition, or
  propagation.

  If both T(p) at w and F(p) at w are on the branch, this is consistent with intuitionistic
  semantics where `botForces = fun _ => False` -- there's no semantic contradiction because
  p can be both true and false at the same world only if the model is inconsistent. But
  the countermodel is constructed precisely to avoid this.

  **Final resolution for implementation**: The implementer should:
  1. Check whether the current `isIntuitionisticallyClosed` (T(bot) only) is sufficient,
     by attempting the truth lemma proof. If atomic T(p)/F(p) at same world is reached
     and can't be excluded, the closure must be strengthened.
  2. If strengthening is needed, the simplest option is to use `isMinimallyClosed` or
     a combined closure (T(bot) OR atomic T(p)/F(p)) for the intuitionistic tableau.
     This doesn't change the logic -- it only makes the tableau close MORE branches,
     which is sound (closing a satisfiable branch is fine for soundness -- wait, no,
     closing a satisfiable branch would BREAK soundness).
  3. Actually, closing on atomic T(p)/F(p) IS sound for intuitionistic logic because
     intuitionistic models require `val w p ↔ not (val w p)` to be impossible (the
     valuation is a function, so val w p is either True or False, never both).

  **Blocker status**: POTENTIAL BLOCKER. The truth lemma for atoms under
  `IntuitionisticClosure` may be unprovable without structural invariant proofs or
  closure modification. Implementation should address this first.

- **bot**: T-direction: T(bot) on an open branch contradicts `hopen` since
  `isIntuitionisticallyClosed` detects T(bot). Vacuously true.
  F-direction: `IForces v intBotForces w bot = intBotForces w = (fun _ => False) w = False`.
  So `not (IForces ...) = not False = True`. Trivially true.

- **imp phi psi**: T-direction: If T(phi -> psi) at w is on the branch and the branch
  is saturated, then for every w' >= w with T(phi) at w', the persistent T(imp) rule
  has added T(psi) at w'. By IH, `IForces v bf w' psi`. So
  `IForces v bf w (phi -> psi) = forall w' >= w, IForces phi -> IForces psi` holds.
  But we need to be careful: the "worlds" in the Kripke model are Nat, and w' >= w
  in the model means w' >= w as natural numbers. The T(imp) persistent rule fires for
  all w' >= w that appear on the branch. But the IForces quantifies over ALL w' >= w,
  not just those on the branch.

  **Resolution**: The Kripke model worlds ARE the world labels on the branch. If
  w' >= w and w' doesn't appear on the branch, then no formulas are at w', so
  `IForces v bf w' phi` would need to be checked against the extracted valuation.
  The extracted valuation only assigns truth based on what's on the branch.

  Actually, the IForces quantifies over ALL w' : Nat with w <= w'. Since the Kripke
  model uses `Nat` with the standard `<=`, there are infinitely many worlds. But the
  valuation is defined from the branch, so at worlds not on the branch, no atoms are
  true. This means `IForces v bf w' phi` for w' not on the branch might be trivially
  false for many formulas, making the implication vacuously true.

  For the T-direction of imp: we need `forall w' >= w, IForces v bf w' phi -> IForces v bf w' psi`.
  If w' is not on the branch, then no atoms are true at w', so `IForces v bf w' phi`
  is likely false (for non-trivial phi), making the implication vacuous. This works.

  If w' IS on the branch, then T(phi -> psi) at w and T(phi) at w' (with w' >= w)
  means the persistent rule has added T(psi) at w'. By IH, the conclusion follows.

  F-direction: If F(phi -> psi) at w is on the branch, the F(imp) world-creating rule
  was applied (since the branch is saturated). This creates a new world w' with T(phi)
  at w' and F(psi) at w'. By IH, `IForces v bf w' phi` and `not (IForces v bf w' psi)`.
  So `not (IForces v bf w (phi -> psi))` = `exists w' >= w, IForces phi and not IForces psi`.
  Taking w' as the created world gives the result.

  BUT: we need w' >= w in the Nat ordering. The created world's label is the `nextWorld`
  counter, which is > any existing world label. So w' > w, giving w' >= w. This works.

- **and phi psi**: T-direction: T(phi /\ psi) saturated means T(phi) and T(psi) are on
  the branch at the same world. By IH. Standard.
  F-direction: F(phi /\ psi) saturated means beta-rule branched to F(phi) or F(psi).
  Since this is a branching rule, the expansion loop processes both branches. The branch
  we have is one of them, so it contains F(phi) or F(psi) (at the same world). By IH.

  Wait -- the beta-rule creates TWO branches. The expansion loop continues with BOTH
  branches. If both branches close, the overall result is closed. If one stays open,
  it's returned. So the open branch we have is one that didn't close. It may or may
  not contain F(phi) or F(psi).

  Actually, the open branch returned IS one of the sub-branches (or an extension of
  one). The F(phi /\ psi) formula was on the branch before branching. After branching,
  it's still on each sub-branch (since `extendMany` prepends new formulas). The sub-
  branches have: one with F(phi) added, one with F(psi) added.

  For the truth lemma, the saturation condition means that for every compound formula
  on the branch, its decomposition results are also on the branch. For F(phi /\ psi)
  at w: since it was expanded (the branch is saturated), either F(phi) at w or F(psi)
  at w is on the branch (beta-rule). By IH.

  **But wait**: Saturation for the intuitionistic truth lemma is stated as
  `hsat : forall sf in b, intStepBranch b [] 0 = none`. This is the same issue as the
  classical case: `intStepBranch b [] 0 = none` means no formula on the branch has an
  applicable rule with `expanded = []`. For atoms and bot, `intApplyRuleFull` returns
  `.notApplicable`. For T(imp), it also returns `.notApplicable` (handled separately by
  persistence). For all other compound formulas, it returns a result. So saturation with
  `expanded = []` means the branch contains only atoms, bot, and T(imp) formulas.

  Again, this saturation hypothesis is TOO STRONG: it says the branch contains no
  expandable formulas at all (with empty expanded set). The actual saturated branch
  from the expansion loop has a non-empty expanded set.

  **Same resolution as classical**: The truth lemma should use Hintikka conditions or
  a more appropriate saturation predicate.

#### I2: `intuitionisticOpenBranch_countermodel` and I3: `intuitionisticTableau_complete`

Similar structure to C2 and C3 but with Kripke semantics instead of Boolean.

I2 connects the expansion loop output to the truth lemma.
I3 uses contrapositive: `IValid phi` + `openBranch b` -> contradiction via I2.

### Minimal Logic (M1, M2)

#### M1: `minimalTableau_sound`

This is a soundness theorem (closed -> MValid). It requires the same loop invariant
infrastructure as the intuitionistic soundness (task 316), but parameterized with
`isMinimallyClosed` and arbitrary `botForces`.

The key difference from intuitionistic soundness: `botForces` is not `fun _ => False`
but universally quantified. The proof structure is the same: contrapositive, loop
invariant, rule preservation, closure unsatisfiability.

The closure unsatisfiability lemma for MinimalClosure needs: if T(p)/F(p) at same
world for atomic p, then any model satisfying the branch has `val w p` and `not (val w p)`,
contradiction.

#### M2: `minimalTableau_complete`

Same as I3 but with `MValid` and `minimalTableau`. The countermodel construction uses
`botForces w = b.any (fun sf => sf.sign == .pos && sf.formula == .bot && sf.label == w)`
instead of `fun _ => False`.

The truth lemma for minimal logic is the same as I1 but with `botForces` as defined above.
The bot case changes: T(bot) at w means `botForces w = true` (by definition of the
extracted botForces), which matches `IForces v bf w bot = bf w`.

## Implementation Recommendations

### Phase Structure

**Phase 1: Classical Completeness (C1, C2, C3)**
- Self-contained, no dependency on task 316
- Cleanest case for developing the proof pattern
- Recommended to address first

**Phase 2: Intuitionistic Completeness (I1, I2, I3)**
- Requires resolving the atomic contradiction issue (potential blocker)
- More complex due to world-indexed branches

**Phase 3: Minimal Soundness + Completeness (M1, M2)**
- Adapts intuitionistic pattern with modified botForces
- M1 is soundness (may overlap with task 316)

### Key Decisions Needed

1. **Truth lemma hypothesis**: The current `classicalStepBranch b [] = none` / 
   `intStepBranch b [] 0 = none` hypotheses are too strong. Options:
   (a) Define explicit Hintikka predicates and use those as hypotheses
   (b) Use `classicalStepBranch b expanded = none` with existentially quantified `expanded`
   (c) Prove a "saturation implies Hintikka" bridge lemma
   
   Recommendation: Option (a) -- explicit Hintikka predicates. This separates the
   expansion loop's output format from the truth lemma's input format.

2. **Intuitionistic atomic contradiction**: Either strengthen `IntuitionisticClosure`
   to include atomic contradictions (becoming equivalent to MinimalClosure for atoms),
   or prove the structural invariant that the expansion never produces T(p)/F(p) at
   the same world. The former is simpler; the latter is more elegant but harder.

3. **Expansion loop invariants**: The proofs of C2, I2 need to extract properties
   from the expansion loop's output. Key invariants:
   - Formulas on the returned branch are a superset of the initial branch
   - The returned branch satisfies the Hintikka conditions
   - The returned branch is open (not closed)
   
   These may require auxiliary lemmas about the expansion loop.

4. **M1 overlap with task 316**: Check whether task 316 will fill `minimalTableau_sound`.
   If so, this task should skip M1 and focus on M2 only.

### Existing Infrastructure to Reuse

| Declaration | Location | Purpose |
|-------------|----------|---------|
| `extractValuation` | Classical/Completeness.lean:57 | Boolean valuation from branch |
| `intExtractValuation` | Intuitionistic/Completeness.lean:57 | Kripke valuation from branch |
| `intBotForces` | Intuitionistic/Completeness.lean:61 | Always-false botForces |
| `BoolEvaluate_*` simp lemmas | Semantics/Bool.lean | Unfolding BoolEvaluate |
| `IForces_*` simp lemmas | Semantics/Kripke.lean | Unfolding IForces |
| `iforces_persistence` | Semantics/Kripke.lean:125 | Monotonicity of forcing |
| `tautology_iff_boolEvaluate_true` | Semantics/Bool.lean:157 | Bridge for tautology |
| `classicalRule_preserves_sat` | Classical/Soundness.lean:168 | Rule preservation (soundness) |
| `intRule_preserves_sat` | Intuitionistic/Soundness.lean:83 | Rule preservation (soundness) |
| `classically_closed_unsatisfiable` | Classical/Soundness.lean:432 | Closure unsatisfiability |
| `intClosed_unsatisfiable` | Intuitionistic/Soundness.lean:196 | Closure unsatisfiability |
| `branchConsistent` | Classical/Soundness.lean:60 | Branch satisfiability predicate |
| `intBranchSatisfied` | Intuitionistic/Soundness.lean:60 | Kripke branch satisfiability |
| `Function.update_of_ne` | Mathlib | For worldOf construction |
| `Function.update_self` | Mathlib | For worldOf construction |
| `List.any_eq_true` | Lean core | Unfolding List.any |
| `List.any_iff_exists_prop` | Mathlib | Propositional List.any bridge |

### Mathlib API Notes

- `Function.update_of_ne : a != a' -> Function.update f a' v a = f a` -- for showing
  worldOf' agrees with worldOf at old labels
- `Function.update_self : Function.update f a v a = v` -- for the new world
- `List.any_eq_true : l.any p = true <-> exists x in l, p x = true` -- core
- `Bool.and_eq_true : (a && b) = true <-> a = true /\ b = true` -- core

### Estimated Effort

| Phase | Sorry Count | Estimated Effort | Difficulty |
|-------|-------------|-----------------|------------|
| Phase 1: Classical (C1, C2, C3) | 3 | 3-4 hours | Medium |
| Phase 2: Intuitionistic (I1, I2, I3) | 3 | 4-6 hours | Hard (blocker potential) |
| Phase 3: Minimal (M1, M2) | 2 | 2-3 hours | Medium (adapts Phase 2) |
| **Total** | **8** | **9-13 hours** | |

## Potential Blockers

### B1: Intuitionistic Truth Lemma Atomic Contradiction

**Severity**: HIGH
**Description**: The F-atom case of the intuitionistic truth lemma requires that T(p) and
F(p) at the same world don't coexist on an open saturated branch. This is not guaranteed
by `IntuitionisticClosure` (which only closes on T(bot)).

**Mitigation options**:
1. Strengthen closure: Use MinimalClosure for intuitionistic tableau too (simplest)
2. Prove structural invariant: Show expansion never creates T(p)/F(p) at same world (hard)
3. Restructure countermodel: Build model that handles both-present case (may not be possible)

**Recommendation**: Option 1 (strengthen closure) if it doesn't break soundness. Option 2
if Option 1 is unacceptable.

### B2: Saturation Hypothesis Mismatch

**Severity**: MEDIUM
**Description**: The truth lemma hypotheses use `classicalStepBranch b [] = none` (empty
expanded list), but the expansion loop returns branches saturated with respect to a
non-empty expanded list. The truth lemma needs the Hintikka conditions that saturation
provides, but the current formulation doesn't connect them correctly.

**Mitigation**: Define explicit Hintikka predicates and use them as truth lemma hypotheses.
Add bridge lemmas connecting expansion loop saturation to Hintikka conditions.

### B3: Task 316 Dependency for M1

**Severity**: LOW
**Description**: M1 (`minimalTableau_sound`) is a soundness proof that may be in task 316's
scope. If both tasks attempt it, there will be conflict.

**Mitigation**: Coordinate with task 316 status. If 316 is still [PARTIAL] when 317
implementation begins, include M1 in 317.

## Literature Proof Structure

Following the Hintikka-set argument (Smullyan 1968, Ch. V; Fitting 1983, Ch. 2 and 4):

1. **Saturation**: Run the tableau expansion until all branches are either closed or
   saturated (no more rules apply).
2. **Hintikka conditions**: A saturated open branch satisfies the Hintikka conditions:
   - Not closed (no contradiction/T(bot) depending on logic)
   - For each compound formula, its decomposition results are on the branch
3. **Truth lemma**: By induction on formula structure, the extracted model satisfies
   all signed formulas on the branch (T -> true, F -> false/not-forced).
4. **Countermodel**: The initial formula F(phi) is on the branch, so phi is false/not-forced
   in the extracted model.
5. **Completeness**: By contrapositive, if phi is valid, the tableau must close.

Steps 2-3 are the hardest formally. Step 1 is handled by the expansion loop. Steps 4-5
are straightforward consequences.

## File Locations Summary

| Sorry ID | File | Line | Declaration |
|----------|------|------|-------------|
| C1 | `Cslib/Logics/Propositional/Tableau/Classical/Completeness.lean` | 79 | `classicalTruthLemma` |
| C2 | `Cslib/Logics/Propositional/Tableau/Classical/Completeness.lean` | 88 | `classicalOpenBranch_countermodel` |
| C3 | `Cslib/Logics/Propositional/Tableau/Classical/Completeness.lean` | 102 | `classicalTableau_complete` |
| I1 | `Cslib/Logics/Propositional/Tableau/Intuitionistic/Completeness.lean` | 89 | `intTruthLemma` |
| I2 | `Cslib/Logics/Propositional/Tableau/Intuitionistic/Completeness.lean` | 98 | `intuitionisticOpenBranch_countermodel` |
| I3 | `Cslib/Logics/Propositional/Tableau/Intuitionistic/Completeness.lean` | 112 | `intuitionisticTableau_complete` |
| M1 | `Cslib/Logics/Propositional/Tableau/Minimal/DecisionProcedure.lean` | 88 | `minimalTableau_sound` |
| M2 | `Cslib/Logics/Propositional/Tableau/Minimal/DecisionProcedure.lean` | 105 | `minimalTableau_complete` |
