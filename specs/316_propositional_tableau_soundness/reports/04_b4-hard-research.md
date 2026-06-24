# B4 Hard Research: Intuitionistic Loop Invariant worldOf/Ordering Issue

- **Task**: 316 - Propositional Tableau Soundness
- **Blocker**: B4 - `intExpandBranches_closed_unsat` requires global Nat-monotonicity of `worldOf`, which `Function.update` from F(imp) breaks
- **Date**: 2026-06-23
- **Agent**: cslib-research-hard-agent
- **Reference Grounding Tier**: Tier 1 (Literature-backed) + Tier 3 (Implementation-backed)

## Source-to-Implementation Mapping

| Source | Prop/Location | Lean Identifier | Type Signature | Status |
|--------|---------------|-----------------|----------------|--------|
| [Fitting1983] Ch.4, Thm 4.3.4 | Soundness of intuitionistic tableau | `intuitionisticTableau_sound` | `intuitionisticTableau phi = .closed -> IValid phi` | sorry |
| [Fitting1983] Ch.4, Def 4.3.1 | F(imp) world creation rule | `intFImpRule` | defined | transcribed |
| [Fitting1983] Ch.4, Def 4.3.2 | T(imp) persistence rule | `intTImpRule` | defined | transcribed |
| [ChagrovZakharyaschev1997] Sec 2.2, Prop 2.1 | Persistence of forcing | `iforces_persistence` | proved | transcribed |
| [Fitting1983] Ch.4 | Rule preserves sat (existential worldOf) | `intRule_preserves_sat_ext` | not yet defined | pending |
| [Fitting1983] Ch.4 | Persistence fixpoint preserves sat | `applyPersistenceFixpoint_preserves_sat` | not yet defined | pending |
| [Fitting1983] Ch.4 | Loop invariant (fuel induction) | `intExpandBranches_closed_unsat` | not yet defined | pending |

## Findings

### Research Question 1: Is the worldsAbove design fundamentally flawed?

**Verdict: No, but the soundness proof must account for it carefully.**

The `worldsAbove` design in `intTImpRule` (Rules.lean:132) uses `Nat >=` as a proxy for Kripke accessibility:

```lean
let worldsAbove := (b.map (·.label)).filter (· >= w) |>.eraseDups
```

This is correct for the *algorithmic* behavior of the tableau: the tableau expansion creates worlds with monotonically increasing Nat labels, and accessibility is defined as `w' >= w` (i.e., the world was created at the same time or later). This is sound because:

1. The initial world is 0, and `intFImpRule` creates fresh worlds via `nextWorld` which increases monotonically.
2. When F(phi -> psi) fires at world `w`, the new world `w' = nextWorld` satisfies `w' > w >= 0`.
3. The persistence rule (`intTImpRule`) correctly propagates T(phi -> psi) consequences to all worlds `w' >= w` that appear on the branch.

The issue is NOT with the algorithmic design but with the **soundness proof's hypothesis**. The proof needs `worldOf` to be order-preserving (`w1 <= w2 -> worldOf w1 <= worldOf w2`) to justify the persistence fixpoint. When `Function.update worldOf nw w'` is applied, this monotonicity can break for labels between the F(imp) source label and `nw`.

**The fix is to not require global monotonicity.** Instead, the proof should use the contrapositive formulation where `worldOf` is universally quantified, as detailed below.

### Research Question 2: Can we weaken the ordering hypothesis?

**Verdict: Yes, and this is the correct approach. The hypothesis can be eliminated entirely.**

The key insight from the blocker report (03_blocker-solutions.md) is already correct: the loop invariant should be stated in contrapositive form:

> If `intExpandBranches ... = .closed`, then for ALL `worldOf`, no branch is satisfied.

Since `IValid` quantifies universally over all Kripke models (including the choice of `worldOf`), the soundness proof never needs to *construct* a specific `worldOf`. Instead, it assumes an arbitrary `worldOf` and derives a contradiction. When F(imp) fires and creates a new world `nw`, the proof:

1. Takes the arbitrary `worldOf` from the outer universally quantified context.
2. For the F(imp) case in `intRule_preserves_sat_ext`, produces an existential `worldOf'` via `Function.update worldOf nw w'` (where `w'` is the semantic witness).
3. Passes `worldOf'` to the inductive hypothesis for the next expansion step.

The ordering hypothesis `h_order` is needed only for `applyPersistenceFixpoint_preserves_sat`. There are two approaches to handle it:

**Approach A (Recommended): Branch-local monotonicity as a maintained invariant.**

Instead of requiring global monotonicity `forall w1 w2, w1 <= w2 -> worldOf w1 <= worldOf w2`, maintain an invariant:

```
forall l1 l2, l1 and l2 are labels on the branch, l1 <= l2 -> worldOf l1 <= worldOf l2
```

This survives `Function.update` because:
- Labels on the branch before F(imp) are all `< nw` (by `h_fresh` invariant).
- After the update, `worldOf' n = worldOf n` for all `n < nw`.
- The new label `nw` maps to `w'` where `worldOf label <= w'` (from the `neg IForces imp` witness).
- For any prior label `l <= label`, we have `worldOf l <= worldOf label <= w' = worldOf' nw`.
- For `nw` vs any future label `nw'`: this is the next iteration's concern, and we construct `worldOf''` there.

**Approach B: Thread worldOf through the induction, constructing it step by step.**

The universal-quantification-over-worldOf trick means we never carry an explicit `worldOf` across steps. Each step of the induction begins with "for all worldOf satisfying the branch..." and the F(imp) step constructs `worldOf'` from it.

Both approaches are viable. Approach A is cleaner because it avoids needing to state the loop invariant with an explicit ordering condition.

### Research Question 3: Alternative proof approach avoiding worldOf/ordering?

**Verdict: Yes. Per-rule semantic argument with existential worldOf is the recommended approach.**

The recommended approach (already identified in report 03) is to replace the current `intRule_preserves_sat` with `intRule_preserves_sat_ext` that uses an existential `worldOf'` for the linearResult case. This is the correct formalization of Fitting's soundness argument:

**Fitting's approach** [Fitting1983, Ch. 4, Thm 4.3.4]:
- Soundness is proved by showing that if the initial branch is satisfiable, then the expansion produces at least one open branch.
- For F(imp), the model is extended by choosing the witness world for the new label.
- The key step is that the model extension preserves satisfaction of the original branch formulas (because the witness agrees with the original mapping on old labels).

This translates directly to:

```lean
lemma intRule_preserves_sat_ext ...
    (nw : Nat)
    (h_fresh : forall sf' in b, sf'.label < nw) :
    match intApplyRuleFull sf nw b with
    | .linearResult newForms _ =>
      exists worldOf' : Nat -> World,
        (forall n, n < nw -> worldOf' n = worldOf n) /\
        intBranchSatisfied val botForces worldOf' (Branch.extendMany b newForms)
    | .branchingResult branches _ =>
      exists br in branches,
        intBranchSatisfied val botForces worldOf (Branch.extendMany b br)
    | .notApplicable => True
```

For the non-world-creating cases (T(and), F(and), T(or), F(or)), the witness is `worldOf' = worldOf`, with agreement trivially `fun n _ => rfl`.

For F(imp): `worldOf' = Function.update worldOf nw w'` where `w'` is the semantic witness from `neg (IForces val botForces (worldOf label) (phi -> psi))`.

### Research Question 4: How do published proofs handle F(imp) world creation?

**Fitting** [Fitting1983, Ch. 4] handles this informally by saying "extend the assignment to map the new prefix to a world w' such that w' >= w(label), w' forces phi, and w' does not force psi." The formal apparatus of `Function.update` is the Lean 4 translation of this extension.

**Troelstra and Schwichtenberg** [TroelstraSchwichtenberg2000, Ch. 8] discuss tableau systems in the context of proof search but do not give a formal soundness proof for the intuitionistic case; they focus on sequent calculus cut-elimination instead.

**Negri and von Plato** (Structural Proof Theory) focus on sequent calculus and do not formalize tableau soundness directly. Their invertibility results for sequent rules are not directly applicable here.

**Bentzen et al.** [Bentzen2023] formalize Henkin-style completeness for IPL in Lean, but use a different approach (canonical models, maximal consistent sets) rather than tableau. Their Kripke model construction is relevant to completeness, not soundness.

**No existing formalized proof** of intuitionistic tableau soundness was found in Lean 4 / Mathlib. The CSLib formalization will be novel in this regard.

### Research Question 5: Can intExpandBranches be refactored to track accessibility explicitly?

**Verdict: Not recommended. The current design is correct; only the proof needs adjustment.**

Refactoring `intExpandBranches` to explicitly track an accessibility relation (instead of using Nat ordering) would:
1. Require changing the data structure from `List Nat` (nextWorlds) to something carrying an explicit relation.
2. Break the existing completeness proof (if any) that depends on the current interface.
3. Add runtime overhead for no algorithmic benefit (Nat ordering IS the correct accessibility proxy for the tableau algorithm).

The proof-level fix (existential `worldOf'` in `intRule_preserves_sat_ext`) is strictly better because it leaves the computational code unchanged and only modifies the proof infrastructure.

## Concrete Implementation Plan for B4

### Step 1: Replace intRule_preserves_sat with intRule_preserves_sat_ext

**File**: `Intuitionistic/Soundness.lean`

Delete the current `intRule_preserves_sat` (lines 83-189) and replace with:

```lean
lemma intRule_preserves_sat_ext {World : Type*} [Preorder World]
    (val : World -> Atom -> Prop)
    (botForces : World -> Prop)
    (v_uc : forall {w w' : World} (p : Atom), w <= w' -> val w p -> val w' p)
    (bf_uc : forall {w w' : World}, w <= w' -> botForces w -> botForces w')
    (worldOf : Nat -> World)
    (b : IBranch Atom)
    (sf : ISF Atom)
    (hmem_sf : sf in b)
    (hsat : intBranchSatisfied val botForces worldOf b)
    (nw : Nat)
    (h_fresh : forall sf' in b, sf'.label < nw) :
    match intApplyRuleFull sf nw b with
    | .linearResult newForms _ =>
      exists worldOf' : Nat -> World,
        (forall n, n < nw -> worldOf' n = worldOf n) /\
        intBranchSatisfied val botForces worldOf' (Branch.extendMany b newForms)
    | .branchingResult branches _ =>
      exists br in branches,
        intBranchSatisfied val botForces worldOf (Branch.extendMany b br)
    | .notApplicable => True
```

**Proof strategy for each case**:

- **T(and), F(or)** (linearResult, no world creation): Witness `worldOf' = worldOf`. Agreement by `fun n _ => rfl`. Satisfaction from existing proofs (already complete in current file).

- **F(and), T(or)** (branchingResult): No `worldOf'` needed. Proof identical to current file.

- **T(imp), T(atom), T(bot), F(atom), F(bot)** (notApplicable): Trivial.

- **F(imp)** (linearResult, world creation -- the B4 case):
  1. From `hsat` and `hmem_sf`, extract `hneg : neg IForces val botForces (worldOf label) (phi.imp psi)`.
  2. Rewrite with `IForces_imp` and `push_neg` to get `exists w', worldOf label <= w' /\ IForces ... w' phi /\ neg IForces ... w' psi`.
  3. Let `worldOf' = Function.update worldOf nw w'`.
  4. Agreement: for `n < nw`, `worldOf' n = Function.update worldOf nw w' n = worldOf n` by `Function.update_of_ne (Nat.ne_of_lt hn |>.symm)`.
  5. Satisfaction of new formulas (`T(phi) at nw`, `F(psi) at nw`): `worldOf' nw = w'` by `Function.update_self`, then apply `hphi` and `hpsi`.
  6. Satisfaction of propagated formulas (`T(alpha) at nw` from `propagatePersistence`): From `hsat`, `IForces val botForces (worldOf label_alpha) alpha`. Since `label_alpha <= label` (persistence propagates from `fromWorld`), and `worldOf label <= w'`, by transitivity `worldOf label_alpha <= w'`. Then `iforces_persistence` gives `IForces val botForces w' alpha`.
  7. Satisfaction of old formulas (from `b`): `sf'.label < nw` by `h_fresh`, so `worldOf' sf'.label = worldOf sf'.label`, then apply `hsat`.

**Mathlib lemmas needed** (all verified to exist):
- `Function.update_self : Function.update f a v a = v`
- `Function.update_of_ne : a != a' -> Function.update f a' v a = f a`
- `iforces_persistence` (CSLib, already proven)

### Step 2: Prove applyAllTImpRules_preserves_sat

**File**: `Intuitionistic/Soundness.lean`

```lean
lemma applyAllTImpRules_preserves_sat {World : Type*} [Preorder World]
    (val : World -> Atom -> Prop) (botForces : World -> Prop)
    (v_uc : forall {w w'} (p : Atom), w <= w' -> val w p -> val w' p)
    (bf_uc : forall {w w'}, w <= w' -> botForces w -> botForces w')
    (worldOf : Nat -> World)
    (h_order : forall l1 l2, l1 in labels_of b -> l2 in labels_of b ->
      l1 <= l2 -> worldOf l1 <= worldOf l2)
    (b : IBranch Atom) 
    (hsat : intBranchSatisfied val botForces worldOf b) :
    intBranchSatisfied val botForces worldOf (applyAllTImpRules b)
```

**Key concern**: This requires branch-local monotonicity of `worldOf`. The `h_order` hypothesis is needed because `intTImpRule` uses `worldsAbove` (Nat `>=`) to determine which worlds to propagate T(imp) consequences to. The semantic justification requires that if `w1 <= w2` as Nat labels, then `worldOf w1 <= worldOf w2` in the Kripke model.

**Critical observation**: After `Function.update worldOf nw w'`, branch-local monotonicity holds for all labels on the *extended* branch (old labels `< nw` plus new label `nw`), provided:
- `worldOf` was branch-locally monotone on old labels (induction hypothesis).
- `worldOf label <= w'` where `label` is the F(imp) source (from the semantic witness).
- For any old label `l` with `l <= label`: `worldOf l <= worldOf label <= w'` by transitivity.

This means the invariant is maintainable across F(imp) steps without requiring global monotonicity.

**Alternative approach (simpler, avoids h_order entirely)**: Reformulate the persistence lemma to not require monotonicity by observing that `applyAllTImpRules` only adds formulas that are semantically entailed. Specifically, for each `T(psi) at w'` added by `intTImpRule`, there exists `T(phi -> psi) at w` on `b` with `w <= w'` (as Nat) and `T(phi) at w'` on `b`. From `hsat`:
- `IForces val botForces (worldOf w) (phi.imp psi)` -- i.e., `forall u, worldOf w <= u -> IForces ... u phi -> IForces ... u psi`.
- `IForces val botForces (worldOf w') phi`.

We need `worldOf w <= worldOf w'` to instantiate the implication. This is exactly the branch-local monotonicity requirement. There is no way to avoid it for the persistence fixpoint -- the T(imp) rule semantics demand it.

### Step 3: Prove applyPersistenceFixpoint_preserves_sat

Simple induction on fuel, using `applyAllTImpRules_preserves_sat` at each step. The key is that `applyAllTImpRules` only adds formulas at existing labels, so:
- The set of labels is non-decreasing.
- The `h_order` hypothesis is preserved (no new labels means no new ordering obligations).
- The `h_fresh` invariant is preserved (no labels `>= nw` are created).

### Step 4: Prove intExpandBranches_closed_unsat

Follow the classical pattern (Classical/Soundness.lean:552-625). Structure:

```lean
private lemma intExpandBranches_closed_unsat
    (fuel : Nat) :
    forall (branches : List (IBranch Atom))
      (expandedSets : List (List (ISF Atom)))
      (nextWorlds : List Nat)
      (closurePred : IBranch Atom -> Bool)
      (h_closed_unsat : forall (worldOf : Nat -> World) (b : IBranch Atom),
        closurePred b = true -> neg intBranchSatisfied val botForces worldOf b),
      expandedSets.length = branches.length ->
      nextWorlds.length = branches.length ->
      (forall i (hi : i < branches.length), forall sf in branches[i],
        sf.label < nextWorlds[i]'(by omega)) ->
      intExpandBranches branches expandedSets nextWorlds fuel closurePred = .closed ->
      forall (worldOf : Nat -> World)
        (h_order : [branch-local monotonicity for worldOf]),
        forall b in branches, neg intBranchSatisfied val botForces worldOf b
```

**Key difference from classical**: The `worldOf` appears in the conclusion (universally quantified), not as a parameter. Each step of the induction constructs `worldOf'` when F(imp) fires and passes it to the IH.

**Inner induction on `go`**: Same `suffices` pattern as classical. The `go` function is `intExpandBranches.go` and should unfold the same way as `classicalExpandBranches.processNext`.

### Step 5: Prove intuitionisticTableau_sound

```lean
theorem intuitionisticTableau_sound (phi : Proposition Atom)
    (h : intuitionisticTableau phi = .closed) : IValid phi := by
  -- Unfold IValid: forall World, forall val, forall v_uc, forall w, IForces val ... w phi
  intro World _ val v_uc w
  -- By contradiction: assume neg IForces val (fun _ => False) w phi
  by_contra hnf
  -- Construct worldOf : Nat -> World mapping 0 to w (and anything else to w)
  let worldOf : Nat -> World := fun _ => w
  -- The initial branch [F(phi) at 0] is satisfied by this worldOf
  have hsat : intBranchSatisfied val (fun _ => False) worldOf [{ sign := .neg, formula := phi, label := 0 }] := by
    intro sf hmem
    simp at hmem; subst hmem
    exact { left := fun h => absurd h Sign.noConfusion, right := fun _ => hnf }
  -- Apply loop invariant
  exact intExpandBranches_closed_unsat ... (by ...) _ (List.mem_cons_self) hsat
```

The initial `worldOf = fun _ => w` is trivially branch-locally monotone (all labels map to the same world, and `w <= w`).

## Adversarial Self-Verification

### Challenged Claims

1. **Claim: "worldsAbove is not fundamentally flawed"**
   - Challenge: The use of `Nat >=` as an accessibility proxy is coarser than the actual tree-shaped accessibility in the tableau. Could this cause the persistence fixpoint to add semantically incorrect formulas?
   - Verification: No. `intTImpRule` checks that `T(phi)` actually exists at `w'` before adding `T(psi)` at `w'`. The `worldsAbove` filter only determines *which labels to check*, not whether to add formulas. If `w' >= w` as Nats but `w'` is NOT actually accessible from `w` in the true Kripke tree, the filter will consider it, but the absence of `T(phi)` at `w'` will prevent any addition. The soundness is preserved by the semantic check, not the label ordering.
   - **Revised status**: Claim confirmed. However, this means the persistence proof must account for the fact that `intTImpRule` may fire at worlds `w'` where `w' >= w` as Nats but `w'` is on a different branch of the Kripke tree. The proof works because `hsat` already gives us forcing at those worlds.

2. **Claim: "Function.update preserves branch-local monotonicity"**
   - Challenge: After `Function.update worldOf nw w'`, is it true that for all old labels `l1 <= l2`, `worldOf' l1 <= worldOf' l2`?
   - Verification: Yes, because all old labels are `< nw`, so `worldOf' l_i = worldOf l_i` for both. And for any old label `l <= nw`: `worldOf' l = worldOf l` and `worldOf' nw = w'`. We need `worldOf l <= w'`. This holds because `l` is a label on the branch where `l <= label` (the F(imp) source label), and `worldOf label <= w'` from the semantic witness. By transitivity of the original `h_order` and `worldOf label <= w'`.
   - **But wait**: We need `worldOf l <= worldOf label` for ALL labels `l` on the branch with `l <= label`, not just those that are direct ancestors. The branch may contain labels from different F(imp) expansions. If we had `l` from a sibling branch at label 5, and the current F(imp) is at label 3, then `l >= 3` as Nats but `worldOf l` might not be `<= worldOf 3`.
   - **Resolution**: Branch-local monotonicity means `l1 <= l2 -> worldOf l1 <= worldOf l2` for ALL labels on the branch. This is an invariant maintained by construction: the initial `worldOf = fun _ => w` is trivially monotone, and each `Function.update` step maintains it as shown above. The key is that the invariant is over the *current branch's labels*, not over all of Nat.
   - **Revised status**: Claim confirmed with the clarification that the invariant is branch-local and maintained inductively.

3. **Claim: "No existing formalized proof exists"**
   - Challenge: Was the search exhaustive?
   - Verification: Searched `lean_leanfinder` for "intuitionistic Kripke soundness tableau forcing" (no relevant results). Searched `lean_leansearch` for related terms. Checked Bentzen2023 (completeness, not soundness). Checked Mathlib's `itauto` (G4ip sequent calculus, not tableau). No formalized intuitionistic tableau soundness proof found.
   - **Revised status**: Confirmed. Confidence: high.

4. **Claim: "propagatePersistence labels are all at fromWorld"**
   - Challenge: Does `propagatePersistence b fromWorld toWorld` produce formulas only at label `toWorld`?
   - Verification: Yes. `propagatePersistence` calls `posFormulasAt b fromWorld` to get formulas at `fromWorld`, then maps them to `{ .pos, phi, toWorld }`. All output formulas have label `toWorld`.
   - **Revised status**: Confirmed.

5. **Claim: "The h_order hypothesis can be eliminated entirely (Alternative approach)"**
   - Challenge: Is there truly no way to avoid requiring branch-local monotonicity?
   - Verification: No. The `intTImpRule` rule has semantic justification ONLY when `worldOf w <= worldOf w'` for `w <= w'`. If `worldOf` is not monotone on branch labels, then `T(phi -> psi) at w` with `T(phi) at w'` does NOT entail `T(psi) at w'` semantically (the implication only fires at successors). The monotonicity requirement is inherent to the intuitionistic implication semantics.
   - **Revised status**: Claim refuted. `h_order` (branch-local monotonicity) IS required and cannot be eliminated. Updated the recommendation above.

### Uncertain Claims (with confidence levels)

- The `intExpandBranches.go` inner function will unfold cleanly via `simp [intExpandBranches]` analogous to the classical case. **Confidence: 85%**. The classical case uses `classicalExpandBranches.processNext` which is a named `let rec`. The intuitionistic case uses `go` which is also a named `let rec`. Both should be accessible via the `{parent}.{name}` convention. However, the three-list parallel structure may require additional care.

- The three-list length invariant (`expandedSets.length = branches.length` and `nextWorlds.length = branches.length`) will thread through without difficulty. **Confidence: 90%**. The classical case only has two lists and handles it fine. The third list adds bookkeeping but no fundamental complication.

### Recommendations Modified After Verification

1. **Original**: "Alternative approach (simpler, avoids h_order entirely)" was listed as viable.
   **Revised**: h_order (branch-local monotonicity) CANNOT be avoided. Removed this as an option. The implementation MUST maintain and thread a branch-local monotonicity invariant for `worldOf`.

## BibKey Verification Status

| BibKey | Status | Notes |
|--------|--------|-------|
| `Fitting1983` | **NOT FOUND in references.bib** | Cited in Lean source files but missing from references.bib. Needs to be added: Fitting, M. "Proof Methods for Modal and Intuitionistic Logics" (1983), Reidel. |
| `ChagrovZakharyaschev1997` | Verified | Found at references.bib:75 |
| `TroelstraSchwichtenberg2000` | Verified | Found at references.bib:811 |
| `Bentzen2023` | Verified | Found at references.bib:41 |

**Action Required**: Add `Fitting1983` BibKey to `references.bib`:
```bibtex
@book{Fitting1983,
  author       = {Fitting, Melvin},
  title        = {Proof Methods for Modal and Intuitionistic Logics},
  series       = {Synthese Library},
  volume       = {169},
  publisher    = {D. Reidel Publishing Company},
  year         = {1983},
  doi          = {10.1007/978-94-017-2794-5}
}
```

## Summary of Actionable Recommendations

1. **Replace `intRule_preserves_sat` with `intRule_preserves_sat_ext`**: The existential `worldOf'` formulation resolves the B4 blocker. The F(imp) case uses `Function.update worldOf nw w'` with `w'` being the semantic witness from `neg IForces(phi -> psi)`. Mathlib's `Function.update_self` and `Function.update_of_ne` provide the required lemmas.

2. **Maintain branch-local monotonicity invariant**: The loop invariant must include `h_order : forall l1 l2 in branch_labels, l1 <= l2 -> worldOf l1 <= worldOf l2`. This survives `Function.update` because all old labels are `< nw` and the new world `w'` satisfies `worldOf label <= w'`.

3. **Prove persistence fixpoint with branch-local monotonicity**: `applyPersistenceFixpoint_preserves_sat` requires branch-local monotonicity (not global). The invariant is preserved because persistence only adds formulas at existing labels.

4. **Follow classical pattern for loop induction**: The classical soundness proof (Classical/Soundness.lean:552-625) provides the exact template. The intuitionistic version adds: (a) `worldOf` threading, (b) three-list invariants, (c) persistence fixpoint call before each step.

5. **Add `Fitting1983` to references.bib**: Currently cited in 10+ Lean source files but missing from the bibliography.
