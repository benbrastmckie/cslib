# Research Report: Propositional Tableau Decidability (Task 298)

## 1. Foundations Tableau Infrastructure (Task 297 Output)

### 1.1 Core Types

All types live in `Cslib.Logic.Tableau` namespace under `Cslib/Foundations/Logic/Tableau/`.

| File | Key Type | Description |
|------|----------|-------------|
| `Sign.lean` | `Sign` | Two-element `{pos, neg}` with `flip`, `isPos`, `isNeg`; derives `DecidableEq, BEq, Hashable` |
| `SignedFormula.lean` | `SignedFormula F L` | Structure with `.sign : Sign`, `.formula : F`, `.label : L`; derives `DecidableEq, BEq, Hashable` |
| `RuleResult.lean` | `RuleResult F L` | Inductive: `linear`, `branching`, `persistent`, `notApplicable` |
| `Branch.lean` | `Branch F L` | Abbreviation for `List (SignedFormula F L)` |
| `Closure.lean` | `ClosureReason F L` | Inductive: `botPos l`, `contradiction phi l`, `atomContradiction p l` |
| `ClosureCondition.lean` | `ClosureCondition F L` | Typeclass with `findClosure : Branch F L -> Option (ClosureReason F L)` |
| `PropositionalRules.lean` | `PropTableauRule` | 8-constructor enum for prop rules; `applyPropRule` and `tryAllPropRules` |

### 1.2 Closure Condition Instances

Three pre-built instances in namespaced sections of `ClosureCondition.lean`:

- **`ClassicalClosure.instance`**: `[BEq F] [BEq L] [HasBot F]` -- closes on T(bot) OR T(phi)/F(phi) at same label
- **`IntuitionisticClosure.instance`**: `[BEq F] [HasBot F]` -- closes on T(bot) only (no `BEq L` needed since only checking formula identity)
- **`MinimalClosure.instance`**: `[BEq F] [BEq L] [IsAtomic F]` -- closes on T(p)/F(p) for atomic p at same label

**Critical Design Note**: The closure instances live in their own namespaces (`ClassicalClosure`, `IntuitionisticClosure`, `MinimalClosure`). Since they all produce `ClosureCondition F L`, they CANNOT coexist as global instances. Each tableau system must open the appropriate namespace or use local instances.

### 1.3 Propositional Rule Application

`applyPropRule` takes four decomposition functions:
```
andOf? : F -> Option (F x F)
orOf?  : F -> Option (F x F)
impOf? : F -> Option (F x F)
negOf? : F -> Option F
```

For `PL.Proposition`, these map directly:
- `andOf?` matches `.and a b => some (a, b)`
- `orOf?` matches `.or a b => some (a, b)`
- `impOf?` matches `.imp a b => some (a, b)`
- `negOf?` matches `.imp a .bot => some a` (since neg is abbreviation for `imp _ .bot`)

All rules preserve the label from the input signed formula (no new world creation).

### 1.4 IsAtomic Typeclass

```lean
class IsAtomic (F : Type*) where
  isAtom : F -> Bool
```

For `PL.Proposition Atom`, the natural instance is:
```lean
instance : IsAtomic (PL.Proposition Atom) where
  isAtom
    | .atom _ => true
    | _ => false
```

### 1.5 Missing Infrastructure for Proposition

**`Hashable` instance**: `PL.Proposition Atom` derives `DecidableEq` and `BEq` but NOT `Hashable`. The `SignedFormula F L` structure derives `Hashable` from its components, which requires `Hashable F` and `Hashable L`. We need to add a `Hashable` instance for `Proposition` (either via `deriving` or manual definition). Since `Proposition` has 5 constructors with recursive structure, a manual `Hashable` instance mixing constructor tags is straightforward.

**`Repr` instance**: Not strictly needed for the algorithm but useful for debugging. Can be deferred.

## 2. Propositional Logic Infrastructure

### 2.1 Proposition Type

```lean
inductive Proposition (Atom : Type u) : Type u where
  | atom (x : Atom)
  | bot
  | imp (a b : Proposition Atom)
  | and (a b : Proposition Atom)
  | or (a b : Proposition Atom)
deriving DecidableEq, BEq
```

Key derived connectives:
- `neg := fun phi => imp phi .bot` (abbreviation)
- `top := .imp .bot .bot` (abbreviation)

Typeclass instances: `Bot`, `Top`, `PropositionalConnectives`, `HasAnd`, `HasOr`.

### 2.2 Axiom Systems

| Axiom Set | Constructors | Key Difference |
|-----------|-------------|----------------|
| `MinPropAxiom` | 8 (implyK, implyS, andI, andE1, andE2, orI1, orI2, orE) | No efq, no peirce |
| `IntPropAxiom` | 9 (+ efq) | No peirce |
| `PropositionalAxiom` | 10 (+ efq + peirce) | Full classical |

Subsumption: `MinPropAxiom.toIntPropAxiom` and `IntPropAxiom.toPropAxiom`.

### 2.3 Semantic Definitions

**Classical (Boolean)**:
- `Evaluate : Valuation Atom -> Proposition Atom -> Prop` (Prop-valued, recursive)
- `BoolEvaluate : BoolValuation Atom -> Proposition Atom -> Bool` (computable)
- `Tautology phi := forall v, Evaluate v phi`
- Bridge: `BoolEvaluate_eq_iff`, `instDecidableTautology [Fintype Atom]`

**Kripke (Intuitionistic/Minimal)**:
- `IForces [Preorder World] (v : World -> Atom -> Prop) (bot_forces : World -> Prop) (w : World) : Proposition Atom -> Prop`
  - atom: `v w p`
  - bot: `bot_forces w`
  - imp: `forall w' >= w, IForces w' phi -> IForces w' psi`
  - and: conjunction
  - or: disjunction
- `IValid phi := forall World [Preorder] val v_uc w, IForces val (fun _ => False) w phi`
- `MValid phi := forall World [Preorder] val bot_forces v_uc bf_uc w, IForces val bot_forces w phi`
- `mvalid_implies_ivalid`: MValid -> IValid (since IValid is MValid with `bot_forces = fun _ => False`)

### 2.4 Existing Decidability

**Classical only**: `instDecidableDerivablePropositionalAxiom [Fintype Atom] [DecidableEq Atom]` via:
1. `prop_completeness_iff_tautology : Tautology phi <-> Derivable PropositionalAxiom phi`
2. `instDecidableTautology` (enumerate 2^n Boolean valuations)

**Intuitionistic and Minimal**: NO existing decidability instances. The completeness theorems (`int_soundness_completeness`, `min_soundness_completeness`) establish IValid <-> Derivable and MValid <-> Derivable, but these quantify over ALL Kripke models (uncountable), so they don't directly yield decidability. The tableau is the path to decidability.

### 2.5 Soundness/Completeness Bridge

| Logic | Soundness | Completeness | Equivalence |
|-------|-----------|--------------|-------------|
| Classical | `prop_soundness_tautology` | `prop_completeness` | `prop_completeness_iff_tautology : Tautology <-> Derivable PropositionalAxiom` |
| Intuitionistic | `int_soundness_derivable` | `int_completeness` | `int_soundness_completeness : IValid <-> Derivable IntPropAxiom` |
| Minimal | `min_soundness_derivable` | `min_completeness` | `min_soundness_completeness : MValid <-> Derivable MinPropAxiom` |

The tableau decidability results will produce:
- Classical: `Decidable (Tautology phi)` (already exists via enumeration, but tableau provides alternative)
- Intuitionistic: `Decidable (IValid phi)` (NEW, via finite model property)
- Minimal: `Decidable (MValid phi)` (NEW, via finite model property)

## 3. Design Strategy for Three Tableau Systems

### 3.1 Classical Tableau (L = Unit)

**Label type**: `Unit` -- all formulas share one implicit world.

**Closure**: `ClassicalClosure` instance (T(bot) or complementary pair at same label).

**Rules**: Standard 8 propositional rules from `PropositionalRules.lean`, plus:
- `negOf?` for `Proposition` must handle `neg phi = imp phi .bot` pattern

**Decomposition functions for Proposition**:
```lean
def propAndOf? : Proposition Atom -> Option (Proposition Atom x Proposition Atom)
  | .and a b => some (a, b)
  | _ => none

def propOrOf? : Proposition Atom -> Option (Proposition Atom x Proposition Atom)
  | .or a b => some (a, b)
  | _ => none

def propImpOf? : Proposition Atom -> Option (Proposition Atom x Proposition Atom)
  | .imp a b => some (a, b)
  | _ => none

def propNegOf? : Proposition Atom -> Option (Proposition Atom)
  | .imp a .bot => some a
  | _ => none
```

**Important**: `negOf?` must NOT match arbitrary `imp a b` -- only `imp a .bot`. This prevents the `impPos` rule from overlapping with `negPos`. The `impPos` rule handles all implications; `negPos` handles only negations. Since `neg` is defined as `imp _ .bot`, BOTH `impOf?` and `negOf?` will match on negations. The implementation should try `negOf?` FIRST (more specific) and fall back to `impOf?` only if `negOf?` fails. Actually, looking at `applyPropRule`, each rule tries its own decomposer independently -- `negPos` uses `negOf?` and `impPos` uses `impOf?`. For `T(neg phi) = T(imp phi .bot)`:
- `negPos` matches: `negOf? (imp phi .bot) = some phi` -> linear [F(phi)]
- `impPos` also matches: `impOf? (imp phi .bot) = some (phi, .bot)` -> branching [F(phi), T(.bot)]

Both give equivalent results (F(phi) is the useful content; T(.bot) immediately closes or is useless), but `tryAllPropRules` returns the first match, which is `andPos` (first in the list). Actually the rule list is `[andPos, andNeg, orPos, orNeg, impPos, impNeg, negPos, negNeg]`, so `impPos` comes before `negPos`. For classical logic this is fine (the branching to T(.bot) is harmless -- that branch closes immediately or we get F(phi) anyway). But for efficiency, we might want to reorder or handle negation specially.

**Decision**: Use `tryAllPropRules` as-is for classical. The slight inefficiency of branching on negation (instead of linear decomposition) is acceptable. An optimization pass can reorder later.

**Termination**: Subformula property. Every rule produces signed formulas whose formula component is a proper subformula of the input. Since `Proposition` is well-founded, expansion terminates. Fuel = `sizeOf phi` (or a suitable formula complexity measure).

**Soundness bridge**: Closed tableau -> for every valuation, some branch closes -> no valuation satisfies F(phi) -> Tautology phi.

**Completeness bridge**: Open saturated branch -> construct Boolean valuation -> countermodel. Atom `p` is true iff T(atom p) is on the branch.

**Decidable instance delivery**:
```lean
instance [Fintype Atom] [DecidableEq Atom] [Hashable Atom] :
    Decidable (Tautology phi) := ...
-- And via prop_completeness_iff_tautology:
instance [Fintype Atom] [DecidableEq Atom] [Hashable Atom] :
    Decidable (Derivable PropositionalAxiom phi) := ...
```

Note: The classical `instDecidableTautology` already exists without Hashable. The tableau provides an alternative decision procedure but doesn't replace the enumeration-based one. The real value is validating the infrastructure for the intuitionistic/minimal cases.

### 3.2 Intuitionistic Tableau (L = Nat)

**Label type**: `Nat` -- each natural number indexes a world in the constructed Kripke premodel.

**Closure**: `IntuitionisticClosure` instance (T(bot) at any label only; complementary pairs do NOT close).

**Rules**: Same 8 propositional rules EXCEPT `T(phi -> psi)` (impPos) which must be modified:

**Classical impPos**: `T(phi -> psi) at label l` -> branch: `[F(phi) at l]` or `[T(psi) at l]`
**Intuitionistic impPos**: `T(phi -> psi) at label l` -> for each label l' >= l on the branch, if T(phi) at l', then add T(psi) at l'. This is a PERSISTENT rule (it must be re-applied when new worlds are created).

Actually, the intuitionistic tableau for propositional logic works differently from the classical one. The standard Fitting-style approach:

**Intuitionistic T(phi -> psi) at world w**:
- This is a "universal" rule: for every world w' >= w on the branch, if T(phi) at w', derive T(psi) at w'.
- It is persistent (must be re-checked when new worlds appear).

**Intuitionistic F(phi -> psi) at world w**:
- Create a NEW world w' > w, add T(phi) at w', F(psi) at w'.
- Also propagate all T-formulas from w to w' (persistence/upward-closure).

**Intuitionistic F(phi or psi) at world w**: F(phi) at w, F(psi) at w (linear, same as classical)
**Intuitionistic T(phi or psi) at world w**: T(phi) at w OR T(psi) at w (branching, same as classical)
**Intuitionistic F(phi and psi) at world w**: F(phi) at w OR F(psi) at w (branching, same as classical)
**Intuitionistic T(phi and psi) at world w**: T(phi) at w, T(psi) at w (linear, same as classical)
**Intuitionistic T(bot) at world w**: Branch closes (intuitionistic closure)
**Intuitionistic F(bot) at world w**: No rule needed (F(bot) is trivially satisfied)

The key difference is the implication rules. The classical `impPos` (branching) must be replaced by a world-creating persistent rule.

**Persistence propagation**: When a new world w' is created as a successor of w, ALL positive signed formulas at w must be propagated to w'. This is because Kripke models have upward-closed valuations. Specifically:
- All `T(atom p)` at w propagate to w'
- All `T(phi -> psi)` at w propagate to w' (they are universally quantified over successors)
- All `T(phi and psi)` at w need NOT propagate (but their components do via the above)
- Actually, the persistence lemma says ALL `T(phi)` propagate to successor worlds. So we propagate all positive formulas.

**However**: Propagating all T-formulas is not how efficient intuitionistic tableaux work. The standard approach (Fitting 1983, Chapter 6) uses the following:

For each world w on the branch, maintain a set of "formulas forced at w". The key rules:
- `F(phi -> psi)` at w: create w' > w with `T(phi)` at w' and `F(psi)` at w'. Copy all `T(alpha)` from w to w' where alpha is an implication or atom (not compound -- those are decomposed first).
- `T(phi -> psi)` at w: for each existing w' >= w with `T(phi)` at w', add `T(psi)` at w'. This is persistent.

**Finite Model Property**: The number of worlds is bounded by the number of subformulas. Each world is characterized by the set of subformulas forced at it. By the subformula property, there are at most 2^n possible world types where n = |subformulas(phi)|. So the search terminates.

**Fuel computation**: `fuel = 2^(2*n)` where n = number of distinct subformulas of the input formula. This is generous but ensures termination. A tighter bound uses the actual number of possible branch states.

**Soundness bridge**: Closed tableau -> IValid phi. Proved by showing every rule is IValid-preserving.

**Completeness bridge**: Open saturated branch -> construct finite Kripke model from the branch -> countermodel for IValid phi. The worlds are the labels appearing on the branch; the accessibility relation is the ordering induced by world creation; the valuation is `v(w, p) = T(atom p) at w is on branch`.

### 3.3 Minimal Tableau (L = Nat)

**Label type**: Same as intuitionistic (`Nat`).

**Rules**: IDENTICAL to intuitionistic tableau rules. The ONLY difference is the closure condition.

**Closure**: `MinimalClosure` instance -- closes on `T(p)/F(p)` for atomic p at same label only. No T(bot) closure, no complementary closure on compound formulas.

**This means**: A branch with `T(bot)` at some world does NOT close in minimal logic. A branch with `T(phi)/F(phi)` for non-atomic `phi` does NOT close.

**Code sharing**: The intuitionistic and minimal tableaux share ALL expansion code. The only parameter that differs is the `ClosureCondition` instance. This is exactly what the typeclass design enables.

**Soundness bridge**: Closed tableau -> MValid phi. Proved by showing rules preserve forcing in models with arbitrary upward-closed `bot_forces`.

**Completeness bridge**: Open saturated branch -> construct finite Kripke model where `bot_forces w = T(bot) at w on branch` -> countermodel for MValid phi.

### 3.4 Code Sharing Analysis

| Component | Classical | Intuitionistic | Minimal |
|-----------|-----------|----------------|---------|
| Label type | `Unit` | `Nat` | `Nat` |
| Closure condition | ClassicalClosure | IntuitionisticClosure | MinimalClosure |
| Prop decomposers | shared | shared | shared |
| And/Or rules | shared (`applyPropRule`) | shared | shared |
| Imp rules | classical (`applyPropRule`) | CUSTOM world-creating | same as intuitionistic |
| Neg rules | shared (`applyPropRule`) | shared | shared |
| Persistence | none | CUSTOM propagation | same as intuitionistic |
| Expansion loop | simple fuel-based | fuel-based + persistence | same as intuitionistic |
| Soundness | Boolean semantics | Kripke semantics | Kripke semantics |
| Completeness | Boolean countermodel | Kripke countermodel | Kripke countermodel |

**Key insight**: Intuitionistic and minimal share ~95% of code (same rules, same expansion, same countermodel construction). The only difference is the `ClosureCondition` instance. Classical is simpler (no world creation, no persistence) and shares the decomposition functions but has its own expansion loop.

## 4. File Organization

### 4.1 Proposed Directory Structure

```
Cslib/Logics/Propositional/Tableau/
  Defs.lean                  -- Proposition-specific decomposers, IsAtomic, Hashable instances
  Classical/
    Expansion.lean           -- Classical expansion loop (fuel-based, L = Unit)
    Soundness.lean           -- Closed tableau -> Tautology
    Completeness.lean        -- Open branch -> countermodel
    DecisionProcedure.lean   -- Decidable (Tautology phi), Decidable (Derivable PropositionalAxiom phi)
  Intuitionistic/
    Rules.lean               -- World-creating imp rules, persistence propagation
    Expansion.lean           -- Intuitionistic expansion loop (fuel-based, L = Nat)
    Soundness.lean           -- Closed tableau -> IValid
    Completeness.lean        -- Open branch -> Kripke countermodel
    DecisionProcedure.lean   -- Decidable (IValid phi), Decidable (Derivable IntPropAxiom phi)
  Minimal/
    DecisionProcedure.lean   -- Decidable (MValid phi), Decidable (Derivable MinPropAxiom phi)
                             -- (reuses Intuitionistic expansion with MinimalClosure)
```

### 4.2 Import Chain

```
Foundations/Logic/Tableau/PropositionalRules.lean  (provides applyPropRule, tryAllPropRules)
  |
  v
Propositional/Tableau/Defs.lean  (Proposition-specific decomposers, instances)
  |
  +---> Classical/Expansion.lean ---> Classical/Soundness.lean ---> Classical/DecisionProcedure.lean
  |                                   Classical/Completeness.lean --|
  |
  +---> Intuitionistic/Rules.lean ---> Intuitionistic/Expansion.lean
  |                                       |
  |                                       +---> Intuitionistic/Soundness.lean ---> Intuitionistic/DecisionProcedure.lean
  |                                       +---> Intuitionistic/Completeness.lean --|
  |
  +---> Minimal/DecisionProcedure.lean (imports Intuitionistic/Expansion + ClosureCondition)
```

## 5. Critical Design Decisions

### 5.1 Negation Handling

`Proposition.neg phi` is defined as `Proposition.imp phi .bot` (an `abbrev`). This means:
- Pattern matching on `neg` requires matching on `.imp _ .bot`
- `negOf?` must match `.imp a .bot => some a`
- `impOf?` also matches on `.imp a .bot => some (a, .bot)`

For correctness, BOTH matches are fine. The `tryAllPropRules` function will find `impPos` first (it's earlier in the rule list) for `T(neg phi)`, which gives branching `[F(phi), T(.bot)]`. The `T(.bot)` branch immediately closes (classically) or is irrelevant. So classical correctness is maintained.

For intuitionistic/minimal, the `negPos` rule should be preferred (it gives the linear result `F(phi)` directly). The custom intuitionistic rules should handle negation specially: `T(neg phi)` at w should be treated as `T(phi -> bot)` and the implication rule applied (which means: for any successor w' where T(phi) holds, add T(bot) at w', which may or may not close depending on the closure condition).

### 5.2 ClosureCondition Instance Selection

Since `ClassicalClosure`, `IntuitionisticClosure`, and `MinimalClosure` all provide `ClosureCondition F L`, they conflict as global instances. The solution:

**Option A**: Use explicit local instances via `letI` or `haveI` at the call site.
**Option B**: Create wrapper types: `ClassicalTableau`, `IntuitionisticTableau`, `MinimalTableau` that carry the closure condition.
**Option C**: Pass the closure condition explicitly as a parameter (not via typeclass).

**Recommendation**: Option C (explicit parameter) for the expansion functions, with convenience wrappers that fix the closure condition for each logic. This matches the bimodal pattern where `FrameClass` is an explicit parameter.

### 5.3 Hashable Instance for Proposition

Required for `SignedFormula (Proposition Atom) L` to derive `Hashable`, which enables efficient hash-based duplicate detection in the `AppliedSet` pattern.

```lean
instance [Hashable Atom] : Hashable (Proposition Atom) where
  hash
    | .atom x => mixHash 0 (hash x)
    | .bot => 1
    | .imp a b => mixHash 2 (mixHash (hash a) (hash b))
    | .and a b => mixHash 3 (mixHash (hash a) (hash b))
    | .or a b => mixHash 4 (mixHash (hash a) (hash b))
```

### 5.4 Formula Size / Subformula Count

For fuel computation, we need a size measure on `Proposition`:
```lean
def Proposition.complexity : Proposition Atom -> Nat
  | .atom _ => 1
  | .bot => 1
  | .imp a b => 1 + a.complexity + b.complexity
  | .and a b => 1 + a.complexity + b.complexity
  | .or a b => 1 + a.complexity + b.complexity
```

Classical fuel: `complexity phi` (each rule strictly reduces complexity).
Intuitionistic/minimal fuel: `2 ^ (2 * complexity phi)` (accounts for world creation bounded by finite model property).

### 5.5 Intuitionistic Implication Rule Design

The key challenge is implementing the intuitionistic `T(phi -> psi)` rule correctly:

**Approach A (Fitting-style)**: `T(phi -> psi)` at w is persistent. Whenever T(phi) appears at any w' >= w, add T(psi) at w'. This requires tracking the accessibility relation and re-checking persistent formulas.

**Approach B (One-shot world creation)**: When processing `T(phi -> psi)` at w:
1. For each existing w' >= w on the branch: if T(phi) at w', add T(psi) at w'.
2. Mark the formula as persistent for future world creations.

The `RuleResult.persistent` variant from the infrastructure supports this: it signals that the formula should be kept for re-application.

**For F(phi -> psi) at w**: Create fresh world w' with successor relation w < w'. Add T(phi) at w', F(psi) at w'. Propagate all T(alpha) from w to w' (for atoms and implications -- by persistence of forcing).

## 6. Soundness and Completeness Proof Strategy

### 6.1 Classical Soundness

**Theorem**: If the classical tableau for F(phi) (started with `[SignedFormula.neg phi ()]`) closes, then `Tautology phi`.

**Proof sketch**:
1. Define `branchSatisfiable b v := forall sf in b, if sf.sign = pos then Evaluate v sf.formula else not (Evaluate v sf.formula)`.
2. Show each classical rule preserves satisfiability (contrapositively: if all output branches are satisfiable, then the input branch was satisfiable).
3. A closed branch (containing T(phi)/F(phi) or T(bot)) is unsatisfiable.
4. By induction on the tableau, the initial branch `[F(phi)]` is unsatisfiable -> `not (Evaluate v phi)` is impossible for all v -> `Tautology phi`.

### 6.2 Classical Completeness

**Theorem**: If the classical tableau for F(phi) produces an open saturated branch, then `not (Tautology phi)`.

**Proof sketch**:
1. From open branch, define `v(p) := T(atom p) is on the branch`.
2. Show by induction on formula structure: T(alpha) on branch -> Evaluate v alpha; F(alpha) on branch -> not (Evaluate v alpha).
3. Since F(phi) is on the initial branch, `not (Evaluate v phi)`, so phi is not a tautology.

### 6.3 Intuitionistic Soundness

**Theorem**: If the intuitionistic tableau for F(phi) at world 0 closes, then `IValid phi`.

**Proof sketch**:
1. For any Kripke model (W, <=, v) and world w, define `branchSatisfied` as: for all `T(alpha) at l` on branch, `IForces v bf w_l alpha`; for all `F(alpha) at l` on branch, `not (IForces v bf w_l alpha)` -- where `w_l` is the world in the model corresponding to label l.
2. Show each rule preserves satisfiability (using Kripke semantics properties: persistence, implication semantics).
3. Closed branch (T(bot) at some label) is unsatisfiable (since `bf = fun _ => False`).
4. By induction, initial branch is unsatisfiable -> IValid phi.

### 6.4 Intuitionistic Completeness

**Theorem**: If the intuitionistic tableau for F(phi) at world 0 produces an open saturated branch, then `not (IValid phi)`.

**Proof sketch**:
1. The labels on the branch form a finite preordered set (world creation introduces strict ordering).
2. Define Kripke model: worlds = labels on branch, l1 <= l2 iff l2 was created as a successor of l1 (reflexive-transitive closure), v(l, p) = T(atom p) at l on branch.
3. Verify upward-closure of v (follows from persistence propagation).
4. Truth lemma: T(alpha) at l on branch -> IForces v bf l alpha; F(alpha) at l on branch -> not (IForces v bf l alpha).
5. Since F(phi) at 0 on branch: not (IForces v bf 0 phi), so phi is not IValid.

### 6.5 Minimal Soundness/Completeness

Same as intuitionistic, but:
- `bot_forces w := T(.bot) at w is on branch` (NOT `fun _ => False`)
- Closure condition is atom-only, so the soundness proof must show that complementary atoms lead to contradiction in models with arbitrary `bot_forces`
- The countermodel uses `bot_forces` that reflects the branch content

## 7. Estimated Line Counts

| Component | Lines |
|-----------|-------|
| Defs.lean (decomposers, instances) | 80-120 |
| Classical/Expansion.lean | 150-200 |
| Classical/Soundness.lean | 200-300 |
| Classical/Completeness.lean | 200-300 |
| Classical/DecisionProcedure.lean | 80-120 |
| Intuitionistic/Rules.lean | 150-200 |
| Intuitionistic/Expansion.lean | 200-300 |
| Intuitionistic/Soundness.lean | 250-350 |
| Intuitionistic/Completeness.lean | 300-400 |
| Intuitionistic/DecisionProcedure.lean | 80-120 |
| Minimal/DecisionProcedure.lean | 80-150 |
| **Total** | **1,770-2,560** |

This aligns with the task estimate of 2,000-2,800 lines.

## 8. Blockers and Risks

### 8.1 No Blockers

Task 297 infrastructure is complete and provides all needed types and typeclasses. The propositional logic infrastructure is mature with soundness/completeness theorems already proved.

### 8.2 Risks

1. **Intuitionistic completeness proof complexity**: The countermodel construction from an open branch requires careful handling of the accessibility relation and the truth lemma. This is the most complex proof in the task.

2. **Persistence propagation correctness**: Getting the intuitionistic persistence rules right (what to propagate when creating new worlds) is subtle. Propagating too little breaks soundness; propagating too much breaks termination.

3. **ClosureCondition instance conflicts**: The three closure instances must be carefully scoped to avoid Lean typeclass resolution conflicts.

4. **Fuel bound tightness**: For the intuitionistic/minimal case, the fuel must be large enough to guarantee saturation but not so large that the algorithm is impractical. The finite model property gives a theoretical bound of `2^n` worlds for n subformulas, but the actual fuel depends on the branching factor.

## 9. Tactic Survey

For the proof obligations identified above:

- **Structural induction on Proposition**: `induction phi` followed by `simp` for base cases. Standard pattern used throughout the codebase.
- **Case analysis on Sign**: `cases sf.sign` followed by `simp`. Well-established pattern.
- **Fuel termination**: `termination_by fuel` with `decreasing_by simp_wf`. Matches bimodal pattern.
- **Kripke semantics reasoning**: Manual `intro`/`apply`/`exact` following the existing soundness proof patterns in `IntSoundness.lean` and `MinSoundness.lean`.
- **Boolean decidability**: `decide` for finite enumeration, `simp` with bridge lemmas.

## 10. Summary

The task is well-scoped and has no blockers. The Foundations tableau infrastructure provides all necessary types and typeclasses. The classical tableau is the simplest (validates infrastructure), the intuitionistic adds world-creation and persistence (the main complexity), and the minimal reuses the intuitionistic with a different closure condition (minimal new code).

Key deliverables:
1. `Decidable (Tautology phi)` via tableau (alternative to existing enumeration-based instance)
2. `Decidable (IValid phi)` via intuitionistic tableau (NEW -- does not exist in CSLib)
3. `Decidable (MValid phi)` via minimal tableau (NEW -- does not exist in CSLib)
4. `Decidable (Derivable IntPropAxiom phi)` and `Decidable (Derivable MinPropAxiom phi)` via completeness bridges
