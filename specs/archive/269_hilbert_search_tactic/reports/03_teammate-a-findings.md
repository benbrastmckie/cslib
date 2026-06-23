# Teammate A Findings: Lean 4 Tactic Implementation Patterns for hilbert_search

**Task 269**: Build generic bounded proof-search tactic for InferenceSystem
**Role**: Lean 4 tactic implementation patterns -- concrete MetaM/TacticM code (Round 2)
**Date**: 2026-06-23

---

## 1. CSLib Infrastructure Analysis

### 1.1 InferenceSystem and DerivableIn

The core abstraction is in `Cslib/Foundations/Logic/InferenceSystem.lean`:

```lean
class InferenceSystem (S : Type*) (α : Type*) where
  derivation (a : α) : Sort v

def DerivableIn S [InferenceSystem S α] (a : α) := Nonempty (S⇓a)
```

**Key structural property for tactic implementation**: `DerivableIn S a` is `Nonempty (S⇓a)`.
At the Expr level, this means goals appear as
`@InferenceSystem.DerivableIn.{u1, u2} α S inst φ` -- an application with 4 arguments
(where `α`, `S`, `inst` are implicit and `φ` is the formula being proved derivable).

The entire proof system algebra operates at the `DerivableIn` level (not at the raw
derivation level), which means the tactic can work entirely with `DerivableIn` without
unwrapping `Nonempty`.

### 1.2 Proof System Hierarchy

The bundled classes in `ProofSystem.lean` form a clean inheritance chain:

```
MinimalHilbert S         -- ImplyK, ImplyS, MP
  └── IntuitionisticHilbert S  -- + EFQ
       └── ClassicalHilbert S      -- + Peirce
            ├── ModalHilbert S         -- + K, Necessitation
            │   ├── ModalTHilbert S        -- + T
            │   ├── ModalS4Hilbert S       -- + T, 4
            │   └── ModalS5Hilbert S       -- + T, 4, B
            └── TemporalBXHilbert S    -- + temporal axioms, temporal necessitation
                 └── BimodalTMHilbert S    -- + modal S5 + interaction
```

**For tactic implementation**: The tactic should try axioms conditionally based on available
typeclass instances. This means using `observing?` with `mkConstWithFreshMVarLevels` for
each axiom -- if the typeclass doesn't exist, the apply will fail and `observing?` rolls back.

### 1.3 Connective Typeclasses (Formula Structure)

Formulas use atomic connective typeclasses (`Connectives.lean`):

| Class | Arity | `isAppOfArity` | Description |
|-------|-------|----------------|-------------|
| `HasBot.bot` | 0 args (2 with implicit) | `isAppOfArity ``HasBot.bot 2` | Falsum |
| `HasImp.imp` | 2 args (4 with implicit) | `isAppOfArity ``HasImp.imp 4` | Implication |
| `HasBox.box` | 1 arg (3 with implicit) | `isAppOfArity ``HasBox.box 3` | Necessity |
| `HasDia.dia` | 1 arg (3 with implicit) | `isAppOfArity ``HasDia.dia 3` | Possibility |
| `HasUntil.untl` | 2 args (4 with implicit) | `isAppOfArity ``HasUntil.untl 4` | Until |
| `HasSince.snce` | 2 args (4 with implicit) | `isAppOfArity ``HasSince.snce 4` | Since |
| `HasAnd.and` | 2 args (4 with implicit) | `isAppOfArity ``HasAnd.and 4` | Conjunction |
| `HasOr.or` | 2 args (4 with implicit) | `isAppOfArity ``HasOr.or 4` | Disjunction |

**These do NOT require the `HasImpView`/`HasBoxView` typeclasses** discussed in Round 1.
The connective typeclasses already exist and are sufficient for formula decomposition at the
Expr level using `isAppOfArity` and `getAppArgs`. The "view" typeclasses mentioned in Round 1
would be needed for a term-mode search function that pattern-matches on formula values at
runtime, but the MetaM tactic approach matches on Expr structure directly.

### 1.4 Bimodal AxiomMatcher Pattern

`Cslib/Logics/Bimodal/Metalogic/Decidability/AxiomMatcher.lean` implements a **term-mode**
axiom matcher (not tactic-mode). It pattern-matches on `Formula Atom` constructors
(`.imp`, `.box`, `.bot`, etc.) and returns `Option (AxiomWitness Atom)`.

**Relevance to hilbert_search**: This pattern is specific to the bimodal logic's concrete
formula type. The generic tactic cannot replicate this directly because `InferenceSystem`
is opaque about the formula structure. Instead, the tactic uses the typeclass-based approach
(trying `HasAxiomK.K` etc. via `apply`) which works generically across all formula types.

### 1.5 BimodalLogic ProofExtraction (buildCompositionalProof)

`ProofExtraction.lean` shows the fuel-based recursive proof construction pattern:

```lean
def buildCompositionalProof (phi : Formula Atom) (fuel : Nat) :
    Option (DerivationTree .Base ([] : Context Atom) phi) :=
  if fuel = 0 then none
  else
    match tryAxiomProof phi with
    | some proof => some proof
    | none =>
    match phi with
    | .box inner => ...  -- recursion on inner
    | .imp a b => ...    -- recursion on a, b
    | _ => none
```

This is the term-mode analog of what `hilbert_search` does in tactic-mode. The key
difference: the tactic version uses `MVarId.apply` + `observing?` instead of pattern
matching on formula constructors directly.

---

## 2. Key Lean 4 MetaM/TacticM APIs

### 2.1 Core APIs with Verified Signatures

All signatures verified via `#check` in a live Lean session:

| API | Signature | Purpose |
|-----|-----------|---------|
| `MVarId.getType` | `MVarId -> MetaM Expr` | Get goal type |
| `MVarId.assign` | `MVarId -> Expr -> m Unit` | Assign proof to goal |
| `MVarId.apply` | `MVarId -> Expr -> ApplyConfig -> MetaM (List MVarId)` | Apply term, get subgoals |
| `MVarId.withContext` | `MVarId -> n α -> n α` | Run in goal's local context |
| `MVarId.isAssigned` | `MVarId -> m Bool` | Check if goal is solved |
| `mkConstWithFreshMVarLevels` | `Name -> MetaM Expr` | Create const with fresh universe vars |
| `mkAppM` | `Name -> Array Expr -> MetaM Expr` | Build application with unification |
| `isDefEq` | `Expr -> Expr -> MetaM Bool` | Definitional equality check |
| `inferType` | `Expr -> MetaM Expr` | Infer type of expression |
| `whnf` | `Expr -> MetaM Expr` | Weak head normal form |
| `observing?` | `m α -> m (Option α)` | Non-destructive attempt (rollback on failure) |
| `getLCtx` | `m LocalContext` | Get local context |
| `LocalContext.foldlM` | `(β -> LocalDecl -> m β) -> β -> m β` | Fold over declarations |
| `LocalDecl.type` | `LocalDecl -> Expr` | Get hypothesis type |

### 2.2 Expr Matching APIs

| API | Signature | Purpose |
|-----|-----------|---------|
| `Expr.isAppOfArity` | `Expr -> Name -> Nat -> Bool` | Check if application of given const |
| `Expr.getAppFn` | `Expr -> Expr` | Get function of application |
| `Expr.getAppArgs` | `Expr -> Array Expr` | Get arguments of application |
| `Expr.isAppOf` | `Expr -> Name -> Bool` | Check head constant name |
| `Expr.app2?` | `Expr -> Name -> Option (Expr * Expr)` | Match 2-arg application |

### 2.3 TacticM APIs

| API | Signature | Purpose |
|-----|-----------|---------|
| `getMainGoal` | `TacticM MVarId` | Get current goal |
| `getMainTarget` | `TacticM Expr` | Get current goal type |
| `replaceMainGoal` | `List MVarId -> TacticM Unit` | Replace goals |
| `closeMainGoal` | `Name -> Expr -> TacticM Unit` | Close goal with proof |
| `closeMainGoalUsing` | `Name -> (Expr -> Name -> TacticM Expr) -> TacticM Unit` | Close via callback |
| `evalTactic` | `Syntax -> TacticM Unit` | Evaluate tactic syntax |
| `liftMetaTactic` | `(MVarId -> MetaM (List MVarId)) -> TacticM Unit` | Lift MetaM to TacticM |

### 2.4 ApplyConfig

The `ApplyConfig` struct controls how `MVarId.apply` handles goals:

```lean
structure ApplyConfig where
  newGoals : NewGoals := .nonDependentFirst
  ...
```

**Critical**: Use `{ newGoals := .nonDependentOnly }` to filter out type-level metavariable
goals. Without this, `apply ModusPonens.mp` produces 3 goals instead of 2 (the third being
the formula type `F` as a goal for the unconstrained implicit `{φ}`).

---

## 3. Concrete Code Patterns (Verified Working)

All patterns below have been verified in a live Lean session against CSLib imports.

### Pattern A: Extract DerivableIn Goal Components

```lean
/-- Extract (S, φ) from `DerivableIn S φ` goal expression.
    Does NOT use whnf -- matches the unevaluated DerivableIn form. -/
def matchDerivableIn (e : Expr) : Option (Expr × Expr) :=
  -- @InferenceSystem.DerivableIn.{u1, u2} : {α} → (S) → [inst] → (a) → Prop
  -- 4 arguments: α, S, inst, a
  if e.isAppOfArity ``InferenceSystem.DerivableIn 4 then
    let args := e.getAppArgs
    some (args[1]!, args[3]!)  -- S and φ
  else
    none
```

### Pattern B: Match Formula Connectives

```lean
/-- Match `HasImp.imp φ ψ` in an Expr. -/
def matchImp (e : Expr) : Option (Expr × Expr) :=
  if e.isAppOfArity ``HasImp.imp 4 then
    let args := e.getAppArgs
    some (args[2]!, args[3]!)  -- φ and ψ
  else
    none

/-- Match `HasBox.box φ` in an Expr. -/
def matchBox (e : Expr) : Option Expr :=
  if e.isAppOfArity ``HasBox.box 3 then
    some (e.getAppArgs[2]!)  -- φ
  else
    none

/-- Match `HasBot.bot` in an Expr. -/
def matchBot (e : Expr) : Bool :=
  e.isAppOfArity ``HasBot.bot 2
```

### Pattern C: Apply Axiom via Typeclass

The correct pattern uses `mkConstWithFreshMVarLevels` (NOT `mkConst`), combined with
`MVarId.apply` for unification:

```lean
/-- Try to close goal with a specific axiom typeclass method.
    Returns true if successful, false otherwise. State is rolled back on failure. -/
def tryAxiom (goal : MVarId) (axiomName : Name) : MetaM Bool := do
  let result ← observing? do
    let c ← mkConstWithFreshMVarLevels axiomName
    let config : ApplyConfig := { newGoals := .nonDependentOnly }
    let newGoals ← goal.apply c config
    if newGoals.isEmpty then return true
    else throwError "has subgoals"
  return result == some true
```

**Why `mkConstWithFreshMVarLevels`**: The axiom methods are universe-polymorphic
(`HasAxiomImplyK.implyK.{u1, u2}`). Using `mkConst` produces universe variables that
don't unify with the goal. `mkConstWithFreshMVarLevels` creates fresh metavariables for
universe levels, which `apply` then unifies with the goal's universe levels.

### Pattern D: Bounded DFS with Backtracking

The complete search function, verified to work on all tested goals:

```lean
partial def hilbertSearch
    (goal : MVarId) (fuel : Nat) : MetaM Bool := do
  if fuel == 0 then return false
  goal.withContext do
    if ← goal.isAssigned then return true
    let goalTy ← goal.getType
    let config : ApplyConfig := { newGoals := .nonDependentOnly }

    -- Strategy 1: Assumption lookup
    let lctx ← getLCtx
    for decl in lctx do
      if decl.isImplementationDetail then continue
      let r ← observing? (isDefEq decl.type goalTy)
      if r == some true then
        goal.assign decl.toExpr
        return true

    -- Strategy 2: Zero-subgoal rules (axioms)
    let axioms := #[
      ``HasAxiomImplyK.implyK, ``HasAxiomImplyS.implyS,
      ``HasAxiomEFQ.efq, ``HasAxiomPeirce.peirce,
      ``HasAxiomK.K, ``HasAxiomT.T, ``HasAxiom4.four,
      ``HasAxiomB.B, ``HasAxiom5.five, ``HasAxiomD.D
    ]
    for ax in axioms do
      let result ← observing? do
        let c ← mkConstWithFreshMVarLevels ax
        let newGoals ← goal.apply c config
        if newGoals.isEmpty then return true
        else throwError "has subgoals"
      if result == some true then return true

    -- Strategy 3: One-subgoal rules (derived + inference)
    let oneArgRules := #[
      ``Theorems.Combinators.identity,
      ``Theorems.Combinators.b_combinator,
      ``Theorems.Modal.Basic.box_mono,
      ``Necessitation.nec
    ]
    for rule in oneArgRules do
      let result ← observing? do
        let c ← mkConstWithFreshMVarLevels rule
        let newGoals ← goal.apply c config
        let mut ok := true
        for g in newGoals do
          if ← g.isAssigned then continue
          ok := ok && (← hilbertSearch g (fuel - 1))
          if !ok then break
        return ok
      if result == some true then return true

    -- Strategy 4: Two-subgoal rules (MP, imp_trans)
    let twoArgRules := #[
      ``Theorems.Combinators.imp_trans,
      ``ModusPonens.mp
    ]
    for rule in twoArgRules do
      let result ← observing? do
        let c ← mkConstWithFreshMVarLevels rule
        let newGoals ← goal.apply c config
        let mut ok := true
        for g in newGoals do
          if ← g.isAssigned then continue
          ok := ok && (← hilbertSearch g (fuel - 1))
          if !ok then break
        return ok
      if result == some true then return true

    return false
```

### Pattern E: TacticM Wrapper

```lean
/-- The `hilbert_search` tactic performs bounded depth-first proof search
    over the `InferenceSystem` typeclass hierarchy. -/
elab "hilbert_search" n:(num)? : tactic => do
  let fuel := n.map (·.getNat) |>.getD 10
  let goal ← getMainGoal
  let ok ← hilbertSearch goal fuel
  if !ok then
    throwTacticEx `hilbert_search goal
      m!"proof search exhausted at depth {fuel}"
```

**Alternative syntax form** (allows future extension with options):

```lean
syntax (name := hilbertSearchTac) "hilbert_search" (num)? : tactic

elab_rules : tactic
  | `(tactic| hilbert_search $[$n]?) => do
    let fuel := n.map (·.getNat) |>.getD 10
    ...
```

---

## 4. Verified Test Results

The following goals were all closed by the prototype tactic in a live Lean session:

| Test | Goal | Depth | Strategy Used |
|------|------|-------|---------------|
| ImplyK | `DerivableIn S (imp a (imp b a))` | 1 | Axiom: `HasAxiomImplyK.implyK` |
| Identity | `DerivableIn S (imp a a)` | 1 | Rule: `Combinators.identity` |
| Box mono | `DerivableIn S (imp (box a) (box b))` from `h : DerivableIn S (imp a b)` | 2 | Rule: `box_mono` + Assumption |
| Nec(id) | `DerivableIn S (box (imp a a))` | 2 | Rule: `Necessitation.nec` + `identity` |
| MP hyps | `DerivableIn S b` from `h1 : DerivableIn S (imp a b)`, `h2 : DerivableIn S a` | 1 | Rule: `ModusPonens.mp` + Assumptions |

---

## 5. Recommended Architecture

### 5.1 File Structure

```
Cslib/Foundations/Logic/Automation/
  HilbertSearch.lean      -- core search + tactic definition
```

### 5.2 Search Function Signature

```lean
namespace Cslib.Logic.Automation

/-- Core bounded proof search for DerivableIn goals.
    Uses DFS with backtracking over axiom application, local
    context assumptions, and modus ponens decomposition. -/
partial def hilbertSearchCore
    (goal : MVarId) (fuel : Nat) : MetaM Bool
```

### 5.3 Rule Organization (Prioritized)

Rules should be organized by priority to minimize wasted search:

1. **Assumption lookup** (always first -- O(n) scan, no recursion)
2. **Zero-subgoal axioms** (direct closure, no recursion)
3. **One-subgoal rules** (identity, box_mono, nec -- one recursive call)
4. **Two-subgoal rules** (imp_trans, MP -- two recursive calls, highest branching)

### 5.4 Extensible Rule Registry

Rather than hardcoding axiom names, the tactic should support a configurable rule table.
The recommended approach:

```lean
/-- A search rule: a constant name and its expected subgoal count. -/
structure SearchRule where
  name : Name
  priority : Nat  -- lower = tried first

/-- Default rule set for minimal propositional logic. -/
def minimalRules : Array SearchRule := #[
  { name := ``HasAxiomImplyK.implyK, priority := 10 },
  { name := ``HasAxiomImplyS.implyS, priority := 10 },
  ...
]

/-- Extended rule set for modal logic. -/
def modalRules : Array SearchRule := minimalRules ++ #[
  { name := ``HasAxiomK.K, priority := 10 },
  { name := ``Necessitation.nec, priority := 20 },
  ...
]
```

This allows users to configure the rule set per-logic without modifying the core search.

### 5.5 Two-Layer Architecture (Confirmed)

Round 1 recommended a two-layer architecture. This round confirms it with tested code:

**Layer 1 (MetaM)**: `hilbertSearchCore : MVarId -> Nat -> MetaM Bool`
- Works directly with Lean's metavariable infrastructure
- Uses `observing?` for backtracking
- Uses `MVarId.apply` with `ApplyConfig { newGoals := .nonDependentOnly }`
- Handles universe polymorphism via `mkConstWithFreshMVarLevels`

**Layer 2 (TacticM)**: `elab "hilbert_search" ... : tactic`
- Thin wrapper: gets main goal, calls Layer 1, reports failure
- Configures depth bound from user syntax

### 5.6 Why NOT Term-Mode Search

Round 1 discussed a term-mode search function returning `Option (DerivableIn S φ)`. After
testing, the MetaM/apply approach is strictly superior for the following reasons:

1. **No formula decomposition needed**: `MVarId.apply` + `isDefEq` handles unification
   automatically. No need for `HasImpView`/`HasBoxView` typeclasses.
2. **Typeclass availability is automatic**: When `HasAxiomK.K` is applied and there's no
   `HasAxiomK S` instance, `apply` simply fails -- no explicit instance checking needed.
3. **Universe polymorphism handled**: `mkConstWithFreshMVarLevels` + `apply` handles
   universe level unification transparently.
4. **Backtracking is native**: `observing?` provides checkpoint/rollback over MetaM state.

The term-mode approach would require re-implementing all of this manually.

---

## 6. Gaps and Open Questions

### 6.1 Modus Ponens Branching Factor

The biggest performance concern is modus ponens backward chaining. When the goal is
`DerivableIn S ψ` and we apply `ModusPonens.mp`, the first subgoal is
`DerivableIn S (imp ?φ ψ)` with `?φ` unconstrained. Every axiom that produces an
implication with conclusion `ψ` will match, creating branching. The current strategy
(try axioms before MP) helps but doesn't eliminate the problem.

**Mitigation options** (for implementation phase):
- Limit MP depth separately from total depth
- Use iterative deepening DFS (IDDFS) instead of plain DFS
- Add heuristic: prefer MP only when goal is not directly an axiom instance
- Track "visited" goal types to detect cycles

### 6.2 Temporal and Bimodal Axioms

The tested prototype includes propositional + modal axioms. Temporal axioms
(`HasAxiomSerialFuture.serialFuture`, etc.) and bimodal axioms (`HasAxiomMF.MF`) need to
be added to the rule table. The same `apply` + `observing?` pattern works -- no new
infrastructure needed, just more entries in the axiom list.

### 6.3 And/Or Axiom Support

`HasAxiomAndI`, `HasAxiomAndE1`, `HasAxiomAndE2`, `HasAxiomOrI1`, `HasAxiomOrI2`,
`HasAxiomOrE` are defined in `ProofSystem.lean` but have no bundled proof system class yet.
They should be added to the rule table for logics that have them.

### 6.4 Custom User Rules

Users should be able to register additional derived theorems (like `box_mono`, `identity`,
`contraposition`) as search rules. A Lean 4 attribute (`@[hilbert_search_rule]`) could
automate this, similar to `@[simp]`. This is a nice-to-have, not a blocker.

### 6.5 Performance Profiling

The `partial def` approach means no termination proof. For a verified tactic, the search
function should use `Nat` fuel and structural recursion. The `partial` annotation is
acceptable for the initial implementation since the tactic is a metalevel tool (not a
proof-relevant term).

### 6.6 `mkAppM` vs `apply` for Proof Construction

`mkAppM ``HasAxiomImplyK.implyK #[]` fails with "result contains metavariables" because
it cannot resolve the implicit formula arguments without an expected type. `MVarId.apply`
succeeds because it has the goal type as context for unification. The implementation
MUST use the `apply` approach, not `mkAppM`.
