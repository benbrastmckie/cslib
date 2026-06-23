# Task 269: Generic Bounded Proof-Search Tactic — Teammate A Findings

## Role: Primary Approach — Implementation Patterns and Architecture

---

## Key Findings

### 1. BimodalLogic modal_search Architecture (Well-Understood Reference)

The reference implementation lives in:
- `/home/benjamin/Projects/BimodalLogic/Theories/Bimodal/Automation/Tactics/Helpers.lean` (~700 lines total)
- `/home/benjamin/Projects/BimodalLogic/Theories/Bimodal/Automation/Tactics/Commands.lean` (~400 lines)

The architecture has five layers:

**Layer 1: Goal extraction**
```lean
def extractDerivationGoal (goalType : Expr) : MetaM (Option (Expr × Expr × Expr))
-- Returns (frameClass, context, formula) triple from a DerivationTree goal
```

**Layer 2: Strategy functions** — each tries one proof step, returns `Bool`
- `tryAxiomMatch`: iterate 42 axiom constructors via `observing?`/`goal.apply`
- `tryDerivedMatch`: try ~26 named derived theorems via `goal.apply`
- `tryAssumptionMatch`: apply `DerivationTree.assumption` + `simp` for membership
- `tryModusPonens`: extract context formulas, find matching antecedents, build recursive proof
- `tryModalK`: if goal is `□Γ ⊢ □φ`, apply `generalized_modal_k` + recurse
- `tryTemporalK`: if goal is `FΓ ⊢ Fφ`, apply `generalized_temporal_k` + recurse

**Layer 3: Core search loop**
```lean
partial def searchProof (goal : MVarId) (depth : Nat) : TacticM Bool
-- Tries strategies in order; recurses with depth-1
```

**Layer 4: Configuration**
```lean
structure SearchConfig where
  depth : Nat := 10
  visitLimit : Nat := 1000
  axiomWeight, assumptionWeight, mpWeight, modalKWeight, temporalKWeight : Nat
```

**Layer 5: Syntax/elaboration**
```lean
syntax "modal_search" (num)? : tactic
elab_rules : tactic | `(tactic| modal_search $[$d]?) => ...
```

**Critical design insight**: The tactic works at the meta-level (TacticM/MetaM), constructing proof terms via `mkAppM` and `goal.assign` rather than returning `Option (Axiom φ)`. This bypasses the Prop vs Type issue — axiom predicates are Props but we need Type-valued proof terms for `DerivationTree`.

---

### 2. CSLib InferenceSystem Architecture (What We Must Target)

CSLib's InferenceSystem is fundamentally different from BimodalLogic's DerivationTree:

```lean
-- CSLib InferenceSystem: polymorphic over (S : Type*) (α : Type*)
class InferenceSystem (S : Type*) (α : Type*) where
  derivation (a : α) : Sort v

-- The goal shape is: InferenceSystem.DerivableIn S φ
-- which unfolds to: Nonempty (S⇓φ) where S⇓φ := InferenceSystem.derivation S φ
```

**Key structural difference from BimodalLogic**: BimodalLogic has a *concrete* `DerivationTree Axioms Γ φ` type with known constructors (`ax`, `assumption`, `modus_ponens`, `necessitation`, `weakening`). CSLib's `InferenceSystem.derivation S φ` is **opaque** — it dispatches to whatever concrete type is registered as an instance.

For example:
- `HilbertCl⇓φ` unfolds to `PL.DerivationTree PropositionalAxiom [] φ` (propositional)
- `HilbertS5⇓φ` unfolds to `Modal.DerivationTree ModalAxiom [] φ` (modal)
- `HilbertTM⇓φ` unfolds to `Bimodal.DerivationTree TMAAxiom [] φ` (bimodal)

The inference rules (`ModusPonens`, `Necessitation`, etc.) are registered separately as typeclasses.

---

### 3. The Generic Tactic Cannot Pattern-Match on InferenceSystem.derivation

**Critical finding**: The BimodalLogic tactic uses `extractDerivationGoal` which pattern-matches on the *shape* of `DerivationTree`:
```lean
| .app (.app (.app (.const ``DerivationTree _) fc) ctx) formula => ...
```

This is only possible because `DerivationTree` is a known type constructor. For CSLib, `InferenceSystem.DerivableIn S φ` unfolds to `Nonempty (S⇓φ)`, and `S⇓φ` is opaque (`InferenceSystem.derivation S φ`). We cannot pattern-match on `S⇓φ` at the meta-level.

**The correct CSLib goal shape** that a generic `hilbert_search` should target is:
```lean
InferenceSystem.DerivableIn S φ
-- which is definitionally: Nonempty (InferenceSystem.derivation S φ)
```

The tactic must detect goals of this exact shape and then apply the typeclass-mediated rules:
- `ModusPonens.mp`
- `HasAxiomImplyK.implyK`, `HasAxiomImplyS.implyS`, etc.
- `Necessitation.nec`
- `TemporalNecessitation.tempNec`, `tempNecPast`

---

### 4. How to Extract Goal Components (CSLib Generic Version)

The goal extractor for CSLib needs to match `InferenceSystem.DerivableIn S φ`:
```lean
-- InferenceSystem.DerivableIn unfolds to:
-- def DerivableIn S [InferenceSystem S α] (a : α) := Nonempty (S⇓a)
-- So the goal type for hilbert_search is:
--   @InferenceSystem.DerivableIn S α inst φ
-- where inst : InferenceSystem S α
```

At the meta-level:
```lean
def extractDerivableGoal (goalType : Expr) : MetaM (Option (Expr × Expr)) := do
  -- Match: InferenceSystem.DerivableIn S φ
  -- This unfolds to: Nonempty (InferenceSystem.derivation S φ)
  match goalType with
  | .app (.app (.app (.app (.const ``InferenceSystem.DerivableIn _) S) _α) _inst) formula =>
    return some (S, formula)
  | _ => return none
```

Note: Unlike BimodalLogic, CSLib proofs have **no context** at the InferenceSystem level (the context is baked into the concrete DerivationTree type or handled via `weakening`). The `DerivableIn` notation is always `DerivableIn S φ`, not `DerivableIn S Γ φ`.

---

### 5. Strategy Dispatch Using Typeclass Constraints

The core insight for generalization: instead of iterating over hardcoded axiom constructor names, use instance queries to find what the system `S` provides.

**Proposed dispatch pattern**:
```lean
-- In searchProof, for each strategy:

-- Strategy: implyK axiom (requires [HasAxiomImplyK S])
if let some inst ← trySynthInstance (mkAppM ``HasAxiomImplyK #[S, ...]) then
  -- Try to match goal formula against ImplyK pattern
  -- Apply inst.implyK to close goal

-- Strategy: modus ponens (requires [ModusPonens S])
if let some inst ← trySynthInstance (mkAppM ``ModusPonens #[S, ...]) then
  -- Try forward/backward modus ponens chaining
```

However, this approach has a problem: `DerivableIn` goals don't carry context — we can't scan a context for usable assumptions in the way BimodalLogic does. The assumptions available to the tactic are Lean *local hypotheses*, not a `List Formula` baked into a derivation tree type.

**Resolution**: The `hilbert_search` tactic should scan Lean's *local context* for hypotheses of type `InferenceSystem.DerivableIn S ψ` and use those as assumptions, applying `ModusPonens.mp` to chain them.

---

### 6. Axiom Matching Strategy Without Concrete Axiom Type

For BimodalLogic, `tryAxiomMatch` iterates 42 named constructor constants and tries `goal.apply (mkConst ctorName)`. For CSLib, the analog is iterating `HasAxiom*` typeclass methods:

```lean
-- List of axiom strategies with their typeclass constraints:
let axiomStrategies : List (Name × List Name) := [
  (``HasAxiomImplyK.implyK, [``HasAxiomImplyK]),   -- φ → (ψ → φ)
  (``HasAxiomImplyS.implyS, [``HasAxiomImplyS]),   -- (φ→(ψ→χ))→((φ→ψ)→(φ→χ))
  (``HasAxiomEFQ.efq, [``HasAxiomEFQ]),            -- ⊥ → φ
  (``HasAxiomPeirce.peirce, [``HasAxiomPeirce]),   -- ((φ→ψ)→φ)→φ
  (``HasAxiomK.K, [``HasAxiomK]),                  -- □(φ→ψ)→(□φ→□ψ)
  (``HasAxiomT.T, [``HasAxiomT]),                  -- □φ→φ
  (``HasAxiom4.four, [``HasAxiom4]),               -- □φ→□□φ
  -- ... etc.
]
```

For each, the tactic uses `observing? do goal.apply (mkConst axiomMethod)` and succeeds if Lean's unifier can match the goal formula.

---

### 7. Directory Placement and Namespace

Based on CSLib's structure, the `hilbert_search` tactic belongs in:
```
Cslib/Foundations/Logic/Automation/ProofSearch.lean
```
or possibly:
```
Cslib/Foundations/Logic/Tactic/HilbertSearch.lean
```

**Namespace**: `Cslib.Logic` (consistent with Foundations usage)

**Import chain**: Must import `Cslib.Init`, `Cslib.Foundations.Logic.ProofSystem`, `Cslib.Foundations.Logic.Theorems`

**Key module annotation**: Tactics live in a `meta section` in CSLib convention. Looking at `Cslib/Foundations/Lint/Basic.lean` and `Cslib/Foundations/Relation/Attr.lean`, CSLib uses `public meta section` and `open Lean Elab Meta` patterns.

---

### 8. Handling System-Specific Rules (Necessitation, Temporal K)

The tactic must conditionally apply system-specific rules based on which typeclasses are available for `S`:

```lean
-- Necessitation (only if Necessitation S is available):
-- Try to prove □φ by first proving φ at empty context and applying nec
-- tryNecessitation goal S formula searchFn depth

-- TemporalNecessitation (only if TemporalNecessitation S):
-- Try to prove Gφ or Hφ by proving φ then applying tempNec/tempNecPast
-- tryTemporalNecessitation goal S formula searchFn depth
```

These are optional search branches gated on `trySynthInstance`.

---

### 9. Normalization Tags Interaction (Task 268)

Task 268 added `@[simp, scoped grind =]` co-tags to structural lemmas in `ListImplication`, `BigConj`, and embedding maps. The `hilbert_search` tactic can use `evalTactic (← \`(tactic| simp))` in its assumption membership check (analogous to BimodalLogic's `tryAssumptionMatch` using simp to prove `φ ∈ Γ`). However, since CSLib's InferenceSystem goals don't have a list context, simp normalization is less central. The main use is to normalize formula equalities before checking axiom matching.

---

### 10. Context Goal vs. DerivableIn Goal — CSLib Convention

Looking at the instance registrations (e.g., `Propositional/ProofSystem/Instances.lean`):
```lean
instance : InferenceSystem Propositional.HilbertCl (PL.Proposition Atom) where
  derivation φ := PL.DerivationTree PropositionalAxiom ([] : List (PL.Proposition Atom)) φ
```

The context is **always empty** (`[]`) in the `InferenceSystem.DerivableIn` formulation. The Hilbert-style systems prove empty-context derivability (`⊢ φ`), not context-relative derivability (`Γ ⊢ φ`). Context-relative reasoning is done through the `imp` connective (deduction theorem).

**Implication for `hilbert_search`**: The tactic operates only on `DerivableIn S φ` goals, not on `Γ ⊢ φ` goals. If a user wants to prove `Γ ⊢ φ` using a Hilbert system, they must either use `listDeduction` or go through the concrete DerivationTree constructors. This is a hard constraint on what `hilbert_search` can do.

---

## Recommended Approach

### High-Level Design

Implement `hilbert_search` as a `TacticM` tactic targeting `InferenceSystem.DerivableIn S φ` goals, using a bounded depth-first search over typeclass-mediated proof steps. The tactic should:

1. Extract `S` and `φ` from the goal via meta-level expression matching on `InferenceSystem.DerivableIn`
2. Use `observing?` + `goal.apply` to try axiom methods (`HasAxiomImplyK.implyK`, etc.)
3. Try local hypothesis matching: scan `lctx` for `DerivableIn S ψ` hypotheses, then try `ModusPonens.mp`
4. Recurse with depth decremented

### File Structure

```
Cslib/Foundations/Logic/Automation.lean         -- barrel import
Cslib/Foundations/Logic/Automation/
  HilbertSearch.lean                            -- main tactic file
```

### Sketch of Core Implementation

```lean
-- In HilbertSearch.lean
import Cslib.Init
import Cslib.Foundations.Logic.ProofSystem
import Cslib.Foundations.Logic.Theorems

open Lean Elab Tactic Meta

namespace Cslib.Logic

/-- Configuration for hilbert_search depth-first proof search. -/
structure HilbertSearchConfig where
  depth : Nat := 10
  deriving Repr, Inhabited

/-- Extract S and φ from a DerivableIn goal. -/
def extractDerivableGoal (goalType : Expr) :
    MetaM (Option (Expr × Expr)) := do
  -- Match InferenceSystem.DerivableIn S φ
  let goalType ← whnf goalType
  match goalType with
  | .app (.app (.app (.app
      (.const ``InferenceSystem.DerivableIn _) S) _α) _inst) formula =>
    return some (S, formula)
  | _ => return none

/-- Try axiom methods in order, using observing? to avoid corrupting mvar state. -/
def tryAxiomMethods (goal : MVarId) : TacticM Bool := do
  let axiomMethods := [
    ``HasAxiomImplyK.implyK,
    ``HasAxiomImplyS.implyS,
    ``HasAxiomEFQ.efq,
    ``HasAxiomPeirce.peirce,
    ``HasAxiomK.K,
    ``HasAxiomT.T,
    ``HasAxiom4.four,
    ``HasAxiomB.B,
    ``HasAxiom5.five,
    ``HasAxiomD.D,
    -- ... temporal axioms ...
  ]
  for mth in axiomMethods do
    let result ← observing? do
      setGoals [goal]
      let _ ← goal.apply (mkConst mth)
      setGoals []
    if result.isSome then return true
  return false

/-- Try local hypotheses as DerivableIn witnesses + ModusPonens. -/
def tryHypothesisMP (goal : MVarId) (S _φ : Expr)
    (searchFn : MVarId → Nat → TacticM Bool) (depth : Nat) : TacticM Bool := do
  -- Scan lctx for hypotheses of shape DerivableIn S ψ
  let lctx ← getLCtx
  for decl in lctx do
    if !decl.isImplementationDetail then
      -- Check if decl.type is DerivableIn S ψ for some ψ
      -- Try applying ModusPonens.mp with this hypothesis
      ...
  return false

/-- Core bounded DFS proof search. -/
partial def searchProof (goal : MVarId) (depth : Nat) : TacticM Bool := do
  if depth = 0 then return false
  let goalType ← goal.getType
  let some (_S, _φ) ← extractDerivableGoal goalType | return false
  if ← tryAxiomMethods goal then return true
  -- tryHypothesisMP and modus ponens chaining
  return false

/-- The hilbert_search tactic entry point. -/
syntax "hilbert_search" (num)? : tactic

elab_rules : tactic
  | `(tactic| hilbert_search $[$d]?) => do
    let depth := d.map (·.getNat) |>.getD 10
    let goal ← getMainGoal
    let goalType ← goal.getType
    let some _ ← extractDerivableGoal goalType
      | throwError "hilbert_search: goal must be DerivableIn S φ"
    let found ← searchProof goal depth
    if !found then
      throwError "hilbert_search: no proof found within depth {depth}"

end Cslib.Logic
```

### Key Challenges and Solutions

| Challenge | Solution |
|-----------|----------|
| InferenceSystem.derivation is opaque | Target `DerivableIn S φ` (Nonempty wrapper), not the concrete type |
| No context in DerivableIn goals | Scan local hypotheses for `DerivableIn S ψ` and chain with `ModusPonens.mp` |
| Axiom constructors are system-specific | Try `HasAxiom*.method` via `observing? + goal.apply` |
| Necessitation requires empty-context subproof | Build a fresh empty-context goal and recurse |
| Different systems have different axioms | `goal.apply` fails gracefully; `observing?` catches failures |
| `scoped grind =` tags from task 268 | Available for `simp` calls within the tactic, but less central here |

---

## Evidence and Examples

### From BimodalLogic: The `observing?` Pattern

```lean
-- Key pattern: observing? avoids corrupting mvar state on failure
def tryAxiomMatch (goal : MVarId) ... : TacticM Bool := do
  let result ← observing? do
    setGoals [goal]
    let axiomExpr := mkConst ``DerivationTree.axiom
    let newGoals ← goal.apply axiomExpr
    -- ... try axiom constructors ...
    for ctorName in axiomCtors do
      try
        let remainingGoals ← axiomGoal.apply (mkConst ctorName)
        if remainingGoals.isEmpty then
          setGoals []
          return ()
      catch _ => continue
    throwError "no axiom matched"
  return result.isSome
```

This exact pattern (observing? + sequential try/catch) is directly portable to CSLib with `HasAxiom*.method` names in place of `ctorName`.

### From CSLib: Instance Registration Pattern

```lean
-- Propositional instance:
instance : InferenceSystem Propositional.HilbertCl (PL.Proposition Atom) where
  derivation φ := PL.DerivationTree PropositionalAxiom [] φ

-- ModusPonens instance:
instance : ModusPonens Propositional.HilbertCl (F := PL.Proposition Atom) where
  mp := fun h1 h2 => by
    obtain ⟨d1⟩ := h1; obtain ⟨d2⟩ := h2
    exact ⟨PL.DerivationTree.modus_ponens [] _ _ d1 d2⟩
```

This shows that `ModusPonens.mp` takes two `DerivableIn` arguments and produces a `DerivableIn` result — precisely the interface `hilbert_search` needs to use at the meta-level.

### Bimodal-Specific AxiomMatcher in CSLib

`Cslib/Logics/Bimodal/Metalogic/Decidability/AxiomMatcher.lean` already exists and implements pure pattern-matching on `Formula Atom` for all 42 TM axiom schemata. This is a computable (not meta-level) matcher used for the tableau decision procedure. It demonstrates that CSLib already has precedent for systematic axiom pattern matching — the generic tactic simply needs to do this at the meta-level using `goal.apply` + `observing?` rather than explicit formula matching.

---

## Confidence Level

**Architecture**: High — The `InferenceSystem.DerivableIn` goal shape is clear, and the `observing?` + `goal.apply` pattern from BimodalLogic is directly applicable. CSLib's typeclass hierarchy is well-designed to support this approach.

**Implementation path**: Medium — The specific meta-level code for extracting `S` from `DerivableIn S φ` goals (after `whnf` unfolding) needs careful testing since `DerivableIn` is a def that unfolds to `Nonempty (S⇓φ)`. The extractor may need to unfold multiple layers.

**Scope**: Medium — The tactic targets only `DerivableIn S φ` goals (empty context Hilbert proofs). It cannot help with context-relative goals `Γ ⊢ φ` directly. This is a fundamental constraint of the CSLib InferenceSystem design and should be documented clearly.

**Zulip consultation need**: High — This is novel cross-cutting infrastructure. The community should weigh in on:
1. Whether `hilbert_search` should live in Foundations or alongside specific logic modules
2. The question of whether to support context-relative goals through a separate tactic
3. The naming convention for the tactic

---

## Appendix: Files Referenced

| File | Purpose |
|------|---------|
| `/home/benjamin/Projects/BimodalLogic/Theories/Bimodal/Automation/Tactics/Helpers.lean` | Reference implementation of modal_search (core logic) |
| `/home/benjamin/Projects/BimodalLogic/Theories/Bimodal/Automation/Tactics/Commands.lean` | Reference implementation (syntax, config, tactic commands) |
| `/home/benjamin/Projects/cslib/Cslib/Foundations/Logic/InferenceSystem.lean` | CSLib InferenceSystem typeclass |
| `/home/benjamin/Projects/cslib/Cslib/Foundations/Logic/ProofSystem.lean` | CSLib HasAxiom*, ModusPonens, Necessitation etc. |
| `/home/benjamin/Projects/cslib/Cslib/Logics/Propositional/ProofSystem/Instances.lean` | Example instance registration |
| `/home/benjamin/Projects/cslib/Cslib/Logics/Modal/Metalogic/DerivationTree.lean` | Modal DerivationTree constructors |
| `/home/benjamin/Projects/cslib/Cslib/Logics/Modal/ProofSystem/Instances/S5.lean` | Modal S5 instance registration |
| `/home/benjamin/Projects/cslib/Cslib/Logics/Bimodal/Metalogic/Decidability/AxiomMatcher.lean` | Computable axiom pattern matcher (precedent) |
| `/home/benjamin/Projects/cslib/Cslib/Foundations/Logic/Theorems/Combinators.lean` | Generic derived theorems (MinimalHilbert) |
| `/home/benjamin/Projects/cslib/Cslib/Foundations/Lint/Basic.lean` | CSLib meta section pattern |
| `/home/benjamin/Projects/cslib/Cslib/Foundations/Relation/Attr.lean` | CSLib TacticM/MetaM usage pattern |
