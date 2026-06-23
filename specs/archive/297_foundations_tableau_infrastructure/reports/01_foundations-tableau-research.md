# Research Report: Task #297

**Task**: 297 - Build shared tableau infrastructure in Foundations/Logic/Tableau/
**Started**: 2026-06-23
**Completed**: 2026-06-23
**Task Type**: cslib
**Domains**: logic, proof theory, typeclass design

## Executive Summary

- The existing `PropositionalTableau.lean` (210 lines, namespace `Cslib.Logic`) defines `PropSign`, `PropSignedFormula`, `PropTableauRule`, `PropRuleResult`, and `applyPropRule` -- all parameterized over abstract decomposition functions. It is NOT imported by any other file in CSLib.
- The bimodal decidability system (namespace `Cslib.Logic.Bimodal.Metalogic.Decidability`) independently defines `Sign`, `SignedFormula` (with `Label` containing world + time indices), `Branch`, `RuleResult` (with `persistent` variant), and full `Closure`/`ClosureReason` infrastructure -- ~860 lines in `SignedFormula.lean` alone.
- Both `Sign` types are structurally identical: two constructors `pos | neg` with `DecidableEq`, `BEq`, `Hashable`. The bimodal version adds `flip`, `flip_flip`, `ReflBEq`, `LawfulBEq`. Unifying them is straightforward.
- The task description requires logic-neutral infrastructure supporting classical, intuitionistic, and minimal tableaux. CSLib already has the axiom hierarchy `MinPropAxiom < IntPropAxiom < PropositionalAxiom` and Kripke semantics with `IValid`/`MValid` via `botForces` parameterization.
- The key design challenge is that intuitionistic/minimal tableaux require world-aware branches even at the propositional level (L = WorldIndex with Kripke-style accessibility), whereas classical propositional tableaux use `L = Unit`. This is achievable through a generic `SignedFormula F L` structure.
- Closure conditions differ fundamentally across logic strengths: classical uses complementary signed pairs T(phi)/F(phi); intuitionistic uses only F(bot); minimal uses only complementary atoms T(p)/F(p). A `ClosureCondition` typeclass is the right abstraction.
- The implication rule `T(phi -> psi)` behaves differently: classical branches into F(phi) | T(psi); intuitionistic/minimal creates a successor world w' with T(phi) and F(psi). A `RuleConfig` parameter or typeclass controls this behavior.

## Findings

### 1. Existing PropositionalTableau.lean Analysis

**Location**: `Cslib/Foundations/Logic/PropositionalTableau.lean` (210 lines)
**Namespace**: `Cslib.Logic`
**Import status**: Imported by NOTHING -- completely standalone

**Types defined**:
- `PropSign`: `| pos | neg` with `Repr, DecidableEq, BEq, Hashable`
- `PropSignedFormula (F : Type*)`: `{ sign : PropSign, formula : F }` with `DecidableEq, BEq, Hashable`
- `PropTableauRule`: 8 constructors (andPos, andNeg, orPos, orNeg, impPos, impNeg, negPos, negNeg)
- `PropRuleResult (F : Type u)`: `| linear | branching | notApplicable`
- `applyPropRule`: Takes 4 decomposition functions (`andOf?`, `orOf?`, `impOf?`, `negOf?`) and applies a rule to a signed formula

**Key design choice**: The rule application is parameterized over decomposition functions rather than requiring typeclass instances. This is important because modal/temporal formulas encode conjunction and disjunction via Lukasiewicz patterns (`and phi psi := neg(phi -> neg psi)`) rather than having native constructors.

**What's missing for the new infrastructure**:
- No label parameter (no world awareness)
- No `flip` operation on signs
- No `persistent` rule result variant
- No `Branch` type
- No closure detection
- No `ClosureCondition` abstraction
- No logic-kind parameterization for rule behavior

### 2. Bimodal Sign/SignedFormula/Branch Analysis

**Location**: `Cslib/Logics/Bimodal/Metalogic/Decidability/SignedFormula.lean` (~860 lines)
**Namespace**: `Cslib.Logic.Bimodal.Metalogic.Decidability`

**Sign type** (lines 166-204): Structurally identical to `PropSign` but with additional API:
- `flip : Sign -> Sign` with `flip_flip` simp lemma
- `ReflBEq` and `LawfulBEq` instances
- `Inhabited` instance (unlike `PropSign`)

**SignedFormula** (lines 221-260): `{ sign : Sign, formula : Formula Atom, label : Label }` where `Label = { world : WorldIndex, time : TimeIndex }` with `WorldIndex = Nat`, `TimeIndex = Nat`.

**Branch** (lines 273-572): `List (SignedFormula Atom)` with extensive query helpers:
- `contains`, `hasPos`, `hasNeg`, `hasPosAt`, `hasNegAt`
- `hasBotPos`, `findContradiction`, `hasContradiction`
- `knownWorlds`, `maxWorld`, `nextWorld`
- `knownTimes`, `maxTime`, `nextTime`
- Various formula collection helpers (boxPosFormulas, diamondNegFormulas, etc.)
- `isSubsetBlocked` for temporal blocking

**Key observation**: The Branch type is heavily bimodal-specific with methods for both world and time dimensions, plus bimodal-specific formula patterns (box, diamond, until, since). The generic Foundations branch should provide only the label-generic core.

### 3. Bimodal Closure Analysis

**Location**: `Cslib/Logics/Bimodal/Metalogic/Decidability/Closure.lean` (~428 lines)

**Closure detection** is three-fold:
1. `checkBotPos`: T(bot) at any label
2. `checkContradiction`: Complementary pair T(phi)/F(phi) at same label
3. `checkAxiomNeg`: F(axiom instance) detected via `matchAxiom`

**Monotonicity proofs**: Closure is monotone under branch extension (`closed_extend_closed`). This is important infrastructure that should be generic.

**Key observation**: The bimodal closure uses all three checks. Classical propositional would use (1) + (2). Intuitionistic would use only (1) -- T(bot). Minimal would use complementary atoms only -- T(p)/F(p) for atomic p. The `ClosureCondition` typeclass must abstract over which checks are active.

### 4. Propositional Logic Three-Strength Architecture

**Axiom hierarchy** (`Cslib/Logics/Propositional/ProofSystem/Axioms.lean`):
```
MinPropAxiom < IntPropAxiom < PropositionalAxiom
```

The differences:
- `MinPropAxiom`: 8 axioms (K, S, and/or intro/elim) -- NO efq, NO peirce
- `IntPropAxiom`: 9 axioms (+ efq: `bot -> phi`)
- `PropositionalAxiom`: 10 axioms (+ peirce: `((phi -> psi) -> phi) -> phi`)

**Subsumption theorems** exist: `MinPropAxiom.toIntPropAxiom`, `IntPropAxiom.toPropAxiom`.

**Kripke semantics** (`Cslib/Logics/Propositional/Semantics/Kripke.lean`):
- `IForces v bot_forces w phi`: Forcing at world w, parameterized by `bot_forces : World -> Prop`
- `IValid`: Intuitionistic validity -- `bot_forces = fun _ => False`
- `MValid`: Minimal validity -- `bot_forces` is arbitrary upward-closed predicate
- `iforces_persistence`: Forcing is persistent under the preorder (upward-closed)

**Formula type** (`Cslib/Logics/Propositional/Defs.lean`):
`PL.Proposition Atom` with 5 constructors: `atom | bot | imp | and | or`

**Algebraic semantics** (`Cslib/Logics/Propositional/Semantics/Algebra/`):
- `GeneralizedHeytingAlgebra` -> minimal logic (MPL)
- `HeytingAlgebra` -> intuitionistic logic (IPL)
- `BooleanAlgebra` -> classical logic (CPL)

**Proof system tags**: `Propositional.HilbertMin`, `Propositional.HilbertInt`, `Propositional.HilbertCl`

### 5. Connective Typeclass Analysis

**Location**: `Cslib/Foundations/Logic/Connectives.lean`

Atomic classes: `HasBot`, `HasImp`, `HasBox`, `HasDia`, `HasUntil`, `HasSince`, `HasNext`, `HasAnd`, `HasOr`

Bundled classes:
- `PropositionalConnectives`: `HasBot` + `HasImp`
- `ModalConnectives`: `PropositionalConnectives` + `HasBox`
- `FutureTemporalConnectives`, `LTLConnectives`, `TemporalConnectives`, `BimodalConnectives`

**Key design note**: `HasAnd` and `HasOr` are standalone atomic classes, NOT part of `PropositionalConnectives`. The propositional formula type (`PL.Proposition`) has instances for all of them. Modal/temporal/bimodal formulas use Lukasiewicz encodings instead.

For tableau decomposition, this means:
- Propositional: native `and`/`or` decomposition (pattern-match on constructors)
- Modal/Temporal/Bimodal: Lukasiewicz decomposition (pattern-match on `imp (imp phi (imp psi bot)) bot` for conjunction)

The existing `applyPropRule` handles this correctly by taking decomposition functions as parameters.

### 6. Design Analysis: Logic-Neutral Tableau Infrastructure

#### 6.1 Sign Unification

Both existing Sign types (`PropSign` and bimodal `Sign`) are structurally identical. The unified type should be:

```lean
inductive Sign : Type where
  | pos : Sign  -- formula asserted true
  | neg : Sign  -- formula asserted false
  deriving Repr, DecidableEq, BEq, Hashable, Inhabited
```

With the full API from the bimodal version: `flip`, `flip_flip`, `ReflBEq`, `LawfulBEq`.

#### 6.2 Generic SignedFormula

The fundamental parameterization is over formula type `F` and label type `L`:

```lean
structure SignedFormula (F : Type*) (L : Type*) where
  sign : Sign
  formula : F
  label : L
  deriving DecidableEq, BEq, Hashable
```

Instantiations:
- Classical propositional: `SignedFormula (PL.Proposition Atom) Unit`
- Intuitionistic/minimal propositional: `SignedFormula (PL.Proposition Atom) WorldIndex`
- Modal K: `SignedFormula (Modal.Formula Atom) WorldIndex`
- Temporal: `SignedFormula (Temporal.Formula Atom) TimeIndex`
- Bimodal: `SignedFormula (Bimodal.Formula Atom) Label` where `Label = { world : WorldIndex, time : TimeIndex }`

#### 6.3 RuleResult

The generic version should include all four variants from day one:

```lean
inductive RuleResult (F : Type*) (L : Type*) : Type _ where
  | linear (formulas : List (SignedFormula F L))
  | branching (branches : List (List (SignedFormula F L)))
  | persistent (formulas : List (SignedFormula F L))
  | notApplicable
```

The `persistent` variant (from the bimodal system) is needed for universal modal rules (T(box A) propagates to all worlds) and universal temporal rules. Even though propositional rules don't use it, having it in the generic type avoids downstream redefinition.

#### 6.4 Branch Type

```lean
abbrev Branch (F : Type*) (L : Type*) [DecidableEq F] [DecidableEq L] [BEq (SignedFormula F L)] :=
  List (SignedFormula F L)
```

The branch should provide:
- Basic operations: `contains`, `extend`, `extendMany`
- Sign-filtered queries: `positives`, `negatives`
- Label-aware queries: `hasPosAt`, `hasNegAt`
- Contradiction detection: `findContradiction` (at same label)

Logic-specific extensions (world creation, time ordering, temporal formula collection) belong in logic-specific modules, not in Foundations.

#### 6.5 ClosureCondition Typeclass

This is the key abstraction enabling logic-neutral closure:

```lean
class ClosureCondition (F : Type*) (L : Type*) where
  isClosed : Branch F L -> Bool
```

Or more structured, to support proof extraction:

```lean
inductive ClosureReason (F : Type*) (L : Type*) where
  | botPos (l : L)                          -- T(bot) at label l
  | contradiction (phi : F) (l : L)         -- T(phi) and F(phi) at same label l
  | atomContradiction (p : F) (l : L)       -- T(p) and F(p) for atomic p at label l

class ClosureCondition (F : Type*) (L : Type*) where
  findClosure : Branch F L -> Option (ClosureReason F L)
```

Instances:
- **Classical**: `findClosure` checks for T(bot) OR complementary T(phi)/F(phi) at same label
- **Intuitionistic**: `findClosure` checks for T(bot) only (F(bot) is immediate from efq)
- **Minimal**: `findClosure` checks for complementary atoms T(p)/F(p) at same label only

**Design consideration**: The `ClosureReason` type above is generic -- logic-specific extensions (like axiom negation checking in the bimodal system) can add constructors by defining their own `ClosureReason` that extends or wraps this one. The `ClosureCondition` typeclass approach is better than an inductive `LogicKind` enum because it allows extensibility without modifying the Foundations module.

**Alternative: Predicate-based approach**. Instead of a typeclass with `findClosure`, we could use a predicate parameter:

```lean
structure ClosureConfig (F : Type*) (L : Type*) where
  isContradiction : Sign -> F -> Sign -> F -> L -> Bool  -- do these two signed formulas at this label contradict?
```

This is more flexible but less structured for proof extraction. The typeclass approach is recommended because proof extraction is a primary use case.

#### 6.6 Rule Behavior Parameterization (T(phi -> psi) rule)

The implication rule differs across logic strengths:

| Logic | T(phi -> psi) behavior |
|-------|------------------------|
| Classical | Branch: left gets F(phi), right gets T(psi) -- same label |
| Intuitionistic | Create successor world w': T(phi) at w', F(psi) at w' -- new label |
| Minimal | Same as intuitionistic |

This means the "propositional" rules are NOT fully logic-neutral for the implication-positive case. Two approaches:

**Approach A: RuleConfig structure** (recommended):

```lean
structure RuleConfig (L : Type*) where
  impPosCreatesWorld : Bool              -- does T(phi -> psi) create a new world?
  freshLabel : L -> L                    -- generate fresh label from current (for world creation)
  -- Additional config fields as needed
```

**Approach B: Override-based**. Keep the classical `impPos` rule in `PropositionalRules.lean` and have intuitionistic/minimal modules override it. This is simpler but less uniform.

**Recommendation**: Use Approach A. The `PropositionalRules.lean` file should define rules parameterized over a `RuleConfig` that controls implication behavior. Classical tableau instantiates with `impPosCreatesWorld = false`; intuitionistic/minimal with `impPosCreatesWorld = true`.

However, the `freshLabel` function is problematic because label generation depends on branch state (e.g., `nextWorld`). A cleaner design:

**Approach C: Logic-kind inductive** (simplest, pragmatic):

```lean
inductive LogicKind where
  | classical
  | intuitionistic
  | minimal
```

The propositional rule application function takes `LogicKind` as a parameter. For classical, `T(phi -> psi)` branches; for intuitionistic/minimal, it signals "needs world creation" via a new `RuleResult` variant or by returning metadata about the required fresh label.

**However**, since label creation requires branch context (what's the next fresh world?), the cleanest separation is:

1. `PropositionalRules.lean` defines classical propositional rules (8 rules, all same-label)
2. A separate `ClosureCondition.lean` defines the closure typeclass
3. Logic-specific modules (in `Logics/Propositional/Tableau/`) override the `impPos` rule for intuitionistic/minimal

This keeps `Foundations/Logic/Tableau/` simple and focused on the classical core, with extensibility points for non-classical logics.

#### 6.7 World-Awareness at Propositional Level

The task description states: "Branch needs world-awareness even at propositional level (L = Unit for classical, L = WorldIndex for intuitionistic/minimal)."

This is architecturally sound. The `SignedFormula F L` with `L = Unit` for classical collapses the label to nothing, while `L = WorldIndex` for intuitionistic/minimal adds Kripke-style world tracking. The `Branch` type and `ClosureCondition` are parameterized over `L`, so they work uniformly.

### 7. Recommended File Structure

```
Cslib/Foundations/Logic/Tableau/
  Sign.lean              -- Unified Sign type (pos/neg) with full API
  SignedFormula.lean      -- Generic SignedFormula F L structure
  RuleResult.lean         -- Generic RuleResult F L (linear/branching/persistent/notApplicable)
  PropositionalRules.lean -- 8 classical propositional rules, parameterized over decomposition functions
  Branch.lean             -- Branch F L type with label-generic operations
  Closure.lean            -- ClosureReason and generic closure detection
  ClosureCondition.lean   -- ClosureCondition typeclass with classical/intuitionistic/minimal instances
```

Plus:
- `Cslib/Foundations/Logic/Tableau.lean` -- Module root (import hub)
- Modify `Cslib/Foundations/Logic.lean` to add Tableau import (if it exists as a module root)

### 8. Line Count Estimates

| File | Estimated Lines | Notes |
|------|----------------|-------|
| Sign.lean | 70-90 | Type + flip + simp lemmas + instances |
| SignedFormula.lean | 80-100 | Structure + constructors + flip + helpers |
| RuleResult.lean | 40-60 | Inductive + basic API |
| PropositionalRules.lean | 150-200 | 8 rules + applyPropRule (refactored from existing 210-line file) |
| Branch.lean | 150-200 | Type + operations + basic lemmas |
| Closure.lean | 80-120 | ClosureReason type + generic detection functions |
| ClosureCondition.lean | 100-150 | Typeclass + 3 instances (classical/intuitionistic/minimal) |
| Tableau.lean (root) | 15-20 | Import hub |
| **Total** | **685-940** | Within task estimate of 800-1,100 |

### 9. Key Design Decisions

**D1: Unify Sign types**. Replace both `PropSign` and bimodal `Sign` with a single `Cslib.Logic.Tableau.Sign`. The bimodal system can import this or keep its own until a migration task.

**D2: SignedFormula parameterized over F and L**. This is the core generic abstraction. `L = Unit` for classical propositional, `L = WorldIndex` for intuitionistic/Kripke-based, `L = Label` for bimodal.

**D3: RuleResult includes persistent from day one**. Even though propositional rules don't need it, including it avoids forcing downstream redefinition.

**D4: ClosureCondition as typeclass, not enum**. Extensible -- new logics can define their own instances without modifying Foundations.

**D5: PropositionalRules stay classical-only in Foundations**. The 8 classical propositional rules (including the classical `impPos` branching rule) live in Foundations. Intuitionistic/minimal override the `impPos` behavior in their logic-specific tableau modules. This keeps Foundations simple.

**D6: Branch is a thin type alias**. `Branch F L := List (SignedFormula F L)` with a namespace of helper functions. Logic-specific extensions add their own helpers in their own namespaces.

**D7: ClosureCondition instances need isAtom predicate for minimal logic**. The minimal closure condition needs to distinguish atomic from compound formulas. This requires either a `[DecidableEq F]` constraint or an explicit `isAtom : F -> Bool` parameter. Since `PL.Proposition` has an `atom` constructor, pattern matching works directly, but the generic typeclass needs a way to express "atomic formula." The recommended approach is to include an `isAtom? : F -> Option A` field in the `ClosureCondition` instance for minimal logic, or define it as a standalone class.

### 10. Risks and Mitigations

| Risk | Likelihood | Impact | Mitigation |
|------|-----------|--------|------------|
| Generic SignedFormula F L creates instance resolution issues with BEq/Hashable | Medium | Medium | Require `[DecidableEq F] [DecidableEq L] [BEq F] [BEq L] [Hashable F] [Hashable L]` constraints; use `deriving` where possible |
| ClosureCondition typeclass too rigid for bimodal's 3-check pattern | Low | Medium | Keep bimodal closure standalone; provide enough generic structure that bimodal can optionally wrap it |
| PropositionalRules decomposition-function approach doesn't compose with logic-kind parameterization | Low | Low | Keep decomposition functions AND logic-kind separate; they're orthogonal concerns |
| Universe polymorphism complications with F and L parameters | Medium | High | Follow CSLib conventions: use `Type*` for F and L; test with concrete instantiations early |
| `deriving` clauses fail for SignedFormula when L has complex constraints | Medium | Medium | Write instances manually if needed; bimodal already does this |

### 11. Tactic Survey

For the proof obligations in this task (primarily `simp` lemmas for `flip_flip`, `BEq` lawfulness, and monotonicity lemmas for branch extension):

- `simp` with `[flip, Sign.flip_flip]`: handles sign algebra
- `decide`: handles finite case analysis on `Sign` (2 constructors)
- `cases` + `rfl`: handles most equality proofs on `Sign` and `SignedFormula`
- `exact nofun`: handles impossibility cases in `RuleResult` discriminator lemmas
- No heavy tactics needed; this is primarily definitional infrastructure

## Recommendations

1. **Create files in the order**: Sign.lean -> SignedFormula.lean -> RuleResult.lean -> Branch.lean -> Closure.lean -> ClosureCondition.lean -> PropositionalRules.lean. This respects the import dependency chain.

2. **Keep the namespace as `Cslib.Logic.Tableau`** (not `Cslib.Logic.Foundations.Tableau`). This matches the existing pattern where `PropSign` lives in `Cslib.Logic`.

3. **Do not delete `PropositionalTableau.lean` yet**. Mark it with a deprecation notice pointing to the new module. Delete it in a follow-up cleanup task.

4. **Test instantiability early**: After creating the generic types, verify that `SignedFormula (PL.Proposition Atom) Unit` and `SignedFormula (PL.Proposition Atom) Nat` both compile and have the expected instances.

5. **The ClosureCondition typeclass should have a `findClosure` method returning `Option ClosureReason`**, not just a `Bool`. This supports proof extraction and diagnostic output.

6. **For the minimal logic closure condition**, introduce a helper predicate `IsAtomicFormula` or use a direct parameter `isAtom : F -> Bool` in the instance definition. This is cleaner than requiring formula-type-specific pattern matching in the generic infrastructure.

7. **The implication-positive rule behavior (classical vs intuitionistic)** should be handled by having `PropositionalRules.lean` define only the classical variant. A separate `IntuitionisticRules.lean` or logic-specific override in `Logics/Propositional/Tableau/` handles the world-creating variant. This avoids over-engineering the Foundations module.
