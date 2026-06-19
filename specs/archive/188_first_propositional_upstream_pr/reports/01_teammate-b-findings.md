# Teammate B Findings: PR Scoping Options for Task 188

## Summary

This report maps the module dependency graph for `Cslib/Logics/Propositional/` and proposes
three alternative PR scopes targeting ~300 LOC of new Propositional code. All options build on
Foundations files already present in CSLib (no Foundations additions required in the PR).

---

## 1. Module Dependency Graph

### Propositional/ files and their imports

```
Defs.lean (204 LOC)
  <- Cslib.Foundations.Logic.Connectives  [already in CSLib, 114 LOC]
  <- Mathlib.Data.FunLike.Basic, Mathlib.Data.Set.Basic, Mathlib.Order.TypeTags

ProofSystem/Axioms.lean (219 LOC)
  <- Propositional.Defs

ProofSystem/Derivation.lean (164 LOC)
  <- Propositional.Defs
  <- Cslib.Foundations.Logic.Metalogic.Consistency  [already in CSLib, 285 LOC]

ProofSystem/Instances.lean (120 LOC)
  <- ProofSystem.Derivation, ProofSystem.Axioms
  <- Cslib.Foundations.Logic.ProofSystem  [already in CSLib, 524 LOC]

ProofSystem/IntMinInstances.lean (169 LOC)
  <- ProofSystem.Derivation, ProofSystem.Axioms
  <- Cslib.Foundations.Logic.ProofSystem  [already in CSLib]

Semantics/Basic.lean (64 LOC)
  <- Propositional.Defs

Semantics/Kripke.lean (170 LOC)
  <- Propositional.Defs
  <- Mathlib.Order.Defs.PartialOrder, Mathlib.Order.Defs.Unbundled

Semantics/SemanticConsequence.lean (180 LOC)
  <- Semantics.Basic, Semantics.Kripke, ProofSystem.Derivation

Metalogic/Soundness.lean (93 LOC)
  <- Semantics.Basic, ProofSystem.Derivation, ProofSystem.Axioms

Metalogic/DeductionTheorem.lean (219 LOC)
  <- ProofSystem.Derivation, ProofSystem.Axioms
  <- Cslib.Foundations.Data.ListHelpers  [already in CSLib, 74 LOC]
  <- Cslib.Foundations.Logic.Metalogic.DeductionHelpers  [already in CSLib, 120 LOC]

Metalogic/MCS.lean (162 LOC)
  <- Metalogic.DeductionTheorem

Metalogic/Completeness.lean (347 LOC)
  <- Semantics.Basic, Metalogic.MCS

Metalogic/StrongCompleteness.lean (235 LOC)
  <- Semantics.SemanticConsequence, Metalogic.Completeness, Metalogic.Soundness

NaturalDeduction/Basic.lean (395 LOC)
  <- Propositional.Defs
  <- Cslib.Foundations.Logic.InferenceSystem  [already in CSLib, 68 LOC]
  <- Mathlib.Data.Finset.Insert, Mathlib.Data.Finset.SDiff, Mathlib.Data.Finset.Image

NaturalDeduction/DerivedRules.lean (252 LOC)
  <- NaturalDeduction.Basic

NaturalDeduction/FromHilbert.lean (320 LOC)
  <- Metalogic.DeductionTheorem  (chains through: Derivation, Axioms, ListHelpers, DeductionHelpers)

NaturalDeduction/HilbertDerivedRules.lean (468 LOC)
  <- NaturalDeduction.FromHilbert

NaturalDeduction/Equivalence.lean (400 LOC)
  <- NaturalDeduction.Basic, NaturalDeduction.FromHilbert, NaturalDeduction.HilbertDerivedRules
```

### Minimal self-contained units

The dependency graph has two independent "leaves" from `Defs.lean`:
- **Hilbert leaf**: Axioms -> Derivation -> (Instances, Soundness, DeductionTheorem)
- **ND leaf**: NaturalDeduction/Basic -> DerivedRules
- **Bridge**: FromHilbert requires DeductionTheorem; Equivalence requires both leaves

The truly minimal self-contained unit is:
```
Defs.lean + ProofSystem/Axioms.lean   (204 + 219 = 423 LOC)
```
Both files build only on `Cslib.Foundations.Logic.Connectives` (already committed). No circular
dependencies. This unit defines the language and the three axiom hierarchies (Min/Int/Classical).

---

## 2. LOC per File

| File | LOC |
|------|-----|
| `Propositional/Defs.lean` | 204 |
| `ProofSystem/Axioms.lean` | 219 |
| `ProofSystem/Derivation.lean` | 164 |
| `ProofSystem/Instances.lean` | 120 |
| `ProofSystem/IntMinInstances.lean` | 169 |
| `Semantics/Basic.lean` | 64 |
| `Semantics/Kripke.lean` | 170 |
| `Semantics/SemanticConsequence.lean` | 180 |
| `Metalogic/Soundness.lean` | 93 |
| `Metalogic/DeductionTheorem.lean` | 219 |
| `Metalogic/MCS.lean` | 162 |
| `Metalogic/Completeness.lean` | 347 |
| `Metalogic/StrongCompleteness.lean` | 235 |
| `NaturalDeduction/Basic.lean` | 395 |
| `NaturalDeduction/DerivedRules.lean` | 252 |
| `NaturalDeduction/FromHilbert.lean` | 320 |
| `NaturalDeduction/HilbertDerivedRules.lean` | 468 |
| `NaturalDeduction/Equivalence.lean` | 400 |
| **TOTAL** | **6086** |

Foundations dependencies (all already in CSLib):

| File | LOC | Used by |
|------|-----|---------|
| `Foundations/Logic/Connectives.lean` | 114 | Defs, Axioms (all options) |
| `Foundations/Logic/InferenceSystem.lean` | 68 | ND/Basic only |
| `Foundations/Logic/Metalogic/Consistency.lean` | 285 | Derivation |
| `Foundations/Logic/Metalogic/DeductionHelpers.lean` | 120 | DeductionTheorem |
| `Foundations/Data/ListHelpers.lean` | 74 | DeductionTheorem |
| `Foundations/Logic/ProofSystem.lean` | 524 | Instances, IntMinInstances |
| `Foundations/Logic/Axioms.lean` | 344 | ProofSystem (via InferenceSystem) |

---

## 3. Foundations Dependency Analysis

All Foundations files required by Propositional/ are already committed to CSLib and used by
multiple other modules (Connectives: 8 importing files; Consistency: 13 importing files).

**No Foundations additions are needed in any of the three proposed options.**

The Foundations files are strictly pass-through: they define generic typeclasses and
metalogical infrastructure that the Propositional module instantiates. A reviewer familiar
with the modal or temporal logic modules will already know the Foundations API.

---

## 4. PR Scoping Options

### Option A: Core Definitions Only

**Files included (Propositional/ only)**:
```
Propositional/Defs.lean              204 LOC
ProofSystem/Axioms.lean              219 LOC
Semantics/Basic.lean                  64 LOC
──────────────────────────────────────────
Total new LOC                        487 LOC
```

**Foundations deps (already in CSLib)**: `Connectives.lean` only.

**What this PR establishes**:
- `Proposition` inductive type with 5 primitives (atom, bot, imp, and, or)
- Derived connectives (`neg`, `top`, `iff`) as `abbrev`s
- `Theory` as `Set (Proposition Atom)`, with `MPL`, `IPL`, `CPL` abbreviations
- `IsIntuitionistic` / `IsClassical` typeclasses and extension lemmas
- `Theory.subst` functor, monad instance for `Proposition`
- `Theory.intuitionisticCompletion`
- `PropositionalAxiom` / `IntPropAxiom` / `MinPropAxiom` inductives (3-level hierarchy)
- Subsumption theorems: `MinPropAxiom.toIntPropAxiom`, `IntPropAxiom.toPropAxiom`
- Axiom witnesses for deduction theorem use
- `Valuation`, `Evaluate`, `Tautology` for bivalent semantics

**What reviewers need to understand**:
- The 5-primitive propositional signature (why `and`/`or` are primitives)
- The three-level axiom hierarchy (Min ≤ Int ≤ Classical)
- CSLib's `module` keyword convention

**What this enables for future PRs**:
- PR 2: `ProofSystem/Derivation.lean` + `DeductionTheorem` (Hilbert engine)
- PR 3: `Soundness` + `Completeness` (metalogic)
- PR 4: `NaturalDeduction/Basic` + `DerivedRules`
- PR 5: `NaturalDeduction/Equivalence` (the crown jewel)

**Assessment**: Clean, small, no proof content. Risk: reviewers may ask "why no theorems?"
487 LOC is already above 300; reducing to Defs + Axioms gives 423 LOC (still reasonable).

---

### Option B: Core + Hilbert Proof System + Soundness

**Files included (Propositional/ only)**:
```
Propositional/Defs.lean              204 LOC
ProofSystem/Axioms.lean              219 LOC
ProofSystem/Derivation.lean          164 LOC
Semantics/Basic.lean                  64 LOC
Metalogic/Soundness.lean              93 LOC
──────────────────────────────────────────
Total new LOC                        744 LOC
```

**Foundations deps (already in CSLib)**: `Connectives.lean` + `Consistency.lean`.

**What this PR establishes**:
Everything in Option A, plus:
- `DerivationTree Axioms` parameterized inductive (4 constructors: ax, assumption, mp, weakening)
- `Deriv`, `Derivable` Prop wrappers
- `DerivationTree.height` measure + height bound lemmas
- Basic `mp_deriv`, `weakening_deriv`, `assumption_deriv` combinators
- `propDerivationSystem` connecting PL to the generic `Consistency` framework
- `prop_axiom_sound`: all 10 axiom schemata are valid under all valuations
- `prop_soundness`: soundness by induction on derivation tree height
- `prop_soundness_tautology`: `⊢ φ → Tautology φ`

**What reviewers need to understand**:
- `DerivationTree` as a `Type` (not `Prop`) for height computation
- Parameterization over axiom predicates (enables Min/Int/Classical sharing)
- How `Consistency.DerivationSystem` is satisfied by `propDerivationSystem`
- The three soundness theorems

**What this enables for future PRs**:
- PR 2: `DeductionTheorem` + `Completeness` (Hilbert metalogic complete)
- PR 3: `Instances` + `IntMinInstances` (typeclass registration)
- PR 4: `NaturalDeduction/Basic` + `DerivedRules`
- PR 5: `NaturalDeduction/Equivalence`

**Assessment**: Well-balanced. Delivers a semantics + proof theory that stands alone
(Hilbert system is sound for PL). 744 LOC is above the 300 target but within a reasonable
first PR range for a formal logic module. Reviewer sees both system definition and its first
metatheorem.

**Reduced variant (Option B-)**: Drop `Derivation.lean`, keep Axioms as a schema definition
without the proof engine:
```
Defs.lean (204) + Axioms.lean (219) + Sem/Basic (64) + Soundness* = infeasible
```
Soundness requires `DerivationTree`, so it cannot be separated from `Derivation.lean`.
The minimal Soundness-inclusive cluster is always Defs + Axioms + Derivation + Sem/Basic
+ Soundness = 744 LOC.

---

### Option C: Core + Natural Deduction Only

**Files included (Propositional/ only)**:
```
Propositional/Defs.lean              204 LOC
NaturalDeduction/Basic.lean          395 LOC
NaturalDeduction/DerivedRules.lean   252 LOC
──────────────────────────────────────────
Total new LOC                        851 LOC
```

**Foundations deps (already in CSLib)**: `Connectives.lean` + `InferenceSystem.lean`.

**What this PR establishes**:
- Everything in the language layer of Option A (Defs)
- `Theory.Derivation` inductive with 10 constructors (using `Finset` contexts)
- `InferenceSystem` instances for sequents and propositions
- `Theory.equiv` + `Theory.Equiv` (equivalence of propositions under a theory)
- `Derivation.weak`, `cut`, `cut_away`, `subs`, `substAtom` (structural rules)
- `equiv_iff_equiv_derivableIn` and `equiv_iff_equiv_derivableIn_hypothesis`
- Full set of derived rules in `DerivedRules.lean`: `botE`, `negI`, `negE`, `topI`, `dne`,
  disjunctive syllogism, etc.

**What reviewers need to understand**:
- ND's `Finset` contexts vs Hilbert's `List` contexts (and why)
- `InferenceSystem S α` typeclass notation `T⇓(Γ ⊢ A)`
- That EFQ is a derived rule requiring `[IsIntuitionistic T]`

**What this enables for future PRs**:
- PR 2: `Hilbert system` (Derivation + Axioms)
- PR 3: `FromHilbert` + `HilbertDerivedRules`
- PR 4: `Equivalence` (requires both systems to be merged)
- Alternatively: PR 2 goes straight to Soundness/Completeness for ND

**Assessment**: 851 LOC is nearly 3x the 300-LOC target. The ND system is architecturally
cohesive but too large for a single first PR. A reduced variant dropping `DerivedRules.lean`
gives Defs + ND/Basic = 599 LOC, which is more manageable but still exceeds 300.
The Finset-based ND system is more complex than the Hilbert system for reviewers unfamiliar
with the `InferenceSystem` typeclass notation.

---

## 5. Dependency Graph Summary

```
Cslib.Init
  └─ Foundations.Logic.Connectives (114)
       └─ Propositional.Defs (204)              ← ALL OPTIONS
            ├─ ProofSystem.Axioms (219)          ← ALL OPTIONS
            │    └─ ProofSystem.Derivation (164) ← Options B
            │         ├─ propDerivationSystem
            │         └─ Metalogic.Soundness (93) ← Option B
            │
            └─ NaturalDeduction.Basic (395)      ← Option C
                 └─ NaturalDeduction.DerivedRules (252) ← Option C

Foundations.Logic.Metalogic.Consistency (285)   ← Options B only
  (already in CSLib, used by 13 files)

Foundations.Logic.InferenceSystem (68)           ← Option C only
  (already in CSLib, used by 5 files)
```

---

## 6. Recommendation

**Recommended: Option A+ (Defs + Axioms + Semantics/Basic)**

The cleanest first PR for a ~300-500 LOC target is Option A: `Defs.lean + Axioms.lean +
Semantics/Basic.lean` (487 LOC). This PR:

1. **Introduces the language** (`Proposition`, `Theory`, connective typeclass instances)
2. **Introduces the axiom hierarchy** (Min, Int, Classical with subsumption theorems)
3. **Introduces the semantics type** (`Valuation`, `Evaluate`, `Tautology`)
4. **Is completely self-contained**: only `Foundations.Logic.Connectives` is required
   from outside Propositional/, and that file is already committed
5. **Has low reviewer cognitive load**: three files, no proofs beyond the subsumption
   theorems, clear separation of concerns
6. **Enables PR 2** to be the Hilbert engine (Derivation + Soundness) and PR 3 to be
   the ND system

If the team prefers showing a metatheorem in PR 1, **Option B** (744 LOC) adds the Hilbert
proof engine and soundness. This is still a single coherent logical unit (a sound Hilbert
system) but exceeds the 300-LOC target by 2.5x.

Option C (ND-first, 851 LOC) should be deferred: the ND system is the more novel
contribution but is architecturally more complex to review, and it depends on `FromHilbert`
for the Equivalence proof which is the payoff theorem.

**Suggested PR sequence given Option A recommendation**:

| PR | Files | LOC | Payoff |
|----|-------|-----|--------|
| 1 (this) | Defs, Axioms, Sem/Basic | 487 | Language + axiom hierarchy + semantics |
| 2 | Derivation, Soundness | 257 | Hilbert system is sound |
| 3 | DeductionTheorem, MCS | 381 | Completeness infrastructure |
| 4 | Completeness, StrongCompleteness | 582 | Classical PL is complete |
| 5 | Instances, IntMinInstances | 289 | Typeclass registration for all three logics |
| 6 | ND/Basic, ND/DerivedRules | 647 | Natural deduction system |
| 7 | ND/FromHilbert, ND/HilbertDerivedRules | 788 | Hilbert → ND direction |
| 8 | ND/Equivalence | 400 | Full Hilbert ↔ ND equivalence |
