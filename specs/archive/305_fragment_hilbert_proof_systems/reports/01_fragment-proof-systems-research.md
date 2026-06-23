# Research Report: Fragment Hilbert Proof Systems (Task 305)

## 1. Objective

Define two fragment-specific Hilbert axiom predicates for sub-IPL proof systems:

1. **ConjImpAxiom** for IPL(and, imp, top) -- the conjunctive-implicational fragment
2. **ImpAxiom** for IPL(imp, top) -- the pure implicational fragment

Prove substitution closure, establish that modus ponens is the sole rule, prove the
deduction theorem for each fragment, provide subsumption lemmas, and create tag types with
typeclass instances. These are the proof-theoretic counterparts to `BrouwerianSemilattice`
(task 303) and `HilbertAlgebra` (task 304).

## 2. Existing Architecture Analysis

### 2.1 Axiom Predicate Pattern

The codebase defines axiom predicates as inductive types on `PL.Proposition Atom -> Prop`:

| Predicate | Axioms | File |
|-----------|--------|------|
| `PropositionalAxiom` | K, S, efq, peirce, andI, andE1, andE2, orI1, orI2, orE (10) | `Axioms.lean` |
| `IntPropAxiom` | K, S, efq, andI, andE1, andE2, orI1, orI2, orE (9) | `Axioms.lean` |
| `MinPropAxiom` | K, S, andI, andE1, andE2, orI1, orI2, orE (8) | `Axioms.lean` |

The new fragment predicates follow the same pattern:

| Predicate | Axioms |
|-----------|--------|
| `ConjImpAxiom` | K, S, andI, andE1, andE2 (5) |
| `ImpAxiom` | K, S (2) |

### 2.2 Subsumption Hierarchy

Current chain: `MinPropAxiom -> IntPropAxiom -> PropositionalAxiom`

Extended chain:
```
ImpAxiom -> ConjImpAxiom -> MinPropAxiom -> IntPropAxiom -> PropositionalAxiom
```

Each subsumption theorem follows the pattern in `Axioms.lean` (lines 155-179): case-match on
the inductive and rebuild with the superset constructor.

### 2.3 Derivation System

`DerivationTree Axioms Gamma phi` (in `Derivation.lean`) is parameterized over an arbitrary
`Axioms : PL.Proposition Atom -> Prop`. It already works with any axiom predicate. The 4
constructors are: `ax`, `assumption`, `modus_ponens`, `weakening`.

`Deriv Axioms Gamma phi := Nonempty (DerivationTree Axioms Gamma phi)` and
`Derivable Axioms phi := Deriv Axioms [] phi` are similarly parameterized.

The `propDerivationSystem Axioms` gives a `Metalogic.DerivationSystem` instance for any
axiom predicate. No new derivation system infrastructure is needed.

### 2.4 Tag Types and Instances

Tag types are `opaque ... : Type := Empty` in `ProofSystem.lean`. Current propositional tags:
- `Propositional.HilbertCl`, `Propositional.HilbertInt`, `Propositional.HilbertMin`

Instance registration in `Instances.lean` and `IntMinInstances.lean` follows a fixed pattern:
1. `InferenceSystem` mapping `derivation` to `DerivationTree AxiomPred []`
2. `ModusPonens` using `DerivationTree.modus_ponens`
3. Individual `HasAxiom*` instances using `DerivationTree.ax [] _ (.constructor _ _)`
4. Bundled class instance (e.g., `MinimalHilbert`)

New tag types needed:
- `Propositional.HilbertConjImp` -- for IPL(and, imp, top)
- `Propositional.HilbertImp` -- for IPL(imp, top)

### 2.5 Bundled Class Consideration

The existing bundled classes in `ProofSystem.lean`:
- `MinimalHilbert S` extends `ModusPonens S`, `HasAxiomImplyK S`, `HasAxiomImplyS S`

`MinimalHilbert` already captures the K + S + MP combination. However, `MinimalHilbert` does
NOT extend the `HasAxiomAnd*` classes -- those are registered separately in the instance files.

For `ImpAxiom`, the bundled class is exactly `MinimalHilbert` (K + S + MP).

For `ConjImpAxiom`, there is no existing bundled class that captures exactly K + S + andI +
andE1 + andE2 + MP. Two options:
- (A) Define a new bundled class `ConjImpHilbert` extending `MinimalHilbert` with
  `HasAxiomAndI`, `HasAxiomAndE1`, `HasAxiomAndE2`.
- (B) Register individual instances without a new bundled class.

**Recommendation**: Option (B) for now -- register individual instances. The bundled classes
in CSLib follow Lean 4 typeclass hierarchy conventions; adding a class only used by one proof
system is premature. The individual `HasAxiom*` instances suffice for downstream consumers.
If task 306/309 need a bundled class, it can be added later.

### 2.6 Deduction Theorem

The deduction theorem in `DeductionTheorem.lean` is already parameterized:

```lean
noncomputable def deductionTheorem
    {Axioms : PL.Proposition Atom -> Prop}
    (h_implyK : forall (phi psi : PL.Proposition Atom), Axioms (phi.imp (psi.imp phi)))
    (h_implyS : forall (phi psi chi : PL.Proposition Atom),
      Axioms ((phi.imp (psi.imp chi)).imp ((phi.imp psi).imp (phi.imp chi))))
    (Gamma : List (PL.Proposition Atom)) (A B : PL.Proposition Atom)
    (d : DerivationTree Axioms (A :: Gamma) B) :
    DerivationTree Axioms Gamma (A -> B)
```

It only needs K and S axioms. Since both `ConjImpAxiom` and `ImpAxiom` include K and S,
the deduction theorem applies immediately by instantiating `h_implyK` and `h_implyS` with
the appropriate constructors. No new proof is needed -- just witness lemmas.

Similarly, `hasDeductionTheorem` wraps this for the `Metalogic.HasDeductionTheorem` typeclass.

### 2.7 Substitution Closure

The substitution closure proofs in `FromHilbert.lean` follow a uniform pattern:
case-match on the axiom inductive and rebuild with `(a.subst f)` applied to each formula.

For example (`subst_preserves_minAxiom`, line 267):
```lean
theorem subst_preserves_minAxiom {phi : PL.Proposition Atom}
    (h : MinPropAxiom phi) (f : Atom -> PL.Proposition Atom') :
    MinPropAxiom (phi.subst f) := by
  cases h with
  | implyK a b => exact .implyK (a.subst f) (b.subst f)
  | implyS a b c => exact .implyS (a.subst f) (b.subst f) (c.subst f)
  | andI a b => exact .andI (a.subst f) (b.subst f)
  ...
```

The new `subst_preserves_conjImpAxiom` and `subst_preserves_impAxiom` follow the same pattern
with fewer cases.

### 2.8 Fragment Predicates (Task 302)

`FragmentPredicates.lean` defines:
- `Proposition.IsOrBotFree` -- no disjunction or falsum (corresponds to ConjImpAxiom fragment)
- `Proposition.IsImpTopOnly` -- only implication and atoms (corresponds to ImpAxiom fragment)

Key observation: Every axiom instance produced by `ConjImpAxiom` must be or-bot-free, and
every axiom instance produced by `ImpAxiom` must be imp-top-only. This is provable by
simple case analysis on the inductive constructors.

### 2.9 Implication Axiom Witnesses Pattern

`Axioms.lean` provides `mem_implyK` and `mem_implyS` witness theorems for each axiom
predicate (lines 183-228). These are used as arguments to the deduction theorem. The new
fragment predicates need the same witnesses.

### 2.10 MinimalAxioms Class

The `MinimalAxioms` class (in `Equivalence.lean`) bundles K, S, and all and/or axioms. It
is used by the Hilbert Lindenbaum algebra construction. The fragment axiom predicates do NOT
satisfy `MinimalAxioms` (they lack disjunction axioms). This is expected -- the fragment
Lindenbaum algebras (tasks 306, 309) will use different algebraic structures.

## 3. Implementation Design

### 3.1 File Location

`Cslib/Logics/Propositional/ProofSystem/FragmentAxioms.lean`

This file should import:
- `Cslib.Logics.Propositional.ProofSystem.Axioms` (for subsumption to `MinPropAxiom`)
- `Cslib.Logics.Propositional.ProofSystem.Derivation` (for `DerivationTree`, `Deriv`, etc.)
- `Cslib.Logics.Propositional.Metalogic.DeductionTheorem` (for `deductionTheorem`, `hasDeductionTheorem`)

### 3.2 Definitions and Theorems

#### Phase 1: Inductive Axiom Predicates

```lean
inductive ConjImpAxiom : PL.Proposition Atom -> Prop where
  | implyK (phi psi : PL.Proposition Atom) :
      ConjImpAxiom (phi.imp (psi.imp phi))
  | implyS (phi psi chi : PL.Proposition Atom) :
      ConjImpAxiom ((phi.imp (psi.imp chi)).imp ((phi.imp psi).imp (phi.imp chi)))
  | andI (phi psi : PL.Proposition Atom) :
      ConjImpAxiom (phi.imp (psi.imp (phi.and psi)))
  | andE1 (phi psi : PL.Proposition Atom) :
      ConjImpAxiom ((phi.and psi).imp phi)
  | andE2 (phi psi : PL.Proposition Atom) :
      ConjImpAxiom ((phi.and psi).imp psi)

inductive ImpAxiom : PL.Proposition Atom -> Prop where
  | implyK (phi psi : PL.Proposition Atom) :
      ImpAxiom (phi.imp (psi.imp phi))
  | implyS (phi psi chi : PL.Proposition Atom) :
      ImpAxiom ((phi.imp (psi.imp chi)).imp ((phi.imp psi).imp (phi.imp chi)))
```

#### Phase 2: Subsumption Hierarchy

```lean
theorem ImpAxiom.toConjImpAxiom : ImpAxiom phi -> ConjImpAxiom phi
theorem ConjImpAxiom.toMinPropAxiom : ConjImpAxiom phi -> MinPropAxiom phi
```

(Transitively: `ImpAxiom -> ConjImpAxiom -> MinPropAxiom -> IntPropAxiom -> PropositionalAxiom`)

#### Phase 3: Implication Axiom Witnesses

```lean
namespace ConjImpAxiom
theorem mem_implyK : forall (phi psi), ConjImpAxiom (phi.imp (psi.imp phi))
theorem mem_implyS : forall (phi psi chi), ConjImpAxiom (...)
end ConjImpAxiom

namespace ImpAxiom
theorem mem_implyK : forall (phi psi), ImpAxiom (phi.imp (psi.imp phi))
theorem mem_implyS : forall (phi psi chi), ImpAxiom (...)
end ImpAxiom
```

#### Phase 4: Substitution Closure

```lean
theorem subst_preserves_conjImpAxiom
    (h : ConjImpAxiom phi) (f : Atom -> PL.Proposition Atom') :
    ConjImpAxiom (phi.subst f)

theorem subst_preserves_impAxiom
    (h : ImpAxiom phi) (f : Atom -> PL.Proposition Atom') :
    ImpAxiom (phi.subst f)
```

#### Phase 5: Fragment Predicate Compatibility

```lean
theorem ConjImpAxiom.isOrBotFree (h : ConjImpAxiom phi) : phi.IsOrBotFree = true
theorem ImpAxiom.isImpTopOnly (h : ImpAxiom phi) : phi.IsImpTopOnly = true
```

These state that fragment axiom predicates produce only formulas within the corresponding
syntactic fragment. This is critical for tasks 306/309 where soundness proofs need to know
that axiom instances stay within the fragment.

#### Phase 6: Deduction Theorem Instances

```lean
noncomputable instance : Metalogic.HasDeductionTheorem (propDerivationSystem (@ConjImpAxiom Atom))
noncomputable instance : Metalogic.HasDeductionTheorem (propDerivationSystem (@ImpAxiom Atom))
```

Or equivalently as named theorems:

```lean
theorem conjImpHasDeductionTheorem :
    Metalogic.HasDeductionTheorem (propDerivationSystem (@ConjImpAxiom Atom)) :=
  hasDeductionTheorem ConjImpAxiom.mem_implyK ConjImpAxiom.mem_implyS

theorem impHasDeductionTheorem :
    Metalogic.HasDeductionTheorem (propDerivationSystem (@ImpAxiom Atom)) :=
  hasDeductionTheorem ImpAxiom.mem_implyK ImpAxiom.mem_implyS
```

### 3.3 Optional: Tag Types and Typeclass Instances

**Decision**: Include tag types and instances in this file. Tasks 306 and 309 depend on them,
and the pattern is mechanical (identical to `IntMinInstances.lean`).

Tag types (to be added in `ProofSystem.lean`):
```lean
opaque Propositional.HilbertConjImp : Type := Empty
opaque Propositional.HilbertImp : Type := Empty
```

Instance registration in `FragmentAxioms.lean` (or a separate `FragmentInstances.lean`):
- `InferenceSystem Propositional.HilbertConjImp` with `DerivationTree ConjImpAxiom []`
- `ModusPonens Propositional.HilbertConjImp`
- `HasAxiomImplyK`, `HasAxiomImplyS`, `HasAxiomAndI`, `HasAxiomAndE1`, `HasAxiomAndE2`
  for `HilbertConjImp`
- `MinimalHilbert Propositional.HilbertConjImp` (K + S + MP satisfied)
- `InferenceSystem Propositional.HilbertImp` with `DerivationTree ImpAxiom []`
- `ModusPonens Propositional.HilbertImp`
- `HasAxiomImplyK`, `HasAxiomImplyS` for `HilbertImp`
- `MinimalHilbert Propositional.HilbertImp` (K + S + MP satisfied)

**Important**: `MinimalHilbert` only requires K + S + MP. Both fragments satisfy this.
The difference is that `HilbertConjImp` additionally has `HasAxiomAnd*` instances while
`HilbertImp` does not. Neither has `HasAxiomOr*` or `HasAxiomEFQ`.

**Alternative**: Place tag types in `ProofSystem.lean` (where the other tags live) and
instances in a separate `FragmentInstances.lean`. This follows the existing organization
where `ProofSystem.lean` has tags and `Instances.lean`/`IntMinInstances.lean` have instances.

**Recommendation**: Tag types in `ProofSystem.lean`, axiom inductive definitions + substitution
+ fragment compatibility in `FragmentAxioms.lean`, instances in `FragmentInstances.lean`.
This mirrors the existing 3-file pattern and keeps each file focused.

## 4. Proof Difficulty Assessment

All proofs in this task are mechanical case-analysis or direct instantiation:

| Proof | Strategy | Difficulty |
|-------|----------|------------|
| Subsumption theorems | Case-match on inductive, rebuild | Trivial |
| `mem_implyK` / `mem_implyS` | Constructor application | Trivial |
| Substitution closure | Case-match, apply `.subst f` to each formula arg | Trivial |
| Fragment predicate compat | Case-match, simp on IsOrBotFree/IsImpTopOnly | Easy |
| Deduction theorem instances | Apply existing `hasDeductionTheorem` with witnesses | Trivial |
| Tag type instances | Constructor-based, identical to existing pattern | Trivial |

**Zero sorry risk**: All proofs follow established patterns with no novel steps.

## 5. Import Dependencies

```
FragmentAxioms.lean
  <- Cslib.Logics.Propositional.ProofSystem.Axioms
  <- Cslib.Logics.Propositional.Semantics.Algebra.FragmentPredicates (for IsOrBotFree, IsImpTopOnly)

FragmentInstances.lean (if separate)
  <- Cslib.Logics.Propositional.ProofSystem.FragmentAxioms
  <- Cslib.Logics.Propositional.ProofSystem.Derivation
  <- Cslib.Logics.Propositional.Metalogic.DeductionTheorem
  <- Cslib.Foundations.Logic.ProofSystem (for HasAxiom* classes)
```

Alternatively, if everything is in one file (`FragmentAxioms.lean`), it imports all of the above.

**Import consideration**: Importing `FragmentPredicates.lean` transitively pulls in
`Conservative.lean` and `Algebra.lean` (GHA evaluation machinery). This is acceptable since
the fragment compatibility theorems genuinely need the predicate definitions. However, if
minimal imports are preferred, the fragment compatibility theorems could be placed in a
separate file or deferred to downstream tasks. Since tasks 306/309 need these results,
including them here is the practical choice.

## 6. Downstream Impact

### Task 306 (Brouwerian Completeness)

Needs: `ConjImpAxiom`, `Derivable ConjImpAxiom`, `ConjImpAxiom.isOrBotFree`,
subsumption `ConjImpAxiom.toMinPropAxiom`, deduction theorem for `ConjImpAxiom`,
tag type `Propositional.HilbertConjImp`.

### Task 309 (Hilbert Algebra Completeness)

Needs: `ImpAxiom`, `Derivable ImpAxiom`, `ImpAxiom.isImpTopOnly`,
subsumption `ImpAxiom.toConjImpAxiom`, deduction theorem for `ImpAxiom`,
tag type `Propositional.HilbertImp`.

### Task 308 (Conservative Extension, Brouwerian)

Needs: `Derivable ConjImpAxiom phi` as the target derivability predicate in the conservative
extension statement.

### Task 311 (Conservative Extension, Hilbert Algebra)

Needs: `Derivable ImpAxiom phi` similarly.

## 7. Open Questions

1. **File organization**: One file (`FragmentAxioms.lean`) or split into `FragmentAxioms.lean`
   + `FragmentInstances.lean`? The single-file approach is simpler; splitting follows the
   existing `Axioms.lean` / `Instances.lean` / `IntMinInstances.lean` pattern.

2. **Tag type placement**: In `ProofSystem.lean` (canonical) or in the new file? Canonical
   placement is cleaner but requires editing a Foundations file.

3. **Bundled class for ConjImpHilbert**: Premature unless needed. Register individual
   instances for now.

**Recommendation**: Single file `FragmentAxioms.lean` containing everything (axiom predicates,
subsumption, substitution, fragment compatibility, witnesses, deduction theorem instances).
Tag types in `ProofSystem.lean`. No separate instances file needed since the instance count
is small. If the planner prefers splitting, `FragmentInstances.lean` can hold the tag type
instances.

## 8. Lint Compliance Checklist

- [ ] All new declarations have docstrings (docBlame)
- [ ] Prop-valued declarations use `lemma`/`theorem` not `def` (defLemma)
- [ ] Names use lowerCamelCase (defsWithUnderscore -- but inductive constructors conventionally use lowerCamelCase already)
- [ ] `@[simp]` lemmas have LHS verification (simpNF) -- unlikely to need simp here
- [ ] Section variables minimal (unusedSectionVars)
- [ ] File starts with `import Cslib.Init` (checkInitImports -- via public import chain)
