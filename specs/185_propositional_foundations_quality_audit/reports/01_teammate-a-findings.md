# Teammate A Findings: Architecture, Organization, and Import Hygiene

## 1. Module Structure and Organization

### 1.1 Propositional/ Directory Layout

```
Cslib/Logics/Propositional/
  Defs.lean                          (201 lines)  -- Proposition type, Theory, IsClassical/IsIntuitionistic
  Metalogic/
    Completeness.lean                (311 lines)  -- Classical canonical model + truth lemma
    DeductionTheorem.lean            (217 lines)  -- Deduction theorem (well-founded recursion)
    IntCompleteness.lean             (182 lines)  -- Intuitionistic canonical model + truth lemma
    IntLindenbaum.lean               (506 lines)  -- IntDCCS, deductive closure, prime extension
    IntSoundness.lean                (128 lines)  -- Intuitionistic soundness
    IntStrongCompleteness.lean       (192 lines)  -- Intuitionistic strong completeness + compactness
    MCS.lean                         (161 lines)  -- Generic MCS properties (parameterized)
    MinCompleteness.lean             (195 lines)  -- Minimal canonical model + truth lemma
    MinLindenbaum.lean               (428 lines)  -- MinTheory, deductive closure, prime extension
    MinSoundness.lean                (121 lines)  -- Minimal soundness
    MinStrongCompleteness.lean       (173 lines)  -- Minimal strong completeness + compactness
    Soundness.lean                   ( 93 lines)  -- Classical soundness
    StrongCompleteness.lean          (252 lines)  -- Classical strong completeness + compactness
  NaturalDeduction/
    Basic.lean                       (395 lines)  -- Standalone ND system (Finset contexts)
    DerivedRules.lean                (253 lines)  -- Derived ND rules (botE, dne, iff, etc.)
    Equivalence.lean                 (306 lines)  -- Hilbert <-> ND equivalence bridge
    FromHilbert.lean                 (320 lines)  -- ND wrappers around Hilbert derivations
    HilbertDerivedRules.lean         (468 lines)  -- Derived rules in Hilbert framework
  ProofSystem/
    Axioms.lean                      (180 lines)  -- PropositionalAxiom/IntPropAxiom/MinPropAxiom
    Derivation.lean                  (163 lines)  -- DerivationTree + Deriv + Derivable
    Instances.lean                   (120 lines)  -- Classical HilbertCl instances
    IntMinInstances.lean             (169 lines)  -- Intuitionistic/Minimal instances
  Semantics/
    Basic.lean                       ( 49 lines)  -- Valuation, Evaluate, Tautology
    Kripke.lean                      (142 lines)  -- KripkeModel, IForces, IValid, MValid
    SemanticConsequence.lean         (181 lines)  -- SetDerivable, SemanticEntails
```

**Total**: 26 files, ~5,905 lines

**Assessment**: The hierarchy is logically organized into four clear subdirectories (Metalogic, NaturalDeduction, ProofSystem, Semantics) plus a root Defs.lean. The separation follows Mathlib conventions well. No files need to be moved between subdirectories.

### 1.2 Foundations/Logic/ Directory Layout

```
Cslib/Foundations/Logic/
  Axioms.lean                        (331 lines)  -- Polymorphic axiom abbrevs
  Connectives.lean                   (114 lines)  -- HasBot/HasImp/HasAnd/HasOr/HasBox typeclasses
  InferenceSystem.lean               ( 68 lines)  -- InferenceSystem typeclass + notation
  LogicalEquivalence.lean            ( 35 lines)  -- LogicalEquivalence typeclass
  ProofSystem.lean                   (524 lines)  -- MinimalHilbert/IntuitionisticHilbert/ClassicalHilbert hierarchy
  Metalogic/
    Consistency.lean                  (278 lines)  -- DerivationSystem, MCS framework, Zorn's lemma
    DeductionHelpers.lean            (120 lines)  -- HasHilbertTree typeclass for deduction theorem
  Theorems/
    Theorems.lean (barrel)           ( 59 lines)  -- Module aggregator
    Combinators.lean                 (339 lines)  -- I/B/C/S combinators, imp_trans
    BigConj.lean                     (142 lines)  -- Big conjunction over lists
    Propositional/
      Core.lean                      (311 lines)  -- LEM, DNE, Peirce, efq
      Connectives.lean               (539 lines)  -- Contraposition, De Morgan, iff rules
    Modal/
      Basic.lean                     (203 lines)  -- K-level modal theorems
      S5.lean                        (533 lines)  -- S5-level modal theorems
    Temporal/
      FrameConditions.lean           ( 89 lines)  -- Frame condition typeclasses (NOT theorems)
      TemporalDerived.lean           (292 lines)  -- BX-system derived theorems
```

**Total**: 16 files, ~3,977 lines

**Assessment**: The hierarchy is well-organized overall. However, there is one misplaced file (see Finding F-1 below).

---

## 2. Findings

### Finding F-1: FrameConditions.lean misplaced under Theorems/

**Priority**: LOW  
**File**: `Cslib/Foundations/Logic/Theorems/Temporal/FrameConditions.lean`

`FrameConditions.lean` defines typeclasses (`LinearTemporalFrame`, `SerialFrame`, `DenseTemporalFrame`, `DiscreteTemporalFrame`) and instances -- it contains zero theorems. It is placed under `Theorems/Temporal/` alongside `TemporalDerived.lean`, but its content is structural (typeclasses + instances), not proof-theoretic.

A more natural location would be `Cslib/Foundations/Logic/Temporal/FrameConditions.lean` (sibling to `Metalogic/`, not under `Theorems/`). However, since this file has downstream consumers and the current placement is documented in the barrel `Theorems.lean`, the cost of moving it may outweigh the benefit.

**Recommendation**: Accept current placement but document the anomaly in the `Theorems.lean` barrel docstring. If a future `Foundations/Logic/Temporal/` directory is created, move it then.

---

### Finding F-2: Unused `Std.Tactic.BVDecide.Normalize` imports

**Priority**: HIGH  
**Files**:
- `Cslib/Logics/Propositional/NaturalDeduction/DerivedRules.lean` (line 10)
- `Cslib/Logics/Propositional/Semantics/SemanticConsequence.lean` (line 12)

Both files contain `public import Std.Tactic.BVDecide.Normalize` but neither file uses any BVDecide-related tactics (`bv_decide`, `bv_omega`). Grep for `bv_decide`, `bv_omega`, `omega`, and `decide` returned zero hits in both files. This is dead import weight that pulls in unnecessary Std dependencies.

`lake shake` did not flag these (likely `--keep-implied` suppresses it), but manual inspection confirms they are unused.

**Recommendation**: Remove both `public import Std.Tactic.BVDecide.Normalize` lines.

---

### Finding F-3: `lake shake` identified import hygiene issues

**Priority**: HIGH  
**Concrete `lake shake` findings** (run with `--add-public --keep-implied --keep-prefix`):

| File | Action | Import |
|------|--------|--------|
| `Metalogic/IntCompleteness.lean` | **remove** | `public import Cslib.Logics.Propositional.Metalogic.IntSoundness` |
| `Metalogic/IntStrongCompleteness.lean` | **add** | `public import Cslib.Logics.Propositional.Metalogic.IntSoundness` |
| `Metalogic/MinCompleteness.lean` | **remove** | `public import Cslib.Logics.Propositional.Metalogic.MinSoundness` |
| `Metalogic/MinStrongCompleteness.lean` | **add** | `public import Cslib.Logics.Propositional.Metalogic.MinSoundness` |

**Pattern**: Both IntCompleteness and MinCompleteness import their respective Soundness modules but do not directly use them. The Soundness modules are actually needed at the StrongCompleteness level. This is a transitive import leakage pattern: IntCompleteness pulls in IntSoundness, and IntStrongCompleteness gets it transitively rather than directly.

**Recommendation**: Apply `lake shake --fix` for these 4 changes. The fix moves the import to where it is actually needed, reducing unnecessary transitive dependency.

---

### Finding F-4: All 68 Propositional imports are `public`; 0 are private

**Priority**: MEDIUM  
**Scope**: All 26 files in `Cslib/Logics/Propositional/`

Every single import in the Propositional module uses `public import`. This means every downstream consumer of any Propositional file transitively receives all of its dependencies. For comparison, `Foundations/Logic/` uses a mixed strategy: 29 `public import` + 15 private `import` (for `Cslib.Init` which is appropriately kept private).

In the Propositional module, `public import Cslib.Init` in `Defs.lean` (line 9) makes `Cslib.Init` transitively public to all downstream consumers. The Foundations pattern of using non-public `import Cslib.Init` is preferable since `Init` is an implementation detail (linting rules, tactics) not part of the public API.

**Recommendation**: Change `Defs.lean` line 9 from `public import Cslib.Init` to `import Cslib.Init`. Review whether Mathlib imports (e.g., `Mathlib.Data.FunLike.Basic`, `Mathlib.Order.TypeTags`) need to be public or could also be made private.

---

### Finding F-5: 3-fold structural duplication in Metalogic (Min/Int/Classical)

**Priority**: MEDIUM  
**Files**: 12 files forming 4 parallel triads:

| Triad | Classical | Intuitionistic | Minimal |
|-------|-----------|----------------|---------|
| Soundness | `Soundness.lean` (93 lines) | `IntSoundness.lean` (128 lines) | `MinSoundness.lean` (121 lines) |
| Completeness | `Completeness.lean` (311 lines) | `IntCompleteness.lean` (182 lines) | `MinCompleteness.lean` (195 lines) |
| Lindenbaum | MCS.lean (161 lines) | `IntLindenbaum.lean` (506 lines) | `MinLindenbaum.lean` (428 lines) |
| StrongCompleteness | `StrongCompleteness.lean` (252 lines) | `IntStrongCompleteness.lean` (192 lines) | `MinStrongCompleteness.lean` (173 lines) |

The three soundness files follow an identical structure (`axiom_sound` -> `soundness` -> `soundness_derivable`). The three completeness files share identical `and` and `or` cases in their truth lemmas (the structural cases are literally the same proof with different axiom predicates). The Lindenbaum files share the same proof scaffolding (deductive closure, prime exclusion via Zorn's lemma).

**Specific duplication patterns**:
1. **Private helper definitions**: `h_implyK` / `h_implyS` are duplicated across 4 files (Completeness, StrongCompleteness, IntLindenbaum, MinLindenbaum) -- 8 definitions total, all doing `fun phi psi => .implyK phi psi`.
2. **Truth lemma and/or cases**: The `| .and phi psi =>` and `| .or phi psi =>` branches in all three truth lemmas (classical, intuitionistic, minimal) are structurally identical since and/or are handled the same way regardless of logic strength.
3. **StrongCompleteness structure**: The `strong_soundness`, `strong_completeness_iff`, `compactness`, `completeness`, and `soundness_completeness` theorems follow identical patterns in all three files.

**Recommendation**: This is a known consequence of Lean 4's lack of inheritance for inductives -- the three axiom predicates are separate types. The current approach is correct and maintainable. Future work could introduce a generic parameterized framework (a `PropLogic` typeclass parameterizing over axiom predicate, validity notion, and world type), but this is a significant refactor with uncertain payoff. Mark as LOW priority for long-term consideration, not an action item.

---

### Finding F-6: Duplicate `private def h_implyK/h_implyS` helpers

**Priority**: MEDIUM  
**Files**:
- `Completeness.lean` lines 43-52: `h_implyK`, `h_implyS` for `PropositionalAxiom`
- `StrongCompleteness.lean` lines 59-68: `sc_h_implyK`, `sc_h_implyS` for `PropositionalAxiom`
- `IntLindenbaum.lean` lines 35-42: `int_h_implyK`, `int_h_implyS` for `IntPropAxiom`
- `MinLindenbaum.lean` lines 47-54: `min_h_implyK`, `min_h_implyS` for `MinPropAxiom`

These are trivial constructor wrappers (e.g., `fun phi psi => .implyK phi psi`). They exist because the deduction theorem and MCS machinery require explicit axiom witnesses, and `private` prevents sharing across files.

Since each axiom predicate defines its own `implyK`/`implyS` constructors, these cannot be unified across logics. However, within each logic:
- `h_implyK` and `sc_h_implyK` in Completeness and StrongCompleteness are identical.

**Recommendation**: Consider defining non-private helper lemmas in `ProofSystem/Axioms.lean` (e.g., `PropositionalAxiom.implyK_proof`, `IntPropAxiom.implyK_proof`), then using them across the Metalogic files. This would eliminate ~16 lines of boilerplate per axiom predicate.

---

### Finding F-7: No barrel import files for Propositional/ subdirectories

**Priority**: LOW  
**Scope**: `Cslib/Logics/Propositional/`

There are no `Metalogic.lean`, `NaturalDeduction.lean`, `ProofSystem.lean`, or `Semantics.lean` barrel files for the four subdirectories. Similarly, there is no `Propositional.lean` barrel file. All 26 files are individually listed in `Cslib.lean`.

This is consistent with CSLib's existing pattern (Modal, Temporal, and Bimodal also lack subdirectory barrel files), but differs from Mathlib convention where each directory typically has a corresponding barrel file.

**Recommendation**: No action needed. The flat listing in `Cslib.lean` serves as the sole barrel mechanism, which is acceptable for a library of this size. If the module grows significantly, consider introducing barrel files.

---

### Finding F-8: NaturalDeduction/DerivedRules and HilbertDerivedRules functional overlap

**Priority**: LOW  
**Files**:
- `NaturalDeduction/DerivedRules.lean` (253 lines) -- Derived rules in standalone ND system
- `NaturalDeduction/HilbertDerivedRules.lean` (468 lines) -- Derived rules in Hilbert framework

Both files define rules with matching names (`negI`/`hilbertNegI`, `negE`/`hilbertNegE`, `topI`/`hilbertTopI`, `botE`/`hilbertBotE`, `andI`/`hilbertAndI`, etc.). The `Equivalence.lean` bridge proves these systems are extensionally equivalent.

This is intentional: the two proof systems (Finset-context ND vs List-context Hilbert) coexist for different use cases. DerivedRules works in the standalone ND system; HilbertDerivedRules works in the Hilbert derivation tree that connects to the metalogic (completeness, soundness).

**Recommendation**: No action needed. The parallel structure is well-documented in `Defs.lean` (Architecture section) and `Equivalence.lean` (bridge module). The naming convention (`Theory.Derivation.X` vs `hilbertX`) clearly distinguishes the two systems.

---

### Finding F-9: `Derivable` name exists in both Foundations and Propositional

**Priority**: LOW  
**Files**:
- `Cslib/Foundations/Logic/InferenceSystem.lean` line 48: `abbrev Derivable` (in namespace `Cslib.Logic.InferenceSystem`)
- `Cslib/Logics/Propositional/ProofSystem/Derivation.lean` line 127: `def Derivable` (in namespace `Cslib.Logic.PL`)

These are distinct concepts:
- `InferenceSystem.Derivable`: Generic derivability in the default inference system (`Nonempty (Default⇓a)`)
- `PL.Derivable`: Propositional derivability from empty context (`Deriv Axioms [] phi`)

The namespace separation prevents ambiguity in practice. However, fully qualified names like `Derivable PropositionalAxiom phi` (PL) vs `InferenceSystem.Derivable a` could confuse readers.

**Recommendation**: No action required. The namespace separation is sufficient. Document the distinction if a user guide is written.

---

### Finding F-10: Foundations/Logic/Theorems.lean is a barrel without `@[expose]`

**Priority**: LOW  
**File**: `Cslib/Foundations/Logic/Theorems.lean`

This is the only file in both directories that lacks `@[expose] public section`. It is a barrel import file (only `import` statements + docstring, no definitions), so `@[expose]` is unnecessary. This is correct behavior.

**Recommendation**: No action needed.

---

## 3. Module Documentation Audit

### 3.1 Docstring Coverage

**All 42 files** in both directories have `/-! ... -/` module docstrings. Coverage is 100%.

### 3.2 Docstring Quality Assessment

| Quality Aspect | Coverage | Notes |
|----------------|----------|-------|
| Purpose statement | 42/42 | All files describe what they contain |
| Main definitions/results | 40/42 | LogicalEquivalence.lean and Theorems.lean (barrel) are brief |
| References | 30/42 | Most Metalogic files reference "CZ" (Chagrov-Zakharyaschev); Foundations files less consistent |
| Architecture notes | 8/42 | Defs.lean, Equivalence.lean, FromHilbert.lean have excellent architecture sections |
| Design rationale | 12/42 | Key design decisions documented (e.g., Kripke.lean explains Preorder vs PartialOrder choice) |

**Missing docstrings**: None -- all files have docstrings.

**Particularly strong docstrings**:
- `Defs.lean`: Comprehensive architecture overview of the two proof systems
- `Connectives.lean`: Explains the hybrid five-primitive design decision with references
- `MCS.lean`: Clear parameterization design documentation
- `StrongCompleteness.lean`: Excellent strategy section explaining the proof approach

---

## 4. Summary of Recommendations

### HIGH Priority (should fix)
1. **F-2**: Remove unused `Std.Tactic.BVDecide.Normalize` imports from DerivedRules.lean and SemanticConsequence.lean
2. **F-3**: Apply `lake shake` fixes (4 import moves between Int/Min Completeness and StrongCompleteness)

### MEDIUM Priority (should consider)
3. **F-4**: Change `public import Cslib.Init` to `import Cslib.Init` in Defs.lean
4. **F-6**: Extract `h_implyK`/`h_implyS` helpers to ProofSystem/Axioms.lean as non-private definitions

### LOW Priority (acceptable as-is)
5. **F-1**: FrameConditions.lean placement under Theorems/ (document anomaly)
6. **F-5**: 3-fold Min/Int/Classical structural duplication (intentional, long-term refactor candidate)
7. **F-7**: No barrel import files for subdirectories (consistent with project convention)
8. **F-8**: DerivedRules/HilbertDerivedRules parallel structure (intentional dual proof system design)
9. **F-9**: Derivable name in two namespaces (sufficient separation)
10. **F-10**: Barrel file without @[expose] (correct behavior)
