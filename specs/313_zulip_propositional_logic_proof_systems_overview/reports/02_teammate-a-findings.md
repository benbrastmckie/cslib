# Teammate A Findings: Current State of CSLib Propositional Logic Proof Systems

**Task**: Inventory the current state of all four proof systems (Hilbert, Natural Deduction, Sequent Calculus, Tableau) and their metalogic across the three logics (minimal, intuitionistic, classical).

**Confidence**: HIGH — all findings are based on direct source reads.

---

## Summary Status Table

| System | Minimal | Intuitionistic | Classical | Sorry Count |
|--------|---------|----------------|-----------|-------------|
| Hilbert (ProofSystem/) | COMPLETE | COMPLETE | COMPLETE | 0 |
| Natural Deduction (NaturalDeduction/) | COMPLETE | COMPLETE | COMPLETE | 0 |
| Sequent Calculus LK | — | — | COMPLETE | 0 |
| Sequent Calculus LJ | — | COMPLETE | — | 1 (CutElim) |
| Tableau Classical | — | — | IN PROGRESS | ~5 (loop induction) |
| Tableau Intuitionistic | — | IN PROGRESS | — | ~6 (soundness/completeness) |
| Tableau Minimal | IN PROGRESS | — | — | 2 (soundness/completeness) |
| Metalogic (MCS/Lindenbaum) | COMPLETE | COMPLETE | COMPLETE | 0 |
| Algebraic Semantics / Conserv. Ext. | — | COMPLETE | COMPLETE | 0 |

---

## 1. Hilbert Proof System

**Location**: `Cslib/Logics/Propositional/ProofSystem/`
**Files**: Axioms.lean, Derivation.lean, Instances.lean, IntMinInstances.lean, FragmentAxioms.lean, FragmentInstances.lean
**Status**: COMPLETE — 0 sorry across 6 files (1197 lines total)

### Three Logics via Axiom Predicates

The Hilbert system is parameterized over an axiom predicate `Axioms : PL.Proposition Atom → Prop`. Three concrete predicates define the three logics:

- **`MinPropAxiom`** (8 axioms): K, S, andI, andE1, andE2, orI1, orI2, orE
- **`IntPropAxiom`** (9 axioms): MinPropAxiom + EFQ (`⊥ → φ`)
- **`PropositionalAxiom`** (10 axioms): IntPropAxiom + Peirce's law (`((φ → ψ) → φ) → φ`)

The subsumption chain is formally proved: `MinPropAxiom.toIntPropAxiom` and `IntPropAxiom.toPropAxiom`.

### Core Types

- `DerivationTree Axioms Γ φ`: Type-valued proof tree (ax, assumption, modus_ponens, weakening)
- `Deriv Axioms Γ φ`: Prop wrapper (`Nonempty (DerivationTree Axioms Γ φ)`)
- `Derivable Axioms φ`: derivability from empty context

### Fragment Axioms

Two additional fragment axiom predicates exist for the conservative extension theorems:
- `ConjImpAxiom`: K, S, andI, andE1, andE2 (IPL⟨∧,→,⊤⟩)
- `ImpAxiom`: K, S only (IPL⟨→,⊤⟩)
- `ConjImpBotAxiom`: K, S, andI, andE1, andE2, EFQ (IPL⟨∧,→,⊥,⊤⟩)

### Tag-Based Instance Registration

The abstract `Propositional.HilbertCl`, `Propositional.HilbertInt`, and `Propositional.HilbertMin` tag types register `InferenceSystem`, `ModusPonens`, `HasAxiomImplyK`, `HasAxiomImplyS`, `HasAxiomEFQ`, `HasAxiomPeirce`, and `ClassicalHilbert`/`IntuitionisticHilbert`/`MinimalHilbert` instances.

---

## 2. Natural Deduction

**Location**: `Cslib/Logics/Propositional/NaturalDeduction/`
**Files**: Basic.lean, DerivedRules.lean, Equivalence.lean, FromHilbert.lean, HilbertDerivedRules.lean
**Status**: COMPLETE — 0 sorry across 5 files (1998 lines total)

### Core Type

`Theory.Derivation {T : Theory Atom}` with 10 primitive constructors:
ax, ass (assumption), andI, andE1, andE2, orI1, orI2, orE, impI, impE

Contexts are `Finset (Proposition Atom)` (vs. `List` in the Hilbert system).

### Three Logics via Theory Parameter

Logic strength is controlled by the `Theory` parameter:
- **MPL** (minimal): empty theory — only the 10 primitive rules
- **IPL** (intuitionistic): adds `⊥ → A` via `[IsIntuitionistic T]`
- **CPL** (classical): adds `¬¬A → A` via `[IsClassical T]`

EFQ is a derived rule (`botE`) requiring `[IsIntuitionistic T]`, not a primitive constructor. This is a deliberate design choice: `⊥` is a primitive constructor of `Proposition` but has no introduction rule, and making its elimination a theory axiom cleanly separates the three logics.

### Derived Rules

`DerivedRules.lean` provides: botE (requires `[IsIntuitionistic T]`), negI, negE, topI, dne (requires `[IsClassical T]`), iffI, iffE1, iffE2.

---

## 3. Hilbert ↔ Natural Deduction Equivalence

**Location**: `Cslib/Logics/Propositional/NaturalDeduction/Equivalence.lean`
**Status**: COMPLETE — 0 sorry

This is the primary cross-system bridge between Hilbert and ND.

### Key Results

| Theorem | Statement | Confidence |
|---------|-----------|------------|
| `hilbert_iff_nd_ctx` | Generic: `Deriv Axioms Γ.toList φ ↔ DerivableIn (AxiomTheory Axioms) (Γ ⊢ φ)` | PROVEN |
| `hilbert_iff_nd_ctx_min` | Minimal instantiation | PROVEN |
| `hilbert_iff_nd_ctx_int` | Intuitionistic instantiation | PROVEN |
| `hilbert_iff_nd_ctx_cl` | Classical instantiation | PROVEN |
| `hilbert_iff_nd_min` | Minimal (empty context) | PROVEN |
| `hilbert_iff_nd_int` | Intuitionistic (empty context) | PROVEN |
| `hilbert_iff_nd_cl` | Classical (empty context) | PROVEN |

### Bridge Architecture

The equivalence is generic over any axiom predicate satisfying `MinimalAxioms` (a typeclass bundling witnesses for K, S, andI, andE1, andE2, orI1, orI2, orE). Instances are provided for all three logics.

- **`hilbertToND`**: Structural translation (computable). List context → Finset context via `List.toFinset`.
- **`ndToHilbert`**: Uses the deduction theorem for `impI` (`noncomputable` because it relies on `Classical.propDecidable`). Finset context → List context via `Finset.toList`.

The key bridge lemma is `Finset.toList_toFinset`.

---

## 4. Sequent Calculus

**Location**: `Cslib/Logics/Propositional/SequentCalculus/`
**Structure**: LK/ (classical), LJ/ (intuitionistic), Defs.lean

### 4a. LK (Classical)

**Files**: Basic.lean, Soundness.lean, Completeness.lean, CutElimination.lean
**Status**: COMPLETE — 0 sorry across 4 files (1632 lines)

**Presentation**: All-additive Finset-based, following Negri and von Plato (2001). Sequents are `LKSequent Atom = Finset × Finset`.

**LK Rules (11 constructors)**:
- `ax`: identity axiom (A in both antecedent and succedent)
- `botL`: left falsum
- `andL`, `andR`: left/right conjunction
- `orL`, `orR`: left/right disjunction
- `impL`, `impR`: left/right implication
- `weakL`, `weakR`: weakening
- `cut`: cut rule

**Key results**:
- `LKProof.sound`: Soundness by structural induction
- `lk_sound`: Semantic soundness
- `ndToLK`: ND derivation → LK proof (structural translation)
- `nd_iff_lk`: `DerivableIn (AxiomTheory PropositionalAxiom) (Γ ⊢ A) ↔ Nonempty (LKProof (Γ ⊢ₛ {A}))`
- `hilbert_iff_lk`: `Deriv PropositionalAxiom Γ.toList φ ↔ Nonempty (LKProof (Γ ⊢ₛ {φ}))`
- `lk_completeness`: `Tautology φ → Nonempty (LKProof (∅ ⊢ₛ {φ}))`
- `lk_iff_tautology`: Full equivalence
- `LKProof.cutElim`: Every LK-derivable sequent has a cut-free proof (Hauptsatz, PROVEN)
- `cutAdmissibility` (LK): PROVEN by structural induction on the cut formula

### 4b. LJ (Intuitionistic)

**Files**: Basic.lean, Soundness.lean, Completeness.lean, CutElimination.lean
**Status**: NEAR-COMPLETE — 1 sorry in CutElimination.lean (828 lines total)

**Key distinction from LK**: Single-conclusion sequents (`LJSequent = Ctx × Proposition`). No `weakR` constructor; right disjunction splits into `orR1` and `orR2`.

**LJ Rules (11 constructors)**:
ax, botL, andL, andR, orL, orR1, orR2, impL, impR, weakL, cut

LJ soundness is with respect to **intuitionistic Kripke semantics** (`IForces v (fun _ => False) w`), not classical Boolean semantics.

**Key results**:
- `LJProof.sound`: Kripke soundness by structural induction (PROVEN)
- `ndToLJ`: ND derivation → LJ proof (structural translation, PROVEN)
- `nd_iff_lj`: `DerivableIn (AxiomTheory IntPropAxiom) (Γ ⊢ A) ↔ Nonempty (LJProof (Γ ⊢ A))` (PROVEN)
- `hilbert_iff_lj`: Full Hilbert–LJ equivalence (PROVEN)
- `lj_iff_ivalid`: `IValid φ ↔ Nonempty (LJProof (∅ ⊢ φ))` (PROVEN)

**Remaining sorry**:
- `cutAdmissibility` (LJ, line 103): "well-founded induction on formula complexity is technically challenging." The theorem is stated, the non-cut cases of `cutElim` are complete, but the inductive step for `cutAdmissibility` itself uses `sorry`. This is the one remaining proof obligation in the sequent calculus.

---

## 5. Tableau Systems

**Location**: `Cslib/Logics/Propositional/Tableau/`
**Shared infrastructure**: `Defs.lean` (signed formulas, closure conditions, generic expansion)

All three tableau systems reuse the intuitionistic expansion machinery (`intExpandBranches`) from `Intuitionistic/Expansion.lean`, differing only in the closure condition.

### 5a. Classical Tableau

**Files**: Expansion.lean (DONE), Soundness.lean (5 sorry), Completeness.lean (3 sorry), DecisionProcedure.lean (0 sorry in structure)
**Status**: IN PROGRESS — 5+3 = ~8 actual sorry in soundness/completeness proofs

**Design**: `L = Unit` (all formulas at a single implicit world). Closure: T(⊥) or T(φ)/F(φ) contradiction.

**`classicalApplyOne`**: Applies rules for pos/neg and, or, imp, negation using `propAndOf?`, `propOrOf?`, `propImpOf?`, `propNegOf?`.

**Sorries in Soundness.lean**:
- Line 162: `classicalRule_preserves_sat` — "full proof by case analysis on rules marked sorry"
- Line 244: `classicalTableau_sound` — "loop induction marked sorry"

**Sorries in Completeness.lean**:
- Line 79: `classicalTruthLemma` — "full proof by formula induction marked sorry"
- Line 88: `classicalOpenBranch_countermodel` — sorry
- Line 102: `classicalTableau_complete` — sorry

**Important note**: The `Decidable (Tautology φ)` instance (`instDecidableTautologyTableau`) and `classicalTableau_decides` are structurally sound but depend on the sorry'd soundness/completeness. The pre-existing `instDecidableTautology` in `Bool.lean` provides a sorry-free decision procedure via Boolean enumeration.

### 5b. Intuitionistic Tableau

**Files**: Expansion.lean (DONE), Rules.lean (DONE), Soundness.lean (2 sorry), Completeness.lean (3 sorry), DecisionProcedure.lean (1 sorry in structure)
**Status**: IN PROGRESS — ~6 sorry total

**Design**: `L = Nat` (world labels). Closure: T(⊥) at any world.

**World-creating rules** (defined in Rules.lean):
- F(φ → ψ) at world w: creates fresh world w' with T(φ), F(ψ), and persistence of T(α) formulas from w
- T(φ → ψ) at world w: for each accessible w' with T(φ), add T(ψ)

`IntTableauState` tracks: branch (labeled signed formulas), nextWorld, expanded (already-processed formulas).

**Sorries in Soundness.lean**:
- Line 162: `intRule_preserves_sat` — "case analysis on rules marked sorry"
- Line 244 (approx): `intuitionisticTableau_sound` — sorry

**Sorries in Completeness.lean**:
- `intTruthLemma` — sorry (formula induction)
- `intuitionisticOpenBranch_countermodel` — sorry
- `intuitionisticTableau_complete` — sorry

**New contribution**: `instDecidableIValid` — `Decidable (IValid φ)` via tableau. This is novel to CSLib; intuitionistic validity was not previously decidable by a constructive procedure. (Depends on sorry'd proofs.)

### 5c. Minimal Tableau

**Files**: DecisionProcedure.lean only (8 sorry total, though only 2 are non-structurally sorry)
**Status**: IN PROGRESS — 2 substantive sorry

**Design**: Reuses `intExpandBranches` with `MinimalClosure`. Closure: T(p)/F(p) for **atomic** p at same world (T(⊥) does NOT close a branch in minimal logic).

**Key difference from intuitionistic**: `botForces w = T(⊥) is on b at world w` — a genuine predicate, not `fun _ => False`.

**Sorries**:
- `minimalTableau_sound` — sorry (lines 86-88)
- `minimalTableau_complete` — sorry (lines 103-105)

**New contribution**: `instDecidableMValid` — `Decidable (MValid φ)` via minimal tableau. Also novel to CSLib.

---

## 6. Algebraic Semantics and Conservative Extension Results

**Location**: `Cslib/Logics/Propositional/Semantics/Algebra/`
**Status**: COMPLETE — 0 sorry across 22 files (5295 lines total)

### Hilbert Algebra Completeness

- **`BooleanAlgebra`** completeness for CPL: BAValid ↔ Derivable PropositionalAxiom
- **`HeytingAlgebra`** completeness for IPL: HAValid ↔ Derivable IntPropAxiom
- **`GeneralizedHeytingAlgebra`** completeness for MPL: GHAValid ↔ Derivable MinPropAxiom
- **`BrouwerianSemilattice`** completeness for IPL⟨∧,→,⊤⟩
- **`PointedBrouwerianSemilattice`** completeness for IPL⟨∧,→,⊥,⊤⟩

### Conservative Extension Theorems

All proven without sorry:

| Theorem | Statement | Location |
|---------|-----------|----------|
| `hilbertIplConservativeOverMpl` | IPL conservative over MPL for bot-free formulas | HilbertConservativeGlivenko.lean |
| `ipl_conservative_over_mpl` | ND corollary of above | HilbertConservativeGlivenko.lean |
| `hilbertGlivenko` | CPL ⊢ φ → IPL ⊢ ¬¬φ (Hilbert form) | HilbertConservativeGlivenko.lean |
| `glivenko` | ND Glivenko theorem | HilbertConservativeGlivenko.lean |
| `hilbertIplConservativeOverConjImp` | IPL conservative over IPL⟨∧,→,⊤⟩ for or-bot-free formulas | ConjImpConservative.lean |
| `ipl_conservative_over_conjImp` | ND corollary | ConjImpConservative.lean |
| `hilbertIplConservativeOverConjImpBot` | IPL conservative over IPL⟨∧,→,⊥,⊤⟩ for or-free formulas | ConjImpBotConservative.lean |
| `ipl_conservative_over_conjImpBot` | ND corollary | ConjImpBotConservative.lean |

### Algebraic Infrastructure

- `Lindenbaum.lean`: Lindenbaum–Tarski algebra construction
- `LindenbaumInstances.lean`: Heyting/Boolean algebra instances on quotients
- `KripkeBridge.lean`: Bridge between algebraic and Kripke semantics
- `FreeJoinCompletion.lean`: `LowerSet B` free join completion for Brouwerian embedding
- `NonemptyLowerSet.lean`: `NonemptyLowerSet B` Heyting algebra (preserves bot, extends ConjImpConservative to ConjImpBot case)
- `Glivenko.lean`: Algebraic core via `Heyting.Regular` regular elements
- `Conservative.lean`: Bot-free predicate and validity subsumption chain

---

## 7. Metalogic

**Location**: `Cslib/Logics/Propositional/Metalogic/`
**Status**: COMPLETE — 0 sorry across all files

### Three Strong Completeness Results

| File | Logic | Method | Key Results |
|------|-------|--------|-------------|
| StrongCompleteness.lean | Classical | MCS (Lindenbaum) | `prop_strong_completeness`, `prop_completeness_iff_tautology`, `prop_compactness` |
| IntStrongCompleteness.lean | Intuitionistic | Prime DCCS Kripke | `int_strong_completeness`, `int_soundness_completeness`, `int_compactness` |
| MinStrongCompleteness.lean | Minimal | Prime MinTheory Kripke | `min_strong_completeness`, `min_soundness_completeness`, `min_compactness` |

### Supporting Infrastructure

- `DeductionTheorem.lean`: Hilbert deduction theorem (used by `ndToHilbert`)
- `MCS.lean`: Generic maximally consistent set API
- `IntLindenbaum.lean`, `MinLindenbaum.lean`: Prime extension lemmas for the respective logics

---

## 8. Cross-System Equivalences: What Is Proven

### Fully Established Chains

```
CPL (classical):
  Derivable PropositionalAxiom
    ↔ DerivableIn (AxiomTheory PropositionalAxiom) [hilbert_iff_nd_cl]
    ↔ Nonempty (LKProof (Γ ⊢ₛ {φ}))       [hilbert_iff_lk]
    ↔ Tautology φ                           [prop_completeness_iff_tautology]
    ↔ BAValid φ                             [Algebra/HilbertCompleteness]
    
IPL (intuitionistic):
  Derivable IntPropAxiom
    ↔ DerivableIn (AxiomTheory IntPropAxiom) [hilbert_iff_nd_int]
    ↔ Nonempty (LJProof (∅ ⊢ φ))           [hilbert_iff_lj]
    ↔ IValid φ                              [int_soundness_completeness]
    ↔ HAValid φ                             [Algebra/HilbertCompleteness]
    
MPL (minimal):
  Derivable MinPropAxiom
    ↔ DerivableIn (AxiomTheory MinPropAxiom) [hilbert_iff_nd_min]
    ↔ MValid φ                              [min_soundness_completeness]
    ↔ GHAValid φ                            [Algebra/HilbertCompleteness]
```

### Pending Equivalences

| Missing Link | Blocker | Priority |
|--------------|---------|----------|
| Tableau ↔ other systems (classical, int, min) | 5/6/2 sorry in soundness/completeness | HIGH — needed to complete the commutative diagram |
| Cut-freeness for LJ | 1 sorry in `cutAdmissibility` | MEDIUM |

### What the Tableau Sorry's Are About

The sorry'd proofs all follow a common pattern: they require induction over the execution of a fuel-based expansion loop. This is the standard difficulty in formalizing tableau algorithms:

- **Soundness** requires: each rule application preserves branch satisfiability + closed branches are unsatisfiable → induction on the loop runs
- **Completeness** requires: a truth lemma (formula induction on the extracted model) + a countermodel extraction from open saturated branches

In all three cases, the formal infrastructure for the loop induction (tracking saturation, relating loop iterations to semantic properties) is the missing piece. The decision procedure `Decidable` instances are structurally present but inherit the sorry tags.

---

## 9. The Three-Logic Hierarchy in Each System

| Logic | Hilbert | ND | LK/LJ | Tableau |
|-------|---------|-----|-------|---------|
| **Minimal** | `MinPropAxiom` | Empty theory | (no SC variant yet) | `MinimalClosure` in `minimalTableau` |
| **Intuitionistic** | `IntPropAxiom` | `IPL` theory | LJ | `IntuitionisticClosure` in `intuitionisticTableau` |
| **Classical** | `PropositionalAxiom` | `CPL ∪ IPL` theory | LK | `ClassicalClosure` in `classicalTableau` |

Note: There is currently no sequent calculus for minimal logic. The LK/LJ pair covers classical and intuitionistic; a minimal sequent calculus (minimal LJ variant, or an LM system) would complete the picture but does not yet exist in CSLib.

---

## 10. Key Design Observations

### Context Representations Across Systems

| System | Context type |
|--------|-------------|
| Hilbert (`DerivationTree`) | `List (Proposition Atom)` |
| ND (`Theory.Derivation`) | `Finset (Proposition Atom)` |
| LK (`LKProof`) | `Finset (Proposition Atom)` × `Finset (Proposition Atom)` |
| LJ (`LJProof`) | `Finset (Proposition Atom)` × `Proposition Atom` |
| Tableau (classical) | `List (SignedFormula (Proposition Atom) Unit)` |
| Tableau (int/min) | `List (SignedFormula (Proposition Atom) Nat)` |

The context bridges (List ↔ Finset via `toFinset`/`toList`) are a recurring theme in the equivalence proofs.

### EFQ Design Choice

EFQ (`⊥ → A`) is NOT a primitive ND constructor but a theory axiom via `[IsIntuitionistic T]`. This separates the three logics cleanly and allows sharing one `Proposition` type with primitive `⊥` across all logics and the modal/temporal extensions.

### Tableau Design

The tableau implementation uses a generic signed-formula framework from `Foundations/` (`Cslib.Logic.Tableau`):
- `SignedFormula Formula Label` — formula with a sign (pos/neg) and a world label
- `RuleResult Formula Label` — linear (alpha-rule) or branching (beta-rule)
- `ClosureCondition` typeclass — checked as `@ClosureCondition.isClosed _ _ inst b`
- Three closure instances: `ClassicalClosure`, `IntuitionisticClosure`, `MinimalClosure`

The shared infrastructure means the three tableau provers share all the generic machinery; only the closure condition differs.

---

## 11. What Remains for a Complete Picture

The vision of four equivalent proof systems for three logics requires:

1. **Tableau completeness** (3 logics × 2 theorems = 6 more sorry-free proofs): The loop induction proofs for soundness and completeness in all three tableau variants.

2. **Tableau ↔ Hilbert/ND bridges**: Once tableau soundness/completeness is proven, `Derivable Axioms φ ↔ tableau closes on φ` can be derived via the existing metalogic completeness.

3. **LJ cut elimination** (1 sorry): `cutAdmissibility` for LJ requires a nested well-founded induction on `(sizeOf A, d₁.height + d₂.height)`. The LK version was completed by structural induction on the cut formula; LJ requires the same approach adapted to single-conclusion sequents.

4. **Minimal sequent calculus** (new): A minimal LJ variant (or LM system) would allow the same Hilbert ↔ ND ↔ SC ↔ Tableau equivalence chain for minimal logic.
