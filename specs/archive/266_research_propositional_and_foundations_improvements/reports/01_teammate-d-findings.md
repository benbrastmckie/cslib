# Teammate D Findings: HORIZONS Research for Task 266

- **Task**: 266 - Research Propositional and Foundations Improvements
- **Role**: HORIZONS researcher (long-term alignment and strategic direction)
- **Date**: 2026-06-22
- **Agent**: cslib-research-agent (Opus)
- **Artifact**: 01 (teammate-d-findings)

---

## Key Findings (Strategic Insights)

### Finding 1: The Project Is Already Remarkably Deep

The Propositional/ module is far more complete than the roadmap headers suggest. It contains:
- **Three-tier Hilbert systems**: MinPropAxiom, IntPropAxiom, PropositionalAxiom (classical), each with full soundness and strong completeness proofs
- **Two proof systems in parallel**: Hilbert-style (DerivationTree) AND natural deduction (Theory.Derivation with 10 constructors), bridged by equivalence theorems for all three logic strengths
- **Three semantic frameworks**: Boolean evaluation (BoolEvaluate for decidability), Kripke semantics (IForces/KripkeModel), and algebraic semantics (AlgEvaluate over GHA/HA/BA), all bridged to each other
- **Strong completeness** for all three logics: classical (MCS/truth-lemma), intuitionistic (prime DCCS worlds), minimal (prime MinTheory)
- **Algebraic completeness**: Lindenbaum-Tarski construction with GHA/HA/BA tier hierarchy

The single remaining sorry is `ipl_conservative_over_mpl` (Conservative.lean line 99), which requires Dedekind-MacNeille completion of the Lindenbaum algebra. This is a genuine mathematical open problem within the formalization, not a missing infrastructure item.

### Finding 2: Foundations/ Is a Strategic Enabler, Not Just Infrastructure

`Foundations/Logic/` contains a remarkably well-designed typeclass hierarchy:
- `InferenceSystem` typeclass (Fabrizio Montesi) enabling polymorphic derivability notation `S⇓a`
- Connective typeclasses (`HasBot`, `HasImp`, `HasAnd`, `HasOr`, `HasBox`, `HasUntil`, `HasSince`) providing composable logic building blocks
- Bundled proof system classes (`MinimalHilbert`, `IntuitionisticHilbert`, `ClassicalHilbert`, `ModalHilbert`, ... `BimodalTMHilbert`) covering the full cube
- 17 modal Hilbert system tags (K, T, D, S4, S5, KB, K4, K5, K45, TB, KB5, D4, D5, D45, DB, and BX temporal, TM bimodal) - most with no concrete instances yet
- `GenericMCS.lean`: algebraic derivation system + free deduction theorem for ANY `MinimalHilbert` system

This architecture means improvements to Foundations/ propagate automatically to ALL logics.

### Finding 3: The Tableau System Is Bimodal-Specific, Not Shared

The existing tableau system in `Cslib/Logics/Bimodal/Metalogic/Decidability/Tableau.lean` is deeply coupled to the Bimodal formula type (`Formula Atom` with 6 constructors including `box`, `untl`, `snce`). It uses `SignedFormula` and `Branch` types that import `Cslib.Logics.Bimodal.Syntax.Subformulas`. This means:
- A propositional tableau would need to be built independently (or the bimodal tableau generalized)
- The bimodal tableau exploits S5-specific properties (all worlds mutually accessible), making it not a generic modal tableau
- The BimodalLogic report (16_witness-count-restructure.md) is about a completely different proof system - Rabinovich's NF/VecEA framework for temporal expressive completeness, not a shared tableau infrastructure

### Finding 4: The `ProofSystem.lean` Tag Types Are Incomplete Stubs

`Foundations/Logic/ProofSystem.lean` defines 19 opaque tag types (HilbertMin, HilbertInt, HilbertCl, HilbertK, HilbertT, ..., HilbertBX, HilbertTM) but the comment explicitly says: "Concrete instances require derivation trees (not yet ported) and are future work." This is a significant gap: the typeclass hierarchy exists but has no concrete inhabitations, meaning `MinimalHilbert Modal.HilbertK (F := Modal.Formula Atom)` instances are not yet registered.

### Finding 5: Linear Logic Already Provides a Sequent Calculus Template

`Cslib/Logics/LinearLogic/CLL/Basic.lean` (authored by Fabrizio Montesi) implements a full CLL sequent calculus with `Proof` as an `InferenceSystem`. This is the closest existing example of a sequent calculus in CSLib and demonstrates the architectural pattern: use `InferenceSystem` + a `Proof` inductive type with sequent-style constructors. Cut elimination is currently stubbed (CutElimination.lean has TODOs).

---

## Roadmap Alignment Analysis

### Direct Roadmap Alignment

The roadmap's primary focus is the BimodalLogic porting effort: Propositional serves as a foundational dependency for Modal and Temporal, which both serve Bimodal. The roadmap is explicit: "Propositional defines the base formula type and imports only from Foundations. Modal and Temporal each import from both Foundations and Propositional."

**Propositional improvements that align with the roadmap:**

1. **Filling the `ipl_conservative_over_mpl` sorry** (Conservative.lean:99) - directly enables the Propositional module to export a clean sorry-free result, which matters for CSLib's overall proof hygiene standard

2. **Concretizing the ProofSystem tag instances** - currently all 19 `HilbertX` tags lack `InferenceSystem` and `HasAxiom*` instances. Without these, the `ClassicalHilbert Modal.HilbertK` instance doesn't exist, meaning the Foundations/ proof system hierarchy is declarative only. This is a prerequisite for any proof-system-polymorphic development.

3. **Abstract shared completeness infrastructure** (listed explicitly in ROADMAP.md under "Remaining") - the roadmap identifies this as needed for both `Logics/Bimodal/Metalogic/` and `Logics/Temporal/Metalogic/`. This would live in Foundations/ or Propositional/ and serve all higher logics.

### Indirect Roadmap Alignment

The roadmap's remaining items are all about Bimodal/Temporal completeness variants (discrete, continuous, dense for temporal; discrete, continuous for bimodal). These require:
- Abstract shared completeness infrastructure (the roadmap explicitly lists this)
- Chronicle construction patterns (already built for dense temporal)

A sequent calculus for propositional logic does NOT appear in the roadmap and would not unblock any of the remaining items. It would be an attractive addition but is currently tangential.

---

## Cross-Module Opportunities

### Opportunity 1: Abstract Completeness Infrastructure (HIGH PRIORITY)

The roadmap explicitly lists "Abstract shared completeness infrastructure" as remaining work for both Bimodal and Temporal. Currently:
- Dense Bimodal completeness: done (BXCanonical, Algebraic, Bundle approaches)
- Discrete/Continuous Bimodal completeness: not done
- Dense Temporal completeness: done (Chronicle pipeline)
- Discrete/Continuous Temporal completeness: not done

The shared pattern across all completeness proofs is: (1) Lindenbaum extension to MCS, (2) canonical model construction, (3) truth lemma, (4) countermodel from non-derivable formula. `GenericMCS.lean` already provides step 1 generically. Steps 2-4 are logic-specific but follow the same abstract pattern. Extracting this as a `Foundations/Logic/Metalogic/AbstractCompleteness.lean` module would directly unblock the remaining roadmap items.

### Opportunity 2: Concretize the ProofSystem Tag Instances (MEDIUM PRIORITY)

The 19 tag types in `ProofSystem.lean` are stubs. Providing:
```lean
instance : InferenceSystem Modal.HilbertK (Modal.Formula Atom) where
  derivation seq := Modal.Derivation seq.1 seq.2
```
...for at least the classical, modal K, and bimodal TM tags would allow the `ClassicalHilbert`, `ModalHilbert`, `ModalS5Hilbert`, and `BimodalTMHilbert` typeclasses to be inhabited. This would make the Foundations/ proof system hierarchy usable across modules.

### Opportunity 3: Propositional Kripke Completeness for Intuitionistic/Minimal (ALREADY DONE)

The `IntStrongCompleteness.lean` and `MinStrongCompleteness.lean` already provide this. No action needed.

### Opportunity 4: Sequent Calculus as a Third Proof System Bridge

Currently Propositional/ has: Hilbert system ↔ Natural deduction (bridged). Adding a sequent calculus (Gentzen LK or LJ) would create a three-way equivalence. The strategic question is: who benefits?

- LK/LJ is useful for cut elimination (a celebrated proof-theoretic result)
- A generic sequent calculus could serve Modal/ and Temporal/ (Fitting-style tableau/sequent systems)
- The CLL module already demonstrates sequent calculus in CSLib via InferenceSystem

**Cross-module potential**: A generic sequent calculus framework parameterized by the logic's connective classes would be the most valuable version. Rather than a propositional-specific LK, building a `Foundations/Logic/SequentCalculus.lean` with:
```lean
structure Sequent (F : Type*) where
  antecedent : Multiset F
  succedent : Multiset F
```
...and structural rules (weakening, contraction, exchange), then instantiating for each logic, would serve Modal/, Temporal/, and Bimodal/ as well.

### Opportunity 5: Decidability for Propositional Logic

`BoolEvaluate` exists and is computable, enabling decidable evaluation. However, there is no verified SAT/tautology-checking procedure. The bimodal module has a full verified tableau decision procedure. A propositional tautology checker (DPLL or resolution-based) would:
- Demonstrate the verified decision procedure pattern at the simpler propositional level
- Serve as a stepping stone for modal decidability
- Benefit external contributors who want to use CSLib as a basis for verified program analysis tools

---

## Alternative Scoping Suggestions

### Option A: "Foundations First" — Concrete Instances + Abstract Completeness

**Focus**: Make the Foundations/ proof system hierarchy usable rather than adding new proof systems.

1. Provide `InferenceSystem` + `ClassicalHilbert` instances for `Modal.HilbertK` (and perhaps `Temporal.HilbertBX` and `Bimodal.HilbertTM`)
2. Extract abstract completeness infrastructure from the existing MCS construction patterns
3. Fill the `ipl_conservative_over_mpl` sorry via Dedekind-MacNeille completion

**Impact**: High. Directly enables multiple downstream tasks and completes the existing architecture.

**Risk**: Low. Well-understood mathematics, mostly code organization.

### Option B: "Proof Systems Survey" — Sequent Calculus + Cut Elimination

**Focus**: Add Gentzen LK (classical sequent calculus) to Propositional/ and prove cut elimination.

1. Implement LK as a third proof system alongside Hilbert and ND
2. Bridge LK ↔ Hilbert via the existing cut rule in ND/Basic.lean
3. Prove cut elimination for LK (syntactic proof, moderate complexity)
4. Demonstrate the pattern for later Modal/ sequent work (Fitting's sequent system for K, S4, S5)

**Impact**: Medium. Enriches Propositional/ but doesn't unblock roadmap items.

**Risk**: Medium. Cut elimination proofs are moderately involved (but well-understood).

### Option C: "Generic Proof Framework" — Parameterized Proof Systems

**Focus**: Build a generic proof system framework that LK, ND, Hilbert, tableau all instantiate.

1. Define `SequentCalculus` typeclass in Foundations/Logic/
2. Implement structural rules (weakening, contraction, exchange) generically
3. Show that the existing ND and Hilbert systems are instances
4. Add LK and modal Fitting-style systems as new instances

**Impact**: Very high long-term. Creates a reusable architecture for all logics.

**Risk**: High. Requires careful abstraction design; risk of over-engineering.

### Option D: "Propositional Decision Procedure" — Verified SAT/DPLL

**Focus**: Build a verified propositional tautology checker as a complement to the bimodal tableau.

1. Implement DPLL as a computable function on `Proposition Atom` (Fintype Atom assumed)
2. Prove correctness: DPLL returns `true` iff the formula is a tautology
3. Instantiate `prop_completeness_iff_tautology` as a decision procedure
4. Generate term witnesses via the soundness direction

**Impact**: Medium-high. Demonstrates verified decision procedures and enables automation.

**Risk**: Low-medium. DPLL is well-understood; the existing `BoolEvaluate` infrastructure helps.

**Recommended scope**: Option A (concrete instances + abstract completeness) as primary, with Option D (decision procedure) as a bonus scope item if time permits. Option B (sequent calculus) is strategically valuable but should be scoped to include the generic framework (Option C) rather than propositional-specific only.

---

## Long-term Architecture Vision

### Vision: CSLib as the Lean Standard for Verified Logic

The current architecture has all the right pieces in place for CSLib to become the definitive Lean 4 library for formal logic. The key architectural insight missing is **composability across proof systems**.

Currently:
- Propositional/ has three proof systems (Hilbert, ND, algebraic) all isolated to one logic
- Modal/ has its own DerivationTree, not connected to Propositional/'s systems
- Temporal/ and Bimodal/ each have their own DerivationTree types
- LinearLogic/ has its own Proof type (via CLL)

The long-term vision should be a **proof system functor**: given a logic (specified by connective classes + axioms), automatically derive:
- A Hilbert system (from `MinimalHilbert` + axiom extensions)
- A natural deduction system (by instantiating `Theory.Derivation` generically)
- A sequent calculus (by instantiating a generic LK/LJ)
- A tableau (by instantiating signed formula expansion rules)

Each proof system should come with verified bridges to the others, and all should share:
- The `InferenceSystem` notation (`S⇓φ`)
- The `HasDeductionTheorem` typeclass
- The `GenericMCS` algebraic framework
- Sound/complete semantic interpretations

This architecture would make adding a new logic (say, description logic ALC or epistemic logic) a matter of:
1. Defining the formula type with connective instances
2. Registering the axiom set
3. Getting proof systems for free from the generic framework
4. Providing only the logic-specific semantics and completeness

### Near-term Vision: Propositional as the Template

Propositional/ is uniquely positioned to be this template. It already has:
- The most complete multi-tier semantics (Bool, Kripke, algebraic)
- The most complete proof system coverage (Hilbert + ND + bridges)
- The three-way logic hierarchy (MPL, IPL, CPL)
- Strong completeness for all three

What it lacks (and should develop first) is:
1. Concrete InferenceSystem instances for the ProofSystem tags
2. A sequent calculus to complete the proof system trifecta
3. Cut elimination as the signature proof-theoretic result
4. Abstract completeness extraction so the pattern propagates to Modal/ etc.

---

## Evidence/Examples

### Evidence for "ProofSystem tags are stubs"

From `Foundations/Logic/ProofSystem.lean` line 465-524:
```lean
-- Note: "This module defines the **interface** only. Concrete instances require
-- derivation trees (not yet ported) and are future work."
opaque Propositional.HilbertMin : Type := Empty
opaque Modal.HilbertK : Type := Empty
...
opaque Bimodal.HilbertTM : Type := Empty
```
These are opaque empty types with no instances. The `ClassicalHilbert` class exists but no type `T` satisfies `ClassicalHilbert T (F := Propositional.Proposition Atom)` via the Propositional.HilbertCl tag.

### Evidence for "Tableau is Bimodal-specific"

`Cslib/Logics/Bimodal/Metalogic/Decidability/SignedFormula.lean`:
```lean
public import Cslib.Logics.Bimodal.Syntax.Formula
public import Cslib.Logics.Bimodal.Syntax.Subformulas
```
The signed formula type imports Bimodal-specific syntax. There is no `Foundations/Logic/Tableau.lean` or generic signed formula infrastructure.

### Evidence for "GenericMCS is a strategic asset"

`Foundations/Logic/Metalogic/GenericMCS.lean`:
```lean
variable {F : Type*} [HasBot F] [HasImp F]
variable {S : Type*} [InferenceSystem S F]
variable [MinimalHilbert S (F := F)]
-- Gives algebraicDerivationSystem + algebraic_has_deduction_theorem for FREE
-- for any MinimalHilbert system
```
This is a proof that the generic MCS infrastructure already works - any logic with `MinimalHilbert` gets Lindenbaum theory for free. The remaining step is concretizing the instances.

### Evidence for "Linear Logic provides the sequent calculus template"

`Cslib/Logics/LinearLogic/CLL/Basic.lean` already defines:
- `Proposition Atom` inductive (12 constructors for full CLL)
- `Sequent Atom` as a multiset
- `Proof : Sequent Atom → Type u` as an `InferenceSystem` with explicit rule constructors
- `Proof.cutFree : Bool` predicate
- `CutFreeProof Γ` subtype

This proves the pattern works in CSLib. A classical sequent calculus LK would follow the exact same structure.

### Evidence for "Conservative extension is the last sorry"

`Cslib/Logics/Propositional/Semantics/Algebra/Conservative.lean` line 96-99:
```lean
theorem ipl_conservative_over_mpl {A : Proposition Atom}
    (_hBF : A.IsBotFree = true) (h : DerivableIn (IPL (Atom := Atom)) A) :
    DerivableIn (MPL (Atom := Atom)) A := by
  sorry
```
This is the only remaining sorry in the Propositional module. The module comment explains why: "The proof requires Dedekind-MacNeille completion of the Lindenbaum algebra (deferred)."

---

## Confidence Level

**High confidence** (directly observed in code):
- ProofSystem tags are stubs with no concrete instances
- The single remaining sorry in Propositional/ is `ipl_conservative_over_mpl`
- The tableau system is Bimodal-specific, not shared
- The Linear Logic CLL module provides the sequent calculus pattern
- GenericMCS provides abstract MCS infrastructure for any MinimalHilbert system
- The Propositional/ module has complete three-tier semantics (Bool, Kripke, algebraic) and two proof systems (Hilbert, ND)

**Medium confidence** (architectural inference):
- Concretizing ProofSystem instances would unlock proof-system-polymorphic development
- Abstract completeness extraction would unblock multiple roadmap items
- A generic sequent calculus framework (vs. propositional-specific LK) would be more strategically valuable

**Lower confidence** (speculative):
- Whether a "proof system functor" architecture is technically feasible in Lean 4 without prohibitive universe overhead
- Whether the Dedekind-MacNeille sorry can be filled without importing heavy Mathlib machinery
- Whether a verified propositional SAT procedure would attract external contributors

---

## Summary of Strategic Recommendations

1. **Primary scope** (highest roadmap alignment): Fill `ipl_conservative_over_mpl` via Dedekind-MacNeille completion, and extract abstract completeness infrastructure from the existing MCS patterns. These directly serve the remaining roadmap items (discrete/continuous Bimodal/Temporal completeness).

2. **Secondary scope** (enabling infrastructure): Concretize at least `Propositional.HilbertCl` and `Modal.HilbertK` as `ClassicalHilbert` and `ModalHilbert` instances. This closes the gap between the typeclass hierarchy (interface) and concrete proof systems (instances).

3. **Stretch scope** (proof system enrichment): Add LK as a third proof system for Propositional/, prove cut elimination, and use the CLL module as the architectural template. Scope this generically (parameterized by connective classes) rather than propositional-specific.

4. **Do NOT scope** (low strategic value): A propositional-specific tableau system. The bimodal tableau is already implemented; a propositional tableau would be a downgrade in complexity and would not serve the roadmap. If tableau work is desired, generalize the bimodal tableau to the generic `Foundations/Logic/` layer.
