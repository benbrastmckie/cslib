# Teammate A Findings: Propositional/ and Foundations/ Research

- **Task**: 266 - Research propositional and foundations improvements
- **Role**: Teammate A (lead investigator — primary implementation approaches and patterns)
- **Date**: 2026-06-22
- **Agent**: cslib-research-agent

---

## Key Findings: What Currently Exists

### Propositional/ Module (30 files)

The `Cslib/Logics/Propositional/` module is the most complete logic module in CSLib. It provides
three-level coverage for MPL (minimal), IPL (intuitionistic), and CPL (classical) propositional logic.

#### Language Layer (`Defs.lean`)

- `Proposition Atom` — inductive type with 5 constructors: `atom`, `bot`, `imp`, `and`, `or`
- Derived connectives: `neg`, `top`, `iff` as `abbrev`s
- `Theory Atom = Set (Proposition Atom)` with `MPL`, `IPL`, `CPL` as specific instances
- Typeclass instances: `PropositionalConnectives`, `HasAnd`, `HasOr`
- Substitution monad: `Proposition.subst`, `Monad Proposition`
- `IsIntuitionistic` / `IsClassical` typeclasses (with `grind` attributes)
- `Theory.intuitionisticCompletion` construction (free intuitionistic extension)
- References: Johansson1937, Gentzen1935, Prawitz1965, TroelstraVanDalen1988, Church1956,
  ChagrovZakharyaschev1997

#### Proof System Layer (`ProofSystem/`)

Three files providing a Hilbert-style system:

**Axioms.lean**:
- `PropositionalAxiom` (10 constructors) — classical: K, S, EFQ, Peirce, andI, andE1, andE2,
  orI1, orI2, orE
- `IntPropAxiom` (9 constructors) — intuitionistic (removes Peirce)
- `MinPropAxiom` (8 constructors) — minimal (removes EFQ)
- Subsumption theorems: `MinPropAxiom.toIntPropAxiom`, `IntPropAxiom.toPropAxiom`

**Derivation.lean**:
- `DerivationTree Axioms Γ φ` — `Type`-valued inductive with 4 rules: `ax`, `assumption`,
  `modus_ponens`, `weakening`
- `height` — computable height function for well-founded recursion in deduction theorem
- `Deriv Axioms Γ φ = Nonempty (DerivationTree Axioms Γ φ)` — `Prop` wrapper
- `propDerivationSystem Axioms` — `DerivationSystem (PL.Proposition Atom)` instance connecting
  to generic MCS framework

**Instances.lean**: Registers `HilbertCl`, `HilbertInt`, `HilbertMin` tag types with instances
for all `HasAxiom*` typeclasses and bundled Hilbert system classes.

**IntMinInstances.lean**: Analogous registrations for `HilbertInt` and `HilbertMin`.

#### Natural Deduction Layer (`NaturalDeduction/`)

Five files providing an independent ND system:

**Basic.lean**:
- `Ctx Atom = Finset (Proposition Atom)` — contexts as finsets (avoids explicit contraction)
- `Sequent` as `Ctx × Proposition` with `Γ ⊢ A` notation
- `Theory.Derivation` — 10-constructor inductive: `ax`, `ass`, `andI`, `andE1`, `andE2`,
  `orI1`, `orI2`, `orE`, `impI`, `impE`
- Theory parameter controls logic strength (MPL/IPL/CPL)
- `InferenceSystem T Sequent` and `InferenceSystem T (Proposition Atom)` instances
- Core structural rules: `Derivation.weak`, `Derivation.cut`, `Derivation.subs`
- Atom substitution: `substAtom`
- Equivalence: `Theory.equiv`, `Theory.Equiv` with congruence lemmas for all connectives

**DerivedRules.lean**: EFQ, double negation intro, indirect proof, classical rules derived
under appropriate theory parameters.

**FromHilbert.lean**: Helpers translating Hilbert combinators to ND derivations.

**HilbertDerivedRules.lean**: Hilbert-style derived rules needed for ND-to-Hilbert translation
(`hilbertAndI`, `hilbertOrE`, `deductionTheorem`).

**Equivalence.lean**:
- `AxiomTheory Axioms` — wraps axiom predicate as ND theory
- `MinimalAxioms` typeclass — bundles 8 axiom witnesses (K, S, andI×3, orI×2, orE)
- `hilbertToND` — computable Hilbert→ND translation
- `ndToHilbert` — noncomputable ND→Hilbert translation (uses classical propDecidable)
- **Bridge theorems**: `hilbert_iff_nd_ctx` (context-based), `hilbert_iff_nd` (closed),
  and 6 specialized corollaries for Min/Int/Cl variants

#### Semantics Layer (`Semantics/`)

**Bool.lean**: Bivalent `Valuation`/`Evaluate`/`Tautology`, computable `BoolValuation`/
`BoolEvaluate`, bridge lemma `BoolEvaluate_eq_iff`, `instDecidableBoolEvaluate`.

**Kripke.lean**: `KripkeModel` with preorder world, upward-closed valuation, `botForces`
predicate. `IForces` — 5-case forcing relation parameterized over `botForces`. `IValid`
(intuitionistic: `botForces = ⊥`) and `MValid` (minimal: arbitrary `botForces`). Persistence
theorem `iforces_persistence`.

**SemanticConsequence.lean**: `SetDerivable` (finite-subset derivability), `SemanticEntails`
(classical), `ISemanticEntails` (intuitionistic Kripke), `MSemanticEntails` (minimal Kripke).

**Algebra.lean**: `AlgEvaluate` — generic evaluator over `GeneralizedHeytingAlgebra` (GHA).
`GHAValid`/`HAValid`/`BAValid`. GHA = MPL semantics, HA = IPL semantics, BA = CPL semantics.

**Algebra/Lindenbaum.lean**: `LindenbaumAlgebra T` — quotient by derivability equivalence,
GHA instance for MPL, HA instance for IPL (with `lindenbaumBot`), BA instance for CPL.

**Algebra/Completeness.lean**: Algebraic completeness across all three tiers using
`AlgTValid`. Truth lemma `Theory.canonicalV_spec`.

**Algebra/Bridge.lean**, **Algebra/KripkeBridge.lean**: Bridges between algebraic and
Kripke semantics.

**Algebra/Conservative.lean**: `ipl_conservative_over_mpl` — DEFERRED WITH SORRY. Needs
Dedekind-MacNeille completion. `GHAValid_implies_HAValid`, `HAValid_implies_BAValid`.

#### Metalogic Layer (`Metalogic/`)

**MCS.lean**: `PropSetConsistent`, `PropSetMaximalConsistent`, `prop_lindenbaum`,
`prop_mcs_bot_not_mem`, `prop_negation_complete`, `prop_closed_under_derivation`,
`prop_implication_property`.

**Soundness.lean**: Classical soundness: `prop_axiom_sound`, `prop_soundness`,
`prop_soundness_derivable`, `prop_soundness_tautology`.

**StrongCompleteness.lean**: Full canonical model construction. `canonicalValuation`,
`prop_truth_lemma` (per-connective helpers + main), `prop_strong_soundness`,
`prop_strong_completeness`, `prop_strong_completeness_iff`, `prop_compactness`,
`prop_completeness`, `prop_completeness_iff_tautology`.

**DeductionTheorem.lean**: Deduction theorem for the Hilbert system.

**MinSoundness/MinStrongCompleteness/MinLindenbaum.lean**: Minimal logic analogs.
**IntSoundness/IntStrongCompleteness/IntLindenbaum.lean**: Intuitionistic analogs.

---

## Foundations/ Role Analysis

The `Cslib/Foundations/` module (66 files) provides the infrastructure shared across ALL
logic modules. It has six subdirectories:

### `Foundations/Logic/` — Core Logic Abstractions

This is the most important subdirectory for supporting Propositional/ and all other logics.

**`Connectives.lean`** (8 typeclass definitions):
- Atomic: `HasBot`, `HasImp`, `HasAnd`, `HasOr`, `HasBox`, `HasUntil`, `HasSince`, `HasNext`
- Bundled: `PropositionalConnectives`, `ModalConnectives`, `FutureTemporalConnectives`,
  `LTLConnectives`, `TemporalConnectives`, `BimodalConnectives`
- Bridge: `priority 100` instance `BimodalConnectives → ModalConnectives`
- Role: Enables polymorphic axiom definitions and notation across all four logic levels

**`Axioms.lean`**: Polymorphic axiom formulas as `abbrev`s parameterized over connective typeclasses.
- Propositional: `ImplyK`, `ImplyS`, `EFQ`, `Peirce`, `AndI`, `AndE1/2`, `OrI1/2`, `OrE`
- Modal: `AxiomK`, `AxiomT`, `Axiom4`, `AxiomB`, `Axiom5`, `AxiomD`
- Temporal: 22 BX temporal axioms
- Interaction: `ModalFuture`
- Role: "Define once, use everywhere" — a single `ImplyK` definition works for Modal,
  Temporal, Bimodal formula types

**`ProofSystem.lean`** (critical infrastructure):
- Individual axiom typeclasses: `ModusPonens`, `Necessitation`, `TemporalNecessitation`,
  `HasAxiomImplyK/S/EFQ/Peirce`, `HasAxiomAndI/E1/E2/OrI1/2/E`, + 20 modal/temporal
- Bundled proof system classes: `MinimalHilbert`, `IntuitionisticHilbert`, `ClassicalHilbert`,
  `ModalHilbert`, `ModalS5Hilbert`, `TemporalBXHilbert`, `BimodalTMHilbert`
  + 15 modal variants (D, T, S4, S5, KB, K4, K5, K45, TB, KB5, D4, D5, D45, DB)
- Tag types: `Propositional.HilbertCl/Int/Min`, `Modal.HilbertK/T/D/S4/S5/B/K4/K5/K45/TB/KB5/D4/D5/D45/DB`,
  `Temporal.HilbertBX`, `Bimodal.HilbertTM`
- Role: The typeclass hierarchy lets any theorem proved generically for `ClassicalHilbert`
  apply to all classical proof systems (propositional, modal, temporal, bimodal)

**`InferenceSystem.lean`**: `InferenceSystem S α` typeclass with `S⇓a` notation,
`DerivableIn S a`, `HasInferenceSystem`. Role: Uniform derivability notation across all systems.

**`LogicalEquivalence.lean`**: Generic `LogicalEquivalence` relation.

**`Metalogic/`** (6 files): Generic MCS theory applicable to all logics:
- `Consistency.lean`: `DerivationSystem F`, `SetConsistent`, `SetMaximalConsistent`,
  Lindenbaum's lemma (`set_lindenbaum`), `HasDeductionTheorem`, closure properties.
  Used directly by propositional, modal, temporal, and bimodal metalogic.
- `GenericMCS.lean`: `algebraicDerivationSystem` — free `DerivationSystem` for any `MinimalHilbert`.
- `ListDeduction.lean`, `ListImplication.lean`, `MCSProperties.lean`,
  `DeductionHelpers.lean`, `SetDeduction.lean`: Supporting lemmas.

**`Theorems/`** (7 files): Generic theorems derivable in any Hilbert system:
- Combinators, propositional core, connectives, BigConj, Modal (K, S5), Temporal frame conditions
- Role: Libraries of derived rules that work in any `[ModalHilbert S]` or `[ClassicalHilbert S]`

### Other Foundations Subdirectories

**`Foundations/Relation/`** (5 files): `Defs.lean` (core relation notions), `Attr.lean`
(relational attributes for `grind`), `Confluence.lean`, `Domain.lean`, `Euclidean.lean`.
Used by LTS semantics and frame condition proofs.

**`Foundations/Semantics/LTS/`** (14 files) and **`FLTS/`** (4 files): LTS/FLTS definitions,
bisimulation, simulation, divergence, execution, omega execution, trace equivalence, etc.
Not directly used by Propositional/.

**`Foundations/Syntax/`** (5 files): `HasSubstitution`, `HasAlphaEquiv`, `HasWellFormed`,
`Context`, `Congruence`. Generic substitution infrastructure.

**`Foundations/Data/`** (13 files): `HasFresh`, `ListHelpers`, `OmegaSequence`, `FinFun`,
`BiTape`, `StackTape`, `RelatesInSteps`, etc. Used by LTS-based logics.

**`Foundations/Control/`** (3 files): Free monad infrastructure for CCS/effects.

**`Foundations/Combinatorics/`** (1 file): Infinite graph Ramsey theorem.

**`Foundations/Lint/`** (1 file): Lint infrastructure.

---

## Propositional/ Gap Analysis

### Gap 1: `ipl_conservative_over_mpl` is Sorry

**File**: `Semantics/Algebra/Conservative.lean:99`
**Gap**: The conservative extension theorem (IPL is conservative over MPL for bot-free formulas)
is stated but contains `sorry`. The proof requires Dedekind-MacNeille completion of the
Lindenbaum-Tarski algebra to embed the GHA quotient into a Heyting algebra while preserving
bot-free evaluation.
**Impact**: Medium. The rest of the algebraic completeness tower is sorry-free; this is an
isolated gap in the algebraic layer.
**Confidence**: High (directly observed).

### Gap 2: No Sequent Calculus

**Gap**: There is no Gentzen-style sequent calculus (LK for classical, LJ for intuitionistic,
LM for minimal) in Propositional/. The `Sequent` type in `NaturalDeduction/Basic.lean` is
only used for the ND system (single-conclusion, context-managed by Finset).
**Impact**: High for extensibility. A sequent calculus would:
1. Enable cut-elimination proofs (admissibility of cut)
2. Provide an alternative, often more computationally tractable proof system
3. Form the foundation for tableau methods and proof search
4. Connect to the BXCanonical/quasimodel construction pattern used in Bimodal/
**Confidence**: High (exhaustive search found no `LK`/`LJ` mention; the `Sequent` type is
only single-conclusion ND style, not the two-sided sequent of Gentzen's calculus).

### Gap 3: No Tableau System

**Gap**: There is no tableau/analytic tableaux system for propositional logic, despite a comment
in `Bool.lean` mentioning "DPLL/SAT procedures." The `BoolEvaluate` infrastructure was designed
with this in mind but no tableau rules or proof search were implemented.
**Impact**: Medium-high. A tableau system would provide:
1. Decision procedure for propositional satisfiability (directly)
2. Constructive model extraction for non-theorems
3. A natural bridge to the Kripke model construction used in completeness proofs
**Confidence**: High (no tableau files found in Propositional/).

### Gap 4: No Decision Procedure / Normal Forms

**Gap**: There is no CNF/DNF transformation, no SAT decision procedure, and no proof-by-reflection
mechanism that uses `BoolEvaluate` to decide propositional theorems. The `instDecidableBoolEvaluate`
instance exists but is not lifted to a tactic or decision procedure.
**Impact**: Medium. A `decide` tactic wrapper or a dedicated `propDecide` tactic that uses
`BoolEvaluate` would be practically useful. However, CSLib's focus is on metalogic rather than
computational proof, so this is lower priority.
**Confidence**: High.

### Gap 5: No Interpolation Theorem

**Gap**: Craig interpolation theorem is absent. This is a fundamental metalogical result: if
`A → B` is a tautology, there exists an interpolant `C` using only shared atoms such that
`A → C` and `C → B` are both tautologies.
**Impact**: Medium. Important for applications to modal/temporal logic extensions.
**Confidence**: High.

### Gap 6: Capture-Avoiding Substitution in `Derivation.subs`

**File**: `NaturalDeduction/Basic.lean:275`
**Gap**: The `subs` function has a `TODO: this implementation is not capture avoiding`. This is a
known limitation in the current formalization.
**Impact**: Low-medium. The existing implementation works for the goals it serves but may produce
incorrect results if used in contexts requiring capture avoidance.
**Confidence**: High (directly observed).

### Gap 7: Algebraic Completeness Not Bridged to Hilbert System

**File**: `Semantics/Algebra/Completeness.lean:32`
**Gap**: The algebraic completeness theorem uses ND-level `DerivableIn` rather than Hilbert-level
`Derivable`. The comment "requires bridging the Hilbert axiomatic system with the natural
deduction system" is marked as deferred, though the equivalence IS proved in
`NaturalDeduction/Equivalence.lean`.
**Impact**: Low. The bridge theorems in `Equivalence.lean` could be used to lift algebraic
completeness to the Hilbert level. This seems like a straightforward composition.
**Confidence**: High.

### Gap 8: Kripke Completeness for IPL/MPL Not Present

**Gap**: The Kripke semantics for IPL/MPL (`IForces`, `IValid`, `MValid`) are defined in
`Semantics/Kripke.lean`, but completeness w.r.t. Kripke semantics is not proved. The
`Int*/Min*` files provide soundness and completeness for the Hilbert system (via MCS/Lindenbaum),
but specifically w.r.t. the algebraic semantics (HA/GHA), not the Kripke semantics. Kripke
completeness for IPL requires showing the Lindenbaum GHA embeds into a Kripke frame (via
prime filters or the Rose-Rosser approach).
**Impact**: High. IPL/MPL Kripke completeness is a major result. The BimodalLogic reference
(Report 16) shows the complexity of Kripke completeness machinery for richer logics.
**Confidence**: High.

---

## Comparison with BimodalLogic Reference (Report 16)

Report 16 describes a tableau-adjacent system (the "witness-count" / EA-formula / VecEA framework
from Rabinovich's proof of Kamp's theorem). Key observations relevant to Propositional/ development:

### What Report 16 Illuminates About Tableau Design

1. **Induction structure matters critically**: Report 16's core finding is that the induction
   variable (NF-depth vs witness-count) determines what base cases arise and what proofs are
   tractable. For a tableau system for propositional logic, the analogous question is: induction
   on formula structure vs on proof tree height vs on the number of branch extensions.

2. **Bridge theorems are expensive**: Report 16 estimates 500-900 lines for an NF-to-VecEA bridge.
   In the propositional context, bridging between a tableau system and the existing Hilbert/ND
   systems would similarly require careful correspondence proofs.

3. **Zone analysis pattern**: The zone decomposition (witness before/at/between/after endpoints)
   is a form of case analysis on where branch labels fall relative to signed assertions.
   For a propositional tableau, the analog is: which branch contains the current formula,
   and what extension applies? The propositional case is dramatically simpler.

4. **The EA-formula framework is a tableau system**: Rabinovich's `[alpha_0, beta_1, ..., beta_n, alpha_n](z_0, z_1)` is precisely a tableau branch with witnessing points. VecEA formulas directly encode tableau branches as first-class syntactic objects. A CSLib propositional tableau would be a simpler version of this.

### Tableau for Propositional Logic (Concrete Design Implications)

A semantic tableau for propositional logic (`T` and `F` signed formulas) would:
- Be a finite tree with nodes labeled by signed formulas
- Branch (disjunctively) on `T(A ∨ B)`, `F(A ∧ B)`, `F(A → B)` is only `T(A)` and `F(B)`
- Extend (conjunctively) on `T(A ∧ B)`, `F(A ∨ B)`, `T(A → B)` (multiple)
- Close when a branch contains both `T(A)` and `F(A)` for some `A`
- Be **open** when fully expanded with no closed branches (witness to unsatisfiability failure)

The CSLib architecture would implement this as:
```
inductive TableauNode (Atom : Type*) where
  | tf : Bool → Proposition Atom → TableauNode  -- signed formula T/F A
inductive Tableau (Atom : Type*) where
  | leaf : List (TableauNode Atom) → Tableau  -- open or closed branch
  | branch : ... -> Tableau -> Tableau -> Tableau  -- bifurcation
```

Key theorems:
1. **Soundness**: If a tableau for `F(A)` closes, then `A` is a tautology
2. **Completeness**: If `A` is a tautology, then the systematic tableau for `F(A)` closes
3. **Decision procedure**: Since propositional logic is decidable, the systematic procedure terminates

---

## Recommended Approach (Prioritized Improvements)

### Priority 1 (High Impact, Moderate Effort): Kripke Completeness for IPL

**What**: Prove that IPL is sound and complete w.r.t. Kripke semantics (`IValid`).
**Approach**: The Lindenbaum GHA for IPL is a `HeytingAlgebra`. The spectrum of prime filters
in a Heyting algebra forms a Kripke frame. The canonical Kripke model is defined by:
- Worlds = prime filters of `LindenbaumAlgebra IPL`
- Preorder = filter inclusion
- `v(w)(p) = atom p ∈ w`
**Evidence for feasibility**: The algebraic Lindenbaum tower for IPL is already in CSLib
(HeytingAlgebra instance in `Algebra/Lindenbaum.lean`). The prime filter construction is
standard Mathlib territory.
**Files**: New `Semantics/Kripke/IPLCompleteness.lean`
**Estimated size**: 200-400 lines

### Priority 2 (High Impact, Low Effort): Bridge Algebraic Completeness to Hilbert

**What**: Lift algebraic completeness from ND-level `DerivableIn` to Hilbert-level `Derivable`
using the existing equivalences in `Equivalence.lean`.
**Approach**: Compose `alg_complete` with `hilbert_iff_nd`.
**Evidence**: `hilbert_iff_nd_min/int/cl` are already proved in Equivalence.lean.
`Theory.alg_complete` is proved in Algebra/Completeness.lean.
**Files**: Add corollaries to `Semantics/Algebra/Completeness.lean` or a new `Bridge.lean`
**Estimated size**: 30-60 lines

### Priority 3 (Medium Impact, High Effort): Dedekind-MacNeille Completion / Conservative Extension

**What**: Prove `ipl_conservative_over_mpl` (filling the sorry).
**Approach**: Construct the Dedekind-MacNeille completion of a GHA as a Heyting algebra.
Show the embedding preserves evaluation of bot-free formulas. Apply to the Lindenbaum GHA for MPL.
**Evidence**: Mathlib has `Order.Completion` infrastructure that may help. The theoretical
argument is standard (Rasiowa 1974, chapter 6).
**Estimated size**: 300-600 lines (significant Mathlib search needed first)

### Priority 4 (High Impact, High Effort): Sequent Calculus LK/LJ

**What**: Add a Gentzen sequent calculus for CPL (LK) and/or IPL (LJ).
**Design**: Two-sided sequents `Γ ⊢ Δ` (multi-conclusion for LK, single-conclusion for LJ).
Inductive rules for each connective (left/right introduction).
**Key theorems**: Admissibility of cut (`cut_admissible`), soundness and completeness.
**Relationship to existing code**: Would bridge to `Theory.Derivation` via the usual cut theorem
connection. The `Sequent` type in `NaturalDeduction/Basic.lean` is single-conclusion ND style
and would need to be distinct from multi-conclusion sequents.
**Estimated size**: 400-800 lines for LK + cut elimination

### Priority 5 (Medium Impact, High Effort): Tableau Decision Procedure

**What**: Semantic tableaux for CPL with a soundness, completeness, and termination proof.
**Design**: Signed formulas, branch closure condition, systematic expansion, open branch
as countermodel extractor.
**Relationship to BimodalLogic reference**: The VecEA/EA-formula framework in BimodalLogic is
a sophisticated version of this. The propositional case is the simplest possible tableau,
with no temporal or modal quantification. This would serve as a foundation for potential
tableau methods in the modal and temporal logic modules.
**Estimated size**: 300-600 lines

### Priority 6 (Low Impact, Low Effort): Fix `subs` Capture Avoidance

**What**: Replace the non-capture-avoiding `subs` implementation with a correct one using fresh
variable generation (or alpha-equivalence).
**Approach**: Use `HasFresh` from `Foundations/Data/HasFresh.lean` which provides fresh atom
generation infrastructure.
**Files**: `NaturalDeduction/Basic.lean`
**Estimated size**: 50-150 lines

---

## Evidence / Specific Code References

### Foundations/ Infrastructure Used by Propositional/

```
Propositional/Defs.lean:
  public import Cslib.Foundations.Logic.Connectives  -- PropositionalConnectives instance

Propositional/ProofSystem/Derivation.lean:
  public import Cslib.Foundations.Logic.Metalogic.Consistency  -- DerivationSystem

Propositional/ProofSystem/Instances.lean:
  public import Cslib.Foundations.Logic.ProofSystem  -- ClassicalHilbert, tag types

Propositional/NaturalDeduction/Basic.lean:
  public import Cslib.Foundations.Logic.InferenceSystem  -- InferenceSystem, S⇓a notation

Propositional/Metalogic/MCS.lean:
  -- uses propDerivationSystem to plug into generic MCS framework
```

### Key Type: `DerivationSystem` (Foundations/Logic/Metalogic/Consistency.lean:55)

```lean
structure DerivationSystem (F : Type*) [HasBot F] [HasImp F] where
  Deriv : List F → F → Prop
  weakening : ∀ {Γ Δ : List F} {φ : F}, Deriv Γ φ → (∀ x ∈ Γ, x ∈ Δ) → Deriv Δ φ
  assumption : ∀ {Γ : List F} {φ : F}, φ ∈ Γ → Deriv Γ φ
  mp : ∀ {Γ : List F} {φ ψ : F}, Deriv Γ (HasImp.imp φ ψ) → Deriv Γ φ → Deriv Γ ψ
```

This structure is instantiated by `propDerivationSystem` (Propositional/) and by modal/temporal
systems. Lindenbaum's lemma (`set_lindenbaum`) works for any `DerivationSystem`.

### Key Theorem: `prop_strong_completeness` (Metalogic/StrongCompleteness.lean:490)

Uses the Lindenbaum extension to build a canonical model from any consistent set, then applies
`prop_truth_lemma` to derive the semantic consequence. This is the template for all completeness
proofs in the library.

### Key Gap: `ipl_conservative_over_mpl` (Semantics/Algebra/Conservative.lean:96-99)

```lean
theorem ipl_conservative_over_mpl {A : Proposition Atom}
    (_hBF : A.IsBotFree = true) (h : DerivableIn (IPL (Atom := Atom)) A) :
    DerivableIn (MPL (Atom := Atom)) A := by
  sorry
```

### Key Design Note: Why Sequent Calculus is NOT Yet Present

The Propositional/ module has a `Sequent` type but it is ND-style (single-conclusion):

```lean
-- NaturalDeduction/Basic.lean:108
abbrev Sequent {Atom} := Ctx Atom × Proposition Atom
```

A Gentzen sequent calculus would need a distinct type `GentzenSequent {Atom} := Ctx Atom × Ctx Atom`
(or `Finset × Finset`) for multi-conclusion (LK) style. The notation conflict with the existing
`⊢` notation would need careful handling.

---

## Confidence Assessment

| Finding | Confidence | Basis |
|---------|------------|-------|
| Complete file inventory of Propositional/ (30 files) | High | Direct filesystem enumeration |
| Complete file inventory of Foundations/ (66 files) | High | Direct filesystem enumeration |
| Sorry in `ipl_conservative_over_mpl` | High | File read, confirmed at line 99 |
| Absence of sequent calculus | High | Exhaustive grep + file review |
| Absence of tableau system | High | Exhaustive grep + file review |
| Kripke completeness gap for IPL | High | File review of Kripke.lean + Metalogic/ |
| Algebraic↔Hilbert bridge gap | High | Both files read, gap confirmed |
| `subs` capture issue (TODO) | High | Direct quote at line 275 |
| Priority rankings | Medium | Based on theory + CSLib patterns; no user input |
| Estimated effort figures | Low | Rough estimates based on analogous CSLib files |

---

## Summary

The Propositional/ module is CSLib's most complete logic module, providing:
- Hilbert proof system (3 axiom variants) with derivation trees
- Natural deduction (10-constructor inductive) with cut/weakening/substitution
- Full equivalence bridge between Hilbert and ND (all 3 logic levels, 8 theorems)
- Bivalent, Boolean, Kripke, and algebraic semantics
- Strong soundness and completeness for CPL (via canonical model)
- Algebraic completeness for MPL/IPL/CPL (via Lindenbaum tower)
- Lindenbaum's lemma and MCS theory (generic, applicable to all logics)

The Foundations/ module provides the shared infrastructure that makes all logics in CSLib
composable: connective typeclasses, polymorphic axiom formulas, the Hilbert hierarchy of proof
system classes, the generic DerivationSystem / MCS framework, and the InferenceSystem notation.

The main gaps are: (1) no sequent calculus, (2) no tableau/decision procedure, (3) no Kripke
completeness for IPL/MPL, (4) one sorry in conservative extension, and (5) a non-capture-avoiding
substitution. Priorities 1-2 are most actionable immediately given existing CSLib infrastructure.
