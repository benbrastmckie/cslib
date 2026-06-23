# Research Report: Task #266 — Teammate A: Primary Angle

**Task**: 266 — Research Propositional/ and Foundations/ Improvements
**Started**: 2026-06-22
**Role**: Teammate A — Current State Analysis, Implementation Patterns, Gap Analysis, BimodalLogic Comparison
**Task Type**: cslib
**Domains**: logic, propositional logic, foundations

---

## Key Findings

1. **CSLib Propositional is substantively complete for a foundation-level library.** All three logic tiers (MPL, IPL, CPL) have Hilbert-style proof systems, natural deduction, soundness, strong completeness, compactness, and Lindenbaum/canonical model infrastructure — all sorry-free. This is rare for a research library at CSLib's maturity level.

2. **A critical gap exists: Hilbert-ND bridge for algebraic completeness.** `Algebra/Completeness.lean` explicitly documents "Future Work: Hilbert-level corollaries require bridging the Hilbert axiomatic system with the natural deduction system. This equivalence is nontrivial and deferred." The bridge exists for `DerivationTree ↔ Theory.Derivation` (in `NaturalDeduction/Equivalence.lean`) but has NOT been composed to produce Hilbert-tier algebraic completeness corollaries.

3. **No decidability or normal-forms module exists for Propositional/.** The Bimodal logic has an extensive `Decidability/` subdirectory (signed formulas, tableau rules, decision procedure, FMP, filtration, correctness, proof extraction). The Propositional layer has `BoolEvaluate` (computable evaluation) but zero decision procedure infrastructure.

4. **No sequent calculus (Gentzen LK/LJ).** The library has Hilbert-style proofs and natural deduction (Finset-context style), but no two-sided sequent calculus. The `LinearLogic/CLL/` directory uses a multiset-based sequent calculus as a reference implementation of a different formalism. For classical/intuitionistic PL, a Gentzen-style LK/LJ is absent.

5. **ProofSystem typeclass hierarchy is defined but only partially instantiated.** `Foundations/Logic/ProofSystem.lean` defines `MinimalHilbert`, `IntuitionisticHilbert`, `ClassicalHilbert` and all the modal/temporal extensions as typeclasses, with opaque tag types for each. `ProofSystem/Instances.lean` registers `HilbertCl`, and `ProofSystem/IntMinInstances.lean` registers `HilbertInt` and `HilbertMin`. But the abstract interface — while clean — is not yet used to provide "generic MCS" reasoning; the actual MCS proofs are hand-written per logic.

6. **The Bimodal Decidability tableau system is far richer than anything in Propositional.** The BimodalLogic tableau (`Decidability/Tableau.lean`) has 30+ rules, signed formulas, label-indexed branches (world × time), persistent vs. consumable rules, the Prior-UZ/SZ discrete axioms, density rules, and a full `applyRule`/`expandOnce`/`expandOnceWithApplied` pipeline. None of this exists for PL.

7. **The BimodalLogic witness-count report (16_witness-count-restructure.md) is about a deep temporal/modal proof problem** — not about propositional decidability. The tableau there is for bimodal TM logic, not CPL. The propositional tableau rules in CSLib's bimodal tableau (andPos/andNeg/orPos/orNeg/impPos/impNeg/negPos/negNeg) are embedded within a much richer system and are not extracted to a standalone propositional tableau.

---

## Current State Analysis

### File Structure

**Cslib/Logics/Propositional/** (31 files, ~6,126 lines total):
```
Defs.lean                          -- Formula type, substitution monad, MPL/IPL/CPL theories
ProofSystem/
  Axioms.lean                      -- MinPropAxiom, IntPropAxiom, PropositionalAxiom (inductive)
  Derivation.lean                  -- DerivationTree, Deriv, propDerivationSystem
  Instances.lean                   -- HilbertCl instance registration
  IntMinInstances.lean             -- HilbertInt, HilbertMin instance registration
NaturalDeduction/
  Basic.lean                       -- Theory.Derivation (10 constructors), cut, subs, substAtom
  DerivedRules.lean                -- Weakening, contradiction helpers
  FromHilbert.lean                 -- hilbertToND translation
  HilbertDerivedRules.lean         -- andI/orE/etc for DerivationTree
  Equivalence.lean                 -- hilbert_iff_nd, hilbert_iff_nd_{min,int,cl}
Metalogic/
  DeductionTheorem.lean            -- deductionTheorem for DerivationTree
  MCS.lean                         -- PropSetMaximalConsistent, Lindenbaum for CPL
  Soundness.lean                   -- prop_soundness for CPL (bool eval)
  StrongCompleteness.lean          -- prop_strong_{soundness,completeness}, compactness
  IntLindenbaum.lean               -- IntDCCS, IntPrimeDCCS, prime_exclusion for IPL
  IntSoundness.lean                -- int_soundness
  IntStrongCompleteness.lean       -- int_strong_{soundness,completeness}, int_truth_lemma
  MinLindenbaum.lean               -- MinTheory, MinPrimeTheory, prime_exclusion for MPL
  MinSoundness.lean                -- min_soundness
  MinStrongCompleteness.lean       -- min_strong_{soundness,completeness}, min_truth_lemma
Semantics/
  Bool.lean                        -- Valuation, Evaluate, Tautology, BoolEvaluate, bridge
  Kripke.lean                      -- KripkeModel, IForces, iforces_persistence, IValid, MValid
  SemanticConsequence.lean         -- SemanticEntails, ISemanticEntails, MSemanticEntails
  Algebra.lean                     -- AlgEvaluate, GHAValid, HAValid, BAValid, AlgTValid
  Algebra/
    Lindenbaum.lean                -- LindenbaumAlgebra, lindenbaumMk, lindenbaumMk_le_mk
    Completeness.lean              -- Theory.alg_complete, MPL/IPL.alg_complete, alg_complete_classical
    Soundness.lean                 -- nd_alg_sound (ND → algebraic)
    Conservative.lean              -- IsBotFree, ipl_conservative_over_mpl
    Glivenko.lean                  -- glivenko_algebraic, glivenko theorem
    KripkeBridge.lean              -- UpsetAlgebra, kripkeAlgBridge, iValidOfHAValid, mValidOfGHAValid
    Bridge.lean                    -- (cross-reference bridge)
```

**Cslib/Foundations/Logic/** (key files):
```
InferenceSystem.lean               -- InferenceSystem typeclass, DerivableIn
ProofSystem.lean                   -- MinimalHilbert, ClassicalHilbert, ModalHilbert etc + tags
Axioms.lean                        -- Axioms.ImplyK, AxiomK, AxiomT, etc. (generic formulas)
Connectives.lean                   -- PropositionalConnectives, HasBox, HasUntil, HasSince, etc.
LogicalEquivalence.lean            -- LogicalEquivalence typeclass
Theorems.lean                      -- re-export of Theorems/
Theorems/Propositional/Core.lean   -- generic propositional theorems
Theorems/Propositional/Connectives.lean
Theorems/Modal/Basic.lean          -- generic modal theorems
Theorems/Modal/S5.lean
Theorems/Temporal/FrameConditions.lean
Theorems/Temporal/TemporalDerived.lean
Metalogic/
  Consistency.lean                 -- DerivationSystem, SetMaximalConsistent, generic MCS API
  GenericMCS.lean                  -- algebraicDerivationSystem, algebraic_mcs_* wrappers
  ListDeduction.lean               -- ListDeriv, list_deduction_theorem
  ListImplication.lean             -- listImp, flip lemmas
  SetDeduction.lean                -- SetDerivable, SetDerivable_empty_iff
  DeductionHelpers.lean            -- deductionWithMem, removeAll
  MCSProperties.lean               -- closed_under_derivation, negation_complete, implication_property
```

### Proof Systems

**Classical (CPL)**:
- `PropositionalAxiom`: 10 axioms (implyK, implyS, efq, peirce, andI, andE1, andE2, orI1, orI2, orE)
- `DerivationTree PropositionalAxiom`: Hilbert derivation trees with 4 constructors (ax, assumption, modus_ponens, weakening)
- `Theory.Derivation`: Natural deduction with 10 constructors (ax, ass, andI, andE1×2, orI×2, orE, impI, impE)
- Bridge: `hilbert_iff_nd_cl` (extensional equivalence)
- Semantics: Bool (`Evaluate`), Kripke (classical = trivial), Algebraic (Boolean algebra)
- Metalogic: `prop_strong_soundness`, `prop_strong_completeness`, `prop_compactness`, `prop_completeness_iff_tautology`
- Algebraic: `alg_complete_classical` (ND tier), NOT lifted to Hilbert tier (see Future Work gap)

**Intuitionistic (IPL)**:
- `IntPropAxiom`: 9 axioms (CPL minus peirce)
- All same infrastructure as CPL
- Kripke: `IForces` with `botForces = fun _ => False`, `IValid`
- Metalogic: `int_strong_completeness`, `int_truth_lemma` (prime DCCS canonical model)
- Algebraic: `IPL.alg_complete` (Heyting algebras), `glivenko` theorem
- `KripkeBridge`: `kripkeAlgBridge` connects `IForces` to `AlgEvaluate` over `UpsetAlgebra`

**Minimal (MPL)**:
- `MinPropAxiom`: 8 axioms (IPL minus efq)
- Kripke: `IForces` with arbitrary upward-closed `botForces`, `MValid`
- Metalogic: `min_strong_completeness`, prime MinTheory canonical model
- Algebraic: `MPL.alg_complete` (Generalized Heyting algebras = Johansson algebras)
- Conservative: `ipl_conservative_over_mpl` for bot-free formulas (WithBot embedding)

### Foundations Infrastructure

The `Foundations/Logic/` layer provides the generic typeclass spine:
- `InferenceSystem S F`: tag-indexed derivability notation `S⇓a`
- `DerivationSystem F`: structural proof system with Deriv, weakening, assumption, mp
- `SetMaximalConsistent`: generic MCS with `closed_under_derivation`, `implication_property`, `negation_complete`
- `MinimalHilbert` → `IntuitionisticHilbert` → `ClassicalHilbert` → `ModalHilbert` → `TemporalBXHilbert` → `BimodalTMHilbert`
- `GenericMCS`: `algebraicDerivationSystem` from any `MinimalHilbert` + free deduction theorem

**Important gap**: The `ProofSystem.lean` module explicitly says "Concrete instances require derivation trees (not yet ported) and are future work." While `Instances.lean` registers `HilbertCl` (it uses `DerivationTree [] φ`), the abstract `HasAxiom*` typeclasses are not leveraged by the generic `GenericMCS` or `algebraicDerivationSystem` for propositional reasoning. The propositional MCS proofs (`MCS.lean`, `StrongCompleteness.lean`) bypass the generic API and work directly with `propDerivationSystem`.

---

## Implementation Patterns

### Formula Representation

`Proposition Atom` uses a 5-constructor inductive (atom, bot, imp, and, or). Negation, top, biconditional are `abbrev` derived. This is **Johansson-style** (minimal-logic-friendly): `neg A := A → ⊥`, `top := ⊥ → ⊥`. The type forms a monad (`pure := .atom`, `bind := .subst`), enabling atom-substitution as monadic bind.

Contexts are `Finset (Proposition Atom)` in natural deduction (avoiding explicit contraction/exchange) and `List (Proposition Atom)` in Hilbert derivation trees. The Hilbert system uses `List` to support the height-based well-founded recursion in the deduction theorem.

### Semantic Layers

Three parallel semantics exist:
1. **Bool/Prop**: `Evaluate v φ : Prop`, `BoolEvaluate v φ : Bool`, `BoolEvaluate_eq_iff` bridge
2. **Kripke**: `IForces v botForces w φ` over preordered worlds
3. **Algebraic**: `AlgEvaluate v botVal φ` over GHA/HA/Boolean algebras

These three layers are connected:
- Bool ↔ Algebraic: `prop_completeness_iff_tautology` (CPL), `int_soundness_completeness`, `min_soundness_completeness`
- Kripke ↔ Algebraic: `kripkeAlgBridge` + `iValidOfHAValid` / `mValidOfGHAValid`
- Hilbert ↔ ND: `hilbert_iff_nd_{min,int,cl}`

---

## Gap Analysis

### Gap 1: Hilbert-Tier Algebraic Completeness (Explicitly Acknowledged)

`Algebra/Completeness.lean` section "Future Work" states:
> "Hilbert-level corollaries require bridging the Hilbert axiomatic system (`DerivationTree`/`Derivable`) with the natural deduction system (`Theory.Derivation`/`DerivableIn`). This equivalence is nontrivial and deferred."

The `hilbert_iff_nd_{min,int,cl}` bridge exists in `NaturalDeduction/Equivalence.lean`. Composing this with `MPL.alg_complete`, `IPL.alg_complete`, and `alg_complete_classical` would yield:
- `Derivable MinPropAxiom φ ↔ GHAValid φ`
- `Derivable IntPropAxiom φ ↔ HAValid φ`
- `Derivable PropositionalAxiom φ ↔ BAValid φ` (or equivalently `Tautology φ`)

These are clean, useful export lemmas for downstream users. The implementation is straightforward: compose the two existing bridges. Estimated effort: 50-100 lines.

### Gap 2: Decidability / Decision Procedure

**No decision procedure exists for propositional logic.** CSLib has:
- `BoolEvaluate`: computable evaluation but no enumeration over all valuations
- No `decide`-based tautology checker (Lean's `decide` tactic would work for finite atoms but requires `Fintype Atom`)
- No analytic tableau for CPL (despite the bimodal tableau having PL rules embedded)
- No DPLL or truth-table construction
- No `instDecidableTautology` instance

A natural addition would be:
1. A tableau system for CPL analogous to the bimodal one, restricted to the 8 propositional rules (andPos/andNeg/orPos/orNeg/impPos/impNeg/negPos/negNeg). With proof-theoretic correctness.
2. Decidability of `Tautology φ` for formulas with finitely many atoms.

### Gap 3: Sequent Calculus (LK / LJ)

**No Gentzen sequent calculus exists.** The library has:
- Hilbert: `DerivationTree` (List context)
- Natural Deduction: `Theory.Derivation` (Finset context)

Missing:
- **LK** (classical sequent calculus): two-sided sequents `Γ ⊢ Δ` with structural rules (weakening, contraction, exchange) and logical rules for each connective
- **LJ** (intuitionistic sequent calculus): one-sided, restricted `Γ ⊢ A`
- Cut-elimination theorem (Gentzen's Hauptsatz)
- Connection to natural deduction via Prawitz normalization

The `LinearLogic/CLL/` module provides a reference implementation with multisets and cut elimination for CLL. The same pattern could be applied to IPL/CPL.

### Gap 4: Normal Forms and Substitution Completeness

**No normal form theorems.** Missing:
- Conjunctive Normal Form (CNF) transformation + correctness proof
- Disjunctive Normal Form (DNF) transformation + correctness proof
- Interpolation theorem (Craig interpolation): for CPL, `φ → ψ` has an interpolant `θ` using only shared variables, derivable both from `φ` and deriving `ψ`
- Uniform substitution (although `Proposition.subst` exists, its full substitution completeness for CPL is not proved)

### Gap 5: Propositional Subformula Property and Related Results

**Missing proof-theoretic results** standard in textbooks:
- Subformula property for the ND/Hilbert systems (every formula in a proof is a subformula of the endsequent or assumptions)
- Interpolation / Beth's definability theorem
- Variable sharing property (for IPL)
- Propositional compactness via the ND system (exists for CPL via strong completeness, but not stated directly for MPL/IPL in a clean form accessible to downstream users)

### Gap 6: `HasDiamond` Typeclass

`Foundations/Logic/Axioms.lean` notes: "Diamond is encoded classically as `◇φ = ¬□¬φ = (□(φ → ⊥)) → ⊥`, since `HasDia` is not yet [defined]." This means modal formulas requiring diamond use the encoded form rather than a dedicated typeclass. A `HasDiamond` typeclass with appropriate axioms would clean this up.

### Gap 7: Generic Propositional MCS Integration

The `GenericMCS.lean` module provides `algebraicDerivationSystem` and `algebraic_mcs_*` wrappers that should work for any `MinimalHilbert`. However, the propositional completeness proofs (`StrongCompleteness.lean`, `IntStrongCompleteness.lean`, `MinStrongCompleteness.lean`) directly use `propDerivationSystem` instead of routing through the generic API. Refactoring to use the generic infrastructure would:
- Reduce code duplication (the MCS lemmas like `prop_closed_under_derivation`, `prop_negation_complete` are one-off rewrites of generic results)
- Enable easier extension to new proof systems

---

## BimodalLogic Comparison

### The Tableau in 16_witness-count-restructure.md

The `16_witness-count-restructure.md` report is NOT about propositional decidability. It concerns:
- **Context**: Kamp's Expressiveness Theorem for linear temporal logic (proving FO = LTL on linear orders)
- **The tableau**: `Cslib/Logics/Bimodal/Metalogic/Decidability/Tableau.lean` (30+ rules for TM bimodal logic: modal S5 + linear temporal)
- **The K=0 problem**: An induction base case failure in `prior_nonconstenv_2var_agree_until` at depth-1 2-var agreement for NF (normal form) composition

The tableau system in CSLib's Bimodal (`Decidability/Tableau.lean`) handles propositional rules as a sub-component:
- `andPos`: T(A∧B) → T(A), T(B) — with A∧B encoded as `¬(A→¬B)`
- `andNeg`: F(A∧B) → F(A) | F(B) — branching
- `orPos`, `orNeg`, `impPos`, `impNeg`, `negPos`, `negNeg`: standard propositional rules

These 8 propositional rules in the bimodal tableau are correct and complete for propositional reasoning within the larger system. **However, they are not extracted or proved correct in isolation** — the tableau correctness (`Decidability/Correctness.lean`) covers the full bimodal system.

### What CSLib's Propositional Layer is Missing (vs. the Bimodal Decidability)

| Feature | Bimodal Decidability | Propositional |
|---------|---------------------|---------------|
| Signed formulas | `SignedFormula` (T/F) | None |
| Tableau rules | 30+ rules, `TableauRule` inductive | None |
| Rule applicability | `isApplicable`, `findApplicableRule` | None |
| Branch expansion | `expandOnce`, `expandOnceWithApplied` | None |
| Termination | `countUnexpanded`, `totalUnexpandedComplexity` | None |
| Correctness | `Decidability/Correctness.lean` | None |
| FMP | `Decidability/FMP/` (filtration, finite model) | None |
| Decision procedure | `Decidability/DecisionProcedure.lean` | None |
| Proof extraction | `Decidability/ProofExtraction.lean` | None |
| Trace certificates | `Decidability/TraceCertificate.lean` | None |

A standalone propositional tableau would be dramatically simpler: no world/time labels, no modal or temporal rules, no frame-class parameterization. It would be roughly 200-400 lines for a complete propositional analytic tableau with correctness and completeness proofs.

### The Witness-Count Problem: CSLib vs. Standard Treatment

The 16-witness-count-restructure report identifies that the NF-depth induction doesn't match Rabinovich's witness-count induction for the Kamp theorem. This is a **deep temporal logic problem** orthogonal to propositional logic. Implications for the Propositional layer:
- The `Proposition.subst` (monadic bind) approach in CSLib PL is clean and sufficient for the propositional layer
- The bimodal completeness proofs (conservative extension, MCS, truth lemma) import propositional infrastructure extensively — confirming the importance of getting propositional right
- The modular design (propositional as foundation for modal/temporal/bimodal) means any gaps in propositional infrastructure propagate upward

---

## Recommended Approach

Listed in priority order (highest value/effort ratio first):

### Priority 1: Hilbert-Tier Algebraic Completeness Corollaries (Low effort, High value)

**Files**: Create `Cslib/Logics/Propositional/Semantics/Algebra/HilbertCompleteness.lean`

Compose `hilbert_iff_nd_{min,int,cl}` with `{MPL,IPL}.alg_complete` and `alg_complete_classical` to state:
```lean
theorem Derivable_MinPropAxiom_iff_GHAValid {A : Proposition Atom} :
    Derivable MinPropAxiom A ↔ GHAValid A
theorem Derivable_IntPropAxiom_iff_HAValid {A : Proposition Atom} :
    Derivable IntPropAxiom A ↔ HAValid A
theorem prop_completeness_iff_BAValid {A : Proposition Atom} :
    Derivable PropositionalAxiom A ↔ BAValid A
```

These are publishable completeness results. Estimated effort: 1-2 days.

### Priority 2: Generic MCS Integration Cleanup (Medium effort, Medium value)

Replace per-logic `prop_closed_under_derivation`, `prop_negation_complete`, `prop_implication_property` in `MCS.lean` with calls to the generic `algebraic_mcs_*` wrappers from `GenericMCS.lean`. This would:
- Reduce ~162 lines of `MCS.lean` to ~30 lines of instance registration + delegation
- Make the pattern visible for future logic extensions

### Priority 3: Propositional Analytic Tableau (High effort, High value)

**Files**: Create `Cslib/Logics/Propositional/Tableau/` with:
- `SignedFormula.lean`: `Sign = pos | neg`, `SignedFormula = Sign × Proposition Atom`
- `Rules.lean`: `TableauRule` for the 8 propositional rules, `applyRule`, `expandOnce`
- `Soundness.lean`: if tableau closes then formula is a tautology
- `Completeness.lean`: if formula is a tautology then all branches close

Estimated effort: 400-600 lines across 4 files. This would also provide the foundation for a CPL decidability proof.

### Priority 4: Sequent Calculus LK (High effort, High value)

**Files**: Create `Cslib/Logics/Propositional/SequentCalculus/` with:
- `LK.lean`: two-sided sequents `Γ ⊢ Δ`, 20 rules
- `CutElimination.lean`: `cut_elimination : LK Γ ⊢ Δ → LKCutFree Γ ⊢ Δ`
- `Equivalence.lean`: `LK_iff_nd_cl`, `LK_iff_hilbert_cl`

Using the `LinearLogic/CLL/CutElimination.lean` as a model. Estimated effort: 600-1000 lines.

### Priority 5: Craig Interpolation (Specialized, Medium effort)

For CPL, Craig interpolation states: if `⊢ φ → ψ` then there exists `θ` using only shared atoms of `φ` and `ψ`, with `⊢ φ → θ` and `⊢ θ → ψ`. Proof via sequent calculus is classical (cut-elimination + interpolation lemma). Requires Priority 4 first. Estimated effort: 300-500 lines after LK.

---

## Evidence/Examples

### Key File References

- `Defs.lean:81` — `Proposition Atom` inductive definition
- `Defs.lean:154-162` — MPL, IPL, CPL as `Theory` abbreviations
- `ProofSystem/Axioms.lean:48-78` — `PropositionalAxiom` with 10 constructors
- `ProofSystem/Derivation.lean:68-83` — `DerivationTree` with 4 constructors
- `NaturalDeduction/Basic.lean:117-146` — `Theory.Derivation` with 10 constructors
- `NaturalDeduction/Equivalence.lean:305-318` — `hilbert_iff_nd` bridge theorem
- `Metalogic/StrongCompleteness.lean:490-512` — `prop_strong_completeness` proof
- `Semantics/Algebra/Completeness.lean:219-229` — `Theory.alg_complete`
- `Semantics/Algebra/Completeness.lean:28-33` — "Future Work" note on Hilbert gap
- `Semantics/Algebra/KripkeBridge.lean` — `kripkeAlgBridge` main bridge theorem
- `Semantics/Algebra/Glivenko.lean:125-141` — `glivenko` theorem proof
- `Foundations/Logic/ProofSystem.lean:50` — "not yet ported, future work" comment
- `Foundations/Logic/Metalogic/GenericMCS.lean:46-61` — `algebraicDerivationSystem`
- `Cslib/Logics/Bimodal/Metalogic/Decidability/Tableau.lean:85-164` — `TableauRule` inductive (30+ rules)
- `Cslib/Logics/Bimodal/Metalogic/Decidability/Tableau.lean:295-338` — `isApplicable`

### Sorry Inventory

**Zero sorries in Propositional/ or Foundations/.** All 31 Propositional files and all Foundations/Logic files are fully sorry-free. This is a significant achievement.

### Interesting Architecture Decisions

1. `⊥` is a primitive constructor but EFQ is NOT a primitive ND rule — it enters as a theory axiom (documented design trade-off in `NaturalDeduction/Basic.lean:55-76`). This allows MPL/IPL/CPL to share one `Derivation` inductive.

2. `AlgEvaluate` takes `bot_val : H` as explicit parameter because GHA (= Johansson algebra) has no canonical bottom. For `HeytingAlgebra`/`BooleanAlgebra`, `bot_val = ⊥` is canonical. The `IsBotFree` predicate (`Conservative.lean`) handles the conservative extension by showing bot-free formulas don't depend on `bot_val`.

3. The Kripke semantics is parameterized by `botForces : World → Prop` (with upward-closure), not hardcoded to `False`. Setting `botForces = fun _ => False` gives intuitionistic semantics; arbitrary upward-closed `botForces` gives minimal semantics. This is analogous to how `AlgEvaluate` is parameterized by `bot_val`.

---

## Confidence Level

| Finding | Confidence |
|---------|------------|
| No sorries in Propositional/Foundations Logic | High — confirmed by grep |
| Hilbert-Algebraic completeness gap explicitly acknowledged | High — exact quote from source |
| No decidability/tableau in Propositional | High — confirmed by directory listing |
| No sequent calculus in Propositional | High — confirmed by directory listing |
| BimodalLogic tableau is for TM logic, not standalone PL | High — read full Tableau.lean |
| 16_witness-count-restructure.md is about temporal Kamp theorem | High — read full report |
| GenericMCS not used by PL metalogic | High — read MCS.lean and GenericMCS.lean |
| The 8 PL tableau rules in Bimodal are embedded, not extracted | High — confirmed in Tableau.lean |
| ProofSystem tags not fully instantiated | Medium — HilbertCl/Int/Min registered but generic API not exercised by PL completeness proofs |
