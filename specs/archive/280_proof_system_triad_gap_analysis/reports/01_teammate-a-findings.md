# Teammate A Findings: Comprehensive Audit of Existing CSLib Proof System Infrastructure

**Task**: 280 — Proof System Triad Gap Analysis  
**Role**: Primary Researcher — Comprehensive Audit of Existing Infrastructure  
**Date**: 2026-06-23

---

## Executive Summary

CSLib's propositional proof system infrastructure is substantially complete for Hilbert and ND tiers. The algebraic semantics are thorough and well-bridged. The Kripke semantics exist for the intuitionistic and minimal logics. Sequent calculus (LK/LJ) is entirely absent — that is the scope of task 279 (not started). The main gaps for closing the "proof system triad" are: (A) no propositional sequent calculus whatsoever (blocked on task 279), (B) no Curry-Howard / normalization results in the ND system, (C) a `Decidable (Tautology φ)` instance exists via Bool semantics but is not composed with Hilbert completeness to yield a `Decidable (Derivable PropositionalAxiom φ)` instance, and (D) several bridge corollaries connecting the Hilbert tier to the algebraic results are either not named at the top level of `ProofSystem.lean` or not yet corollaried for each logic tier via the `HilbertCl`/`HilbertInt`/`HilbertMin` tag types.

---

## Key Findings

### 1. Hilbert System — Status: Very Strong

**Axiom schemata** (`ProofSystem/Axioms.lean`):
- Three complete axiom sets: `PropositionalAxiom` (classical, 10 schemata), `IntPropAxiom` (intuitionistic, 9 schemata), `MinPropAxiom` (minimal, 8 schemata).
- Axiom subsumption theorems: `MinPropAxiom.toIntPropAxiom`, `IntPropAxiom.toPropAxiom` — both fully proved.
- Witness lemmas (`mem_implyK`, `mem_implyS`) for all three tiers.

**Derivation trees** (`ProofSystem/Derivation.lean`):
- `DerivationTree Axioms Γ φ` — parameterized inductive with 4 constructors: ax, assumption, modus_ponens, weakening. Computable (lives in `Type`).
- `Deriv Axioms Γ φ` — `Prop`-level wrapper via `Nonempty`.
- `Derivable Axioms φ` — derivability from empty context.
- `propDerivationSystem Axioms` — `DerivationSystem (PL.Proposition Atom)` instance connecting to generic MCS framework.
- Height measure and height properties for well-founded recursion.
- Combinators: `mp_deriv`, `weakening_deriv`, `assumption_deriv`.

**Deduction theorem** (`Metalogic/DeductionTheorem.lean`):
- `deductionTheorem` — fully proved by well-founded recursion on height.
- `deductionWithMem` — helper for eliminiation of hypothesis from the middle of context.
- `hasDeductionTheorem` — `HasDeductionTheorem` instance plugging into generic MCS.

**MCS machinery** (`Metalogic/MCS.lean`):
- Parameterized over arbitrary `Axioms` predicate.
- `prop_lindenbaum` — Lindenbaum's lemma (via generic `set_lindenbaum`).
- `prop_closed_under_derivation`, `prop_implication_property`, `prop_negation_complete`.
- Propositional-specific: `prop_mcs_bot_not_mem`, `prop_mcs_neg_of_not_mem`, `prop_mcs_not_mem_of_neg`, `prop_mcs_mem_iff_neg_not_mem`.

**Tag type instances** (`ProofSystem/Instances.lean`, `ProofSystem/IntMinInstances.lean`):
- `Propositional.HilbertCl` — full `ClassicalHilbert` instance (all 10 axioms + MP).
- `Propositional.HilbertInt` — full `IntuitionisticHilbert` instance (9 axioms + MP).
- `Propositional.HilbertMin` — full `MinimalHilbert` instance (8 axioms + MP).

**Strong completeness** (`Metalogic/StrongCompleteness.lean`):
- `prop_truth_lemma` — full structural truth lemma for MCS.
- `prop_strong_soundness`, `prop_strong_completeness`, `prop_strong_completeness_iff`.
- `prop_compactness`.
- `prop_completeness`, `prop_completeness_iff_tautology`.

**Intuitionistic and minimal completeness** (via Kripke canonical model):
- `int_strong_soundness`, `int_strong_completeness`, `int_strong_completeness_iff`, `int_compactness`, `int_completeness`, `int_soundness_completeness` (`IntStrongCompleteness.lean`).
- Corresponding minimal versions in `MinStrongCompleteness.lean`.

**CONFIDENCE**: High — fully verified, zero sorries.

---

### 2. Natural Deduction System — Status: Strong, Missing Curry-Howard

**Core system** (`NaturalDeduction/Basic.lean`):
- `Theory.Derivation` — inductive with 10 primitive constructors: ax, ass, andI, andE1, andE2, orI1, orI2, orE, impI, impE.
- Logic strength controlled by theory parameter: `MPL` (empty theory), `IPL` (adds `⊥ → A`), `CPL` (adds `¬¬A → A`).
- Context type: `Ctx Atom = Finset (Proposition Atom)` — avoids explicit contraction/exchange.
- Weakening: `Theory.Derivation.weak` — fully structural translation.
- Cut: `Theory.Derivation.cut` — proved via `impI`/`impE`.
- Cut-away (multi-premise cut): `DerivableIn.cut_away` — proved by induction on `Finset`.
- Substitution: `Theory.Derivation.subs` — substitution of derivations for hypotheses.
- Atom substitution: `Theory.Derivation.substAtom` — transport along atom substitution.
- Equivalence: `Theory.equiv`, `Theory.Equiv`, full `Equivalence` relation, congruence for all connectives.

**Derived rules** (`NaturalDeduction/DerivedRules.lean`):
- `botE` (requires `[IsIntuitionistic T]`), `negI`, `negE`, `topI`, `dne` (requires `[IsClassical T]`), `iffI`, `iffE1`, `iffE2`.

**Hilbert-ND bridge** (`NaturalDeduction/Equivalence.lean`):
- `AxiomTheory`, `HilbertAxiomTheory`.
- `MinimalAxioms` typeclass bundling 8 witnesses; instances for all three axiom sets.
- `hilbertToND` — computable structural translation.
- `ndToHilbert` — noncomputable (uses deduction theorem).
- `hilbert_iff_nd_ctx` — generic context-based equivalence (primary form).
- `hilbert_iff_nd_ctx_min`, `hilbert_iff_nd_ctx_int`, `hilbert_iff_nd_ctx_cl` — concrete corollaries.
- `hilbert_iff_nd`, `hilbert_iff_nd_min`, `hilbert_iff_nd_int`, `hilbert_iff_nd_cl` — closed-context corollaries.

**GAP — Curry-Howard / Normalization**: Entirely absent. The file header of `Basic.lean` cites [SorensenUrzyczyn2006] for the Curry-Howard isomorphism, but no type-theoretic interpretation or normalization result is present anywhere in the codebase. `Theory.Derivation` is a `Type u` (not `Prop`), making it in principle suitable for a Curry-Howard correspondence with simply-typed lambda calculus, but no such translation exists.

**GAP — ND normalization**: No normal form theorem (neither Prawitz-style normalization eliminating detours, nor cut-admissibility for the pure ND system stated in ND terms). The `cut` rule is available as a derived rule but its admissibility (existence of cut-free proofs) is not proved.

**CONFIDENCE**: High for what exists; high that Curry-Howard / normalization are entirely absent.

---

### 3. Sequent Calculus — Status: Entirely Absent (Task 279)

No LK or LJ sequent calculus exists for propositional logic. This is the scope of task 279 (not started).

The only sequent calculus in CSLib is `CLL/Basic.lean` (classical linear logic), which has:
- A well-designed two-sided sequent system with `Proof` inductive type.
- `cutFree` predicate on proofs.
- Cut elimination (`CLL/CutElimination.lean`): commented out as TODO — `Proof.cutAdm` and `Proof.cut_elim` are both skeleton stubs with no implementation.

The abstract tableau infrastructure exists in `Foundations/Logic/PropositionalTableau.lean`:
- `PropSign`, `PropSignedFormula`, `PropTableauRule`, `PropRuleResult`, `applyPropRule` — these are the 8 standard propositional tableau rules (alpha/beta) in a fully generic form.
- This is an analytic tableau framework, not a sequent calculus, but it is the closest propositional-logic proof search structure in Foundations/.

**CONFIDENCE**: High — confirmed by directory scan and file inspection.

---

### 4. Algebraic Semantics — Status: Comprehensive

**Core definitions** (`Semantics/Algebra.lean`):
- `AlgEvaluate` — generic evaluator over any `GeneralizedHeytingAlgebra`, parameterized by valuation `v : Atom → H` and `bot_val : H`.
- `AlgTValid`, `GHAValid` (MPL), `HAValid` (IPL), `BAValid` (CPL) — validity in respective algebra classes.

**Lindenbaum algebra** (`Semantics/Algebra/Lindenbaum.lean`):
- `LindenbaumAlgebra T` — quotient of `Proposition Atom` by `T`-equivalence.
- `lindenbaumMk`, `lindenbaumTop`, `lindenbaumBot` (for intuitionistic theories).
- `HeytingAlgebra` and `BooleanAlgebra` instances on `LindenbaumAlgebra` for intuitionistic/classical theories.

**Hilbert Lindenbaum algebra** (`Semantics/Algebra/HilbertLindenbaum.lean`):
- `HilbertLindenbaumAlgebra Axioms` — quotient by Hilbert equivalence.
- `hilbertLindenbaumMk_eq_top_iff` — characterizes derivability.

**ND-level algebraic completeness** (`Semantics/Algebra/Completeness.lean`):
- `Theory.canonicalV`, `Theory.canonicalV_spec` (truth lemma).
- `nd_alg_sound_aux`, `nd_alg_sound`.
- `lindenbaumMk_eq_top_iff`.
- `Theory.alg_complete` — general completeness for any theory.
- `MPL.alg_complete`, `IPL.alg_complete`, `alg_complete_classical`.

**Hilbert-level algebraic completeness** (`Semantics/Algebra/HilbertCompleteness.lean`):
- `MPL.hilbert_alg_complete`: `Derivable MinPropAxiom φ ↔ GHAValid φ`.
- `IPL.hilbert_alg_complete`: `Derivable IntPropAxiom φ ↔ HAValid φ`.
- `CPL.hilbert_alg_complete`: `Derivable PropositionalAxiom φ ↔ BAValid φ`.

**Bridges and metatheorems** (`Semantics/Algebra/HilbertConservativeGlivenko.lean`):
- `hilbertIplConservativeOverMpl` — Hilbert-primary conservative extension theorem.
- `hilbertGlivenko` — Hilbert-primary Glivenko theorem.
- `derivableInMplIffDerivableMin`, `derivableInIplIffDerivableInt`, `derivableInCplIffDerivableProp` — algebraic bridges connecting ND `DerivableIn` to Hilbert `Derivable`.
- `ipl_conservative_over_mpl`, `glivenko` — ND corollaries.

**Soundness** (`Semantics/Algebra/Soundness.lean`):
- Algebraic soundness for all three Hilbert tiers (min, int, classical).

**Bool bridge** (`Semantics/Algebra/Bridge.lean`):
- `propEvaluateEq` — Prop-valued evaluator = AlgEvaluate at `Prop`.
- `boolEvaluateEq` — Bool-valued evaluator = AlgEvaluate at `Bool`.

**CONFIDENCE**: High — fully verified, zero sorries.

---

### 5. Kripke Semantics — Status: Present for IPL/MPL, No Classical Kripke

**Core definitions** (`Semantics/Kripke.lean`):
- `KripkeModel` — bundles `World` preorder, valuation, `botForces`, upward-closure proofs.
- `IForces` — forcing relation for 5 connectives; fully standalone (does not reuse `Modal.Satisfies`).
- `iforces_persistence` — persistence (monotonicity under ≤).
- `IValid` (intuitionistic) and `MValid` (minimal) — validity in respective Kripke semantics.
- `mvalid_implies_ivalid` — minimal → intuitionistic.

**Kripke–Algebraic bridge** (`Semantics/Algebra/KripkeBridge.lean`):
- `UpsetAlgebra World` — type alias for `LowerSet (OrderDual World)`.
- `mkUpset`, `upsetVal`, `upsetBotVal`.
- `upsetHimpChar` — Heyting implication in upset algebra = Kripke forcing clause.
- `kripkeAlgBridge` — main bridge: `IForces v bf w φ ↔ toDual w ∈ AlgEvaluate (upsetVal v hv) (upsetBotVal bf hbf) φ`.
- `iValidOfHAValid` — HA-validity implies intuitionistic Kripke validity (soundness direction).
- `mValidOfGHAValid` — GHA-validity implies minimal Kripke validity.

**IPL and MPL Kripke completeness** (via canonical model in `IntStrongCompleteness.lean`, `MinStrongCompleteness.lean`):
- Both have Kripke soundness and strong completeness.
- `int_soundness_completeness`: `IValid φ ↔ Derivable IntPropAxiom φ`.

**GAP — Classical (Boolean) Kripke semantics**: No classical Kripke semantics (two-valued models, satisfaction is classical). The `Bool.lean` module provides `BoolEvaluate` (truth-table semantics), and `Tautology` is defined over `Valuation = Atom → Prop`. These are not presented as Kripke models but they are functionally equivalent.

**GAP — Completeness direction of Kripke–algebraic duality**: `KripkeBridge.lean` proves only the soundness direction (HA-validity → Kripke validity). The converse (Kripke validity → HA-validity → derivability) routes through completeness proved in `Completeness.lean` rather than through a direct Kripke → algebraic → Hilbert path. This is architecturally correct but the explicit Kripke → algebraic corollary is not stated as a standalone theorem.

**CONFIDENCE**: High for what exists; medium for what the Kripke–algebraic completeness direction explicitly names.

---

### 6. Decidability — Status: Present but Partially Disconnected

**Bool semantics** (`Semantics/Bool.lean`):
- `instDecidableBoolEvaluate` — `Decidable (Evaluate (fun a => v a = true) φ)`.
- `tautology_iff_boolEvaluate_true` — bridge lemma.
- `instDecidableTautology` — `Decidable (Tautology φ)` when `[Fintype Atom] [DecidableEq Atom]`.

**GAP — `Decidable (Derivable PropositionalAxiom φ)`**: Not stated as a `Decidable` instance. The `prop_completeness_iff_tautology` theorem gives `Tautology φ ↔ Derivable PropositionalAxiom φ`. Composing with `instDecidableTautology` would yield this instance. It is not registered.

**GAP — Intuitionistic and minimal decidability**: No decidability result for `Derivable IntPropAxiom φ` or `Derivable MinPropAxiom φ` over a finite atom type. For intuitionistic logic this requires a more sophisticated decision procedure (e.g., contraction-free sequent search). The sequent calculus (task 279) would be the vehicle for this.

**CONFIDENCE**: High.

---

## File Inventory

| File | Key Declarations | Status |
|------|------------------|--------|
| `ProofSystem/Axioms.lean` | `PropositionalAxiom`, `IntPropAxiom`, `MinPropAxiom`, subsumption theorems, witness lemmas | Complete, zero sorries |
| `ProofSystem/Derivation.lean` | `DerivationTree`, `Deriv`, `Derivable`, `propDerivationSystem`, `DerivationTree.height` | Complete, zero sorries |
| `ProofSystem/Instances.lean` | `ClassicalHilbert Propositional.HilbertCl` instance + all axiom instances | Complete |
| `ProofSystem/IntMinInstances.lean` | `IntuitionisticHilbert HilbertInt`, `MinimalHilbert HilbertMin` instances | Complete |
| `Metalogic/DeductionTheorem.lean` | `deductionTheorem`, `deductionWithMem`, `hasDeductionTheorem` | Complete |
| `Metalogic/MCS.lean` | Parameterized MCS: lindenbaum, closed_under_derivation, implication_property, negation_complete | Complete |
| `Metalogic/StrongCompleteness.lean` | Truth lemma, strong soundness/completeness, compactness, `Tautology ↔ Derivable` | Complete |
| `Metalogic/IntStrongCompleteness.lean` | IPL canonical model, soundness/completeness, `IValid ↔ Derivable IntPropAxiom` | Complete |
| `Metalogic/MinStrongCompleteness.lean` | MPL canonical model, soundness/completeness, `MValid ↔ Derivable MinPropAxiom` | Complete |
| `Metalogic/IntLindenbaum.lean` | `IntDCCS`, prime DCCS infrastructure | Complete |
| `Metalogic/MinLindenbaum.lean` | Minimal DCCS infrastructure | Complete |
| `Metalogic/IntSoundness.lean` | IPL Kripke soundness | Complete |
| `Metalogic/MinSoundness.lean` | MPL Kripke soundness | Complete |
| `Metalogic/Soundness.lean` | CPL truth-table soundness | Complete |
| `NaturalDeduction/Basic.lean` | `Theory.Derivation` (10 constructors), weakening, cut, subs, substAtom, `Theory.Equiv` | Complete |
| `NaturalDeduction/DerivedRules.lean` | botE, negI, negE, topI, dne, iffI, iffE1, iffE2 | Complete |
| `NaturalDeduction/FromHilbert.lean` | Hilbert derived rule builders | Complete |
| `NaturalDeduction/HilbertDerivedRules.lean` | Hilbert derived rules via ND | Complete |
| `NaturalDeduction/Equivalence.lean` | `hilbert_iff_nd_ctx` (generic + 3 concrete corollaries), `MinimalAxioms` | Complete |
| `Semantics/Bool.lean` | `BoolEvaluate`, `instDecidableTautology`, `tautology_iff_boolEvaluate_true` | Complete |
| `Semantics/Kripke.lean` | `IForces`, `KripkeModel`, `iforces_persistence`, `IValid`, `MValid` | Complete |
| `Semantics/SemanticConsequence.lean` | `SemanticEntails`, `SetDerivable`, `Tautology` definitions | Complete |
| `Semantics/Algebra.lean` (barrel) | Re-exports Algebra/ | Complete |
| `Semantics/Algebra/Lindenbaum.lean` | `LindenbaumAlgebra T`, HeytingAlgebra/BooleanAlgebra instances | Complete |
| `Semantics/Algebra/HilbertLindenbaum.lean` | `HilbertLindenbaumAlgebra Axioms`, `hilbertLindenbaumMk_eq_top_iff` | Complete |
| `Semantics/Algebra/Soundness.lean` | Hilbert algebraic soundness (min/int/classical) | Complete |
| `Semantics/Algebra/Completeness.lean` | ND algebraic completeness (MPL/IPL/classical), truth lemma | Complete |
| `Semantics/Algebra/HilbertCompleteness.lean` | `MPL/IPL/CPL.hilbert_alg_complete` | Complete |
| `Semantics/Algebra/HilbertConservativeGlivenko.lean` | Conservative extension, Glivenko, algebraic bridges | Complete |
| `Semantics/Algebra/Bridge.lean` | `propEvaluateEq`, `boolEvaluateEq` | Complete |
| `Semantics/Algebra/KripkeBridge.lean` | `kripkeAlgBridge`, `iValidOfHAValid`, `mValidOfGHAValid`, `UpsetAlgebra` | Complete |
| `Semantics/Algebra/Conservative.lean` | Bot-freeness (IsBotFree, coe_AlgEvaluate) | Complete |
| `Semantics/Algebra/Glivenko.lean` | `glivenko_algebraic` | Complete |
| `Foundations/Logic/PropositionalTableau.lean` | Abstract tableau: PropSign, PropSignedFormula, PropTableauRule, applyPropRule | Complete (no proofs, pure defs) |
| `LinearLogic/CLL/CutElimination.lean` | `CutFreeProof`, `Proof.cutAdm` (stub), `Proof.cut_elim` (stub) | Incomplete — two proofs are TODO stubs |

---

## Gaps Identified

### Gap A: Sequent Calculus Entirely Absent (Task 279 Scope)

**What's missing**: Any LK (classical two-sided) or LJ (intuitionistic) sequent calculus for propositional logic.

**What task 279 will deliver**: The sequent system itself. This is appropriately scoped.

**What remains after task 279**: 
- Cut elimination completeness witness (a decision procedure for derivability via contraction-free sequent search)
- `Decidable (Derivable IntPropAxiom φ)` via the cut-free sequent calculus (since cut-elimination + finite search = decidability)
- Hilbert–sequent bridge (sequent calculus sound/complete w.r.t. Hilbert)
- LK–ND bridge (sequent calculus ↔ natural deduction for classical logic)
- LJ–ND bridge (sequent calculus ↔ natural deduction for intuitionistic logic)

### Gap B: Curry-Howard Correspondence Entirely Absent

**What's missing**: No type-theoretic interpretation of `Theory.Derivation`. Specifically:
- No simply-typed lambda calculus (STLC) or minimal type theory corresponding to MPL/IPL derivations.
- No normalization theorem (confluence or strong normalization for derivation reduction).
- No terms-as-proofs, types-as-propositions mapping.
- The citation to [SorensenUrzyczyn2006] in `Basic.lean` is aspirational, not realized.

**What would be needed**:
- A `Term Atom` type (variables, abstraction, application, pairs, projections, injections, case).
- A `HasType` judgment or just a computable function assigning types to terms.
- `reduceOne` or `beta` reduction steps.
- Strong normalization theorem (or at least the type-theoretic interpretation).

**Scope note**: This is a significant standalone project, not a missing corollary. It would likely require 200-400 lines of new Lean code.

### Gap C: `Decidable (Derivable PropositionalAxiom φ)` Not Registered as Instance

**What exists**: `instDecidableTautology [Fintype Atom] [DecidableEq Atom]` and `prop_completeness_iff_tautology`.

**What's missing**: A registered `Decidable (Derivable PropositionalAxiom φ)` instance that composes these.

**Effort**: Small — a one-liner `Decidable` instance using `decidable_of_iff _ prop_completeness_iff_tautology.symm`. Requires `[Fintype Atom] [DecidableEq Atom]`.

**Note**: This may overlap with task 266 ("assemble a `Decidable (Tautology φ)` instance" — but `instDecidableTautology` already exists). Task 266 should verify whether the Hilbert-level `Decidable (Derivable PropositionalAxiom φ)` instance is also expected.

### Gap D: Missing Bridge Corollaries at Top Level

**What exists**: All metatheorems are proved but some are not surfaced through the `ProofSystem.lean` documentation index or exposed as corollaries using the tag types.

**Specifically**: 
- No theorem of the form `InferenceSystem.DerivableIn Propositional.HilbertCl φ ↔ GHAValid φ` (Hilbert completeness stated via tag type rather than via `Derivable PropositionalAxiom φ`).
- This matters for downstream modal logics that want to instantiate completeness via tag types.

**Effort**: Small — one-liner corollaries composing existing theorems with instance unfolding.

### Gap E: CLL Cut Elimination (Non-Propositional, for Reference)

`LinearLogic/CLL/CutElimination.lean` has two stub definitions (`Proof.cutAdm`, `Proof.cut_elim`) marked as TODO. This is not in scope for propositional logic but is the only existing sequent calculus in CSLib with actual proof rules, and its incompleteness is relevant as a template reference.

### Gap F: No `Derivable (IntPropAxiom / MinPropAxiom)` Decidability

Intuitionistic and minimal propositional logic are decidable (by the finite-model property or sequent calculus), but CSLib has no decision procedure for either. The sequent calculus in task 279 would be the natural foundation for an intuitionistic decidability proof.

### Gap G: Kripke–Algebraic Completeness Direction Unnamed

`KripkeBridge.lean` proves `iValidOfHAValid` (soundness direction only). The converse — "Kripke validity implies HA-validity" — routes through Lindenbaum completeness but is not stated as a standalone theorem `haValidOfIValid`.

---

## Confidence Levels

| Finding | Confidence | Basis |
|---------|------------|-------|
| Hilbert system complete (axioms, derivation, MCS, completeness) | High | Direct file reading, zero sorries |
| ND system complete (10-constructor inductive, cut, subs, bridges) | High | Direct file reading, zero sorries |
| Hilbert–ND bridge complete for all 3 tiers | High | `Equivalence.lean` read in full |
| Algebraic semantics comprehensive (MPL/IPL/CPL alg completeness) | High | All Algebra/ files read |
| Kripke semantics present for IPL/MPL only | High | `Kripke.lean` and `KripkeBridge.lean` read |
| Sequent calculus entirely absent | High | Directory scan confirmed; CLL stubs only |
| No Curry-Howard correspondence | High | Grep for Curry-Howard returned only citation; no STLC defined |
| `instDecidableTautology` exists | High | `Bool.lean` read in full |
| `Decidable (Derivable PropositionalAxiom φ)` absent | High | No such instance found by grep |
| CLL cut elimination is a stub | High | `CutElimination.lean` read |
| Tag-type-based completeness corollaries not stated | Medium | Only partial documentation scan; may be in barrel files not read |

---

## Task 266 Overlap Analysis

Task 266 (implementing) covers:
- Hilbert-ND bridge algebraic completeness corollaries (**now done** — `HilbertConservativeGlivenko.lean` proves these)
- Stale `ProofSystem.lean` documentation (**Phase 1 of 266 plan, marked COMPLETED**)
- Propositional test coverage (**Phase 6 of 266 plan, not yet executed**)
- ProofSystem tag instances for modal/temporal/bimodal (**completed by tasks 281-285**)
- Propositional tableau extraction to Foundations/ (**Phase 3 of 266 plan, not yet executed**)
- `HasDia` primitive (**Phase 2 of 266 plan, not yet executed**)
- `Decidable (Tautology φ)` — **already exists** as `instDecidableTautology` in `Bool.lean`. Task 266 plan's Phase 4 goal appears to already be accomplished.

**Key finding**: The task 266 plan's Phase 4 ("Create `Decidable (Tautology φ)` instance using BoolEvaluate and Fintype enumeration") is already accomplished. What remains is the Hilbert-derivability version (`Decidable (Derivable PropositionalAxiom φ)`) — a one-liner using `prop_completeness_iff_tautology.symm`.

## Task 279 Overlap Analysis

Task 279 (not started) is the entire scope of Gap A above — it introduces LK/LJ from scratch. Any new task created by task 280 that relates to sequent calculus must list task 279 as a prerequisite.
