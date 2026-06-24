# Teammate A Findings: CSLib Propositional Logic Proof Systems

## Key Findings

### Overview

CSLib formalizes propositional logic across **two proof systems** (Hilbert and Natural Deduction), not three. There is **no sequent calculus** for propositional logic in CSLib. The ND file `Basic.lean` mentions sequent-style notation (`Γ ⊢ A`) but this is a naming convention for the ND system, not a sequent calculus. The actual sequent calculus with cut-elimination in CSLib lives in `Cslib/Logics/LinearLogic/CLL/` (Classical Linear Logic), not in the Propositional directory.

Both proof systems cover **three logic strengths**:
- **MPL** (Minimal Propositional Logic, Johansson 1937): no explosion/EFQ
- **IPL** (Intuitionistic Propositional Logic): adds EFQ (`⊥ → A`)
- **CPL** (Classical Propositional Logic): adds Peirce's law / DNE

### System 1: Hilbert-Style Proof System

**Location**: `Cslib/Logics/Propositional/ProofSystem/`

**Structure**:
- `Axioms.lean`: Three inductive axiom predicates — `MinPropAxiom` (8 axioms: K, S, ∧/∨ rules), `IntPropAxiom` (9 axioms: adds EFQ), `PropositionalAxiom` (10 axioms: adds Peirce's law). Subsumption theorems proved.
- `Derivation.lean`: Parameterized `DerivationTree Axioms Γ φ` with 4 constructors (ax, assumption, modus_ponens, weakening). `DerivationTree` is a `Type` (not `Prop`) to enable computable height for well-founded recursion. `Deriv` is the `Prop` wrapper. `propDerivationSystem` connects to the generic MCS framework.
- `Instances.lean`: Registers `InferenceSystem`, `ModusPonens`, and axiom instances for `HilbertCl`.
- `IntMinInstances.lean`: Instances for intuitionistic and minimal variants.

**Key results established**:
- `Metalogic/DeductionTheorem.lean`: **Deduction theorem** (`A :: Γ ⊢ B → Γ ⊢ A → B`) by well-founded recursion on derivation tree height. Parameterized over any axiom predicate with K and S. Four constructor cases, including `deductionWithMem` helper for the weakening case. Instance `hasDeductionTheorem` connects to generic framework.
- `Metalogic/Soundness.lean`: **Soundness** for CPL (`prop_soundness`, `prop_soundness_derivable`, `prop_soundness_tautology`). All 10 axioms verified against Boolean valuations.
- `Metalogic/StrongCompleteness.lean`: **Strong completeness** for CPL via canonical model (MCS construction). Results: `prop_strong_soundness`, `prop_strong_completeness`, `prop_strong_completeness_iff`, `prop_compactness`, `prop_completeness`, `prop_completeness_iff_tautology`. The decidability instance `instDecidableDerivablePropositionalAxiom` for finite atom types follows as a corollary.
- `Metalogic/MCS.lean`: Lindenbaum's lemma and MCS properties (`prop_lindenbaum`, consistency criteria, negation completeness).
- `Metalogic/IntStrongCompleteness.lean`: **Strong completeness for IPL** via prime DCCS Kripke canonical model (`int_strong_soundness`, `int_strong_completeness`, `int_strong_completeness_iff`, `int_compactness`, `int_completeness`, `int_soundness_completeness`).
- `Metalogic/MinStrongCompleteness.lean`: **Strong completeness for MPL** via prime MinTheory Kripke canonical model (`min_strong_soundness`, `min_strong_completeness`, `min_strong_completeness_iff`, `min_compactness`, `min_completeness`, `min_soundness_completeness`).
- `Semantics/Algebra/HilbertCompleteness.lean`: **Algebraic completeness** for all three tiers via Hilbert Lindenbaum algebra: `MPL.hilbert_alg_complete` (GHA-validity ↔ derivable), `IPL.hilbert_alg_complete` (HA-validity ↔ derivable), `CPL.hilbert_alg_complete` (BA-validity ↔ derivable).
- `Semantics/Algebra/HilbertConservativeGlivenko.lean`: **Conservative extension** (`hilbertIplConservativeOverMpl`: IPL is conservative over MPL for bot-free formulas) and **Glivenko's theorem** (`hilbertGlivenko`: CPL ⊢ φ → IPL ⊢ ¬¬φ), both proved at the Hilbert level, with ND corollaries derived via algebraic bridges.

### System 2: Natural Deduction (Standalone)

**Location**: `Cslib/Logics/Propositional/NaturalDeduction/`

**Structure**:
- `Basic.lean`: Standalone `Theory.Derivation` inductive with **10 primitive constructors**: ax, ass, andI, andE1, andE2, orI1, orI2, orE, impI, impE. Uses `Finset` contexts (avoids explicit contraction/exchange). Theory parameter controls logic strength. Authors: Thomas Waring, Benjamin Brast-McKie.
  - The Lean file explicitly notes the design trade-off: EFQ (`⊥ → A`) is a theory axiom via `[IsIntuitionistic T]`, not a primitive constructor. This enables API uniformity across the multi-logic hierarchy while preserving the ND symmetry argument.
  - Key results: `Derivation.weak` (weakening), `Derivation.cut` (cut rule), `Derivation.subs` (hypothesis substitution), `Derivation.substAtom` (atom substitution), `Theory.equiv_equivalence` (equivalence is an equivalence relation), congruence lemmas for all connectives.
- `DerivedRules.lean`: Derived rules — `botE` (needs `[IsIntuitionistic T]`), `negI`/`negE`, `topI`, `dne` (needs `[IsClassical T]`), biconditional rules `iffI`/`iffE1`/`iffE2`. All have `DerivableIn`-level wrappers.
- `FromHilbert.lean`: Hilbert-flavored wrappers with ND names (`impI`, `impE`, `botE`, `axiomRule`, `assume`, `hilbertCut`, `hilbertWeakening`) and substitution (`hilbertSubstitution`). Bridges the two systems at the tactic level.
- `HilbertDerivedRules.lean`: Hilbert implementation of ND conjunction/disjunction rules as derived operations using the axiom schemata (needed for `ndToHilbert` translation direction).
- `Equivalence.lean`: **Hilbert ↔ ND equivalence** for all three logic strengths.
  - `MinimalAxioms` typeclass bundles 8 axiom witnesses; instances for `MinPropAxiom`, `IntPropAxiom`, `PropositionalAxiom`.
  - `hilbertToND`: Structural, computable translation Hilbert → ND.
  - `ndToHilbert`: Noncomputable translation ND → Hilbert (uses deduction theorem for `impI` case).
  - Context-based: `hilbert_iff_nd_ctx` (primary generic form), plus `_min`, `_int`, `_cl` corollaries.
  - Closed-context: `hilbert_iff_nd` plus `_min`, `_int`, `_cl` corollaries.

**Key results in ND**:
- `Semantics/Algebra/Completeness.lean`: **ND algebraic completeness** for MPL (GHA), IPL (HA), CPL (BA) via Lindenbaum-Tarski algebra. Canonical valuation (`Theory.canonicalV`) and canonical bottom value.
- `Semantics/Algebra/Conservative.lean`: `IsBotFree` predicate, `GHAValid → HAValid → BAValid` subsumption, `WithBot` Heyting algebra construction.
- `Semantics/Algebra/Glivenko.lean`: Algebraic Glivenko lemma using regular elements of a Heyting algebra. `IsIntuitionistic (IPL ∪ CPL)` and `IsClassical (IPL ∪ CPL)` theory instances.
- `Semantics/Algebra/HilbertConservativeGlivenko.lean`: Algebraic bridges (`derivableInMplIffDerivableMin`, `derivableInIplIffDerivableInt`, `derivableInCplIffDerivableProp`) and ND corollaries `ipl_conservative_over_mpl`, `glivenko`.

### No Sequent Calculus for Propositional Logic

The search confirms there is no Gentzen-style sequent calculus (LK/LJ) for propositional logic in CSLib. The only references to "sequent" in the propositional files are:
1. `Defs.lean` line 42: "Layer 1 — Natural Deduction (`NaturalDeduction/Basic.lean`)" with the comment that derivation is "done in 'sequent style'" — meaning explicit hypotheses at each step, NOT a sequent calculus.
2. The notation `Γ ⊢ A` in `Basic.lean` is ND sequent notation, not LK/LJ.

CSLib's sequent calculus work lives in `Cslib/Logics/LinearLogic/CLL/CutElimination.lean` — for linear logic.

---

## Recommended Approach for the Zulip Comment

The Zulip post should:

1. **Accurately describe two proof systems** (not three): Hilbert and Natural Deduction.
2. **Note the three logic strengths** shared across both systems: MPL, IPL, CPL.
3. **Describe what each system is best suited for** based on what has actually been built:
   - **Hilbert system**: Best suited for completeness proofs (MCS/Lindenbaum constructions use it natively), algebraic correspondence, and metalogical theorems. The deduction theorem is the key technical workhorse. Computable height measure enables well-founded recursion.
   - **Natural Deduction**: Best suited for proof-theoretic analysis, derivation search, equational reasoning about propositions (via `Theory.equiv`), substitution theorems, and Curry-Howard correspondence. The `Finset` context representation avoids contraction/exchange bookkeeping. The standalone system also connects directly to the `InferenceSystem` typeclass.
   - **The bridge** (`Equivalence.lean`): Allows results from one system to transfer to the other. The Hilbert → ND direction is computable; the ND → Hilbert direction is noncomputable (uses classical deduction theorem).
4. **Mention key completed results**: strong soundness/completeness for all three tiers (both Boolean and Kripke semantics for IPL/MPL), algebraic completeness via Heyting/GHA/Boolean algebras, conservative extension (IPL over MPL for bot-free formulas), Glivenko's theorem, decidability for finite atom types.
5. **Note the design decision** in ND: EFQ as theory axiom rather than primitive constructor, documented in `Basic.lean` with discussion of the trade-off.

If the topic mentions "three proof systems," it may be referring to a planned sequent calculus. Based on the current codebase, sequent calculus for propositional logic has **not yet been formalized** in CSLib.

---

## Evidence / Examples

### Hilbert System - Strong Completeness Signature
```lean
-- prop_strong_completeness_iff (StrongCompleteness.lean, line 519)
@[simp]
theorem prop_strong_completeness_iff {Γ : Set (PL.Proposition Atom)} {φ : PL.Proposition Atom} :
    SemanticEntails Γ φ ↔ SetDerivable PropositionalAxiom Γ φ
```

### Hilbert System - Decidability Corollary
```lean
-- instDecidableDerivablePropositionalAxiom (StrongCompleteness.lean, lines 565-568)
instance instDecidableDerivablePropositionalAxiom [Fintype Atom] [DecidableEq Atom]
    (phi : PL.Proposition Atom) : Decidable (Derivable PropositionalAxiom phi) :=
  decidable_of_iff (Tautology phi) prop_completeness_iff_tautology
```

### ND System - Equivalence Bridge (Equivalence.lean, line 305)
```lean
theorem hilbert_iff_nd
    {Axioms : PL.Proposition Atom → Prop}
    [MinimalAxioms Axioms]
    {φ : PL.Proposition Atom} :
    Derivable Axioms φ ↔
    DerivableIn (AxiomTheory Axioms : Theory Atom)
      ((∅ : Ctx Atom) ⊢ φ)
```

### Conservative Extension
```lean
-- hilbertIplConservativeOverMpl (HilbertConservativeGlivenko.lean)
-- IPL is a conservative extension of MPL for bot-free formulas
-- ipl_conservative_over_mpl -- ND corollary
```

### Glivenko's Theorem
```lean
-- hilbertGlivenko (HilbertConservativeGlivenko.lean)
-- CPL derives φ → IPL derives ¬¬φ
-- glivenko -- ND corollary
```

---

## Confidence Level

**High** on all findings:
- The file structure was exhaustively enumerated and every file read for key definitions and theorems.
- The absence of a sequent calculus is confirmed by a grep over all propositional files for sequent-calculus keywords.
- The hierarchy of results (soundness, completeness, Glivenko, conservative extension, decidability) is directly read from theorem declarations and module docstrings.
- The ND design trade-off (EFQ as theory axiom) is explicitly documented in `Basic.lean`'s module header.

The only uncertainty is whether "three proof systems" in the Zulip topic description reflects a planned sequent calculus not yet started, or is simply imprecise language for the two systems plus their algebraic semantics.
