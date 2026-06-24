# Teammate B Findings: Inter-System Connections and Bridge Theorems

**Focus**: Relationships BETWEEN proof systems — bridge theorems, translations, semantic layer, unique capabilities, in-progress work.

---

## Key Findings

### 1. The Three Proof Systems (Clarification)

The task description mentions "Hilbert, Natural Deduction, Sequent Calculus." In the actual CSLib codebase for `Cslib.Logics.Propositional`, there are exactly **two** proof systems for propositional logic:

- **Natural Deduction** (`NaturalDeduction/Basic.lean`): `Theory.Derivation`, 10 constructors, `Finset`-based context. This is the primary computational system.
- **Hilbert System** (`ProofSystem/`): `DerivationTree Axioms Γ φ`, axiom schemata (`MinPropAxiom` / `IntPropAxiom` / `PropositionalAxiom`), `List`-based context.

There is **no standalone Sequent Calculus** for propositional logic in `Cslib.Logics.Propositional/`. The only sequent calculus in CSLib is for **Linear Logic** (`Cslib.Logics.LinearLogic.CLL`), which is a completely separate logic.

The ND system _is_ "sequent style" (each rule carries explicit context), but it is not a Gentzen LK/LJ system in the traditional sense.

### 2. Core Bridge: Hilbert ↔ ND Equivalence

**File**: `NaturalDeduction/Equivalence.lean`

This is the main inter-system bridge. It proves extensional equivalence between the two proof systems for all three logic strengths (minimal/intuitionistic/classical):

**Translations**:
- `hilbertToND`: structural, computable — maps each `DerivationTree` constructor to its ND counterpart; context bridge via `List.toFinset`.
- `ndToHilbert`: uses `noncomputable` deduction theorem + `MinimalAxioms` typeclass; the key `orE` case requires the deduction theorem twice.

**Typeclass pattern** (`MinimalAxioms`): Bundles 8 axiom witnesses (K, S, andI, andE1, andE2, orI1, orI2, orE). Instances provided for all three axiom tiers. This lets the equivalence theorems be stated once and instantiated three times.

**Primary theorem** (`hilbert_iff_nd_ctx`):
```lean
theorem hilbert_iff_nd_ctx [MinimalAxioms Axioms] {Γ : Ctx Atom} {φ : PL.Proposition Atom} :
    Deriv Axioms Γ.toList φ ↔ DerivableIn (AxiomTheory Axioms) (Γ ⊢ φ)
```

**Six named corollaries** (closed-context and context-based forms) for MPL, IPL, CPL:
- `hilbert_iff_nd_min`, `hilbert_iff_nd_int`, `hilbert_iff_nd_cl`
- `hilbert_iff_nd_ctx_min`, `hilbert_iff_nd_ctx_int`, `hilbert_iff_nd_ctx_cl`

**Context representation difference**: Hilbert uses `List` (allows duplicates/order), ND uses `Finset` (unordered, no duplicates). The bridge lemma `Finset.toList_toFinset` is the key glue. This is a genuine architectural difference, not a bug.

### 3. ND-as-Hilbert-Wrapper Layer

**File**: `NaturalDeduction/FromHilbert.lean`

A complementary layer: ND-flavored **names** (`impI`, `impE`, `botE`, `assume`, `axiomRule`) as thin wrappers around `DerivationTree`. This gives users the familiar Gentzen-style interface while retaining the Hilbert infrastructure underneath. Also provides:
- `hilbertCut`: cut rule derived from deduction theorem + MP (needs K + S witnesses)
- `hilbertWeakening`: direct wrapper
- `hilbertSubstitution`: transport derivation along atom substitution

### 4. Algebraic Semantic Layer (The Hub)

**Files**: `Semantics/Algebra/`, specifically `HilbertCompleteness.lean`, `Completeness.lean`, `HilbertConservativeGlivenko.lean`

The algebraic layer is the **common semantic hub** connecting all three proof systems to each other and to Kripke semantics. Three algebra tiers:

| Logic | Algebra class | Hilbert completeness | ND completeness |
|-------|--------------|---------------------|-----------------|
| MPL | `GeneralizedHeytingAlgebra` | `MPL.hilbert_alg_complete` | `MPL.alg_complete` |
| IPL | `HeytingAlgebra` | `IPL.hilbert_alg_complete` | `IPL.alg_complete` |
| CPL | `BooleanAlgebra` | `CPL.hilbert_alg_complete` | `alg_complete_classical` |

**Algebraic bridges** (ND ↔ Hilbert via algebra):
```lean
-- MPL bridge
theorem derivableInMplIffDerivableMin : DerivableIn (∅ : Theory Atom) φ ↔ Derivable MinPropAxiom φ
-- IPL bridge
theorem derivableInIplIffDerivableInt : DerivableIn IPL φ ↔ Derivable IntPropAxiom φ
-- CPL bridge
theorem derivableInCplIffDerivableProp : DerivableIn (IPL ∪ CPL) φ ↔ Derivable PropositionalAxiom φ
```

These three bridge theorems route through both the ND and Hilbert Lindenbaum algebras as the common intermediate, enabling proof-theoretic results to move between systems via semantics.

### 5. Glivenko Theorem: IPL → CPL Relationship

**Files**: `Semantics/Algebra/Glivenko.lean`, `Semantics/Algebra/HilbertConservativeGlivenko.lean`

Glivenko's theorem formalizes how classical derivability relates to intuitionistic derivability:

- **Hilbert-primary** `hilbertGlivenko`: If `Derivable PropositionalAxiom φ` then `Derivable IntPropAxiom (¬¬φ)`.
- **ND corollary** `glivenko`: If `DerivableIn (IPL ∪ CPL) A` then `DerivableIn IPL (¬¬A)`.

Proof strategy: routes through algebraic validity using the **regular elements** of a Heyting algebra (`Heyting.Regular H`, a Boolean algebra via `instBooleanAlgebra`). The embedding lemma `eval_regular_val` is the core: `(evalR v A).val = (AlgEvaluate v ⊥ A)ᶜᶜ`.

### 6. Conservative Extension: MPL ≤ IPL for Bot-Free Formulas

**File**: `Semantics/Algebra/HilbertConservativeGlivenko.lean`

The conservative extension theorem (`hilbertIplConservativeOverMpl`, ND corollary `ipl_conservative_over_mpl`):

If `φ.IsBotFree = true` and IPL derives `φ`, then MPL also derives `φ`.

Proof strategy: uses the `WithBot G` construction — adjoining a fresh bottom to any `GeneralizedHeytingAlgebra G` yields a `HeytingAlgebra`. Bot-free formulas "do not see" the fresh bottom (`coe_AlgEvaluate` lemma). This lets validity in IPL be witnessed by evaluation in `WithBot G`, which reduces to validity in `G` (i.e., GHAValid, i.e., MPL).

### 7. Kripke–Algebraic Bridge

**File**: `Semantics/Algebra/KripkeBridge.lean`

Connects the algebraic semantics to Kripke semantics:

- `kripkeAlgBridge`: `IForces v bf w φ ↔ toDual w ∈ AlgEvaluate (upsetVal v hv) (upsetBotVal bf hbf) φ`
- Uses `UpsetAlgebra World = LowerSet (OrderDual World)`, which inherits `HeytingAlgebra` from Mathlib's `LowerSet` completions.
- `iValidOfHAValid`: HA-validity implies IValid (semantic soundness, algebraic → Kripke direction).
- `mValidOfGHAValid`: GHA-validity implies MValid.

The converse direction (Kripke → algebraic) goes through the derivability route (soundness/completeness chain).

### 8. Bool Evaluator as Algebraic Instance

**File**: `Semantics/Algebra/Bridge.lean`

Both `Evaluate` (Prop-valued, for classical completeness) and `BoolEvaluate` (Bool-valued, for decidability) are instances of `AlgEvaluate`:
- `propEvaluateEq`: `Evaluate v φ ↔ AlgEvaluate (fun a => v a) False φ` (Prop as HeytingAlgebra)
- `boolEvaluateEq`: `BoolEvaluate v φ = AlgEvaluate (fun a => v a) false φ` (Bool as BooleanAlgebra)

This unifies the semantic hierarchy under the algebraic framework.

### 9. Axiom Subsumption Chain (Proof-Theoretic Hierarchy)

**File**: `ProofSystem/Axioms.lean`

Explicit subsumption theorems encode the MPL ≤ IPL ≤ CPL hierarchy:
- `MinPropAxiom.toIntPropAxiom`: MPL axioms are IPL axioms
- `IntPropAxiom.toPropAxiom`: IPL axioms are CPL axioms

This gives a direct proof-theoretic weakening that does NOT require the algebraic route.

### 10. Decidability via Algebraic Completeness

**File**: `Metalogic/StrongCompleteness.lean`

The CPL system achieves decidability via:
```lean
instance instDecidableDerivablePropositionalAxiom [Fintype Atom] [DecidableEq Atom]
    (phi : PL.Proposition Atom) : Decidable (Derivable PropositionalAxiom phi) :=
  decidable_of_iff (Tautology phi) prop_completeness_iff_tautology
```

This reduces CPL derivability to tautology-checking (enumerating all Bool valuations), which is decidable for `Fintype Atom`. Neither MPL nor IPL has a corresponding decidability instance (undecidable in general for infinite atoms; minimal and intuitionistic logic over infinite signatures are not decidable by Boolean valuation checking).

### 11. What Is IN PROGRESS or TODO

- **CLL Cut Elimination** (`Cslib/Logics/LinearLogic/CLL/CutElimination.lean`): Two `-- TODO` stubs:
  - `Proof.cutAdm` (cut admissibility) — commented out
  - `Proof.cut_elim` (cut elimination) — commented out
  These are the only TODO/sorry markers in any sequent-style proof system in CSLib. The basic `CutFreeProof` type is defined but the main theorems are unimplemented.
- **Zero sorry markers** in `Cslib.Logics.Propositional`. The entire propositional logic development (Hilbert + ND + algebraic + Kripke) is complete.

---

## Recommended Approach

For the Zulip comment, the architecture should be described accurately:

1. **Correct the framing**: CSLib's propositional logic has Hilbert and ND systems (not "Hilbert, ND, Sequent Calculus"). The ND system uses sequent-style notation (`Γ ⊢ A`) but is a standard ND inductive, not an LK/LJ sequent calculus. The only sequent calculus in CSLib is for Linear Logic (CLL), not propositional logic.

2. **Lead with the architectural insight**: The two systems (Hilbert + ND) are extensionally equivalent via `hilbert_iff_nd_ctx`, with the algebraic layer serving as the semantic hub connecting both to each other and to Kripke semantics.

3. **Highlight the three-tier logic hierarchy** (MPL/IPL/CPL) as the unifying thread — each tier has both Hilbert and ND formulations, with algebraic bridges connecting them.

4. **Bridge theorems as the story**: The Glivenko theorem and conservative extension theorem show what CSLib has PROVEN about the relationships between the three logic tiers, not just that the systems exist.

5. **Unique capabilities per system**:
   - **Hilbert system**: Algebraic completeness is proved Hilbert-primary; Lindenbaum algebra construction works directly on `DerivationTree`. Deduction theorem enables the ND-to-Hilbert translation.
   - **ND system**: Computable `hilbertToND` translation (no noncomputable needed); natural cut rule (`Theory.Derivation.cut`) from `impI`/`impE`; finset contexts avoid explicit contraction/exchange.
   - **Algebraic layer**: The hub enabling inter-system bridging, Glivenko, conservative extension, and the Kripke–algebraic duality. Also enables decidability (`instDecidableDerivablePropositionalAxiom`).

---

## Evidence/Examples

Key theorems serving as cross-system bridges (all in `Cslib.Logics.Propositional`):

```
NaturalDeduction/Equivalence.lean:
  hilbert_iff_nd_ctx       -- Hilbert ↔ ND (primary, context form)
  hilbert_iff_nd_cl        -- CPL closed-context equivalence
  hilbert_iff_nd_int       -- IPL closed-context equivalence
  hilbert_iff_nd_min       -- MPL closed-context equivalence

Semantics/Algebra/HilbertConservativeGlivenko.lean:
  hilbertGlivenko          -- CPL → IPL for ¬¬φ (Hilbert-primary)
  glivenko                 -- CPL → IPL for ¬¬A (ND corollary)
  hilbertIplConservativeOverMpl  -- IPL conservative over MPL (bot-free)
  ipl_conservative_over_mpl     -- ND corollary
  derivableInMplIffDerivableMin  -- ND ↔ Hilbert for MPL
  derivableInIplIffDerivableInt  -- ND ↔ Hilbert for IPL
  derivableInCplIffDerivableProp -- ND ↔ Hilbert for CPL

Semantics/Algebra/KripkeBridge.lean:
  kripkeAlgBridge          -- Kripke forcing ↔ algebraic evaluation
  iValidOfHAValid          -- HA-validity → Kripke validity

Metalogic/StrongCompleteness.lean:
  instDecidableDerivablePropositionalAxiom  -- Decidability (CPL only)
```

---

## Confidence Level

**High** for all structural findings about the bridge theorems and inter-system relationships — these are directly read from the Lean source with verified file paths.

**High** for the absence of a Sequent Calculus for propositional logic — exhaustive directory scan confirms no such module exists.

**High** for the zero-sorry status of propositional logic — grep confirms no sorry markers.

**High** for the CLL cut elimination being TODO — directly confirmed from `CutElimination.lean`.
