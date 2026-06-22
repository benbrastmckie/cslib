# Teammate B Findings: CSLib Propositional Logic Infrastructure Survey

**Date**: 2026-06-22
**Focus**: Alternative Approaches — broad landscape, gaps, Mathlib prior art, ecosystem patterns

---

## Key Findings

### 1. Zulip Thread Access

The Zulip thread at `https://leanprover.zulipchat.com/#narrow/channel/513188-CSLib/topic/Propositional.20Logic/near/605813681` requires authentication and cannot be fetched by an automated agent. The WebFetch tool returns only JavaScript loading errors. The thread URL is, however, cross-referenced in the codebase itself at `/home/benjamin/Projects/cslib/Cslib/Logics/Propositional/NaturalDeduction/Basic.lean` line 76, suggesting it is a living design discussion.

### 2. What CSLib Actually Has for Propositional Logic

The CSLib propositional logic infrastructure is mature and well-structured. The namespace is `Cslib.Logic.PL` and lives primarily in two locations:

**`Cslib/Logics/Propositional/`** (31 files total):
- `Defs.lean` — `Proposition`, `Theory`, `MPL`/`IPL`/`CPL`, substitution monad (`Proposition.subst`), `IsIntuitionistic`/`IsClassical` typeclasses
- `ProofSystem/Axioms.lean` — Three inductive axiom predicates: `PropositionalAxiom` (10 axioms, classical), `IntPropAxiom` (9, intuitionistic), `MinPropAxiom` (8, minimal), plus subsumption theorems
- `ProofSystem/Derivation.lean` — `DerivationTree` Hilbert-style proof trees (parameterized, 4 constructors: ax, assumption, modus_ponens, weakening)
- `ProofSystem/Instances.lean` — Registers `ClassicalHilbert` instances for `Propositional.HilbertCl` tag type
- `ProofSystem/IntMinInstances.lean` — Instances for `HilbertInt` and `HilbertMin` tags
- `NaturalDeduction/Basic.lean` — `Theory.Derivation` with 10 constructors (Finset contexts), weakening, cut, substitution, atom substitution
- `NaturalDeduction/DerivedRules.lean` — botE, negI, negE, dne, iffI, iffE1, iffE2
- `NaturalDeduction/FromHilbert.lean` — Translation Hilbert → ND
- `NaturalDeduction/HilbertDerivedRules.lean` — Hilbert system derived rules
- `NaturalDeduction/Equivalence.lean` — `hilbert_iff_nd_ctx`, `hilbert_iff_nd_ctx_min`, `hilbert_iff_nd_ctx_int`, `hilbert_iff_nd_ctx_cl`, and 4 closed-context corollaries
- `Semantics/Bool.lean` — `Valuation`, `Evaluate`, `Tautology`, `BoolValuation`, `BoolEvaluate`, bridge lemma
- `Semantics/Kripke.lean` — `KripkeModel`, `IForces`, `iforces_persistence`, `IValid`, `MValid`, `mvalid_implies_ivalid`
- `Semantics/SemanticConsequence.lean` — `SetDerivable`, `SemanticEntails`, `ISemanticEntails`, `MSemanticEntails`
- `Semantics/Algebra.lean` — `AlgEvaluate`, `GHAValid`, `HAValid`, `BAValid`, `AlgTValid`
- `Semantics/Algebra/Bridge.lean` — `UpsetAlgebra`, `kripkeAlgBridge`, `iValidOfHAValid`, `mValidOfGHAValid`
- `Semantics/Algebra/Soundness.lean` — Algebraic soundness for MPL/IPL/CPL
- `Semantics/Algebra/Completeness.lean` — Algebraic completeness theorems
- `Semantics/Algebra/Conservative.lean` — `IsBotFree`, `AlgEvaluate_botFree_independent`, `ipl_conservative_over_mpl` (one `sorry`)
- `Semantics/Algebra/KripkeBridge.lean` — Kripke–algebraic duality bridge
- `Semantics/Algebra/Lindenbaum.lean` — Lindenbaum algebra construction
- `Metalogic/MCS.lean`, `MinLindenbaum.lean`, `MinSoundness.lean`, `MinStrongCompleteness.lean` — Minimal logic MCS results
- `Metalogic/IntLindenbaum.lean`, `IntSoundness.lean`, `IntStrongCompleteness.lean` — Intuitionistic results
- `Metalogic/Soundness.lean`, `StrongCompleteness.lean`, `DeductionTheorem.lean` — Classical results

**`Cslib/Foundations/Logic/`** (shared abstractions):
- `Connectives.lean` — `HasBot`, `HasImp`, `HasAnd`, `HasOr`, `HasBox`, `HasUntil`, `HasSince`, `HasNext`; bundled: `PropositionalConnectives`, `ModalConnectives`, `TemporalConnectives`, `BimodalConnectives`, `LTLConnectives`
- `InferenceSystem.lean` — `InferenceSystem` typeclass, `DerivableIn`, `Derivable`
- `ProofSystem.lean` — `ModusPonens`, `Necessitation`, `MinimalHilbert`, `IntuitionisticHilbert`, `ClassicalHilbert`, `ModalHilbert`, ..., all the way to `BimodalTMHilbert` — a full Hilbert system typeclass hierarchy
- `Axioms.lean` — Generic formula-level axiom constructors (`ImplyK`, `ImplyS`, `EFQ`, `Peirce`, `AndI`, `AndE1`, etc.) parameterized by `HasBot`/`HasImp`/`HasAnd`/`HasOr`

### 3. Design Decision: efq as Theory Axiom (not ND Primitive)

The most distinctive design choice in the CSLib propositional ND system is that `⊥` is a primitive *constructor* of `Proposition` but ex falso quodlibet (`⊥ → A`) is NOT a primitive constructor of `Theory.Derivation`. Instead:
- MPL: `⊥` constructor exists but `efq` is absent from derivations
- IPL: `efq` enters as an axiom via `Theory.IPL` (a set of all `⊥ → A`)
- CPL: extends IPL with `¬¬A → A`

This is controlled by the `[IsIntuitionistic T]` typeclass. The `botE` derived rule in `DerivedRules.lean` requires `[IsIntuitionistic T]`.

The file `NaturalDeduction/Basic.lean` lines 54-76 contain an extensive design rationale for this choice, acknowledging that it departs from Gentzen-style presentations (Prawitz 1965, Troelstra-van Dalen) and explaining the trade-off:
- **Pro**: Single `Proposition` type shared across MPL/IPL/CPL/Modal/Temporal/Bimodal; avoids duplication of the `FromPropositional` embeddings
- **Con**: Loses constructor-rule correspondence for `⊥`

The comment notes `⊥` has 0 introduction rules and 1 elimination rule — making `efq` a theory axiom "reflects this asymmetry directly."

### 4. The One Outstanding Sorry

Only one `sorry` exists in the entire propositional logic infrastructure:

File: `/home/benjamin/Projects/cslib/Cslib/Logics/Propositional/Semantics/Algebra/Conservative.lean` line 99

```lean
theorem ipl_conservative_over_mpl {A : Proposition Atom}
    (_hBF : A.IsBotFree = true) (h : DerivableIn (IPL (Atom := Atom)) A) :
    DerivableIn (MPL (Atom := Atom)) A := by
  sorry
```

This is the Johansson conservative extension theorem: IPL is conservative over MPL for bot-free formulas. The docstring explicitly states the proof requires "Dedekind-MacNeille completion of the Lindenbaum algebra" and marks this as deferred.

### 5. What Mathlib Provides (Relevant Items)

Mathlib does NOT have a direct formalization of propositional logic at this level of specificity. What it provides that CSLib builds on:
- `GeneralizedHeytingAlgebra`, `HeytingAlgebra`, `BooleanAlgebra` (used for algebraic semantics)
- `LowerSet (OrderDual World)` with `HeytingAlgebra` instance (used for Kripke-algebraic bridge)
- `Finset` infrastructure (used for ND contexts)
- `Set.image`, `Set.range` (used for theory definitions)
- `Mathlib.Order.TypeTags` — imported in `Defs.lean`
- `Classical.propDecidable` — used noncomputably in strong completeness proofs

The `lean_leansearch` query for "propositional logic soundness completeness Hilbert axiom system" returned only `peirce`, `FirstOrder.Language.Theory.IsComplete`, and `Classical.prop_complete` — none of these are the propositional Hilbert system CSLib implements. CSLib's formalization is substantially original.

### 6. Three-Logic Hierarchy Consistency

The architecture supports three logic strengths with a single unified `Proposition` type:

| Logic | ND Theory | Hilbert Axioms | Semantic Validity | Completeness Status |
|-------|-----------|----------------|-------------------|--------------------|
| MPL (minimal) | `Theory.MPL = ∅` | `MinPropAxiom` (8) | `MValid` | Complete (via algebra) |
| IPL (intuitionistic) | `Theory.IPL = Set.range (⊥ → ·)` | `IntPropAxiom` (9) | `IValid` | Complete (Kripke + algebra) |
| CPL (classical) | `Theory.CPL = Set.range (¬¬· → ·)` | `PropositionalAxiom` (10) | `Tautology` | Complete (canonical MCS) |

All three have strong completeness results (quantifying over infinite premise sets). Weak completeness is derived as a corollary.

### 7. Notation and Typeclass Instances

`Proposition` registers three typeclass instances in `Defs.lean`:
- `PropositionalConnectives (Proposition Atom)` — for `bot` and `imp`
- `HasAnd (Proposition Atom)` — for `and`
- `HasOr (Proposition Atom)` — for `or`

Notation uses standard Unicode: `⊥ ⊤ ∧ ∨ → ↔ ¬` as scoped infix/prefix operators.

The `Connectives.lean` docstring notes that `PropositionalConnectives` was extended to include `and`/`or` as part of task 173 (referenced in the module comment as a deferred extension). This extension has since been completed, as the actual file shows `HasAnd` and `HasOr` instances registered in `Defs.lean`.

### 8. Bimodal/Modal Reuse of Propositional Infrastructure

The propositional logic is reused upstream:
- `Cslib/Logics/Modal/FromPropositional.lean` — embedding PL into Modal logic
- `Cslib/Logics/Temporal/FromPropositional.lean` — embedding PL into Temporal logic
- `Cslib/Logics/Bimodal/Embedding/PropositionalEmbedding.lean` — PL into Bimodal
- `Cslib/Foundations/Logic/Theorems/Propositional/` — generic propositional theorems shared by all logics

---

## Recommended Approach

Since the Zulip thread could not be fetched, any claim verification must be done by cross-referencing codebase evidence against claims that can be inferred from the thread context. Based on the codebase:

1. **The main architectural claims in the thread are likely accurate**: The two-layer (Hilbert + Natural Deduction) proof system with bridge equivalences is fully implemented and seems to be the subject of the thread.

2. **The design rationale file is the authoritative source**: `NaturalDeduction/Basic.lean` lines 1-88 constitute the "implementation notes" section that would be the subject of a design discussion thread.

3. **The one sorry is documented and acknowledged**: `ipl_conservative_over_mpl` in `Conservative.lean` is the only outstanding proof gap and is properly documented.

4. **Teammate A should verify specific Zulip claims** against these codebase facts. This report establishes the ground truth from the code side.

---

## Evidence/Examples

### Architecture Summary (from Defs.lean docstring)

```
Two proof systems:
- Layer 1 — Natural Deduction (NaturalDeduction/Basic.lean): Theory.Derivation inductive
  with 10 primitive constructors. Logic strength via Theory parameter.
- Layer 2 — Hilbert System (ProofSystem/): axiom predicate hierarchy 
  (MinPropAxiom / IntPropAxiom / PropositionalAxiom).
- Bridge: NaturalDeduction/Equivalence.lean establishes extensional equivalence.
  hilbert_iff_nd, hilbert_iff_nd_min, hilbert_iff_nd_int, hilbert_iff_nd_cl
  (and context-based: hilbert_iff_nd_ctx, hilbert_iff_nd_ctx_min, hilbert_iff_nd_ctx_int, 
   hilbert_iff_nd_ctx_cl)
```

### Key Theorem Names (actual, verified by file inspection)

Classical propositional logic:
- `prop_strong_soundness` — `SetDerivable PropositionalAxiom Γ φ → SemanticEntails Γ φ`
- `prop_strong_completeness` — `SemanticEntails Γ φ → SetDerivable PropositionalAxiom Γ φ`
- `prop_strong_completeness_iff` — biconditional (marked `@[simp]`)
- `prop_completeness` — `Tautology φ → Derivable PropositionalAxiom φ`
- `prop_completeness_iff_tautology` — `Tautology φ ↔ Derivable PropositionalAxiom φ` (marked `@[simp]`)
- `prop_compactness` — finite witness extraction

Intuitionistic:
- `int_strong_soundness`, `int_strong_completeness`, `int_strong_completeness_iff`
- `int_compactness`, `int_completeness`, `int_soundness_completeness`

Minimal:
- `min_strong_soundness`, `min_strong_completeness` (in MinStrongCompleteness.lean)

Bridge:
- `hilbert_iff_nd_ctx` (generic, parameterized by `[MinimalAxioms]`)
- `hilbert_iff_nd_ctx_cl` / `hilbert_iff_nd_cl` (classical instantiation)
- `hilbert_iff_nd_ctx_int` / `hilbert_iff_nd_int` (intuitionistic)
- `hilbert_iff_nd_ctx_min` / `hilbert_iff_nd_min` (minimal)

Kripke semantics:
- `iforces_persistence` — persistence under preorder
- `IValid`, `MValid` — intuitionistic and minimal validity
- `mvalid_implies_ivalid` — minimal validity implies intuitionistic validity

Algebraic:
- `kripkeAlgBridge` — IForces ↔ AlgEvaluate over UpsetAlgebra
- `iValidOfHAValid`, `mValidOfGHAValid` — algebraic soundness
- `AlgEvaluate_botFree_independent` — bot-free formulas independent of bot_val

### The Sorry (actual location)

```
/home/benjamin/Projects/cslib/Cslib/Logics/Propositional/Semantics/Algebra/Conservative.lean:99
theorem ipl_conservative_over_mpl ... := by
  sorry
```

---

## Confidence Level

- **High** for: file/directory structure, theorem names, axiom counts, one-sorry fact, design rationale
- **Medium** for: what the Zulip thread specifically claims (cannot fetch the thread)
- **Low** for: whether the Zulip thread makes specific claims that differ from what is in the code — this cannot be assessed without thread access

The Zulip thread URL is referenced in `NaturalDeduction/Basic.lean` as a citation for the design discussion about `efq`. This suggests the thread's main topic is the `⊥`-as-primitive vs `efq`-as-primitive design debate, and the codebase documentation explicitly addresses this as a deliberate design trade-off.
