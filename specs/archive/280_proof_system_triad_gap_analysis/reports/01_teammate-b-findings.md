# Teammate B Findings: Alternative Approaches — Gap Analysis and Task Proposals

- **Task**: 280 - Proof System Triad Gap Analysis
- **Angle**: Alternative Approaches — identifying gaps NOT covered by tasks 266 and 279
- **Date**: 2026-06-23
- **Author**: Teammate B

---

## Audit Summary: What Exists

Before identifying gaps, here is a precise accounting of what CSLib already has for propositional
logic proof systems (as of task 266 completion):

### Hilbert System (ProofSystem/)

| Component | Status | Location |
|-----------|--------|----------|
| Parameterized `DerivationTree` (MPL/IPL/CPL) | Exists | `ProofSystem/Derivation.lean` |
| `Derivable`, `Deriv`, `propDerivationSystem` | Exists | `ProofSystem/Derivation.lean` |
| Axiom predicates `MinPropAxiom`, `IntPropAxiom`, `PropositionalAxiom` | Exists | `ProofSystem/Axioms.lean` |
| `Decidable (Tautology φ)` instance (via `BoolEvaluate` + `Fintype Atom`) | Exists (task 266) | `Semantics/Bool.lean` |
| `propDerivationSystem` instances for MPL/IPL/CPL | Exists | `ProofSystem/Instances.lean` |
| Deduction theorem | Exists | `Metalogic/DeductionTheorem.lean` |

### Natural Deduction System (NaturalDeduction/)

| Component | Status | Location |
|-----------|--------|----------|
| `Theory.Derivation` with `Finset` contexts, 10 constructors | Exists | `NaturalDeduction/Basic.lean` |
| Weakening, cut, cut_away, subs | Exists | `NaturalDeduction/Basic.lean` |
| `substAtom` (atom substitution transport) | Exists | `NaturalDeduction/Basic.lean` |
| `Theory.Equiv`, congruence lemmas (imp, and, or) | Exists | `NaturalDeduction/Basic.lean` |
| Derived rules: `botE`, `negI`/`negE`, `dne`, `iffI`/`iffE1`/`iffE2`, `topI` | Exists | `NaturalDeduction/DerivedRules.lean` |
| `hilbert_iff_nd` (MPL, IPL, CPL + context forms) | Exists | `NaturalDeduction/Equivalence.lean` |
| `hilbertToND`, `ndToHilbert` structural translations | Exists | `NaturalDeduction/Equivalence.lean` |
| `MinimalAxioms` typeclass + instances for MPL/IPL/CPL | Exists | `NaturalDeduction/Equivalence.lean` |
| HilbertDerivedRules (AndI/E, OrI/E Hilbert helpers) | Exists | `NaturalDeduction/HilbertDerivedRules.lean` |
| FromHilbert module | Exists | `NaturalDeduction/FromHilbert.lean` |

### Algebraic Semantics

| Component | Status | Location |
|-----------|--------|----------|
| Generic `AlgEvaluate` over `GeneralizedHeytingAlgebra` | Exists | `Semantics/Algebra.lean` |
| `GHAValid`, `HAValid`, `BAValid` | Exists | `Semantics/Algebra.lean` |
| ND algebraic soundness (`nd_alg_sound`) | Exists | `Semantics/Algebra/Completeness.lean` |
| ND algebraic completeness (`Theory.alg_complete`, MPL, IPL, CPL variants) | Exists | `Semantics/Algebra/Completeness.lean` |
| Hilbert Lindenbaum algebra | Exists | `Semantics/Algebra/HilbertLindenbaum.lean` |
| ND Lindenbaum algebra | Exists | `Semantics/Algebra/Lindenbaum.lean` |
| Hilbert algebraic completeness (MPL/IPL/CPL) | Exists | `Semantics/Algebra/HilbertCompleteness.lean` |
| Algebraic Glivenko (`glivenko_algebraic`) | Exists | `Semantics/Algebra/Glivenko.lean` |
| Conservative extension (IPL over MPL) for bot-free formulas | Exists | `Semantics/Algebra/HilbertConservativeGlivenko.lean` |
| Algebraic-Hilbert bridges (`derivableInMplIff...` etc.) | Exists | `Semantics/Algebra/HilbertConservativeGlivenko.lean` |
| Kripke–algebraic bridge (`kripkeAlgBridge`, `iValidOfHAValid`, `mValidOfGHAValid`) | Exists | `Semantics/Algebra/KripkeBridge.lean` |

### Kripke Semantics

| Component | Status | Location |
|-----------|--------|----------|
| `KripkeModel`, `IForces`, `iforces_persistence` | Exists | `Semantics/Kripke.lean` |
| `IValid`, `MValid` | Exists | `Semantics/Kripke.lean` |
| Hilbert Kripke soundness (MPL, IPL) | Exists | `Metalogic/IntSoundness.lean`, `MinSoundness.lean` |
| Hilbert Kripke completeness (MPL, IPL) | Exists | `Metalogic/IntStrongCompleteness.lean`, `MinStrongCompleteness.lean` |
| `IValid φ ↔ Derivable IntPropAxiom φ` | Exists | `Metalogic/IntStrongCompleteness.lean` |
| `MValid φ ↔ Derivable MinPropAxiom φ` | Exists | `Metalogic/MinStrongCompleteness.lean` |
| Classical (CPL) soundness and strong completeness via MCS | Exists | `Metalogic/StrongCompleteness.lean` |
| `Tautology φ ↔ Derivable PropositionalAxiom φ` | Exists | `Metalogic/StrongCompleteness.lean` |
| MCS framework for propositional logic | Exists | `Metalogic/MCS.lean` |

### Already Planned (Tasks 266 and 279)

Task 266 (implementing) covers:
- Hilbert-ND bridge composition with algebraic completeness (corollaries)
- `HasDia` primitive, `Decidable (Tautology φ)` — both already done by task 266
- Propositional tableau extraction, ProofSystem documentation
- GenericMCS bridge scoping

Task 279 (not started, depends on 280) covers:
- LK and LJ sequent calculus with `Finset`-based antecedents/succedents
- Cut elimination (Hauptsatz) for both LK and LJ
- Soundness and completeness for LK/LJ
- `hilbert_iff_lk`, `nd_iff_lk` bridges

---

## Key Findings: Gaps Organized by Proof System

### Gap Area 1: Natural Deduction — Proof Theory and Curry-Howard

The ND system (`Theory.Derivation`) is well-developed as a proof-combinatorial object (weakening,
cut, substitution, translation to/from Hilbert). However, it is missing its **proof-theoretic**
metatheory entirely. Specifically:

**Gap 1A: ND Normalization Theorem (Prawitz)**

There is no normalization theorem for `Theory.Derivation`. Prawitz's result states that every
ND derivation in IPL or MPL can be transformed into a normal form where no detour exists (no
`impI` immediately followed by `impE` on the same formula). The `NaturalDeduction/Basic.lean`
module docstring references Prawitz [Prawitz1965] but only for the system design, not for a
normalization theorem.

No `isNormal`, `normalize`, or strong normalization result appears anywhere in the propositional
ND modules. A normal derivation would be defined as one having no maximal formula (a formula that
is both the conclusion of an introduction rule and the major premise of an elimination rule).

**Gap 1B: Curry-Howard Correspondence**

CSLib has a full STLC implementation (`Languages/LambdaCalculus/LocallyNameless/Stlc/`) with
strong normalization for STLC. However, there is **no formal link** between:
- `Theory.Derivation Γ A` (ND proof objects for propositional logic)
- `Typing Γ t τ` (STLC typing judgments)

The Curry-Howard isomorphism for IPL states that ND proofs of `A` from `Γ` correspond
bijectively to STLC terms of type `A` in context `Γ`, where formulas are types. This
correspondence maps:
- `impI` to lambda abstraction
- `impE` to application
- `andI` to pairing
- `andE1`/`andE2` to projections
- `orI1`/`orI2` to injections
- `orE` to case analysis
- `ass` to variable reference
- `ax` to a distinguished constant

None of these correspondences are formalized. CSLib references [SorensenUrzyczyn2006] in the
`Basic.lean` header (acknowledging the design decision about `botE`) but does not formalize
the isomorphism.

**Gap 1C: ND Completeness Independent of Hilbert Bridge**

ND completeness (for MPL/IPL/CPL) currently flows through the Hilbert system: the algebraic
bridges `derivableInMplIffDerivableMin` etc. connect ND derivability to Hilbert derivability,
and Hilbert algebraic completeness is then applied. There is no direct proof that
`DerivableIn T A ↔ GHAValid A` (for MPL) purely in ND terms — i.e., an ND-primary
completeness proof. The existing `Theory.alg_complete` is ND-primary (uses `nd_alg_sound` and
the Lindenbaum algebra `LindenbaumAlgebra T` derived from ND equivalence), so this gap is
actually already closed. No additional task needed here.

**Gap 1D: Subformula Property for Normal Proofs**

No subformula property is stated or proved for normal ND derivations. This is a corollary of
normalization: every formula in a normal ND derivation is a subformula of the conclusion or
a hypothesis. The subformula property has significant downstream consequences (interpolation,
decidability via proof search in finite search spaces).

### Gap Area 2: Proof System Equivalence Bridges

**Gap 2A: Hilbert ↔ ND — Already Covered**

`hilbert_iff_nd` (MPL, IPL, CPL; closed and context forms) all exist in
`NaturalDeduction/Equivalence.lean`. This gap is fully closed. No task needed.

**Gap 2B: Hilbert ↔ SC / ND ↔ SC — Covered by Task 279**

`hilbert_iff_lk` and `nd_iff_lk` are the deliverables of task 279.

**Gap 2C: Three-Way Equivalence Theorem**

After task 279 completes, the three-way equivalence (Hilbert ↔ ND ↔ SC) can be stated as a
single `List.TFAE` theorem via Mathlib's `TFAE` machinery. No dedicated module currently
orchestrates this. The dependency is task 279 completing first.

**Gap 2D: ND Algebraic Completeness Corollary Stated at ND Level**

`Theory.alg_complete` is the ND-primary algebraic completeness theorem and already exists. The
algebraic-Hilbert bridge theorems also exist. What is missing is a unified top-level module
collecting the ND-level corollaries:
- `nd_glivenko`: `DerivableIn (IPL ∪ CPL) A → DerivableIn IPL (¬¬A)` — is this stated at ND
  level? The Hilbert version `hilbertGlivenko` exists but the ND corollary should be verified.
- An analogous to `prop_completeness_iff_tautology` but for ND (exists via algebraic bridge).

Checking: `glivenko` (ND form) is listed as a deliverable of `HilbertConservativeGlivenko.lean`.
Need to verify it is actually stated and proved there.

### Gap Area 3: Algebraic-Side Gaps

**Gap 3A: ND-Level Glivenko and Conservative Extension Already Present**

`HilbertConservativeGlivenko.lean` lists `glivenko` and `ipl_conservative_over_mpl` as ND
corollaries derived via algebraic bridges. These appear to be present. No task needed.

**Gap 3B: Lindenbaum-Tarski Algebra — Specific Propositional Instantiations**

The Lindenbaum-Tarski algebra is built generically over `Theory Atom` (ND equivalence classes).
The concrete instances for MPL, IPL, and CPL — `LindenbaumAlgebra (∅ : Theory Atom)` is a
GHA, `LindenbaumAlgebra IPL` is a HA, `LindenbaumAlgebra (IPL ∪ CPL)` is a BA — are used
implicitly in completeness proofs but are not named or exported as standalone instances.

Downstream users who want to reason "the Lindenbaum-Tarski algebra of CPL is a Boolean algebra"
cannot reach this conclusion without tracing through the completeness proof internals. Named
instances would improve usability.

**Gap 3C: Stone Duality / Representation**

Stone's representation theorem for Boolean algebras (every Boolean algebra embeds into a power
set Boolean algebra) is not connected to CPL's Lindenbaum-Tarski algebra. Mathlib has
`Mathlib.Order.Category.BoolAlg` and the Stone space infrastructure. This would establish that
CPL's Lindenbaum algebra is "the" free Boolean algebra on the atom set, connecting to the
classical Stone duality. This is a medium/large task but is more of a mathematical enrichment
than needed for metatheoretic completeness purposes.

**Gap 3D: Algebraic Completeness for Intuitionistic Logic via Heyting Algebras — Covered**

`IPL.alg_complete` and `IPL.hilbert_alg_complete` exist. The Heyting algebra completeness is
already proved for both Hilbert and ND. The Kripke-algebraic bridge is also established. No
gap here.

### Gap Area 4: Decidability Pipeline

**Gap 4A: `Decidable (Tautology φ)` — Already Completed by Task 266**

`instDecidableTautology [Fintype Atom] [DecidableEq Atom] (φ : Proposition Atom) : Decidable (Tautology φ)` now exists in `Semantics/Bool.lean`. Done.

**Gap 4B: Decidability of IPL via Cut-Free Sequent Calculus**

Intuitionistic propositional logic (IPL) is decidable, but this is **harder to demonstrate**
than CPL. For CPL, the `BoolEvaluate` + `Fintype` approach gives a direct enumeration
algorithm. For IPL, decidability is typically established via:
1. The finite model property (Kripke models of bounded size suffice)
2. Cut-free completeness of LJ + backward proof search terminates
3. Direct tableau procedures

None of these approaches are formalized for IPL in CSLib. The `int_completeness` theorem
(`IValid φ ↔ Derivable IntPropAxiom φ`) does not give a decision procedure because `IValid`
is not computably checkable (infinite Kripke models).

After task 279 delivers LJ with cut elimination, a decidability proof for IPL via
LJ proof search becomes feasible. But a `Decidable (IValid φ)` or `Decidable (Derivable IntPropAxiom φ)` instance is not currently present and is not planned.

**Gap 4C: MPL Decidability**

Same situation as IPL. MPL (minimal propositional logic) is decidable but no decision procedure
instance exists. After task 279 (minimal sequent calculus, if included), this becomes feasible.

**Gap 4D: Connection Between Cut-Free Sequent Calculus and Decidability**

Once LJ (from task 279) has cut elimination, the standard argument is:
- LJ without cut is a backwards-chaining system
- The search space is finite and bounded by the subformulas of the sequent
- Therefore LJ proof search terminates and constitutes a decision procedure for IPL

Formalizing this argument — i.e., showing that the cut-free LJ system is a computable decision
procedure — is a gap not covered by task 279 as stated. Task 279's deliverables are cut
elimination, soundness, completeness, and bridges. It does not include a `Decidable` instance
from LJ.

---

## Proposed New Tasks

### Task P1: ND Normalization and Subformula Property [MEDIUM]

**Title**: Natural deduction normalization for propositional logic

**Description**: Formalize Prawitz-style normalization for CSLib's `Theory.Derivation` (MPL and
IPL cases). Define a `Derivation.isNormal` predicate (no maximal formula), prove existence of
a normalization function `normalize : T⇓(Γ ⊢ A) → T⇓_normal (Γ ⊢ A)`, and derive the
subformula property as a corollary: every formula appearing in a normal derivation is a
subformula of the conclusion or a member of `Γ`. The proof follows Prawitz [Prawitz1965],
Ch. IV for the implicational fragment and Ch. V for full intuitionistic ND.

**Dependencies**:
- Task 266 (NaturalDeduction/Basic.lean stable)
- No dependency on 279 (orthogonal to sequent calculus)

**Estimated Scope**: Medium (3-5 days). The inductive proof on derivation structure is
well-understood but the Lean 4 encoding requires care: `Theory.Derivation` is a `Type`
(not `Prop`), so the normalization function can be computable. The implicational fragment
alone (no `and`, `or`) would be small; full ND with disjunction requires the full permutation
reductions.

**Metatheoretic Purpose**: Curry-Howard prerequisite; subformula property enables decidability
by bounded proof search.

**Confidence**: High (well-trodden mathematical territory; STLC strong normalization already
in CSLib provides infrastructure).

---

### Task P2: Curry-Howard Correspondence for Propositional ND [LARGE]

**Title**: Curry-Howard isomorphism: ND proofs and STLC terms

**Description**: Establish the formal Curry-Howard isomorphism between `Theory.Derivation Γ A`
(propositional ND proofs) and `Typing Γ t τ` (STLC typing judgments). The correspondence maps
propositional connectives to STLC types (implication to function type, conjunction to product,
disjunction to sum) and derivation constructors to term constructors. Formalize:
1. `curry_howard_forward : T⇓(Γ ⊢ A) → Σ t, Typing (formulasToCtx Γ) t (formulaToType A)` —
   extract a well-typed term from a derivation
2. `curry_howard_backward : Typing Γ t τ → T⇓(ctxToFormulas Γ ⊢ typeToFormula τ)` —
   extract a derivation from a well-typed term
3. `curry_howard_roundtrip` — the two maps are mutually inverse (up to proof-term equality)
4. Derive: normal derivations correspond to beta-normal STLC terms, and ND normalization
   corresponds to STLC beta-reduction.

**Dependencies**:
- Task P1 (ND normalization for the roundtrip property)
- Task 266 (NaturalDeduction/Basic.lean stable)
- Existing `Languages/LambdaCalculus/LocallyNameless/Stlc/Basic.lean`

**Estimated Scope**: Large (1-2 weeks). Requires bridging two different representation styles
(ND uses `Finset` contexts, STLC uses `List`-based contexts; product and sum types need to
be added to `Stlc.Ty`; the locally-nameless representation must be related to the
context-indexed ND style).

**Note on Scope Reduction**: A simpler initial version can omit disjunction (sum types are
often omitted from basic Curry-Howard expositions) and focus on the {`→`, `∧`} fragment, which
maps directly to {arrow, product} types in STLC. This would be a medium-sized task.

**Metatheoretic Purpose**: The central purpose of the ND system. Establishes CSLib's
propositional ND as a foundation for type-theoretic developments.

**Confidence**: Medium (mathematically standard; technically complex due to representation
mismatch between ND's `Finset` contexts and STLC's list contexts).

---

### Task P3: Three-Way Proof System Equivalence (Post-279) [SMALL]

**Title**: Three-way equivalence: Hilbert ↔ ND ↔ sequent calculus for propositional logic

**Description**: After task 279 delivers `hilbert_iff_lk` and `nd_iff_lk`, create a unifying
module `Cslib/Logics/Propositional/ProofSystemEquivalence.lean` stating the three-way
equivalence as a `List.TFAE` theorem. For MPL, IPL, and CPL respectively, prove:
- `[Derivable Axioms φ, DerivableIn (AxiomTheory Axioms) (∅ ⊢ φ), LKDerivable φ].TFAE`
  (for CPL)
- `[Derivable IntPropAxiom φ, DerivableIn IPL (∅ ⊢ φ), LJDerivable φ].TFAE`
  (for IPL)
- Similarly for MPL

The bridges are all pairwise available (two from task 279, one from task 266).

**Dependencies**:
- Task 279 (hilbert_iff_lk, nd_iff_lk)
- Task 266 (hilbert_iff_nd)

**Estimated Scope**: Small (half a day once 279 completes). Composition of existing bridges.

**Metatheoretic Purpose**: Provides the definitive statement that all three proof systems are
co-extensional, enabling users to choose whichever system is most convenient for any given
argument.

**Confidence**: High (purely compositional; depends only on 279 deliverables being well-formed).

---

### Task P4: Decidability of IPL via LJ Proof Search [MEDIUM]

**Title**: Decidable IPL derivability via cut-free LJ proof search

**Description**: After task 279 delivers cut-free LJ, formalize the connection between cut
elimination and decidability. The key steps:
1. Define a bounded proof search procedure over LJ: given a sequent `Γ ⊢ A`, enumerate
   all possible last-rule applications; the search space is finite because all subformulas
   of `{Γ, A}` must appear in any cut-free proof.
2. Prove termination: the `mul` of sizes strictly decreases (standard measure), or use
   Kripke's finite model property bound.
3. Produce a `Decidable (LJDerivable (Γ ⊢ A))` instance.
4. Lift via `nd_iff_lk` to `Decidable (DerivableIn IPL (Γ ⊢ A))`.

The connection to the finite model property is: a sequent is LJ-unprovable iff there exists
a finite countermodel (by LJ completeness + cut elimination). The decision procedure searches
for one or the other.

**Dependencies**:
- Task 279 (LJ with cut elimination, nd_iff_lk bridge)

**Estimated Scope**: Medium (2-4 days). The mathematical argument is standard but the Lean
encoding of "proof search terminates" requires a well-founded measure argument.

**Metatheoretic Purpose**: IPL decidability; connects cut elimination to decidability.

**Confidence**: Medium-high (standard result; technical challenge is the well-founded
termination argument in Lean 4).

---

### Task P5: Named Lindenbaum-Tarski Algebra Instances [SMALL]

**Title**: Export named Lindenbaum-Tarski algebra instances for MPL, IPL, CPL

**Description**: Add named `abbrev` or `instance` declarations that make explicit:
- `Cslib.Logic.PL.MPLLindenbaumAlgebra Atom : GeneralizedHeytingAlgebra (...)` 
- `Cslib.Logic.PL.IPLLindenbaumAlgebra Atom : HeytingAlgebra (...)`
- `Cslib.Logic.PL.CPLLindenbaumAlgebra Atom : BooleanAlgebra (...)`

These are currently implicit in the algebraic completeness proofs but not exported as standalone
usable facts. A user who wants to "use the Lindenbaum algebra of CPL" has no named entry point.

Additionally, export a theorem:
- `CPL.lindenbaum_free_boolean`: The `CPLLindenbaumAlgebra Atom` is the free Boolean algebra
  over `Atom` — i.e., every map `Atom → B` (for `B : BooleanAlgebra`) extends uniquely to
  an algebra homomorphism `CPLLindenbaumAlgebra Atom → B`. This is a consequence of
  `CPL.hilbert_alg_complete` and the universal property of quotient algebras.

**Dependencies**:
- Task 266 (algebraic infrastructure stable)

**Estimated Scope**: Small (2-4 hours for the instance declarations; 1-2 days for the free
algebra universal property).

**Metatheoretic Purpose**: Algebraic completeness corollary; connects to free algebra theory.

**Confidence**: High for the instance declarations; Medium for the free algebra universal
property (requires verifying the universal property against Mathlib's algebra API).

---

### Task P6: Stone Representation for CPL [LARGE — OPTIONAL]

**Title**: Stone duality: CPL Lindenbaum algebra and the Stone space of atoms

**Description**: Using Mathlib's `Mathlib.Order.Category.BoolAlg` and Stone space machinery
(if available), establish that the Stone space of `CPLLindenbaumAlgebra Atom` is homeomorphic
to the Cantor space `Atom → Bool` (the product of discrete two-point spaces over the atoms).
This would connect CPL's completeness to a topological interpretation.

**Dependencies**:
- Task P5 (named algebra instances)
- Mathlib's Stone duality infrastructure (needs verification it is complete enough)

**Estimated Scope**: Large (1-2 weeks; Mathlib's Stone duality may require adaptation).

**Metatheoretic Purpose**: Mathematical enrichment; connects CPL to topology. Lower priority
than P1–P5.

**Confidence**: Low (Mathlib's Stone space machinery for Boolean algebras may not be sufficiently
developed for a direct application; would need investigation).

---

## Mathlib Reuse Opportunities

| Mathlib Component | How It Applies |
|-------------------|----------------|
| `List.TFAE` / `Mathlib.Tactic.TFAE` | Three-way equivalence theorem (Task P3) |
| `Mathlib.Order.Heyting.Regular` | Already used for Glivenko; reusable in P5 |
| `Mathlib.Order.Category.BoolAlg` | Stone duality for CPL Lindenbaum algebra (P6) |
| `Mathlib.Data.Fintype.Pi` | Already used in `instDecidableTautology` |
| `Heyting.IsRegular` | Available for algebraic results |
| `Mathlib.Tactic.ITauto` | CSLib has its own ND system; ITauto is a tactic, not a structure |
| `Languages/LambdaCalculus/.../Stlc/StrongNorm.lean` | STLC strong normalization via saturated sets — reusable pattern for ND normalization (Task P1) |
| `Mathlib.Data.List.TFAE` | Three-way equivalence packaging (Task P3) |

The STLC strong normalization proof (David Wegmann, `StrongNorm.lean`) uses saturated sets.
The same technique — logical relations / reducibility candidates — applies to ND normalization
(Task P1). The technical gap is that ND normalization concerns derivation *structure* (eliminating
detours), while STLC strong normalization concerns *evaluation* (all beta reductions terminate).
These are related by Curry-Howard but are technically distinct.

---

## Priority Assessment and Dependency Graph

```
Task P5 (Lindenbaum instances) [SMALL, independent]
Task P1 (ND normalization) [MEDIUM, independent] ──────────────────┐
Task P2 (Curry-Howard) [LARGE, needs P1] ──────────────────────────┤
Task 279 (LK/LJ) [NOT STARTED, planned] ─────────────────────────┐ │
Task P3 (three-way equiv) [SMALL, needs 279] ────────────────────┐│ │
Task P4 (IPL decidability) [MEDIUM, needs 279] ──────────────────┘│ │
Task P6 (Stone duality) [LARGE, needs P5] ─────────────────────────┘ │
                                                                       (optional)
```

**Recommended creation order**:
1. Task P5 (small, high confidence, independent) — create immediately
2. Task P1 (medium, high confidence, independent) — create immediately
3. Task P3 (small, create as blocked on 279) — create with dependency on 279
4. Task P4 (medium, create as blocked on 279) — create with dependency on 279
5. Task P2 (large, create as blocked on P1) — create with dependency on P1
6. Task P6 (large, optional, low priority) — defer until P5 done

---

## Confidence Summary

| Task | Proposal | Confidence |
|------|----------|------------|
| P1 | ND Normalization + Subformula Property | High |
| P2 | Curry-Howard Isomorphism | Medium |
| P3 | Three-Way Equivalence (post-279) | High |
| P4 | IPL Decidability via LJ | Medium-High |
| P5 | Named Lindenbaum Instances | High (instances); Medium (free algebra) |
| P6 | Stone Duality | Low |

---

## Non-Gaps (Items Investigated and Found Closed)

- `hilbert_iff_nd` (all three logics, closed and context forms): **fully present**
- ND algebraic completeness (`Theory.alg_complete`): **fully present**
- IPL Kripke completeness (`int_soundness_completeness`): **fully present**
- CPL semantic completeness (`prop_completeness_iff_tautology`): **fully present**
- `Decidable (Tautology φ)`: **done by task 266**
- Glivenko and conservative extension (ND forms): **listed as present in HilbertConservativeGlivenko.lean**
- `HasDia` primitive: **done by task 266**

The main actionable gaps are ND proof theory (normalization, Curry-Howard), the three-way
equivalence orchestration (post-279), IPL decidability via LJ (post-279), and named
Lindenbaum algebra instances.
