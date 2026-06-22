# Task 266: Critic Findings — Propositional/ and Foundations/ Research

- **Task**: 266 — Research Propositional and Foundations Improvements
- **Role**: CRITIC (Teammate C)
- **Date**: 2026-06-22
- **Scope**: Gaps, blind spots, unvalidated assumptions, missing research areas

---

## Key Findings (Gaps and Blind Spots)

### 1. Zero Test Coverage for Propositional Logic

**Critical finding**: There are NO test files in `CslibTests/` that import or exercise any
`Cslib.Logics.Propositional.*` module. The entire Propositional/ subtree — including Hilbert
system, Natural Deduction, all three completeness theorems, and both semantic layers — is
exercised only by compilation, not by any behavioral test. This is in contrast to LTS
(`CslibTests/LTS.lean`, `CslibTests/Bisimulation.lean`), CCS, HML, and other modules that
have explicit test files.

**Evidence**: `grep -rn "import.*Propositional" CslibTests/` returns nothing.

**Risk**: A proposal to add sequent calculus or tableau without first establishing test
infrastructure is backwards. The existing completeness results have never been explicitly
validated against example instances.

### 2. Actual Sorry Count Is Higher Than Apparent

The codebase has **two distinct** sorry locations in Propositional/, not one:

1. `Cslib/Logics/Propositional/Semantics/Algebra/Conservative.lean:99` — the
   `ipl_conservative_over_mpl` theorem, explicitly documented as "deferred."

2. `Cslib/Logics/Propositional/NaturalDeduction/Basic.lean:276` — the `subs` substitution
   function has a `TODO: this implementation is not capture avoiding.` comment. This is a
   correctness defect, not a missing theorem: the substitution used by `cut_away` may fail
   for formulas with shared subformulas in context.

**Evidence**: Line 275-276 of `NaturalDeduction/Basic.lean`:
```
/-- Substitution of a family of derivations `D` for hypotheses in the context `Γ` of `E`. TODO:
this implementation is not capture avoiding. -/
```

This is underreported: researchers may only identify the algebraic `sorry`, missing the
substitution correctness gap.

### 3. PropositionalConnectives Does Not Include HasAnd/HasOr (Task 173 Status)

**Finding**: `PropositionalConnectives` in `Foundations/Logic/Connectives.lean` only bundles
`HasBot` and `HasImp` — explicitly **not** `HasAnd` and `HasOr`. The comment at line 130 says
this is "deferred to task 173." Task 173 appears to have been TOMBSTONED (referenced in
`Cslib/Logics/Bimodal/Metalogic/Bundle/SuccRelation.lean` as "TOMBSTONE task 173; blocked on
task 37"), not completed.

**Consequence**: Any generic code parameterized over `[PropositionalConnectives F]` cannot use
conjunction or disjunction, even though `PL.Proposition` has native `and`/`or` constructors.
The typeclass hierarchy is structurally incomplete for the connective set it claims to cover.

This also means the biconditional (`iff`) is not yet formalized as a typeclass (also deferred to
task 173).

**Evidence**: `Connectives.lean` lines 129-131:
```
`HasAnd` and `HasOr` are defined as standalone atomic classes in this module.
Extending `PropositionalConnectives` to include them is deferred to task 173,
when the four concrete formula types will be updated...
```

### 4. Algebraic Completeness Has Unresolved Hilbert Bridge

`Cslib/Logics/Propositional/Semantics/Algebra/Completeness.lean` explicitly defers the
Hilbert-level corollaries (`Derivable MinPropAxiom φ ↔ GHAValid φ` and similarly for Int/Cl):

> "Hilbert-level corollaries require bridging the Hilbert axiomatic system with the natural
> deduction system. This equivalence is nontrivial and deferred."

**This is a significant gap**: the algebraic completeness result is stated for `DerivableIn`
(natural deduction `Theory.Derivation`) but NOT yet connected to `Derivable PropositionalAxiom`
(the Hilbert `DerivationTree` system). The `hilbert_iff_nd` bridge exists in
`NaturalDeduction/Equivalence.lean`, but it does NOT directly bridge to the semantic layers
via the algebraic route. Researchers should explicitly note this gap.

**Consequence**: The algebraic completeness and the Hilbert/ND equivalence exist as separate
islands; no direct `Derivable MinPropAxiom φ ↔ GHAValid φ` theorem exists yet.

### 5. `ProofSystem.lean` Tag Types Are Interface-Only — Instances Are Scattered

The `Foundations/Logic/ProofSystem.lean` file explicitly states:
> "This module defines the **interface** only. Concrete instances require derivation trees
> (not yet ported) and are future work."

**However**: `HilbertCl`, `HilbertInt`, and `HilbertMin` DO have concrete instances in
`ProofSystem/Instances.lean` and `ProofSystem/IntMinInstances.lean`. The comment in
`ProofSystem.lean` is outdated and misleading for the propositional case (though still accurate
for some modal/temporal tags). Any research report that quotes this comment as describing the
current state is propagating stale documentation.

**Partial exception**: Modal systems (HilbertK through HilbertDB) also have instances in their
respective `Instances/` files. The temporal and bimodal tags may still lack complete instances.

---

## Unvalidated Assumptions

### A. "Foundations/ Is Well-Factored"

The `Foundations/Logic/` subdirectory contains a mix of:
- Typeclass interfaces (`Connectives.lean`, `ProofSystem.lean`, `InferenceSystem.lean`)
- Concrete axiom definitions (`Axioms.lean`) 
- Generic metalogic (`Metalogic/Consistency.lean`, `GenericMCS.lean`, `ListDeduction.lean`, etc.)

**Unvalidated**: Whether the `ProofSystem.lean` typeclass hierarchy (with 20+ bundled class
definitions from `MinimalHilbert` to `BimodalTMHilbert`) is actually used in the downstream
concrete proofs or is largely decorative. The critical question is whether the generic axiom
typeclasses (`HasAxiomK`, `HasAxiomT`, etc.) are exercised by any proof in the library beyond
their own instance declarations.

**Evidence gap**: The `Foundations/Logic/ProofSystem.lean` defines `MinimalHilbert`,
`IntuitionisticHilbert`, etc., and instances exist for `HilbertCl/Int/Min`. But no upstream
theorems appear to be stated generically over `[MinimalHilbert S]` — the actual completeness
proofs use `PropositionalAxiom` directly, not through the typeclass hierarchy.

### B. "The Natural Deduction System Is Complete As-Is"

The `NaturalDeduction/Equivalence.lean` establishes Hilbert ↔ ND equivalence. But:
- The `subs` substitution is not capture-avoiding (explicitly flagged)
- There is no proof that `Derivation.subs` is even admissible in full generality

This means the substitution lemma for ND — essential for proving the deduction theorem
constructively — may be subtly incorrect.

### C. "Decidability of the Propositional Logic Already Exists"

The `Proposition` type derives `DecidableEq` and `BEq`. But there is no:
- Boolean satisfiability checker (`decide` or native algorithm)
- Normal form computation (CNF/DNF) for the Propositional fragment specifically
- Tautology checker that evaluates via `Bool.lean`

The `Semantics/Bool.lean` file exists but has not been verified to connect to any executable
procedure.

### D. "Adding Sequent Calculus Is Straightforward"

Claim: sequent calculus for PL is a natural next step. **Critical risks not yet assessed**:

1. **Context representation conflict**: The ND uses `Finset` (unordered, no duplicates);
   the Hilbert system uses `List`. A sequent calculus would need a decision: use multisets
   (Gentzen-style with structural rules), sequences, or sets. Each has different formalization
   costs for exchange, contraction, and weakening.

2. **Structural rules**: The existing ND bakes in weakening (the `Ctx` is a `Finset`),
   avoiding explicit structural rules. A Gentzen sequent calculus requires explicit structural
   rules, which creates divergence from the existing design.

3. **Cut elimination**: For CPL this is a major theorem. Without it, a sequent calculus is
   merely a second proof system (adding complexity without adding power). Cut elimination in
   Lean 4 for a classical sequent calculus with `and`, `or`, `imp` all as primitives is a
   ~500-line proof with significant case analysis.

4. **Integration with existing semantics**: Adding sequent calculus creates a third proof
   system. Connecting it to both the Hilbert system and ND — without creating circular
   dependencies — requires careful import structure.

---

## Missing Research Areas

### M1. Decidability and Decision Procedures

The `Logics/Bimodal/Metalogic/Decidability/` folder has a full tableau-based decision
procedure for the TM bimodal logic. The propositional logic has **no such infrastructure**.
Key missing pieces:
- A `decide` tactic-compatible tautology check for PL
- A verified CNF/DNF converter beyond the trivial embedding in `Bimodal/Separation/FormulaOps.lean`
- A DPLL-based SAT solver instance using the Boolean semantics
- Connection between `Semantics/Bool.lean` and an executable `isValid : Proposition Atom → Bool`

**This is the most practically important missing research area.** CSLib already has a bimodal
tableau system; the simpler propositional case is unaddressed.

### M2. Normal Forms for Propositional Logic Specifically

`Cslib/Logics/Bimodal/Metalogic/Separation/FormulaOps.lean` has trivial CNF/DNF embeddings
for the bimodal formula type. There is no corresponding CNF/DNF theory for `PL.Proposition`.
Normal forms are important for:
- Proof search efficiency
- Connection to SAT solving
- Simplification lemmas used by `simp` extensions

### M3. Curry-Howard Correspondence

The `Foundations/Logic/` module and the ND system do not establish any Curry-Howard connection.
The NaturalDeduction's `Derivation` type IS a `Type` (not `Prop`), enabling potential term
extraction — but this is not exploited. The reference to [SorensenUrzyczyn2006] in the ND file
suggests this was considered. No λ-calculus embedding exists.

### M4. Relationship to Mathlib's `Propositional` Facilities

Mathlib has its own propositional logic formalization in `Mathlib.Logic.Propositional.*` and
`Mathlib.Tactic.Tauto`. The research has not examined whether CSLib's propositional module
duplicates, extends, or conflicts with Mathlib's infrastructure. If there is overlap, this
is an argument against adding more proof systems to PL before reconciling with Mathlib.

### M5. Compactness and Its Applications

The compactness theorem is proved in `StrongCompleteness.lean` (classical) and similar for
intuitionistic. But its downstream applications — König's lemma, Ramsey theory over formulas,
ultraproduct constructions — are not developed. These would normally appear in a mature
propositional logic library.

### M6. Proof-Theoretic Strength Ordering

The library has three logics (MPL ⊆ IPL ⊆ CPL) but lacks:
- A proof that each inclusion is strict (verified countermodel witnesses)
- The relationship between Kripke semantics and these strengths is established only at the
  completeness level, not via explicit separating formulas with witnesses

---

## Approach Limitations

### L1. BimodalLogic Report 16 Tableau Is Not Propositional PL

The tableau described in
`/home/benjamin/Projects/BimodalLogic/specs/305_rabinovich_ea_formula_implementation/reports/16_witness-count-restructure.md`
is NOT a propositional logic tableau. It is part of the TM bimodal logic's decision procedure.
The report discusses:
- Witness-count induction for EA-formulas over temporal structures
- NF-to-VecEA bridges for Prior structures
- A between-zone predicate transfer problem specific to multi-variable temporal logic

**This is irrelevant to propositional PL in a dangerous way**: if researchers use it as a
reference for "what a tableau system looks like in CSLib," they will be importing complexity
far beyond what PL requires. A PL tableau (for CPL) involves only signed formula expansion
rules with no world indices, no temporal connectives, and no witness placement — it is ~20
rules vs. the bimodal's 30+ rules with temporal coherence constraints.

**Key concern**: The BimodalLogic report explicitly concludes that the K=0 sorry remains
unresolved after 16 research rounds. Using this complex infrastructure as a model for
propositional additions would introduce an unresolved foundational debt.

### L2. Sequent Calculus Addition Risks

If a sequent calculus is added to `Cslib/Logics/Propositional/`, there is a design question
about whether it lives:
(a) Under `Propositional/SequentCalculus/` as a third independent proof system
(b) Under `Foundations/Logic/` as a generic infrastructure analogous to `InferenceSystem`

Option (a) creates a third proof system without a forcing function to keep it in sync.
Option (b) requires the sequent calculus to be generic enough for modal/temporal extensions
— but Gentzen sequent calculus does not generalize smoothly to modal logics (labeled sequents
require new infrastructure).

### L3. Diamond Operator Not Formalized

The `HasBox` typeclass exists, but `HasDia` (possibility/diamond) does not. The comment in
`Axioms.lean` notes:
> "Diamond is encoded classically as `◇φ = ¬□¬φ`... Non-classical modal logics require a
> separate `HasDia` typeclass."

This means any proposed "improvements" to the Foundations that involve intuitionistic modal
logic or the propositional logic of possibility are blocked by this known gap. The research
should flag this dependency.

### L4. The Conservative Extension Sorry Has an Active Task

Task 265 (`track_conservative_lean_sorry`) is currently in `researching` status and targets
the `ipl_conservative_over_mpl` sorry. Any research into "what remains to be done" in
Propositional/ must coordinate with task 265's findings to avoid duplicated work.

---

## Scope Completeness Assessment

The task description asks about:
1. What Propositional/ and Foundations/ currently contain — partially addressable by reading files
2. Supporting roles these modules play — requires understanding downstream usage
3. What remains to be done — requires full audit
4. Comparison with BimodalLogic Report 16 tableau — needs clarification (that report is about bimodal, not PL)
5. Additions like sequent calculus — needs feasibility assessment

**Critical scope gaps**:

- **No assessment of what the generic Foundations/ MCS machinery is actually used for**.
  The `GenericMCS.lean` and `ListDeduction.lean` infrastructure is present, but research has
  not mapped which downstream proofs actually use it vs. their own concrete versions.

- **No assessment of import dependencies**. A `lake shake` analysis would reveal whether
  `Foundations/Logic/Metalogic/` is actually used by modal/temporal completeness proofs or
  whether each logic re-implements its own MCS theory independently.

- **Kripke semantics for minimal logic is new but unconnected**. The `Kripke.lean` file proves
  persistence and defines `IValid`/`MValid`, but there is no minimal logic completeness
  theorem anywhere. The `IntStrongCompleteness` only covers `IntPropAxiom`, not `MinPropAxiom`
  with Kripke semantics.

- **Algebra/KripkeBridge.lean is unidirectional**. The file proves algebraic soundness implies
  Kripke validity (one direction only). The converse (Kripke validity implies algebraic
  validity, needed for Kripke completeness) is not established in that file.

---

## Evidence and Examples

### Evidence 1: Zero tests for Propositional/
```bash
$ grep -rn "import.*Propositional" CslibTests/ --include="*.lean"
# Returns nothing
```

### Evidence 2: Non-capture-avoiding substitution
`NaturalDeduction/Basic.lean`, lines 275-276:
```lean
/-- Substitution of a family of derivations `D` for hypotheses in the context `Γ` of `E`. TODO:
this implementation is not capture avoiding. -/
def Theory.Derivation.subs {Γ Γ' Δ : Ctx Atom} {B : Proposition Atom}
    (Ds : ∀ A ∈ Γ', T⇓(Δ ⊢ A)) :
      T.Derivation Γ B → T.Derivation (Γ \ Γ' ∪ Δ) B
```

### Evidence 3: Task 173 TOMBSTONED, PropositionalConnectives incomplete
`Connectives.lean`, line 133:
```lean
class PropositionalConnectives (F : Type*) extends HasBot F, HasImp F
```
`HasAnd` and `HasOr` are NOT in `PropositionalConnectives`. Referenced ticket (173) is tombstoned.

### Evidence 4: ProofSystem.lean comment is stale
`ProofSystem.lean`, line 51:
```
This module defines the **interface** only. Concrete instances require
derivation trees (not yet ported) and are future work.
```
But `Instances.lean` and `IntMinInstances.lean` exist and register concrete instances for
HilbertCl, HilbertInt, HilbertMin. The comment contradicts the code.

### Evidence 5: Algebraic completeness does not include Hilbert bridge
`Semantics/Algebra/Completeness.lean`, lines 30-32:
```
Hilbert-level corollaries (`Derivable MinPropAxiom φ ↔ GHAValid φ`, etc.) require bridging
the Hilbert axiomatic system (`DerivationTree`/`Derivable`) with the natural deduction system
(`Theory.Derivation`/`DerivableIn`). This equivalence is nontrivial and deferred.
```

### Evidence 6: Kripke soundness but no Kripke completeness for minimal logic
`Semantics/Algebra/KripkeBridge.lean` proves `iValidOfHAValid` and `mValidOfGHAValid` but
these are soundness-only (algebraic → Kripke). No Kripke completeness theorem for MPL exists.

---

## Confidence Level

| Finding | Confidence |
|---------|-----------|
| Zero test coverage for Propositional/ | **High** — verified by grep |
| Non-capture-avoiding substitution TODO | **High** — text in source |
| PropositionalConnectives incomplete (task 173 tombstoned) | **High** — code + state.json |
| Algebraic completeness missing Hilbert bridge | **High** — explicit comment in code |
| ProofSystem.lean comment is stale | **High** — contradicted by Instances.lean |
| No decidability/decision procedure for PL | **High** — no such files exist |
| Kripke completeness for MPL missing | **High** — no such theorem found |
| BimodalLogic Report 16 tableau is not PL | **High** — report clearly states TM bimodal |
| Sequent calculus risks (import structure, cut elimination) | **Medium** — design analysis |
| GenericMCS actually used downstream | **Medium** — requires lake shake verification |
| Curry-Howard gap | **Medium** — referenced but unexplored |
