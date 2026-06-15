# Teammate D (Horizons): Strategic Analysis of Temporal/Modal Refactoring

## Key Findings

### 1. CSLib's Logic Library is Architecturally Significant and Growing

CSLib currently contains six logic systems at different maturity levels:

| Logic | Directory | Maturity | Metalogic |
|-------|-----------|----------|-----------|
| Propositional (PL) | `Logics/Propositional/` | High | Min/Int/Cl completeness, NaturalDeduction, 3 Hilbert systems |
| Modal | `Logics/Modal/` | High | DeductionThm, MCS, Soundness, Completeness (S5) |
| Temporal | `Logics/Temporal/` | High | DeductionThm, MCS, Soundness, Completeness, Chronicle pipeline |
| Bimodal | `Logics/Bimodal/` | Very High | Full metalogic: separation, conservative extension, decidability, FMP |
| HML | `Logics/HML/` | Moderate | Theory equivalence = bisimilarity |
| Linear Logic (CLL) | `Logics/LinearLogic/CLL/` | Low-Moderate | Cut elimination, eta expansion, phase semantics |

The library also has `Foundations/Logic/` providing shared infrastructure (Connectives, ProofSystem, Axioms, InferenceSystem, Metalogic) and `Foundations/Semantics/` providing LTS/FLTS frameworks used by HML and Languages/CCS.

The six systems span distinct paradigms: classical Hilbert-style (PL, Modal, Temporal, Bimodal), process-algebraic (HML), and substructural (Linear Logic). Any refactoring must accommodate this diversity.

### 2. The Current Four-Layer Formula Duplication is the Central Problem

The project currently duplicates formula types across four logic levels:

```
PL.Proposition      : {atom, bot, imp, and, or}          -- 5 constructors
Modal.Proposition   : {atom, bot, imp, box}               -- 4 constructors
Temporal.Formula    : {atom, bot, imp, untl, snce}        -- 5 constructors
Bimodal.Formula     : {atom, bot, imp, box, untl, snce}   -- 6 constructors
```

Each formula type independently defines `neg`, `top`, `and` (Lukasiewicz), `or` (Lukasiewicz), `iff`, and various derived operators. The metalogic machinery (DerivationTree, DeductionTheorem, MCS, Soundness, Completeness) is structurally identical across all four levels, differing only in the formula constructors being matched and the inference rules available.

**Quantifying the duplication**: Modal Metalogic is 1,370 LOC; Temporal Metalogic is 3,259 LOC; Bimodal Core Metalogic is 1,467 LOC. Significant portions of the DeductionTheorem, MCS, and basic proof infrastructure are structural copies. The `HasHilbertTree` typeclass in `DeductionHelpers.lean` already extracts the common deduction-theorem helpers, demonstrating that the abstraction path is viable.

### 3. The Isabelle Propositional_Logic_Class Pattern

The task references Isabelle's `Propositional_Logic_Class` formalization (Asta From, documented in the AFP). The key insight from that approach:

**Isabelle's approach**: Define a locale (= typeclass in Lean terms) `Propositional_Logic` parameterized by a formula type and the connectives it supports. Prove all propositional-level theorems once at the locale level. Then each concrete logic (classical, intuitionistic, modal, temporal) instantiates the locale and immediately inherits all propositional theorems.

**What CSLib already does**: The `Connectives.lean` typeclass hierarchy (`HasBot`, `HasImp`, `HasBox`, `HasUntil`, `HasSince` -> `PropositionalConnectives`, `ModalConnectives`, `TemporalConnectives`, `BimodalConnectives`) mirrors Isabelle's locale parameters. The `ProofSystem.lean` hierarchy (`MinimalHilbert`, `IntuitionisticHilbert`, `ClassicalHilbert` -> `ModalHilbert`, `TemporalBXHilbert`, `BimodalTMHilbert`) mirrors Isabelle's proof system locales.

**What CSLib does NOT yet do**: The theorems in `Foundations/Logic/Theorems/` ARE parameterized over the connective typeclasses (polymorphic axiom definitions in `Axioms.lean`), but the metalogic infrastructure (DerivationTree, DeductionTheorem, MCS, Soundness, Completeness) is NOT. Each logic reimplements these from scratch.

### 4. The "Dependent Type System Approach" Opportunity

Lean 4 offers capabilities beyond Isabelle's locale system through dependent types and universes. The key opportunities:

**a. Formula as a dependent type family**: Rather than four separate inductive types, one could define a universe-indexed formula type parameterized by a "connective signature":

```lean
structure ConnectiveSignature where
  hasBox : Bool
  hasUntil : Bool
  hasSince : Bool
  hasAnd : Bool
  hasOr : Bool

inductive Formula (sig : ConnectiveSignature) (Atom : Type u) : Type u where
  | atom : Atom -> Formula sig Atom
  | bot : Formula sig Atom
  | imp : Formula sig Atom -> Formula sig Atom -> Formula sig Atom
  | box : sig.hasBox = true -> Formula sig Atom -> Formula sig Atom
  | untl : sig.hasUntil = true -> Formula sig Atom -> Formula sig Atom ->
           Formula sig Atom
  -- etc.
```

However, this approach has serious ergonomic problems: every pattern match on `box` requires carrying a proof witness, notation breaks, and the `deriving` mechanism fails.

**b. A more practical Lean 4 approach -- Typeclass-parameterized metalogic**: Instead of unifying the formula type, unify the metalogic machinery by parameterizing over the formula type via typeclasses:

```lean
class HasDerivationTree (F : Type*) where
  Tree : List F -> F -> Type*
  height : {G : List F} -> {f : F} -> Tree G f -> Nat
  -- inference rules as typeclass fields
```

This is the direction already started by `HasHilbertTree` and `DerivationSystem`. The refactoring would extend this to cover the full metalogic pipeline.

**c. Using Lean's universe polymorphism**: Lean's universe polymorphism can avoid code duplication that Isabelle handles with locales. Theorems proven once at the `ClassicalHilbert` level can be instantiated at any logic extending it.

### 5. HML and Linear Logic Follow Different Patterns

HML (`Logics/HML/Basic.lean`) uses an inductively-defined satisfaction relation (not a recursive function like Modal/Temporal), parameterized by an LTS rather than a Kripke model. Its formula type includes labeled modalities (`diamond mu phi`, `box mu phi`) rather than plain `box phi`. This is fundamentally different from the Modal pattern.

Linear Logic (`Logics/LinearLogic/CLL/`) uses sequent calculus rather than Hilbert systems, with cut elimination and phase semantics. It shares almost no structural code with the Hilbert-style logics.

These two systems should NOT be forced into the same abstraction as the Hilbert-style logics. The refactoring should focus on the PL-Modal-Temporal-Bimodal stack.

## Strategic Alignment Analysis

### Alignment with Roadmap

The ROADMAP.md focuses on "Porting BimodalLogic to CSLib" -- extracting content from a standalone BimodalLogic repository into four CSLib modules. The remaining items are Dense/Discrete/Continuous completeness variants and "Abstract shared completeness infrastructure."

The "Abstract shared completeness infrastructure" item directly calls for what this refactoring would accomplish. The roadmap already recognizes the need; this task would provide the research foundation.

### Alignment with PR #649 and Upstream Strategy

PR #649 established the precedent of using `Connectives.lean` as a shared typeclass foundation. The Modal PR (task 197) extends this with `HasBox`/`ModalConnectives`. The proposed refactoring would be the natural next step: after the connective typeclasses are established, lift the proof infrastructure to the same level of generality.

However, this is a multi-PR effort. Upstream acceptance requires incremental changes, not a massive refactoring PR. The strategy should be:

1. **PR #649 merges** (temporal formula type + connectives)
2. **Modal PR merges** (adds HasBox/ModalConnectives)
3. **Shared metalogic infrastructure PR** (lifts DerivationTree/DeductionTheorem)
4. **Logic-specific instantiation PRs** (prove each logic is an instance)

## Future-Proofing Considerations

### Logics Not Yet Implemented

The refactoring must accommodate logics that CSLib could formalize in the future:

| Logic Family | Key Operators | Signature Extension |
|-------------|--------------|-------------------|
| Epistemic | K_i (agent-indexed box) | `HasIndexedBox` |
| Deontic | O (obligation), P (permission) | `HasDeonticBox` / reuse `HasBox` |
| Dynamic (PDL) | [alpha]phi (program-indexed) | `HasProgramBox` |
| Hybrid | @_i, downarrow | `HasNominal`, `HasBinder` |
| Description Logic | concept constructors | Separate framework |
| CTL/CTL* | path quantifiers | `HasPathQuantifier` |
| Intuitionistic Modal | independent box + dia | `HasDia` (already anticipated in Connectives.lean) |

The current design already anticipates the intuitionistic modal case (documented in `Connectives.lean` docstring). The agent-indexed and program-indexed cases require a qualitatively different typeclass (`HasIndexedBox (F : Type*) (I : Type*) where box : I -> F -> F`) that goes beyond the current `HasBox`.

**Key insight**: The connective typeclass hierarchy scales well for classical extensions. The proof system hierarchy (`MinimalHilbert` -> `IntuitionisticHilbert` -> `ClassicalHilbert` -> `ModalHilbert` etc.) already accommodates the three-level propositional strength. Future logics would add branches at the `ModalHilbert` level.

### The Propositional Foundation Question

The task asks whether Propositional/ should also be refactored. The answer is nuanced:

**Yes, partially**: The `PL.Proposition` type uses `{atom, bot, imp, and, or}` -- it has native `and`/`or` constructors, unlike Modal/Temporal/Bimodal which use Lukasiewicz encodings. This asymmetry means PL cannot directly instantiate a unified formula type shared with Modal.

However, PL's metalogic (DeductionTheorem, MCS, Soundness, Completeness) IS structurally parallel to Modal's. The `HasHilbertTree` abstraction already covers all four logics. The refactoring should:

1. Keep `PL.Proposition` as its own type (it has different constructors)
2. Unify the metalogic machinery via typeclasses that PL, Modal, Temporal, and Bimodal all instantiate
3. The connective typeclasses already handle the signature difference (`PL.Proposition` has `HasAnd`/`HasOr` instances; Modal does not)

### The "BimodalConnectives avoids the diamond" Pattern

The `BimodalConnectives` class definition reveals a careful design choice:

```lean
class BimodalConnectives (F : Type*) extends ModalConnectives F, HasUntil F, HasSince F
```

It extends `ModalConnectives` (which extends `PropositionalConnectives` + `HasBox`) and adds `HasUntil`/`HasSince` directly, rather than extending `TemporalConnectives`. This avoids a typeclass diamond (`BimodalConnectives -> ModalConnectives -> PropositionalConnectives` and `BimodalConnectives -> TemporalConnectives -> PropositionalConnectives`). This design discipline must be maintained in any refactoring.

## Upstream Acceptance Factors

### What CSLib Reviewers and Maintainers Value

Based on PR #649 patterns and the codebase conventions:

1. **Incremental PRs** (~300-500 LOC net): The PR #649 precedent establishes this. A massive refactoring PR will be rejected.

2. **Backward compatibility**: Every change must maintain existing API. Renaming or removing definitions requires deprecation or aliases. The local `LogicalEquivalence.lean` already shows this discipline (dropping unused infrastructure but preserving the core `Context`/`fill`/`congruence` API).

3. **Complete CI verification**: `lake build`, `checkInitImports`, `lint`, `lint-style`, `test`, `shake` must all pass.

4. **Documentation conventions**: `## Main definitions`, `## Notation`, `## References` sections with BibKey format. Docstrings explaining design rationale (not just what, but why).

5. **Zero sorrys**: The entire metalogic codebase currently has zero sorrys. Any refactoring must maintain this.

6. **Self-contained semantic units**: Each PR should represent a complete, self-contained change. The Connectives.lean + Formula.lean pattern from PR #649 shows a complete "add a new formula type" unit.

### What Would Make Reviewers Skeptical

1. **Over-abstraction**: Parameterizing everything to the point where concrete proofs become obscure. The current approach of concrete formula types with shared typeclass infrastructure is intentional and readable.

2. **Performance regressions**: Typeclass resolution overhead from deep inheritance hierarchies. The current 15-system modal cube (`Cube.lean`) already uses `grind` extensively; adding more typeclass layers could degrade elaboration performance.

3. **Breaking downstream**: The Bimodal module is the most developed (~6000+ LOC). Any refactoring that requires touching Bimodal proofs will be scrutinized heavily.

4. **Category-theoretic abstraction without payoff**: Using functors/natural transformations to describe logic morphisms is elegant but adds complexity without clear proof automation benefit in Lean 4.

## Novel Approaches Worth Exploring

### 1. Proof Morphisms via Typeclass-Parameterized Metalogic

The most impactful and practical novel approach: define a typeclass `HasMetalogicPipeline` that bundles the full metalogic pipeline (DerivationTree, DeductionTheorem, MCS, Soundness, Completeness) parameterized over a formula type and proof system. This would allow:

- Proving the deduction theorem ONCE for any logic extending `ClassicalHilbert`
- Proving Lindenbaum's lemma ONCE (already done via `set_lindenbaum`)
- Proving the MCS closure properties ONCE
- Each concrete logic only needs to supply: formula type, axiom predicate, inference rules, and semantic evaluation function

This is beyond what Isabelle's `Propositional_Logic_Class` does (which only covers propositional-level theorems) and would be genuinely novel for a Lean 4 logic library.

### 2. Embedding Hierarchy as Lean 4 Coercions

The Bimodal embedding infrastructure (`PropositionalEmbedding`, `ModalEmbedding`, `TemporalEmbedding`) defines translation functions between formula types. These could be formalized as Lean 4 coercions (`Coe`) with automatic lifting of theorems. Currently the embeddings are defined manually; typeclass-based coercions would make them usable transparently.

### 3. Axiom Predicate Algebra

Rather than defining axiom predicates as monolithic inductive types (`ModalAxiom`, `PropositionalAxiom`, etc.), define an algebra of axiom predicates:

```lean
-- Axiom predicate combinators
def PropAxioms (F : Type*) [HasBot F] [HasImp F] : F -> Prop := ...
def ModalKAxiom (F : Type*) [HasBox F] [HasBot F] [HasImp F] : F -> Prop := ...

-- Compose via disjunction
def S5Axioms := PropAxioms || ModalKAxiom || ModalTAxiom || Modal4Axiom || ModalBAxiom
```

This would make it trivial to define new logics by composing axiom sets, matching the lattice structure of normal modal logics.

### 4. Lean 4 Meta-Programming for Formula Type Generation

A Lean 4 macro or derive handler could generate formula types from a connective signature specification:

```lean
@[logic_formula {bot, imp, box}]
inductive Modal.Proposition (Atom : Type u) : Type u
```

This would auto-generate the derived connectives, BEq instances, connective typeclass instances, and structural properties. This is speculative but would eliminate the formula duplication entirely.

### 5. Duality as a First-Class Concept

Temporal logic has a strong duality (past/future) that is currently handled by manually defining `swapTemporal`. This could be elevated to a typeclass:

```lean
class HasDuality (F : Type*) where
  dual : F -> F
  dual_involution : forall f, dual (dual f) = f
```

With the duality inference rule ("if provable phi then provable dual(phi)") also captured at the typeclass level. This would halve the axiom count for temporal-like logics.

## Recommended Strategic Direction

### Near-Term (Aligned with PR #649 merge)

1. **Do not attempt a massive refactoring now.** The immediate priority is merging PR #649 and the Modal PR (task 197). These establish the connective typeclass foundation.

2. **Document the abstraction targets.** Create a design document (not code) identifying exactly which metalogic components can be unified, with concrete type signatures for the unified versions.

3. **Extend `HasHilbertTree` incrementally.** The `DeductionHelpers.lean` pattern already works. The next step is a `HasMetalogicPipeline` typeclass covering the MCS pipeline, proven once and instantiated per-logic.

### Medium-Term (Post-Bimodal completion)

4. **Implement the axiom predicate algebra.** Replace monolithic axiom inductive types with composable axiom predicates. This is a non-breaking change that adds new definitions alongside existing ones.

5. **Unify DerivationTree via a parameterized inductive.** Define a single `DerivationTree` type parameterized by a "rule set" structure that specifies which inference rules (MP, necessitation, temporal necessitation, temporal duality, etc.) are available. Each logic instantiates this with its specific rule set.

6. **Extract common MCS-to-Completeness pipeline.** The pattern DeductionTheorem -> MCS -> Lindenbaum -> Canonical Model -> Truth Lemma -> Completeness is shared across Modal, Temporal, and Bimodal. The logic-specific parts (canonical model construction, truth lemma) differ, but the surrounding infrastructure is identical.

### Long-Term (Library maturity)

7. **Add epistemic, deontic, and CTL.** Use the unified infrastructure to add new logics with minimal boilerplate. Each new logic should require only: formula type (or instantiation of a parameterized type), axiom predicate (via composition), semantic evaluation function, and truth lemma for the canonical model.

8. **Consider the Lean 4 macro approach.** Once the manual pattern is well-established and proven to work across 5+ logics, codify it as a macro or derive handler.

## Confidence Level

**Medium-High**.

Justification:
- **High confidence** in the diagnosis: the formula duplication and metalogic code duplication are clearly visible in the codebase. Zero sorrys across all metalogic files confirms the existing proofs are structurally sound.
- **High confidence** in the incremental strategy: PR #649's pattern establishes the upstream acceptance model. Massive refactoring PRs will not be accepted.
- **Medium confidence** in the specific abstraction approach: The `HasHilbertTree` pattern works for deduction helpers, but extending it to the full metalogic pipeline (especially the truth lemma and canonical model construction, which differ substantially across logics) requires more detailed investigation of what can actually be unified vs. what must remain logic-specific.
- **Lower confidence** in the novel approaches (formula generation macros, axiom predicate algebra): These are speculative and require prototyping to assess feasibility in Lean 4.

The main risk is over-abstraction: creating a framework so general that it becomes harder to use than the current concrete approach. The Isabelle `Propositional_Logic_Class` succeeds because it abstracts at the right level (propositional theorems) without trying to unify everything. CSLib should follow this same principle of "abstract what is truly shared, keep concrete what is logic-specific."
