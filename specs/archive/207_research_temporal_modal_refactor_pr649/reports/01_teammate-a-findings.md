# Teammate A Findings: Refactoring Temporal/ and Modal/ Based on PR #649 Review

## Key Findings

1. **The Isabelle `Propositional_Logic_Class` AFP entry** (Matthew Doty, 2022) provides a class-based approach where `implication_logic` is a typeclass with exactly three parameters: a deduction predicate, an implication connective, and three axioms (K, S, modus ponens). All propositional reasoning (deduction theorem, cut rule, monotonicity, MCS construction) is proven generically at this level. `classical_logic` extends it by adding falsum and double negation. All derived connectives and metatheory flow from these minimal axiom classes.

2. **CSLib currently has a dual-layer architecture** that partially achieves the same goal but with significant structural friction:
   - **Layer A (Concrete)**: Each logic has its own `Formula`/`Proposition` inductive type with its own `DerivationTree` inductive, its own axiom inductive, and its own concrete metalogic proofs (deduction theorem, MCS, soundness, completeness).
   - **Layer B (Abstract)**: `Foundations/Logic/` provides typeclass-based `ProofSystem.lean` (MinimalHilbert, ClassicalHilbert, ModalHilbert, TemporalBXHilbert), `Axioms.lean` (polymorphic axiom formulas), `Connectives.lean` (HasBot, HasImp, HasBox, etc.), and `Theorems/` (generic propositional/modal/temporal derived theorems).
   
3. **The core architectural issue** is that the two layers are not well-connected. The concrete `DerivationTree` types in Modal/ and Temporal/ do NOT use the abstract `InferenceSystem`/`ProofSystem` infrastructure as their primary proof mechanism. Instead, they have bespoke inductive types that are bridge-connected to the abstract layer via `wrap`/`unwrap` patterns (see `PropositionalHelpers.lean`). This means:
   - **Duplicate metalogic**: The deduction theorem is proven separately for Modal and Temporal, with nearly identical structure.
   - **Bridge tax**: Every use of a generic Foundations theorem inside concrete metalogic requires wrapping/unwrapping between `DerivationTree` and `Nonempty (DerivationTree)`.
   - **No generic MCS**: The MCS construction is done separately for each logic despite having identical structure.

4. **The Isabelle approach suggests a cleaner alternative**: Define a single parametric proof system where the axiom set is itself a parameter. The deduction theorem, MCS construction, cut rule, and monotonicity are all proven once at the abstract level and instantiated for each logic.

5. **Lean 4's dependent type system enables an even more powerful version** of the Isabelle approach, since Lean typeclasses can carry proofs, dependent types can express the relationship between formula structure and axiom schemas, and universe polymorphism eliminates the need for separate Sort-level workarounds.

## Current Architecture Analysis

### File Structure Overview

```
Cslib/Foundations/Logic/
  Connectives.lean          -- HasBot, HasImp, HasBox, HasUntil, HasSince, bundled classes
  Axioms.lean               -- Polymorphic axiom formulas (ImplyK, AxiomK, SerialFuture, etc.)
  InferenceSystem.lean      -- Generic InferenceSystem typeclass (by Montesi)
  ProofSystem.lean          -- HasAxiom* typeclasses, bundled systems (MinimalHilbert..BimodalTMHilbert)
  Theorems/
    Combinators.lean        -- imp_trans, identity, b_combinator, flip, etc.
    Propositional/Core.lean -- efq, raa, double_negation, lce_imp, rce_imp
    Modal/Basic.lean        -- box_mono, diamond_mono, G_distribution
    Temporal/TemporalDerived.lean -- F_mono, G_distribution (temporal version)

Cslib/Logics/Temporal/
  Syntax/Formula.lean       -- Formula inductive (atom|bot|imp|untl|snce)
  ProofSystem/
    Axioms.lean             -- Concrete Axiom inductive (28 constructors)
    Derivation.lean         -- DerivationTree inductive (6 constructors)
    Derivable.lean          -- Prop-valued wrapper
    Instances.lean          -- InferenceSystem + HasAxiom* instances
  Metalogic/
    DeductionTheorem.lean   -- Deduction theorem (concrete proof)
    MCS.lean                -- Maximally consistent sets (concrete)
    Soundness.lean          -- Soundness proof
    Completeness.lean       -- Completeness proof
    PropositionalHelpers.lean -- wrap/unwrap bridge to Foundations

Cslib/Logics/Modal/
  Basic.lean                -- Proposition inductive (atom|bot|imp|box)
  Metalogic/
    DeductionTheorem.lean   -- Deduction theorem (concrete proof, near-identical to Temporal)
    MCS.lean                -- Maximally consistent sets (concrete)
    Soundness.lean          -- Per-system soundness (15+ files)
    Completeness.lean       -- Per-system completeness (15+ files)
```

### The Bridge Pattern (PropositionalHelpers.lean lines 47-80)

The current approach uses wrap/unwrap to connect concrete derivation trees to abstract typeclass theorems:

```lean
-- Current: Manual bridging in each logic's metalogic
def wrap {φ : Formula Atom}
    (d : DerivationTree FrameClass.Base [] φ) :
    InferenceSystem.DerivableIn Temporal.HilbertBX φ := ⟨d⟩

def unwrap {φ : Formula Atom}
    (h : InferenceSystem.DerivableIn Temporal.HilbertBX φ) :
    DerivationTree FrameClass.Base [] φ := h.some

-- Then each theorem must be manually bridged:
def doubleNegation (φ : Formula Atom) :
    DerivationTree FrameClass.Base [] (¬¬φ → φ) :=
  unwrap (@Theorems.Propositional.Core.double_negation
    _ _ _ Temporal.HilbertBX _ _ (φ := φ))
```

This pattern is repeated for every theorem needed in concrete metalogic, creating significant boilerplate.

### Concrete DerivationTree (Temporal, lines 50-72)

```lean
-- Current: Bespoke inductive per logic
inductive DerivationTree (fc : FrameClass) :
    Context Atom → Formula Atom → Type u where
  | axiom (Γ : Context Atom) (φ : Formula Atom) (h : Axiom φ)
      (h_fc : h.minFrameClass ≤ fc) : DerivationTree fc Γ φ
  | assumption (Γ : Context Atom) (φ : Formula Atom) (h : φ ∈ Γ) :
      DerivationTree fc Γ φ
  | modus_ponens (Γ : Context Atom) (φ ψ : Formula Atom)
      (d1 : DerivationTree fc Γ (φ.imp ψ))
      (d2 : DerivationTree fc Γ φ) : DerivationTree fc Γ ψ
  | temporal_necessitation (φ : Formula Atom)
      (d : DerivationTree fc [] φ) : DerivationTree fc [] φ.allFuture
  | temporal_duality (φ : Formula Atom)
      (d : DerivationTree fc [] φ) : DerivationTree fc [] φ.swapTemporal
  | weakening (Γ Δ : Context Atom) (φ : Formula Atom)
      (d : DerivationTree fc Γ φ) (h : Γ ⊆ Δ) : DerivationTree fc Δ φ
```

The modal version is essentially identical, with `box` instead of `temporal_necessitation`/`temporal_duality`.

## Reviewer's Suggestion Analysis

While I could not directly access the Zulip thread (it requires authentication), the task description combined with the PR structure, the Isabelle reference, and the codebase analysis point clearly to the following critique:

**The reviewer is suggesting that CSLib should adopt the Isabelle `Propositional_Logic_Class` pattern**: define the proof system abstractly through typeclasses (as Isabelle does with locales/classes), prove metatheory generically once, and then instantiate for each specific logic. The current approach duplicates metalogic across Modal/ and Temporal/ when it should be factored through the abstract typeclass layer.

Specifically, the linked Isabelle `Implication_Logic.thy` (offset 15878-15899) shows the `implication_logic` class:

```isabelle
class implication_logic =
  fixes deduction :: "'a => bool" ("⊢ _" [60] 55)
  fixes implication :: "'a => 'a => 'a" (infixr "→" 70)
  assumes axiom_k: "⊢ φ → ψ → φ"
  assumes axiom_s: "⊢ (φ → ψ → χ) → (φ → ψ) → φ → χ"
  assumes modus_ponens: "⊢ φ → ψ ==> ⊢ φ ==> ⊢ ψ"
```

And then everything -- `list_deduction`, `set_deduction`, the deduction theorem, monotonic growth, cut rule, maximally consistent sets, MCS extension via Zorn's lemma -- is proven once generically inside this class.

The key insight: **In Isabelle, the `deduction` predicate and `implication` connective are class parameters.** This means ANY type with an implication-like binary operation and a truth predicate that satisfies K, S, and MP automatically gets all propositional metatheory for free.

## Isabelle Formalization Analysis

### The Isabelle Hierarchy

```
implication_logic(deduction, implication, axiom_k, axiom_s, modus_ponens)
  |
  +-- list_deduction (derived interpretation)
  +-- set_deduction (derived interpretation)
  +-- deduction_theorem (metatheorem)
  +-- maximally_consistent_sets (construction via Zorn's lemma)
  |
  v
classical_logic extends implication_logic
  + falsum :: 'a
  + double_negation: "⊢ ((φ → ⊥) → ⊥) → φ"
  |
  +-- ex_falso_quodlibet (derived)
  +-- contraposition (derived)
  +-- conjunction, disjunction (defined via ⊥ and →)
  +-- conventional MCS (φ-MCS becomes ⊥-MCS)
  |
  v
classical_logic_completeness extends classical_logic
  + strong soundness and completeness
```

### What Isabelle Achieves That CSLib Does Not

1. **Single deduction theorem proof**: The deduction theorem is proven once in `implication_logic` and inherited by all extensions. CSLib proves it separately in `Temporal/Metalogic/DeductionTheorem.lean` and `Modal/Metalogic/DeductionTheorem.lean`.

2. **Single MCS construction**: MCS with Zorn's lemma is proven once in `implication_logic`. CSLib proves it separately in `Temporal/Metalogic/MCS.lean` and `Modal/Metalogic/MCS.lean`.

3. **Derived interpretation**: Isabelle proves that `list_deduction` and `set_deduction` are themselves implication logics, getting all theorems for free. CSLib has no such recursive instantiation.

4. **Type-generic cut rule**: Cut elimination/rule is proven once and available everywhere.

### Key Design Differences

| Aspect | Isabelle | CSLib (current) |
|--------|----------|-----------------|
| Axioms | Class parameters (abstract) | Both abstract (ProofSystem.lean) AND concrete (Axioms.lean inductive) |
| Deduction predicate | Class parameter (`⊢ _`) | Concrete DerivationTree per logic |
| Metatheory | Proven once, inherited | Proven per-logic (duplicate) |
| Connective derivation | Inside class | Split: Connectives.lean (interface) + per-formula abbrevs |
| MCS | Proven once with Zorn | Proven per-logic |

## Recommended Refactoring Approach

### Phase 1: Generic Derivation Framework (High Priority)

Define a single parametric derivation tree type in Foundations that is parameterized by the axiom set:

```lean
-- New: Cslib/Foundations/Logic/Derivation/Generic.lean

/-- A generic axiom predicate: given formula type F, an axiom predicate says
    which formulas are axioms. -/
abbrev AxiomPredicate (F : Type*) := F -> Prop

/-- Generic derivation tree parameterized by axiom predicate.
    The axiom predicate determines which logic this derivation tree is for. -/
inductive GenericDerivation (axiomPred : AxiomPredicate F) [HasImp F] :
    List F → F → Type _ where
  | axiom (Γ : List F) (φ : F) (h : axiomPred φ) :
      GenericDerivation axiomPred Γ φ
  | assumption (Γ : List F) (φ : F) (h : φ ∈ Γ) :
      GenericDerivation axiomPred Γ φ
  | modus_ponens (Γ : List F) (φ ψ : F)
      (d1 : GenericDerivation axiomPred Γ (HasImp.imp φ ψ))
      (d2 : GenericDerivation axiomPred Γ φ) :
      GenericDerivation axiomPred Γ ψ
  | weakening (Γ Δ : List F) (φ : F)
      (d : GenericDerivation axiomPred Γ φ) (h : Γ ⊆ Δ) :
      GenericDerivation axiomPred Δ φ
```

This single type replaces the bespoke `DerivationTree` in both Modal/ and Temporal/ for the propositional core. Logic-specific rules (necessitation, temporal duality) can be added via extension.

### Phase 2: Generic Deduction Theorem (High Priority)

Prove the deduction theorem once at the Foundations level:

```lean
-- New: Cslib/Foundations/Logic/Derivation/DeductionTheorem.lean

/-- A generic axiom predicate satisfies ImplyK and ImplyS. -/
class HasPropositionalAxioms (axiomPred : AxiomPredicate F) [HasBot F] [HasImp F] where
  has_implyK : ∀ (φ ψ : F), axiomPred (HasImp.imp φ (HasImp.imp ψ φ))
  has_implyS : ∀ (φ ψ χ : F), axiomPred (HasImp.imp (HasImp.imp φ (HasImp.imp ψ χ))
    (HasImp.imp (HasImp.imp φ ψ) (HasImp.imp φ χ)))

/-- The deduction theorem for any axiom predicate with K and S. -/
theorem generic_deduction_theorem [HasBot F] [HasImp F]
    {axiomPred : AxiomPredicate F} [HasPropositionalAxioms axiomPred]
    {A : F} {Γ : List F} {φ : F}
    (d : GenericDerivation axiomPred (A :: Γ) φ) :
    GenericDerivation axiomPred Γ (HasImp.imp A φ) := by
  sorry -- One-time proof, replaces TWO separate proofs in Modal/ and Temporal/
```

### Phase 3: Generic MCS Construction (Medium Priority)

Following the Isabelle pattern, define the MCS construction once:

```lean
-- New: Cslib/Foundations/Logic/Derivation/MCS.lean

/-- Generic MCS: a maximally consistent set relative to derivability. -/
structure GenericMCS (axiomPred : AxiomPredicate F) [HasBot F] [HasImp F] where
  carrier : Set F
  consistent : ¬ GenericDerivable axiomPred carrier HasBot.bot
  maximal : ∀ φ, φ ∈ carrier ∨ (HasImp.imp φ HasBot.bot) ∈ carrier
```

### Phase 4: Connect Existing Logics as Instantiations (Medium Priority)

Each specific logic instantiates the generic framework:

```lean
-- Updated: Cslib/Logics/Temporal/ProofSystem/Derivation.lean

/-- Temporal axiom predicate: bundles propositional + temporal axioms. -/
def temporalAxiomPred (fc : FrameClass) : AxiomPredicate (Formula Atom) :=
  fun φ => ∃ (h : Axiom φ), h.minFrameClass ≤ fc

/-- Temporal derivation is a specialization of generic derivation
    extended with temporal-specific rules. -/
inductive TemporalDerivation (fc : FrameClass) :
    Context Atom → Formula Atom → Type u where
  | core (d : GenericDerivation (temporalAxiomPred fc) Γ φ) :
      TemporalDerivation fc Γ φ
  | temporal_necessitation (φ : Formula Atom)
      (d : TemporalDerivation fc [] φ) : TemporalDerivation fc [] φ.allFuture
  | temporal_duality (φ : Formula Atom)
      (d : TemporalDerivation fc [] φ) : TemporalDerivation fc [] φ.swapTemporal
```

This way, the deduction theorem for the propositional core is inherited, and only the temporal-specific cases need new proofs.

### Phase 5: Eliminate Bridge Pattern (Low Priority)

With the generic framework, the `wrap`/`unwrap` bridge in `PropositionalHelpers.lean` becomes unnecessary. The generic theorems directly produce `GenericDerivation` terms that the temporal-specific derivation can embed.

### Alternative Approach: Lean-Idiomatic Typeclass Interpretation

A more Lean-idiomatic approach (vs. the Isabelle locale interpretation) leverages Lean's typeclass inheritance more directly:

```lean
-- Alternative: Use the existing MinimalHilbert/ClassicalHilbert typeclasses
-- but make them the PRIMARY proof mechanism, not a secondary layer

-- The key change: instead of separate DerivationTree types, make
-- `InferenceSystem.derivation` (S⇓φ) the ONLY proof type,
-- with the concrete derivation tree as the implementation:

instance : InferenceSystem Temporal.HilbertBX (Formula Atom) where
  derivation φ := DerivationTree FrameClass.Base [] φ

-- Then ALL generic Foundations theorems work directly on DerivationTree
-- without wrap/unwrap, because the typeclass resolution resolves
-- InferenceSystem.DerivableIn = Nonempty (DerivationTree ...)
```

This is actually already partially implemented in `Instances.lean` but not fully utilized -- the metalogic still works with raw `DerivationTree` rather than through the typeclass interface.

## Comparison: Current vs. Proposed Architecture

### Current Flow (Temporal Deduction Theorem)
```
Temporal/Metalogic/DeductionTheorem.lean
  -- Manually proves deduction theorem on DerivationTree
  -- ~150 lines of proof code
  -- Nearly identical to Modal/Metalogic/DeductionTheorem.lean
  
Temporal/Metalogic/PropositionalHelpers.lean  
  -- wrap/unwrap bridge (~50 lines boilerplate)
  -- Manually delegates each Foundations theorem
```

### Proposed Flow (Temporal Deduction Theorem)
```
Foundations/Logic/Derivation/DeductionTheorem.lean
  -- Proves deduction theorem ONCE for GenericDerivation
  -- ~150 lines of proof code (same complexity, but done ONCE)

Temporal/ProofSystem/Derivation.lean
  -- TemporalDerivation embeds GenericDerivation
  -- Inherits deduction theorem for propositional core automatically
  -- Only needs proofs for temporal_necessitation/temporal_duality cases
  -- ~30 lines additional
```

**Net savings per new logic added**: ~150 lines (deduction theorem) + ~200 lines (MCS) + ~50 lines (bridge boilerplate) = ~400 lines.

## Risks and Considerations

1. **Lean typeclass inference performance**: Deep typeclass hierarchies can cause slow elaboration. The Isabelle approach relies on locale interpretation which has different performance characteristics. Need to benchmark with realistic formula types.

2. **Universe polymorphism complications**: The generic derivation tree needs careful universe handling since `Formula Atom : Type u` and the derivation tree itself may live in a different universe.

3. **Compatibility with existing metalogic**: The ~2000 lines of existing Temporal metalogic (chronicle construction, completeness) depend on the concrete `DerivationTree` type. A refactor must provide a migration path, not require rewriting completeness proofs.

4. **Dependent formula constructors**: The Isabelle approach works with an abstract formula type where `implication` is a function parameter. In CSLib, each formula type has specific constructors (atom, bot, imp, untl, snce). The generic derivation tree approach preserves this since it is parameterized over the formula type.

5. **Frame class parameterization**: The temporal `DerivationTree` is parameterized by `FrameClass` (Base/Dense/Discrete). This must be accommodated in the generic framework, possibly via a more general "axiom filtering" mechanism.

## Confidence Level: HIGH

**Justification**: 
- The architectural analysis is based on thorough reading of all relevant source files in both Foundations/ and Logics/.
- The Isabelle formalization has been fully extracted and analyzed.
- The duplicate code pattern (Temporal vs Modal metalogic) is objectively verifiable.
- The proposed refactoring follows established patterns (Isabelle's Propositional_Logic_Class has been maintained since 2022 and used in multiple downstream AFP entries).
- The Phase 1-2 changes (generic derivation + generic deduction theorem) are low-risk since they add new abstractions without modifying existing code.
- The higher phases (connecting existing logics) are medium-risk due to the large existing codebase depending on concrete types.

**One area of uncertainty**: Without access to the actual Zulip discussion, I am reconstructing the reviewer's suggestion from the Isabelle link, the PR context, and the codebase structure. The reviewer may have additional specific suggestions beyond what I've identified. The core recommendation (factor metalogic through abstract typeclasses, following the Isabelle pattern) is well-supported regardless.
