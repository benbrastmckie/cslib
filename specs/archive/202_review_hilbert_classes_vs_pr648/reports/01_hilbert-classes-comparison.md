# Hilbert Classes Comparison: thomaskwaring/cslib_SKI vs PR #648 vs This Fork

## Executive Summary

Three independent Hilbert system implementations targeting CSLib were compared: (1) Thomas Waring's `Cslib/Logics/Hilbert/Classes.lean` on the `hilbert` branch of `cslib_SKI`, (2) PR #648 (`feat/propositional-v2`) submitted by this fork to upstream `leanprover/cslib`, and (3) this fork's full `Cslib/Logics/Propositional/` hierarchy. The three share the same logical content (S, K, MP, deduction theorem, ex falso, Peirce) but differ fundamentally in their architectural approach:

- **Waring's Classes.lean** builds a maximally polymorphic "contextual inference system" framework using abstract context typeclasses (`Context`, `ExContext`), an opaque `Hilbert` tag, and structural classes (`HasS`, `HasK`, `Deductive`, `HasCut`, etc.). Derivation is modeled as `axAssDer` (axiom/assumption/MP inductive) with the deduction theorem proved by SKI abstraction.
- **PR #648** (this fork's upstream contribution) introduces a connective typeclass hierarchy (`HasBot`, `HasImp`, `HasAnd`, `HasOr`, `PropositionalConnectives`) and a five-primitive `Proposition` type (`atom`, `bot`, `imp`, `and`, `or`), with natural deduction as the primary proof system.
- **This fork** extends PR #648 with a complete two-layer proof system: natural deduction (Layer 1) plus a Hilbert-style `DerivationTree` (Layer 2), connected by a proven extensional equivalence. It includes three axiom hierarchies (minimal/intuitionistic/classical), semantics, soundness, and strong completeness.

Key finding: **No blocking conflicts exist**. The three approaches are complementary. Waring's polymorphic framework could serve as a generic backend that this fork's concrete Proposition type instantiates, but significant refactoring would be needed to align the abstraction layers. PR #648 is a strict subset of this fork's development and is fully compatible with it.

---

## Source 1: thomaskwaring/cslib_SKI `Hilbert/Classes.lean`

### Location
`https://github.com/thomaskwaring/cslib_SKI/blob/hilbert/Cslib/Logics/Hilbert/Classes.lean`

### Architecture

Waring's design is **maximally polymorphic**: everything is parameterized over abstract types for formulas (`alpha`), contexts (`beta`), and proof systems (`S`), connected via typeclasses. The key design decisions are:

#### 1. Context Abstraction (`Context`, `ExContext`)

Instead of concrete `List`, `Finset`, or `Set` for contexts, Waring defines abstract `Context` and `ExContext` typeclasses (in a separate `Data/Context.lean`) that axiomatize membership (`in`), subset (`subseteq`), empty, adjoin, and extend operations. This allows the same Hilbert system infrastructure to work with any context implementation.

Instances are provided for `Set`, `List`, `Multiset`, and `Finset`.

#### 2. Contextual Inference System

```lean
class ContextualInferenceSystem (S alpha beta : Type*) where
  derivation (Gamma : beta) (A : alpha) : Sort v
```

This generalizes the upstream `InferenceSystem S alpha` by adding an explicit context parameter `beta`. The notation `Gamma |- [S] A` is used.

#### 3. Structural Typeclasses

The file defines a rich hierarchy of structural properties as individual typeclasses:

| Typeclass | Meaning |
|-----------|---------|
| `HasAss` | Assumption rule: `A in Gamma -> Gamma |- A` |
| `HasWk` | Weakening: `Gamma subseteq Delta -> (Gamma |- A) -> Delta |- A` |
| `Extensional` | Context equivalence preserves derivability |
| `HasAddMP` | Additive modus ponens (same context) |
| `HasMultMP` | Multiplicative modus ponens (separate contexts, joined) |
| `Deductive` | Deduction theorem: `adjoin A Gamma |- B -> Gamma |- A -> B` |
| `HasCut` | Cut rule: `adjoin A Gamma |- B -> Delta |- A -> (Gamma join Delta) |- B` |
| `HasS` | S combinator axiom |
| `HasK` | K combinator axiom |
| `HasI` | I combinator axiom (derived from S+K) |
| `HasBotImpl` | Ex falso: `empty |- bot -> A` |
| `HasDNImpl` | Double negation elimination: `empty |- not not A -> A` |

#### 4. Concrete Hilbert Derivation: `axAssDer`

The concrete derivation is an inductive `axAssDer T Gamma A` with three constructors:
- `ax`: axiom from a set `T` of axiom formulas
- `ass`: assumption from context membership
- `mp`: modus ponens

This is parameterized over a `Set alpha` of axioms (not an inductive axiom predicate).

#### 5. Opaque Hilbert Tag

```lean
opaque Hilbert (T : Set alpha) : Type _ := T
```

The `Hilbert T` type serves as a proof system tag, with notation `H` followed by Gothic H. `ContextualInferenceSystem (H T) alpha beta` is instantiated to `axAssDer T`.

#### 6. Deduction Theorem via SKI Abstraction

The deduction theorem is proved by `axAssDer.absSK`, which performs SKI combinator abstraction on derivation trees. This requires `[HasS (H T) alpha beta]`, `[HasK (H T) alpha beta]`, and `[DecidableEq alpha]`.

#### 7. Connective Handling

Uses `HasImpl` (from `Operators/Impl.lean`), `HasNot` (from `Operators/Not.lean`), and `ImplNot` (connecting `not A = A -> bot`). The `HasImpl` class provides `impl` and overrides `->` notation. This is the **Operators/ approach** from PR #607 by Montesi.

#### 8. Equivalence Structure

Defines `ContextualInferenceSystem.Equivalence` as a structure with `fwd` and `bwd` derivations between singletons, with `symm`, `trans`, `mapConcl`, `mapHyp` operations.

### Key Theorems

- S + K implies I: `instance [HasS S alpha beta] [HasK S alpha beta] [HasAddMP S alpha beta] : HasI S alpha beta`
- Weakening implies Extensionality: automatic instance
- Additive MP + Weakening implies Multiplicative MP: automatic instance
- Deductive + Multiplicative MP implies Cut: automatic instance
- S + K + DecidableEq implies Deductive for Hilbert systems: `instance [HasS (H T)] [HasK (H T)] [DecidableEq alpha] : Deductive (H T)`
- HasDNImpl implies HasBotImpl (with ImplNot): proven
- Peirce's law derived from HasDNImpl: `HasDNImpl.pierce`

---

## Source 2: PR #648 (`feat/propositional-v2`)

### Location
`https://github.com/leanprover/cslib/pull/648`

### What It Changes (Relative to Upstream Main)

PR #648 is the first in a 9-PR roadmap contributing this fork's propositional logic foundations upstream. It introduces three files:

#### 1. New: `Cslib/Foundations/Logic/Connectives.lean`

Defines the connective typeclass hierarchy:
- **Atomic classes**: `HasBot`, `HasImp`, `HasAnd`, `HasOr`
- **Bundled class**: `PropositionalConnectives` (extends `HasBot`, `HasImp`)

This is **not** the same as Waring's `HasImpl`/`HasNot` from the Operators/ directory, nor the same as Montesi's PR #607 layout. Key differences from Waring:
- Uses `HasImp` with field name `imp`, not `HasImpl` with field name `impl`
- Uses `HasBot` rather than relying on Mathlib's `Bot`
- Does not define `HasNot` (negation is derived as `imp x bot`)
- Bundles into `PropositionalConnectives`, not individual classes only
- Also defines `HasAnd`, `HasOr` as standalone classes

#### 2. Modified: `Cslib/Logics/Propositional/Defs.lean`

Changes the `Proposition` type from 4 constructors `{atom, and, or, impl}` (with `bot` simulated via `[Bot Atom]`) to 5 constructors `{atom, bot, imp, and, or}`:
- `bot` becomes primitive (solves substitution, `Inhabited` problems)
- `impl` renamed to `imp` (consistency with Bimodal/Temporal formula types)
- Negation, verum, biconditional are derived `abbrev`s
- `PropositionalConnectives`, `HasAnd`, `HasOr` instances registered

#### 3. Modified: `NaturalDeduction/Basic.lean`

Adapts ND constructors to new naming (`implI` -> `impI`, `implE` -> `impE`, subscripts -> ASCII).

### Design Rationale Highlights

From the PR description:
- **Why primitive `bot`**: Substitution preserves `bot` by construction; `top` no longer depends on `Inhabited`; constraints removed from `neg`, `top`, `IPL`, `IsIntuitionistic`, `IsClassical`.
- **Why `imp` not `impl`**: Consistency with CSLib's existing convention (Bimodal, Temporal use `imp`).
- **Why `HasBot`/`HasImp` not Mathlib's `Bot`/`HImp`**: Mathlib's `Bot` and `HImp` use different field/notation conventions (`himp`, `==>`) that conflict with CSLib's `imp`/`->`.

### Relationship to Other PRs

- **PR #607** (Montesi): Introduces per-operator typeclass files under `Operators/`. Overlaps in propositional case. PR #648 can align with or subsume #607's propositional operators.
- **PR #536** (Waring): Refactors `IsClassical`/`IsIntuitionistic` to refer to inference systems. Conceptually independent.
- **PR #587** (Waring): Model/semantics typeclasses. Orthogonal (semantic vs syntactic).

---

## Source 3: This Fork's `Cslib/Logics/Propositional/`

### Location
`/home/benjamin/Projects/cslib/Cslib/Logics/Propositional/`

### Architecture

This fork extends PR #648's foundations with a complete two-layer proof system plus metalogic results. The full file tree:

```
Propositional/
  Defs.lean                     -- 5-primitive Proposition, Theory, MPL/IPL/CPL
  NaturalDeduction/
    Basic.lean                  -- ND derivation (10 constructors), equivalence
    DerivedRules.lean           -- Derived ND rules
    Equivalence.lean            -- ND <-> Hilbert bridge
    FromHilbert.lean            -- Hilbert -> ND translation
    HilbertDerivedRules.lean    -- ND -> Hilbert helpers
  ProofSystem/
    Axioms.lean                 -- 3 axiom inductives (Min/Int/Cl, 8/9/10 constructors)
    Derivation.lean             -- DerivationTree inductive (4 constructors)
    Instances.lean              -- ClassicalHilbert instance for HilbertCl tag
    IntMinInstances.lean        -- Int/Min Hilbert instances
  Metalogic/
    DeductionTheorem.lean       -- Deduction theorem (well-founded recursion)
    MCS.lean                    -- Maximal consistent sets
    MinSoundness.lean           -- Minimal logic soundness
    IntSoundness.lean           -- Intuitionistic soundness
    Soundness.lean              -- Classical soundness
    MinLindenbaum.lean          -- Minimal Lindenbaum's lemma
    IntLindenbaum.lean          -- Intuitionistic Lindenbaum
    MinStrongCompleteness.lean  -- Minimal strong completeness
    IntStrongCompleteness.lean  -- Intuitionistic strong completeness
    StrongCompleteness.lean     -- Classical strong completeness
  Semantics/
    Basic.lean                  -- Valuation-based semantics
    Kripke.lean                 -- Kripke frame semantics
    SemanticConsequence.lean    -- Semantic consequence
```

### Key Differences from Waring's Approach

| Aspect | This Fork | Waring's Classes.lean |
|--------|-----------|----------------------|
| **Context type** | Concrete `List` (Hilbert) / `Finset` (ND) | Abstract `Context alpha beta` typeclass |
| **Formula type** | Concrete `Proposition Atom` inductive | Abstract `alpha` with `HasImpl alpha` |
| **Axiom representation** | Inductive predicate `PropositionalAxiom : Proposition Atom -> Prop` | Set `T : Set alpha` of axiom formulas |
| **Derivation tree** | `DerivationTree Axioms Gamma phi` (4 constructors: ax, assumption, modus_ponens, weakening) | `axAssDer T Gamma A` (3 constructors: ax, ass, mp) |
| **Deduction theorem** | Well-founded recursion on `height` | SKI abstraction (`absSK`) |
| **Logic strength** | 3 separate axiom inductives (Min 8, Int 9, Cl 10 constructors) | Structural classes (`HasS`, `HasK`, `HasBotImpl`, `HasDNImpl`) |
| **Connective classes** | `HasBot`, `HasImp`, `HasAnd`, `HasOr` (Connectives.lean) | `HasImpl` (Operators/Impl.lean), `HasNot`, `ImplNot` |
| **Proof system tag** | `opaque Propositional.HilbertCl/Int/Min : Type := Empty` | `opaque Hilbert (T : Set alpha) : Type := T` |
| **Proof system hierarchy** | `MinimalHilbert`, `IntuitionisticHilbert`, `ClassicalHilbert` (ProofSystem.lean) | `HasS`, `HasK`, `HasBotImpl`, `HasDNImpl`, `Deductive` (individual) |
| **ND system** | Full 10-constructor ND derivation | Not present (Hilbert-only) |
| **Bridge** | Proven equivalence (Equivalence.lean) | Not applicable |
| **Semantics** | Valuation + Kripke, soundness, completeness | Not present |

### Connective Naming Comparison

| Concept | This Fork (Connectives.lean) | Waring (Operators/) | Upstream (pre-PR#648) |
|---------|------------------------------|--------------------|-----------------------|
| Implication class | `HasImp` | `HasImpl` | N/A |
| Implication field | `imp` | `impl` | N/A |
| Implication notation | `->` at priority 30 | `->` at priority 25 | Lean built-in |
| Bottom class | `HasBot` | uses Mathlib's `Bot` | N/A |
| Negation | Derived `abbrev` (`imp x bot`) | `HasNot` class + `ImplNot` bridge | N/A |
| And class | `HasAnd` | Not defined in Classes.lean | N/A |
| Or class | `HasOr` | Not defined in Classes.lean | N/A |

---

## Detailed Comparison

### 1. Overlap: Core Mathematical Content

All three implementations capture the same mathematical content for Hilbert systems:

- **K axiom**: `phi -> (psi -> phi)` -- present in all three
- **S axiom**: `(phi -> (psi -> chi)) -> ((phi -> psi) -> (phi -> chi))` -- present in all three
- **Modus ponens**: present in all three
- **Deduction theorem**: proven in Waring (SKI abstraction) and this fork (well-founded recursion)
- **Ex falso quodlibet**: `bot -> phi` -- in all three (Waring: `HasBotImpl`, this fork: `efq` axiom constructor, PR #648: theory-level `IPL`)
- **Peirce's law / DNE**: in Waring (`HasDNImpl.pierce`) and this fork (`peirce` axiom constructor)
- **Weakening**: in all three

### 2. Differences: Abstraction Level

**Waring** operates at the highest abstraction level:
- Context type is abstract (any `Context alpha beta` instance)
- Formula type is abstract (any `HasImpl alpha`)
- Proof system is abstract (any `ContextualInferenceSystem S alpha beta`)
- Results are maximally reusable across different logics

**This fork** operates at a middle abstraction level:
- Connective typeclasses (`HasBot`, `HasImp`, etc.) are polymorphic
- But the proof systems are concrete (built on `Proposition Atom`)
- The typeclass hierarchy (`MinimalHilbert`, etc.) provides polymorphic proof system interfaces
- Results can be instantiated for modal, temporal, bimodal logics via the typeclass hierarchy

**PR #648** is the minimal abstraction needed to upstream the connective typeclasses.

### 3. Differences: `HasImpl` vs `HasImp`

This is the most visible naming conflict:

- **Waring/Montesi (PR #607)**: `HasImpl` with field `impl`, from `Operators/Impl.lean`
- **This fork (PR #648)**: `HasImp` with field `imp`, from `Connectives.lean`

The PR #648 body explains the rationale: `imp` aligns with CSLib's existing constructor names in Bimodal and Temporal formula types, and matches the rule name prefix convention (`impI`/`impE`). Waring's `HasImpl` was originally authored by Montesi (PR #607) and uses `impl` to match the original `Proposition.impl` constructor name that PR #648 renames.

**Resolution**: If PR #648 merges, `HasImp`/`imp` becomes canonical. Waring's `HasImpl`/`impl` would need renaming to `HasImp`/`imp`. This is a straightforward search-and-replace.

### 4. Differences: Negation Handling

- **Waring**: `HasNot` typeclass with an independent `not` field, plus `ImplNot` bridge asserting `not A = (A -> bot)`. This allows logics where negation is not defined as `imp`-to-`bot`.
- **This fork**: Negation is always a derived `abbrev`: `neg A := imp A bot`. No `HasNot` typeclass.

Waring's approach is more general (supports negation-as-primitive logics like Nelson's N4). This fork's approach is simpler and sufficient for minimal, intuitionistic, and classical propositional logic.

### 5. Differences: Context Abstraction

- **Waring**: Abstract `Context` / `ExContext` typeclasses with instances for Set, List, Multiset, Finset. The multiplicative/additive MP distinction and the Cut rule are meaningful because contexts can be joined (`extend`/`join`).
- **This fork**: Concrete `List` for Hilbert derivation trees, `Finset` for ND derivations. The bridge between them uses `toList`/`toFinset` conversions.

Waring's approach is elegant and would be valuable for substructural logics (linear logic, relevant logic) where context manipulation matters. For propositional logic, the concrete approach is simpler.

### 6. Differences: Deduction Theorem Strategy

- **Waring**: SKI combinator abstraction (`absSK`). Requires `DecidableEq alpha` and `HasS`/`HasK` instances. More algebraic; directly constructs the term.
- **This fork**: Well-founded recursion on derivation tree height. Requires explicit `implyK`/`implyS` axiom witnesses. More traditional proof-theoretic approach.

Both are correct. The SKI approach is more modular (can work with any system that has S+K); the height-based approach is more explicit about the recursion structure.

### 7. Differences: Axiom Representation

- **Waring**: Axioms as an arbitrary `Set alpha`. No structure imposed on what axioms look like.
- **This fork**: Axioms as an inductive predicate `PropositionalAxiom : Proposition Atom -> Prop` with explicit constructors for each schema. Three levels: `MinPropAxiom` (8), `IntPropAxiom` (9), `PropositionalAxiom` (10).

Waring's approach is more general (can axiomatize anything). This fork's approach gives better pattern matching and automation.

### 8. Potential Conflicts

| Area | Conflict Level | Description |
|------|---------------|-------------|
| `HasImpl` vs `HasImp` | **Low** | Naming difference; resolvable by renaming |
| `HasNot` existence | **None** | Waring adds it; this fork omits it; both can coexist |
| `Context` abstraction | **None** | Waring adds it; this fork uses concrete types; no conflict |
| `ContextualInferenceSystem` vs `InferenceSystem` | **Medium** | Different abstraction; CIS adds context parameter. Would need alignment if both are in same project. |
| `axAssDer` vs `DerivationTree` | **Low** | Different inductive types for the same concept; can coexist under different namespaces |
| `Hilbert` tag vs `Propositional.HilbertCl` | **None** | Different namespaces and parametrization |
| Deduction theorem approach | **None** | Different proof strategies; both correct |
| Connectives.lean location | **Medium** | This fork: `Foundations/Logic/Connectives.lean`. Waring: `Foundations/Logic/Operators/*.lean` (per-file). |

### 9. What Each Adds That the Others Lack

**Waring only**:
- Abstract `Context`/`ExContext` typeclasses
- `ContextualInferenceSystem` (context-parameterized inference)
- Multiplicative vs additive MP distinction
- `HasCut` typeclass
- `Equivalence` structure with `mapConcl`/`mapHyp`/`trans`
- `HasNot` / `ImplNot` negation typeclasses
- SKI abstraction-based deduction theorem
- Support for substructural contexts

**This fork only**:
- Complete ND system (10-constructor `Theory.Derivation`)
- Three axiom hierarchies (Min/Int/Cl) as inductive predicates
- `DerivationTree` with height measure
- Proven ND-Hilbert equivalence (both directions)
- Kripke semantics + valuation semantics
- Soundness (3 strengths) and strong completeness (3 strengths)
- MCS construction
- `DerivationSystem` instance for generic MCS framework
- `HasAxiom*` typeclass hierarchy in `ProofSystem.lean`
- `PropositionalConnectives`, `ModalConnectives`, `TemporalConnectives`, `BimodalConnectives` bundled classes

**PR #648 only** (vs upstream):
- `Connectives.lean` with `HasBot`, `HasImp`, `HasAnd`, `HasOr`, `PropositionalConnectives`
- Five-primitive `Proposition` type
- Constraint-free derived connectives

---

## Recommendations for This Fork

### 1. No Action Needed for PR #648

PR #648 is a strict subset of this fork's development. It introduces the connective typeclasses and five-primitive Proposition type that are already present and working in this fork. The PR is correctly scoped and does not conflict with anything in the fork.

### 2. Monitor Waring's Classes.lean for Upstream Adoption

If Waring's `Hilbert/Classes.lean` or any descendant is merged into upstream CSLib, this fork would need to consider whether to:

**(a) Instantiate Waring's framework**: Define instances like `ContextualInferenceSystem (H T) (Proposition Atom) (List (Proposition Atom))` and show that the existing `DerivationTree` maps into `axAssDer`. This would make the fork's concrete results available through Waring's polymorphic API.

**(b) Replace the fork's Hilbert layer**: If Waring's framework becomes canonical, the fork could potentially replace `DerivationTree` and the `ProofSystem/` directory with instances of Waring's typeclasses. This would require reworking the deduction theorem, the ND-Hilbert bridge, and the metalogic chain.

**(c) Coexist**: Keep both layers. The fork's `Propositional.HilbertCl` tag and `DerivationTree` live in a different namespace and serve a different purpose (concrete proofs) from Waring's abstract framework (polymorphic infrastructure).

**Recommendation**: Option (c) in the short term. The fork's concrete results (completeness, soundness, MCS, equivalence) are valuable and should not be blocked on framework alignment. In the medium term, option (a) would be beneficial -- provide instances that bridge the fork's concrete types to Waring's abstract typeclasses.

### 3. Naming Alignment: `HasImp` is the Right Choice

If both PR #648 and Waring's work proceed toward upstream, the `HasImp`/`imp` naming from PR #648 should win because:
- It matches CSLib's existing convention across 4 formula types (Proposition, Modal, Temporal, Bimodal)
- Constructor names align with rule name prefixes (`impI`/`impE`)
- PR #648 explicitly documents the rationale with references

Waring's `HasImpl`/`impl` predates the rename and will need to follow.

### 4. Consider `HasNot` for Future Extension

Waring's `HasNot` and `ImplNot` typeclasses are not needed for classical/intuitionistic/minimal propositional logic (where negation is always `A -> bot`), but they would be useful for:
- Nelson's paraconsistent logic N4 (negation is primitive)
- Non-normal modal logics with independent negation
- Any logic where `not A` is not definitionally `A -> bot`

**Recommendation**: Do not add `HasNot` now, but keep it in mind for future extension. If CSLib formalizes paraconsistent or non-normal logics, a `HasNot` typeclass (under whatever naming convention is canonical) would be the right abstraction.

### 5. `ContextualInferenceSystem` is Valuable but Orthogonal

Waring's `ContextualInferenceSystem` adds explicit context parameters to the inference system typeclass. This is a genuine extension over the upstream `InferenceSystem` (which has no context parameter). It enables:
- The additive/multiplicative MP distinction
- Abstract cut rules
- Substructural logic support

**Recommendation**: This is worth tracking but not blocking on. The fork's concrete approach (List/Finset contexts) works well for propositional logic. If CSLib develops substructural logics, `ContextualInferenceSystem` would be the right abstraction. It does not conflict with anything in this fork.

### 6. PR Roadmap Remains Valid

The 9-PR roadmap described in PR #648 is not affected by Waring's work:
1. PR #648 (connectives + formula type) -- independent of Waring
2. PR 2 (Hilbert system) -- uses `DerivationTree`/`PropositionalAxiom`, not `axAssDer`/`Set alpha`
3. PR 3 (ND-Hilbert equivalence) -- specific to the fork's two-layer design
4. PRs 4-9 (semantics, completeness, tableaux) -- concrete results, no overlap with Waring

If Waring's framework is merged upstream before these PRs, the fork could optionally provide bridging instances (recommendation 2a above) but should not delay the roadmap.

---

## Summary Table

| Feature | Waring Classes.lean | PR #648 | This Fork |
|---------|-------------------|---------|-----------|
| Connective typeclasses | HasImpl (Operators/) | HasImp (Connectives.lean) | HasImp (Connectives.lean) |
| Context type | Abstract (Context typeclass) | Concrete (Finset) | Concrete (List + Finset) |
| Formula type | Abstract (alpha) | Concrete (Proposition Atom) | Concrete (Proposition Atom) |
| Hilbert derivation | axAssDer (3 constructors) | N/A | DerivationTree (4 constructors) |
| ND derivation | N/A | Theory.Derivation (10 ctors) | Theory.Derivation (10 ctors) |
| Deduction theorem | SKI abstraction | N/A | Well-founded recursion |
| Logic strengths | S/K/BotImpl/DNImpl | MPL/IPL/CPL (theory-level) | Min/Int/Cl (axiom inductive) |
| Proof system hierarchy | Individual typeclasses | N/A | MinimalHilbert -> IntuitionisticHilbert -> ClassicalHilbert |
| Semantics | N/A | N/A | Valuation + Kripke |
| Soundness/Completeness | N/A | N/A | 3 strengths each |
| ND-Hilbert bridge | N/A | N/A | Proven equivalence |
| Blocking conflicts | None | None | N/A |
