# Teammate B Findings: Alternative Design Patterns for Propositional Logic (PR #648)

## Key Findings

1. **CSLib PR #648 implements a well-studied design pattern** -- the "one typeclass per operator" approach (following Montesi's PR #607 direction) -- that is a mainstream choice in formal logic libraries.

2. **Two major design traditions exist for Lean 4 propositional logic** and PR #648 chooses one explicitly: the *connective typeclass* tradition (polymorphic, per-operator) vs. the *Mathlib lattice/algebra* tradition (re-uses HeytingAlgebra/BooleanAlgebra). These are complementary, not competing.

3. **The concurrent Waring `Classes.lean` fork** shows a third option: maximally abstract context typeclasses (`ContextualInferenceSystem`) that generalizes beyond the PR #648 design. Waring's design is more general but requires more infrastructure; PR #648 is simpler and correctly scoped.

4. **Mathlib has no competing propositional logic proof system** at this level of formalization (named axioms, deduction theorem, soundness/completeness). Mathlib's `ITauto` is a decision procedure, not a foundational system. CSLib fills a real gap.

5. **The `HasBot`/`HasImp`/`HasAnd`/`HasOr` atomic typeclass approach is validated by Lean 4 best practice** for multi-operator structures: one class per operator, composed via `extends`. This is exactly how Mathlib structures `Lattice`, `SemilatticeSup`, `SemilatticeInf`, etc.

6. **The tag-type pattern** (`opaque Propositional.HilbertCl : Type := Empty`) is well-established in CSLib's existing modal/temporal/bimodal logic files and is the canonical way to identify proof systems without carrying instances.

---

## Alternative Design Patterns Found

### Pattern A: Lattice/Algebra Reuse (Mathlib Direction)

**What it would look like**: Define `Proposition Atom` and derive a `HeytingAlgebra` (or `BooleanAlgebra`) instance, then use Mathlib's `himp` (`⇨`) notation for implication.

**Mathlib availability**: `Prop.instHeytingAlgebra` (in `Mathlib.Order.Heyting.Basic`). The `HImp` typeclass uses field `himp` and notation `⇨`. A `GeneralizedHeytingAlgebra` provides `a ⇨ b` with `a ≤ himp b c ↔ a ⊓ b ≤ c`.

**Evidence**:
- `HeytingAlgebra` in `Mathlib.Order.Heyting.Basic` -- provides `himp : α → α → α` with `⇨` notation
- `Prop.instHeytingAlgebra` -- Mathlib already registers `Prop` itself as a Heyting algebra
- `BooleanAlgebra` extends this for classical logic

**Assessment**: This pattern works well for semantic models (e.g., a Kripke frame where worlds form a Heyting algebra) but is **not suitable for the proof-system layer**. The reasons are:
- `himp` notation (`⇨`) conflicts with CSLib's formula connective `→` at priority 30
- `HeytingAlgebra` requires a full order structure (`DistribLattice ⊓ BoundedOrder`), which `Proposition Atom` does not have by construction -- it's a free algebra, not a lattice
- The semantic models (Kripke frames, Boolean algebras) can still use `HeytingAlgebra`, independently of the syntactic connective hierarchy
- PR #648's `HasBot`/`HasImp` is precisely the *syntactic* half; `HeytingAlgebra` is the *semantic* half

**Verdict**: Complementary, not competing. PR #648 handles syntax; Mathlib's algebra handles semantics.

### Pattern B: Abstract Context Typeclasses (Waring's Classes.lean)

**What it would look like**: A `ContextualInferenceSystem (S alpha beta : Type*)` with explicit context parameter, plus abstract `Context`/`ExContext` typeclasses that admit List, Set, Finset, Multiset instances. Structural properties (`HasAss`, `HasWk`, `Extensional`, `HasAddMP`, `HasMultMP`, `Deductive`, `HasCut`) are separate typeclasses.

**Evidence from the codebase**: Thomas Waring's `cslib_SKI` fork (`thomaskwaring/cslib_SKI`, `hilbert` branch) contains `Cslib/Logics/Hilbert/Classes.lean` with this architecture. Key features:
- `class ContextualInferenceSystem (S alpha beta : Type*)` generalizes upstream `InferenceSystem S alpha` by adding context parameter
- Context instances for Set, List, Multiset, Finset
- Additive MP (same context) vs multiplicative MP (joined contexts) distinction
- Deduction theorem via SKI combinator abstraction (`axAssDer.absSK`)
- `opaque Hilbert (T : Set alpha) : Type := T` for proof system tags

**Key structural classes**:
```lean
class HasS (S alpha beta) -- S combinator axiom
class HasK (S alpha beta) -- K combinator axiom
class Deductive (S alpha beta) -- deduction theorem property
class HasCut (S alpha beta)  -- cut rule
class HasBotImpl (S alpha beta) -- ex falso
class HasDNImpl (S alpha beta)  -- double negation elimination
```

**Assessment**: More general than PR #648 in two ways:
1. Context abstraction handles substructural logics (linear, relevant) where multiplicative vs additive MP distinction matters
2. SKI-based deduction theorem is more modular (works for any `HasS`/`HasK` system)

However, this generality comes at the cost of complexity. For propositional logic specifically, the concrete `List`/`Finset` approach in PR #648 is simpler and sufficient. Waring's framework is a better fit for a future general infrastructure module if CSLib develops substructural logics.

**Verdict**: Valuable but orthogonal to PR #648's scope. The two approaches can coexist. PR #648's `InferenceSystem` could eventually be bridged to Waring's `ContextualInferenceSystem` via an instance.

### Pattern C: Single Axiom Predicate vs Inductive Hierarchy (Refinement)

**What it would look like**: Instead of three separate inductive types (`MinPropAxiom`, `IntPropAxiom`, `PropositionalAxiom`), use a single inductive axiom predicate parameterized over a "level" flag, or use a family of `Prop`-valued predicates defined by subset inclusion.

**Current CSLib approach**: Three inductives with explicit subsumption theorems:
- `MinPropAxiom` (8 constructors) -- minimal logic
- `IntPropAxiom` (9 constructors, adds EFQ)
- `PropositionalAxiom` (10 constructors, adds Peirce)
- `MinPropAxiom.toIntPropAxiom` and `IntPropAxiom.toPropAxiom` theorems

**Alternative**: A single parameterized inductive or set inclusion:
```lean
inductive AxiomLevel | Min | Int | Cl
def AxiomsAt : AxiomLevel → Proposition Atom → Prop
  | .Min => MinPropAxiom
  | .Int => IntPropAxiom
  | .Cl  => PropositionalAxiom
```

Or alternatively, use a set inclusion approach:
```lean
-- MinAxioms ⊂ IntAxioms ⊂ ClAxioms as sets of propositions
```

**Assessment**: The three-inductive approach in PR #648/Derivation.lean is clean and explicit. Pattern matching on constructors is direct and automation (simp, cases) works naturally. The "parameterized predicate" alternative would add indirection without benefit. The subset relationship is already captured by the subsumption theorems.

**Verdict**: The current three-inductive approach is correct and idiomatic for Lean 4. No change needed.

### Pattern D: Natural Deduction as Primary vs Hilbert as Primary

**What it would look like**: Make natural deduction (ND) the primary proof system and derive Hilbert provability as a defined notion, rather than the current two-layer approach where both exist independently.

**Current CSLib approach**: Two equal layers (ND in `NaturalDeduction/`, Hilbert in `ProofSystem/`) with proven equivalence (`NaturalDeduction/Equivalence.lean`).

**Alternative**: Use the 10-constructor ND derivation as the sole primitive and define Hilbert provability as:
```lean
def HilbertDerivable (φ : Proposition Atom) : Prop :=
  ∃ (D : Theory.Derivation MPL ∅ φ), D uses only specific rules
```

Or, conversely, use Hilbert derivation trees as the sole primitive and give ND as derived.

**Assessment**: The two-layer approach is more valuable because:
- ND is better for human reasoning (closer to mathematical practice)
- Hilbert is better for metalogic (deduction theorem, Lindenbaum construction)
- The bridge theorem (`Equivalence.lean`) is a non-trivial mathematical result worth formalizing
- Having both systems independently specified allows cross-validation

**Verdict**: The current two-layer design is the right architectural choice. It follows the standard proof theory textbook pattern (e.g., Troelstra-van Dalen Chapter 2 proves ND-Hilbert equivalence explicitly).

### Pattern E: `Set` vs `List` vs `Finset` for Contexts

**What it would look like**: Use `Set (Proposition Atom)` for contexts throughout (no finiteness requirement), allowing:
- Structural rules (contraction, exchange) for free via set membership
- Lindenbaum construction directly over subsets of the formula type

**Current CSLib approach**: `Finset` for ND contexts (in `NaturalDeduction/Basic.lean`), `List` for Hilbert derivation contexts (in `ProofSystem/Derivation.lean`), `Set` for theories and MCS.

**Assessment**: The current choice is well-motivated:
- `Finset` in ND gives decidable membership (needed for `impI` which adds/removes from context) and avoids explicit contraction/exchange rules
- `List` in Hilbert gives computable height (needed for well-founded induction in the deduction theorem)
- `Set` for theories allows uncountable axiom sets (needed for Lindenbaum)

The three different context types serve different algorithmic needs. This is the standard approach in formal logic formalizations.

**Verdict**: Current design is correct. No single context type would serve all three purposes as well.

---

## Best Practices Summary

### Lean 4 Best Practices for Logic Libraries

1. **One typeclass per operator, compose via `extends`**: Exactly what `HasBot`, `HasImp`, `HasAnd`, `HasOr` do. This follows Mathlib's lattice typeclass hierarchy exactly (cf. `SemilatticeSup` extends `Sup`, `SemilatticeInf` extends `Inf`).

2. **Opaque tag types for proof system identification**: The `opaque Propositional.HilbertCl : Type := Empty` pattern avoids cluttering instances with concrete types while allowing typeclass registration. This is a Lean 4 idiom used throughout CSLib's modal/bimodal/temporal logic.

3. **`Type` vs `Prop` for derivation trees**: Use `Type` (not `Prop`) for derivation trees when you need structural induction (height measure, computable functions). Wrap in `Nonempty` to get the `Prop` version. This is what both `Theory.Derivation` (ND) and `DerivationTree` (Hilbert) do.

4. **Derived connectives as `abbrev`s**: Negation, verum, biconditional defined as `abbrev`s (not `def`s) unfold transparently for the elaborator without explicit unfolding lemmas. This is correct Lean 4 practice for definitional equality purposes.

5. **Parameterize over axiom predicates, not axiom sets**: `DerivationTree (Axioms : Proposition Atom → Prop)` is more convenient than `DerivationTree (T : Set (Proposition Atom))` because inductive predicates support pattern matching, case analysis, and decision procedures more naturally.

6. **Separate connective interface from proof system interface**: `Connectives.lean` defines what connectives a type has; `ProofSystem.lean` defines what axioms a proof system proves. These are orthogonal concerns and should be separate files/typeclasses.

7. **`Finset` context for ND avoids structural rules**: Using `Finset` instead of `List` for ND contexts means contraction and exchange are automatic (set identity), reducing the number of constructors needed.

### Design Practices Validated by Prior Art

| Practice | Where Used | Validation |
|---------|------------|------------|
| Per-operator typeclasses | Mathlib's `Lattice` hierarchy, Montesi's PR #607 | Standard for composable algebraic structures |
| Inductive axiom predicate | CSLib Modal/Temporal/Bimodal, this PR | Pattern matches directly on axiom constructors |
| Tag-type proof system IDs | CSLib throughout (`Modal.HilbertK`, etc.) | Avoids instance pollution, supports multiple proof systems |
| Two-layer ND+Hilbert | Standard proof theory textbooks | Enables metalogic at multiple levels of abstraction |
| `Nonempty` wrapper for derivability | Throughout CSLib | Proof irrelevance where desired, computable where needed |
| Well-founded recursion for deduction theorem | This fork | Height measure is natural for tree induction |

---

## Recommended Approach

The current PR #648 architecture is well-designed and follows established Lean 4 best practices. Three specific recommendations for the PR review context:

### Recommendation 1: Keep `HasBot`/`HasImp` (Not Mathlib's `HImp`/`Bot`)

The PR correctly uses custom `HasBot`/`HasImp` rather than Mathlib's `Bot`/`HImp` (which uses `himp` field and `⇨` notation). The reasons given in the PR are valid:
- Mathlib's `HImp` is for Heyting algebras (order-theoretic structures), not free syntactic algebras
- The `⇨` notation at Mathlib's priority would conflict with CSLib's `→` for implications
- CSLib's multi-logic convention uses `bot`/`imp` field names consistently across all formula types

### Recommendation 2: Accept `HasAnd`/`HasOr` as Standalone Classes

The PR treats `HasAnd`/`HasOr` as standalone classes rather than bundling them into `PropositionalConnectives`. This is the right call because:
- Modal/Temporal/Bimodal formula types lack primitive `and`/`or` (they use Lukasiewicz encodings)
- Keeping `PropositionalConnectives` minimal (`HasBot + HasImp`) allows the class to apply to all formula types
- `HasAnd`/`HasOr` are added to `Proposition` via separate instances -- this is extensible without changing the core hierarchy

### Recommendation 3: The `PropositionalConnectives extends HasBot, HasImp` design correctly uses the minimal interface

The choice to have `PropositionalConnectives` extend only `HasBot` and `HasImp` (not `HasAnd`/`HasOr`) aligns with the Hilbert-system perspective where classical propositional logic can be axiomatized with just `{bot, imp}`. The `{and, or}` connectives are added for the five-primitive formula type to support natural deduction. This asymmetry is intentional and correct.

### Regarding the Zulip Reviewer Comment

Without seeing the specific Zulip comment content (it requires authentication), based on the PR structure the likely concerns would be:

1. **Naming: `HasImp` vs `HasImpl`** -- PR #648 correctly uses `HasImp`/`imp` for consistency with existing CSLib conventions. This naming should be adopted.

2. **Bundling strategy** -- The `PropositionalConnectives` minimal bundle is correct; `HasAnd`/`HasOr` as separate classes is better than forcing all formula types to have them.

3. **`HasBot` vs using Mathlib's `Bot`** -- Using a custom class is justified because Mathlib's `Bot` does not guarantee the same field naming convention.

4. **Separation of connectives from proof systems** -- The split between `Connectives.lean` and `ProofSystem.lean` is good architecture.

---

## Evidence / Examples

### Example 1: Mathlib's Lattice Pattern (Validates Per-Operator Typeclasses)

```lean
-- Mathlib structure: one class per operator
class Sup (α : Type u) where sup : α → α → α
class Inf (α : Type u) where inf : α → α → α
class SemilatticeSup extends Sup α, Preorder α
class SemilatticeInf extends Inf α, Preorder α
class Lattice extends SemilatticeSup α, SemilatticeInf α
```

CSLib's pattern mirrors this exactly:
```lean
class HasBot (F : Type*) where bot : F
class HasImp (F : Type*) where imp : F → F → F
class HasAnd (F : Type*) where and : F → F → F
class HasOr (F : Type*) where or : F → F → F
class PropositionalConnectives (F : Type*) extends HasBot F, HasImp F
```

### Example 2: `Prop.instHeytingAlgebra` Confirms Semantic/Syntactic Split

Mathlib registers `Prop` itself as a Heyting algebra (`Prop.instHeytingAlgebra`). This shows that `Prop` (the universe of propositions in Lean's type theory) can have algebra structure. But `PL.Proposition Atom` (the syntactic formula type) is a different kind of thing -- a free algebra, not a Heyting algebra. The CSLib connective typeclasses are for the *syntactic* level; Mathlib's algebra is for the *semantic* level.

### Example 3: `Theory.Derivation` Uses `Finset` Context (ND Best Practice)

The ND derivation in `NaturalDeduction/Basic.lean` uses `Ctx Atom := Finset (Proposition Atom)`:
- `impI` constructor: `Derivation (insert A Γ) B → Derivation Γ (A → B)` -- set insertion, no order issues
- `orE` constructor: uses `insert A G` and `insert B G` -- symmetric treatment
- No explicit weakening/contraction/exchange constructors needed

This confirms that `Finset` is the right context type for ND, matching standard Lean 4 practice.

### Example 4: Waring's `axAssDer` vs CSLib's `DerivationTree`

Both are 3-4 constructor Hilbert derivation trees. Waring:
```lean
inductive axAssDer (T : Set alpha) (Gamma : beta) (A : alpha) : Prop
  | ax : A ∈ T → axAssDer T Gamma A
  | ass : A ∈_ Gamma → axAssDer T Gamma A
  | mp : axAssDer T Gamma (impl B A) → axAssDer T Gamma B → axAssDer T Gamma A
```

CSLib:
```lean
inductive DerivationTree (Axioms : PL.Proposition Atom → Prop) :
    List (PL.Proposition Atom) → PL.Proposition Atom → Type _ where
  | ax ... | assumption ... | modus_ponens ... | weakening ...
```

Key difference: CSLib uses `Type` (not `Prop`) for the derivation tree, enabling computable height. CSLib also includes `weakening` as a primitive constructor (Waring derives it). CSLib uses an inductive predicate rather than a `Set`.

### Example 5: `module` Declaration in CSLib Files

All CSLib files in the Foundations/Logic hierarchy use the `module` keyword (lines 7-8 in each file). This is a CSLib-specific convention enforced by `checkInitImports`. PR #648 correctly follows this convention.

---

## Confidence Level

**High** for:
- The per-operator typeclass pattern being correct Lean 4 practice (validated by Mathlib)
- `HasBot`/`HasImp` naming being correct (validated by CSLib conventions across all formula types)
- `PropositionalConnectives` bundle being appropriately minimal (validated by modal/temporal need)
- Tag-type pattern for proof systems being canonical CSLib idiom
- Separation of connectives from proof systems being good architecture

**Medium** for:
- The specific Zulip reviewer concern (not seen directly; inferred from PR structure)
- Whether Waring's `ContextualInferenceSystem` would conflict if both are merged (depends on upstream decisions)
- Whether the three-inductive axiom hierarchy is the best long-term design vs a parameterized single inductive

**Low** for:
- Whether Mathlib may develop a competing propositional logic formalization that CSLib should align with (Mathlib currently has no such module)
- Future integration paths between CSLib's concrete proof systems and Waring's abstract framework
