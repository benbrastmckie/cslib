# Teammate B: Alternative Approaches for Temporal/Modal Refactoring

## Key Findings

1. **Massive code duplication**: Modal (~8k LOC), Temporal (~15k LOC), and Bimodal (~51k LOC) each define their own Formula inductive, derived connectives (neg, top, and, or), notation, BEq instances, DerivationTree, DeductionTheorem, MCS, Soundness, and Completeness. The derived connective definitions (`neg`, `top`, `and`, `or`) are **character-for-character identical** across all three formula types.

2. **The Isabelle AFP approach** (`Propositional_Logic_Class` by Doty 2022) uses a **class-based** (not locale-based) pattern: `implication_logic` parameterizes over a carrier type `'a`, a deduction predicate, and an implication operation, with axioms K, S, and modus ponens. `classical_logic` extends `implication_logic` by adding `falsum` and double negation. Derived connectives (conjunction, disjunction, negation) are **defined within the class** from implication + falsum. The key insight: all propositional metatheory (deduction theorem, MCS, completeness) is proved **once at the class level** and inherited by every instance.

3. **Three viable alternative approaches** exist for CSLib: (A) a parametric `FormulaFunctor`-based approach exploiting initial algebras, (B) a mixin-property-class approach mirroring Mathlib's algebraic hierarchy, and (C) an Isabelle-inspired class-based approach using `outParam`-keyed dependent typeclasses.

4. **Lean 4 typeclass resolution** differs critically from Isabelle's: Lean uses backtracking instance search with `outParam` for output-mode parameters, while Isabelle locales use explicit interpretation. This means diamond-free hierarchies matter more in Lean. CSLib's current `BimodalConnectives` already documents a diamond-avoidance choice (line 130 of Connectives.lean).

5. **The Foundations/Logic/Theorems/ layer** already demonstrates the target pattern: theorems like `box_mono`, `diamond_mono`, and all propositional combinators are proved generically over `[ModalHilbert S]` / `[TemporalBXHilbert S]` at the typeclass level. The refactoring question is how to **unify the per-logic Formula types** while preserving this generic theorem machinery.

---

## Prior Art Survey

### Isabelle AFP: Propositional_Logic_Class (Doty 2022)

**Architecture**: Five theory files organized as a class hierarchy:

```
implication_logic (axiom_k, axiom_s, modus_ponens)
  |
  +-- classical_logic (adds falsum, double_negation)
        |
        +-- consistent_classical_logic (adds consistency: not |- bot)
```

**Key design decisions**:
- Carrier type `'a` is fully abstract -- no concrete inductive formula type at the class level
- `deduction :: "'a => bool"` is a field (a derivability predicate), not computed from a tree
- `implication :: "'a => 'a => 'a"` is a field, enabling any connective encoding
- Derived connectives defined **within the locale**: `negation phi = phi -> falsum`, `conjunction phi psi = (phi -> psi -> falsum) -> falsum`
- All metatheory (list deduction, set deduction, MCS, Zorn extension) proved once at the `implication_logic` or `classical_logic` level
- Concrete `propositional_calculus` (an inductive type) shown to **instantiate** the class, then inherits all metatheory for free

**What translates to Lean 4**: The pattern of proving metatheory at the typeclass level and instantiating for concrete formulas translates directly. CSLib's `Foundations/Logic/Theorems/` already does this.

**What does NOT translate**: Isabelle locales support `interpretation` (renaming + instantiation) which Lean 4 typeclasses lack. Isabelle's `definition (in classical_logic)` syntax has no exact Lean analog; the closest is using `variable` sections with typeclass constraints.

### Mathlib Algebraic Hierarchy (Lean 4)

**Pattern**: Unbundled atomic classes + bundled composition classes + mixin properties.

```
Mul, Add, One, Zero          -- atomic operation classes
Semigroup extends Mul         -- bundled: operation + law
Monoid extends Semigroup, One -- bundled: more operations + laws
IsCancelMul [Mul G] : Prop   -- mixin property class
```

Key design principles (from `HierarchyDesign.lean`):
- **Extension over mixins** to avoid term-size blowup (Ralf Jung's 2019 analysis)
- New classes only when there is "real mathematics" or "meaningful gain in simplicity"
- Transfer instances (products, pi types, opposites, ulift) for each new class
- Avoid exponential explosion by not creating classes for every combination

**Relevance to CSLib**: CSLib's `HasBot`/`HasImp`/`HasBox` are already unbundled atomic classes. The `PropositionalConnectives`/`ModalConnectives`/`TemporalConnectives` are bundled composition classes. The Mathlib pattern validates this two-level design. The question is whether to also abstract over the **formula type** itself.

### Coq/MathComp Patterns

MathComp uses **packed classes** (canonical structures) rather than typeclasses for algebraic hierarchy. The `HB` (Hierarchy Builder) tool automates this. Relevant pattern: "factories" that allow declaring structures from different axiom sets that are then shown equivalent. This is analogous to having multiple ways to instantiate a logic class (e.g., from an axiom-based proof system or from a semantics-based one).

### Agda Formalized Logic Libraries

The `agda-stdlib` uses **record types** with fields for operations and laws, composed via record extension. The `agda-categories` library demonstrates a typeclass hierarchy for categorical structures. Modal/temporal logic formalizations in Agda (e.g., `agda-modal-logic` by Maggesi) typically use indexed inductive families rather than typeclasses.

---

## Alternative Approach 1: Parametric FormulaFunctor (Initial Algebra Pattern)

### Concept

Factor each formula type as the **fixed point of a functor** built from composable building blocks. Each "logic feature" (propositional, modal, temporal) is a functor that can be combined via coproducts.

### Code Sketch

```lean
-- Building blocks: each is a "feature functor" over a recursive parameter
inductive PropF (R : Type u) : Type u where
  | atom (p : Atom) | bot | imp (l r : R)

inductive BoxF (R : Type u) : Type u where
  | box (φ : R)

inductive UntilSinceF (R : Type u) : Type u where
  | untl (l r : R) | snce (l r : R)

-- Compose features via Sum
abbrev ModalFeatures (R : Type u) := PropF R ⊕ BoxF R
abbrev TemporalFeatures (R : Type u) := PropF R ⊕ UntilSinceF R
abbrev BimodalFeatures (R : Type u) := PropF R ⊕ BoxF R ⊕ UntilSinceF R

-- Fixed point (simplified; real version needs W-types or quotient)
inductive Fix (F : Type u -> Type u) : Type u where
  | mk : F (Fix F) -> Fix F

-- Each formula type is a fixed point
abbrev Modal.Formula' := Fix ModalFeatures
abbrev Temporal.Formula' := Fix TemporalFeatures
abbrev Bimodal.Formula' := Fix BimodalFeatures

-- Shared derived connectives: defined once for any F containing PropF
class HasPropLayer (F : Type u) where
  injProp : PropF F -> F

def neg' [HasPropLayer F] (φ : F) : F := HasPropLayer.injProp (.imp φ (HasPropLayer.injProp .bot))
def top' [HasPropLayer F] : F := HasPropLayer.injProp (.imp (HasPropLayer.injProp .bot) (HasPropLayer.injProp .bot))
```

### Pros
- **Zero duplication** for shared connectives (neg, top, and, or, iff) -- defined once
- **Principled composition**: adding a new connective layer (e.g., epistemic) requires only a new functor, not a new inductive type
- Embedding functions between formula types become **structural injections** (`inl`/`inr`), not recursive translations
- Pattern matching on the "propositional layer" works uniformly

### Cons
- **Lean 4 positivity checker** rejects `inductive Fix (F : Type -> Type)` directly; requires W-types or manual encoding with well-founded recursion, adding significant boilerplate
- **Pattern matching ergonomics** degrade: matching `Fix.mk (Sum.inl (PropF.imp a b))` is worse than matching `Formula.imp a b`
- **Notation** becomes complex: scoped notation must be defined per-composition, not per-feature
- **Performance**: extra indirection through `Fix`/`Sum` constructors may slow elaboration
- **Breaks existing API**: Every file referencing `Modal.Proposition.imp`, `Temporal.Formula.untl`, etc. must be rewritten
- **No prior art in Lean 4**: No existing Lean 4 library uses this pattern for a production hierarchy

### Verdict: HIGH RISK, HIGH REWARD if it worked. Lean 4's positivity checker and pattern matching limitations make this impractical without significant compiler support.

---

## Alternative Approach 2: Mixin Property Classes (Mathlib-Aligned)

### Concept

Keep concrete formula inductives but extract all **shared metatheory** into property-class mixins that can be instantiated by any formula type. The `Foundations/Logic/Theorems/` layer already does this partially; this approach completes the pattern by also factoring out the DerivationTree, DeductionTheorem, MCS, Soundness, and Completeness machinery.

### Code Sketch

```lean
-- Layer 0: Existing connective classes (unchanged)
-- HasBot, HasImp, HasBox, HasUntil, HasSince

-- Layer 1: Formula-level property classes (NEW)
-- A formula type "is propositional" if it has bot+imp and derived connectives unfold correctly
class IsPropositionalFormula (F : Type*) extends HasBot F, HasImp F where
  neg_def : forall (φ : F), neg φ = HasImp.imp φ HasBot.bot  -- if a `neg` abbrev exists
  top_def : top = HasImp.imp (HasBot.bot : F) HasBot.bot

class IsModalFormula (F : Type*) extends IsPropositionalFormula F, HasBox F where
  diamond_def : forall (φ : F), diamond φ = HasImp.imp (HasBox.box (HasImp.imp φ HasBot.bot)) HasBot.bot

class IsTemporalFormula (F : Type*) extends IsPropositionalFormula F, HasUntil F, HasSince F where
  someFuture_def : forall (φ : F), someFuture φ = HasUntil.untl φ top
  allFuture_def : forall (φ : F), allFuture φ = neg (someFuture (neg φ))

-- Layer 2: Generic DerivationTree (NEW)
-- Parameterize over an axiom predicate AND the formula type
inductive GenericDerivationTree {F : Type*} [HasImp F]
    (Axioms : F -> Prop) (Rules : List F -> F -> Prop) :
    List F -> F -> Type where
  | ax (Gamma : List F) (phi : F) : Axioms phi -> GenericDerivationTree Axioms Rules Gamma phi
  | assumption (Gamma : List F) (phi : F) : phi in Gamma -> GenericDerivationTree Axioms Rules Gamma phi
  | modus_ponens (Gamma : List F) (phi psi : F) :
      GenericDerivationTree Axioms Rules Gamma (HasImp.imp phi psi) ->
      GenericDerivationTree Axioms Rules Gamma phi ->
      GenericDerivationTree Axioms Rules Gamma psi
  | rule (Gamma : List F) (phi : F) : Rules Gamma phi -> GenericDerivationTree Axioms Rules Gamma phi
  | weakening (Gamma Delta : List F) (phi : F) :
      GenericDerivationTree Axioms Rules Gamma phi ->
      Gamma ⊆ Delta ->
      GenericDerivationTree Axioms Rules Delta phi

-- Layer 3: Generic Deduction Theorem (NEW)
-- Proved once for GenericDerivationTree, requires only HasImp + axiom_k + axiom_s
theorem generic_deduction_theorem {F : Type*} [HasImp F]
    {Axioms : F -> Prop} {Rules : List F -> F -> Prop}
    (h_k : forall phi psi, Axioms (HasImp.imp phi (HasImp.imp psi phi)))
    (h_s : forall phi psi chi, Axioms (HasImp.imp (HasImp.imp phi (HasImp.imp psi chi))
                                        (HasImp.imp (HasImp.imp phi psi) (HasImp.imp phi chi))))
    (h_rules_empty : forall phi, Rules [] phi -> GenericDerivationTree Axioms Rules [] phi)
    {A : F} {Gamma : List F} {B : F}
    (d : GenericDerivationTree Axioms Rules (A :: Gamma) B) :
    GenericDerivationTree Axioms Rules Gamma (HasImp.imp A B) := sorry -- proved by structural recursion

-- Instantiate for Modal:
abbrev Modal.DTree := GenericDerivationTree (F := Modal.Proposition Atom) Modal.KAxiom Modal.ModalRules
-- Instantiate for Temporal:
abbrev Temporal.DTree := GenericDerivationTree (F := Temporal.Formula Atom) Temporal.BXAxiom Temporal.TempRules
```

### Pros
- **Incremental adoption**: Can be introduced alongside existing code; migration is gradual
- **Preserves concrete formula types**: No change to `Modal.Proposition`, `Temporal.Formula`, `Bimodal.Formula`
- **Eliminates the biggest duplication**: DeductionTheorem (currently ~200 LOC each in Modal, Temporal, Bimodal) proved once
- **Mathlib-aligned pattern**: Follows the property-class mixin pattern that Lean 4 is designed for
- **Notation preserved**: Each formula type keeps its own scoped notation
- **Type-level computation**: Lean 4's typeclass resolution handles the dispatch automatically

### Cons
- **Rules abstraction is tricky**: Modal has `necessitation`, Temporal has `temporal_necessitation + temporal_duality`, Bimodal has all three. The `Rules` predicate must be generic enough to cover all cases
- **Performance concern**: Additional typeclass layers may slow elaboration in large proof files
- **Does NOT eliminate Formula-level duplication**: `neg`, `top`, `and`, `or`, `iff` still defined per-type (but these are one-liners, so the cost is low)
- **Partial solution**: Addresses metatheory duplication but not formula construction duplication

### Verdict: MEDIUM RISK, MEDIUM-HIGH REWARD. Most practical path forward. Directly mirrors the Isabelle approach adapted to Lean 4's typeclass system.

---

## Alternative Approach 3: Isabelle-Inspired Dependent Typeclass Hierarchy

### Concept

Follow the Isabelle AFP `Propositional_Logic_Class` pattern more directly: define a typeclass hierarchy where the **formula type is a parameter** and the **derivability predicate** is a field, not computed from a concrete tree. This decouples metatheory from concrete syntax entirely.

### Code Sketch

```lean
-- The core pattern from Isabelle, translated to Lean 4:

/-- An implication logic: a type F with implication and a derivability predicate
    satisfying axiom K, axiom S, and modus ponens. -/
class ImplicationLogic (F : Type*) where
  imp : F -> F -> F
  deriv : F -> Prop
  axiom_k : forall (φ ψ : F), deriv (imp φ (imp ψ φ))
  axiom_s : forall (φ ψ χ : F), deriv (imp (imp φ (imp ψ χ)) (imp (imp φ ψ) (imp φ χ)))
  mp : forall {φ ψ : F}, deriv (imp φ ψ) -> deriv φ -> deriv ψ

/-- Classical logic: implication logic + falsum + double negation elimination. -/
class ClassicalLogic (F : Type*) extends ImplicationLogic F where
  bot : F
  dne : forall (φ : F), deriv (imp (imp (imp φ bot) bot) φ)

-- Derived connectives are definitions within the class
namespace ClassicalLogic
variable {F : Type*} [ClassicalLogic F]
def neg (φ : F) : F := ImplicationLogic.imp φ ClassicalLogic.bot
def top : F := ImplicationLogic.imp ClassicalLogic.bot ClassicalLogic.bot
def conj (φ ψ : F) : F := ImplicationLogic.imp (ImplicationLogic.imp φ (neg ψ)) ClassicalLogic.bot
def disj (φ ψ : F) : F := ImplicationLogic.imp (neg φ) ψ
end ClassicalLogic

/-- Normal modal logic: classical logic + box + necessitation + K axiom. -/
class NormalModalLogic (F : Type*) extends ClassicalLogic F where
  box : F -> F
  nec : forall {φ : F}, deriv φ -> deriv (box φ)
  axiom_K : forall (φ ψ : F), deriv (imp (box (imp φ ψ)) (imp (box φ) (box ψ)))

/-- S5 modal logic: normal modal logic + T + 4 + B. -/
class S5Logic (F : Type*) extends NormalModalLogic F where
  axiom_T : forall (φ : F), deriv (imp (box φ) φ)
  axiom_4 : forall (φ : F), deriv (imp (box φ) (box (box φ)))
  axiom_B : forall (φ : F), deriv (imp φ (box (NormalModalLogic.diamond φ)))

-- Now ALL propositional metatheory is proved ONCE at ImplicationLogic level:
namespace ImplicationLogic
variable {F : Type*} [ImplicationLogic F]

/-- List implication: Gamma :-> phi means phi1 -> phi2 -> ... -> phi. -/
def listImp : List F -> F -> F
  | [], φ => φ
  | ψ :: Ψ, φ => imp ψ (listImp Ψ φ)

/-- Context deduction: Gamma |- phi iff |- Gamma :-> phi. -/
def contextDeriv (Gamma : List F) (φ : F) : Prop := deriv (listImp Gamma φ)

/-- Deduction theorem. -/
theorem deduction_theorem {Gamma : List F} {A B : F} :
    contextDeriv (A :: Gamma) B <-> contextDeriv Gamma (imp A B) := by
  constructor
  · exact id  -- by definition of listImp
  · exact id

-- MCS theory, proved once:
def consistent (φ : F) (Gamma : Set F) : Prop :=
  not (exists Psi : List F, (forall x, x in Psi -> x in Gamma) /\ deriv (listImp Psi φ))

end ImplicationLogic
```

### Pros
- **Maximum code reuse**: Propositional metatheory (deduction theorem, consistency, MCS, Lindenbaum extension) proved ONCE at `ImplicationLogic` and inherited by all logics
- **Faithful to Isabelle pattern**: Direct translation of the AFP approach
- **Deduction theorem becomes trivial**: By defining `contextDeriv` via `listImp`, the deduction theorem is literally definitional equality
- **Clean modal extension**: Adding `box` + `nec` + axiom K gives a normal modal logic; adding temporal operators gives temporal logic
- **No formula type duplication**: Formula types can be concrete inductives that instantiate the class

### Cons
- **Derivability is a predicate, not a tree**: Loses the `Type`-valued `DerivationTree` that CSLib currently uses for pattern matching, height functions, and computable proof extraction. The `DerivableIn S φ` wrapper (`Nonempty (S downArrow φ)`) already exists, but many proofs rely on tree structure.
- **Lean 4 diamond problem**: The hierarchy `ClassicalLogic -> NormalModalLogic` and `ClassicalLogic -> TemporalLogic` both extend `ClassicalLogic`, creating a diamond when composing to `BimodalLogic`. Must be resolved carefully with `extends` vs field duplication.
- **Instance search depth**: Deep hierarchies (ImplicationLogic -> ClassicalLogic -> NormalModalLogic -> S5Logic -> BimodalS5TemporalLogic) may hit Lean 4's default instance search depth limit.
- **Breaks existing structure**: The current `InferenceSystem` + tag-type pattern (`Modal.HilbertK`) is different from this `deriv`-as-field pattern. Major refactoring needed.
- **Loss of proof-system polymorphism**: Currently, a formula type can have MULTIPLE proof systems (K, T, S4, S5) via different tag types. The class-based approach bakes the proof system into the type.

### Critical Issue: Proof System Polymorphism

CSLib's current design supports:
```lean
-- Same formula type, different proof systems
instance : InferenceSystem Modal.HilbertK (Modal.Proposition Atom) where ...
instance : InferenceSystem Modal.HilbertT (Modal.Proposition Atom) where ...
instance : InferenceSystem Modal.HilbertS5 (Modal.Proposition Atom) where ...
```

The Isabelle approach puts `deriv` as a field on the formula type, meaning `Modal.Proposition Atom` could only have ONE `ImplicationLogic` instance. To recover polymorphism, one must:
- Use a **tag type** as an additional parameter: `class ImplicationLogic (S : Type*) (F : Type*) where ...` (which is essentially what CSLib already does)
- Or use **type synonyms**: `abbrev KFormula := Modal.Proposition Atom` with different instances

**This means the pure Isabelle approach does not translate directly.** The CSLib design with tag types + `InferenceSystem` is already the correct Lean 4 adaptation of the Isabelle pattern.

### Verdict: MEDIUM-HIGH RISK. The pure version breaks proof-system polymorphism. The adapted version (with tag types) converges back to CSLib's existing `InferenceSystem` + `ProofSystem.lean` pattern, suggesting the refactoring target is Approach 2 (generalize the metatheory) rather than a wholesale redesign.

---

## Comparison Matrix

| Criterion | Approach 1: FormulaFunctor | Approach 2: Mixin Properties | Approach 3: Isabelle-Style Classes |
|---|---|---|---|
| **Formula duplication eliminated** | Yes (complete) | No (abbrevs stay) | Partial (instances needed) |
| **Metatheory duplication eliminated** | Yes | Yes (main win) | Yes (main win) |
| **Notation preserved** | Degraded | Preserved | Must be rebuilt |
| **Pattern matching ergonomics** | Significantly worse | Preserved | Preserved (if concrete types kept) |
| **Lean 4 compatibility** | Poor (positivity checker) | Excellent | Good (with diamond care) |
| **Incremental migration** | No (big bang) | Yes (gradual) | Partial |
| **Proof system polymorphism** | Preserved | Preserved | Lost (pure) / preserved (adapted) |
| **Breaks existing code** | ~100% of Modal/Temporal/Bimodal | ~20% (metatheory files) | ~60% of infrastructure |
| **Prior art in Lean 4** | None | Mathlib (extensive) | Isabelle AFP (needs adaptation) |
| **Risk level** | High | Medium | Medium-High |
| **Estimated effort** | 6+ months | 2-4 weeks | 2-3 months |

---

## Evidence/Examples

### Evidence of Duplication (quantified)

| Duplicated Component | Modal | Temporal | Bimodal | Savings if unified |
|---|---|---|---|---|
| neg/top/and/or/iff abbrevs | 5 defs | 5 defs | 5 defs | 10 defs eliminated |
| BEq reflexivity + lawfulness | ~60 LOC | ~60 LOC | ~60 LOC | ~120 LOC |
| DerivationTree inductive | ~30 LOC | ~30 LOC | ~40 LOC | ~60 LOC |
| height function + lemmas | ~30 LOC | ~30 LOC | ~30 LOC | ~60 LOC |
| Deriv/Derivable wrappers | ~20 LOC | ~20 LOC | ~20 LOC | ~40 LOC |
| DeductionTheorem | ~200 LOC | ~200 LOC | ~200 LOC | ~400 LOC |
| MCS infrastructure | ~100 LOC | ~100 LOC | ~100 LOC | ~200 LOC |
| **Total duplication** | | | | **~890 LOC** |

### Example: DeductionTheorem Could Be Generic

The Modal, Temporal, and Bimodal deduction theorems all follow the same structure:
1. Case on `DerivationTree` constructors
2. For `axiom`: apply K axiom to wrap in implication
3. For `assumption`: either identity (if the formula is the one being deducted) or K axiom
4. For `modus_ponens`: S combinator application
5. For `necessitation`/`temporal_necessitation`/`temporal_duality`: impossible (empty context required)
6. For `weakening`: recursive call with `removeAll`

The ONLY differences are:
- Which constructors exist (Modal lacks temporal_necessitation/duality, Bimodal has all three)
- Which formula type is used
- Which axiom names for K and S

A `GenericDerivationTree` with a `Rules` callback for the logic-specific rules would unify all three.

### Example: What the Isabelle Pattern Gets Right

The key insight from Doty's `Propositional_Logic_Class` is that `listImp` (list implication) makes the deduction theorem **trivially true by definition**:

```
contextDeriv (A :: Gamma) B
  = deriv (listImp (A :: Gamma) B)    -- by definition
  = deriv (imp A (listImp Gamma B))   -- by listImp unfolding
  = contextDeriv Gamma (imp A B)       -- by definition
```

This is a zero-cost abstraction. CSLib's current DerivationTree-based approach requires a ~200 LOC proof because the deduction hypothesis appears as a **constructor** rather than a **structural prefix**.

---

## Confidence Level: MEDIUM-HIGH

**Justification**:

- **High confidence** that Approach 2 (Mixin Properties) is the best path forward: it aligns with Mathlib patterns, preserves existing code, enables incremental migration, and addresses the most impactful duplication (metatheory, not formula definitions).

- **Medium confidence** on the specific `GenericDerivationTree` design: the `Rules` callback abstraction needs careful design to handle the varying rule sets (Modal has 1 extra rule, Temporal has 2, Bimodal has 3). The right level of abstraction may be a typeclass rather than a callback parameter.

- **High confidence** that Approach 1 (FormulaFunctor) is impractical in current Lean 4 without significant workarounds for the positivity checker.

- **High confidence** that the pure Isabelle Approach 3 does not translate to Lean 4 because it loses proof-system polymorphism. The adapted version (with tag types) converges to the existing CSLib pattern, suggesting the real win is at the metatheory level (Approach 2), not the type-hierarchy level.

**Recommendation**: Pursue Approach 2 with the following priority order:
1. **Phase 1**: Generic `DeductionTheorem` and `MCS` infrastructure in `Foundations/Logic/Metalogic/`
2. **Phase 2**: Generic `DerivationTree` in `Foundations/Logic/` with a `Rules` typeclass
3. **Phase 3**: Generic `Soundness` theorem parameterized over semantics
4. **Phase 4**: Consider whether formula-level deduplication (derived connectives, BEq) is worth the complexity cost
