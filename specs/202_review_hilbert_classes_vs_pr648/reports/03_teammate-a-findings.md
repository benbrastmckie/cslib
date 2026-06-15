# Teammate A Findings: Analysis of the `Atom -> Prop` Design

**Task**: 202 - Review Hilbert Classes vs PR648
**Focus**: Rigorous analysis of the current `Atom -> Prop` approach and its downstream implications
**Files examined**: `Semantics/Basic.lean`, `Semantics/Kripke.lean`, `Semantics/SemanticConsequence.lean`,
  `Metalogic/Soundness.lean`, `Metalogic/StrongCompleteness.lean`, `Metalogic/IntSoundness.lean`,
  `Metalogic/IntStrongCompleteness.lean`, `Metalogic/IntLindenbaum.lean`, `Metalogic/MCS.lean`,
  `ProofSystem/Axioms.lean`, `NaturalDeduction/Basic.lean`, `Modal/Basic.lean`

---

## Key Findings

1. **`Atom -> Prop` is a deliberate architectural choice, not a convenience default.** The semantics
   layer uses `Atom -> Prop` for bivalent valuations (classical), world-indexed `World -> Atom -> Prop`
   for Kripke valuations (intuitionistic/minimal), and `World -> Atom -> Prop` for modal models.
   This uniform `Prop`-valued semantic domain is the same type across all three logic layers.

2. **The classical completeness proof requires `Classical.propDecidable` precisely because `Prop`
   is classical.** The `by_contra` strategy and `prop_negation_complete` lemma (which requires
   `φ ∈ S ∨ ¬φ ∈ S` for MCS `S`) both implicitly use excluded middle. An `Atom -> Bool` design
   would not require this -- it would push the "bivalence" burden onto `Bool`, but at the cost of
   separating the classical semantic domain from the intuitionistic/minimal semantic domain.

3. **The Kripke layer already uses `World -> Atom -> Prop` with no `Bool` anywhere.** Both
   `IForces` (intuitionistic) and `IValid`/`MValid` use `Prop`-valued world valuations. This
   means `Atom -> Bool` for the classical layer would introduce an architectural split: classical
   uses one type, constructive uses another.

4. **Switching to `Atom -> Bool` would break the canonical model construction.** The canonical
   valuation `canonicalValuation S := fun p => Proposition.atom p ∈ S` returns a `Valuation Atom`
   (i.e., `Atom -> Prop`). A `Bool`-valued canonical valuation requires decidability of set
   membership (`DecidablePred S`), which is unavailable for the general `Set (PL.Proposition Atom)`
   type. This is not merely a style issue -- it is a fundamental type-theoretic obstacle.

5. **The completeness proof uses `Evaluate v (¬φ) = True ↔ Evaluate v φ = False` implicitly.**
   In the `Prop` model, `Evaluate v (¬φ)` is `Evaluate v φ → False`, which is `¬(Evaluate v φ)`.
   The truth lemma for negation relies on `MCS negation completeness` and `⊥ ∉ S` -- both
   `Prop`-native arguments. In `Bool`, `¬ true = false` is structurally different and requires
   `Bool`-level negation reasoning with `decide` tactics.

6. **Lean 4's `Prop` is proof-irrelevant.** The canonical valuation `fun p => atom p ∈ S` is a
   `Prop`-valued function; proof terms are ignored. `Bool` would require a concrete choice of
   `true` or `false`, which introduces computable extraction obligations the completeness proof
   does not need.

7. **The modal and temporal logic layers in CSLib also use `World -> Atom -> Prop`.** Both
   `Modal.Model.v` and `Temporal.TemporalModel.valuation` and `Bimodal.TaskModel.valuation`
   are `World -> Atom -> Prop`. The propositional layer's `Atom -> Prop` is architecturally
   consistent as the "one-world" degenerate case of Kripke semantics.

---

## Technical Analysis

### 1. The `Valuation` Definition

```lean
-- Cslib/Logics/Propositional/Semantics/Basic.lean
abbrev Valuation (Atom : Type*) := Atom -> Prop
```

This is defined as an `abbrev`, meaning it is a transparent alias. The `Evaluate` function
recursively unfolds `Prop`-level connectives:

```lean
def Evaluate (v : Valuation Atom) : PL.Proposition Atom -> Prop
  | .atom x => v x
  | .bot    => False
  | .imp a b => Evaluate v a -> Evaluate v b
  | .and a b => Evaluate v a /\ Evaluate v b
  | .or  a b => Evaluate v a \/ Evaluate v b
```

The critical observation: `Evaluate v (imp a b) = (Evaluate v a -> Evaluate v b)` is a
_definitional equality_ in Lean 4, not a rewrite. This means proof terms for `Evaluate v (a -> b)`
are literally Lean function applications. This is the most natural embedding of propositional
logic into type theory -- the implication `->` in the object language maps to `->` in the
meta-language. This is the Curry-Howard correspondence at its purest.

By contrast, if `Valuation Atom := Atom -> Bool`, then `Evaluate v (imp a b)` would need to be
`(Evaluate v a == true) -> (Evaluate v b == true)` or `!Evaluate v a || Evaluate v b`, neither
of which is definitionally equal to Lean's `->`.

### 2. Classical Soundness and Peirce's Law

The classical soundness proof (`Metalogic/Soundness.lean`) handles the `peirce` axiom case:

```lean
| peirce φ ψ =>
    intro h; by_contra h_not
    exact h_not (h (fun h_phi => absurd h_phi h_not))
```

This `by_contra` works because the goal `Evaluate v φ` is a `Prop`, and `Classical.propDecidable`
is available. The proof that `((φ -> ψ) -> φ) -> φ` holds at the `Prop` level is essentially
proving that `Prop`-excluded middle validates Peirce's law. With `Bool`, this case would
become `decideAble` computation rather than a mathematical proof, losing the semantic connection
to why Peirce's law is classically valid.

### 3. The Canonical Model and the Truth Lemma

The strongest structural argument for `Atom -> Prop` comes from the canonical model construction:

```lean
-- canonicalValuation : Valuation Atom
def canonicalValuation (S : Set (PL.Proposition Atom)) : Valuation Atom :=
  fun p => Proposition.atom p ∈ S
```

This definition is **noncomputable by nature**: `S` is an abstract `Set (PL.Proposition Atom)`,
and membership in such a set is in general undecidable. The canonical valuation must be
`Prop`-valued precisely because it is defined by set membership. A `Bool`-valued alternative
would require `DecidablePred S`, which is unavailable for the abstract `Set` type.

The truth lemma then states: `Evaluate (canonicalValuation S) φ ↔ φ ∈ S`. In the `Prop` model,
this is a genuine iff between two `Prop`-valued assertions. In the `Bool` model, one side
would need to be `Evaluate v φ = true ↔ φ ∈ S`, which requires the additional `= true` coercion
and does not unfold as cleanly.

The `StrongCompleteness.lean` file contains:

```lean
attribute [local instance] Classical.propDecidable
```

This single line activates classical logic for the entire completeness proof. The `Bool` approach
would instead rely on decidability intrinsically, but the completeness argument works over
**arbitrary atom types** `{Atom : Type u}`, where there is no `DecidableEq Atom` assumed in
the semantics (only in `Defs.lean` for the syntax). The `Prop` model permits valuations over
non-decidable atom types.

### 4. Strong Completeness via Contrapositive

The strong completeness proof follows this structure:
1. Assume `¬ SetDerivable PropositionalAxiom Γ φ`
2. Construct `Γ ∪ {¬φ}` is consistent (`PropSetConsistent`)
3. Extend to MCS `M ⊇ Γ ∪ {¬φ}` via Lindenbaum
4. Use `prop_truth_lemma`: `Evaluate (canonicalValuation M) φ ↔ φ ∈ M`
5. Since `¬φ ∈ M`, truth lemma gives `Evaluate v (¬φ) = True`, so `Evaluate v φ = False`
6. All `ψ ∈ Γ` are in `M`, so truth lemma gives `Evaluate v ψ = True`
7. This contradicts `SemanticEntails Γ φ`

Step 5 is the critical step. In the `Prop` model, `Evaluate v (¬φ) = Evaluate v φ -> False`,
so obtaining `Evaluate v (¬φ)` from `¬φ ∈ M` and then applying it to `Evaluate v φ` is a
direct function application. In the `Bool` model, this step would require a Boolean negation
computation and a separate lemma `bool_neg_true_of_false` or similar.

### 5. Intuitionistic and Minimal Kripke Semantics: `World -> Atom -> Prop`

The Kripke layer does NOT use any Bool:

```lean
-- Kripke.lean
def IForces [Preorder World]
    (v : World -> Atom -> Prop) (bot_forces : World -> Prop)
    (w : World) : PL.Proposition Atom -> Prop
  | .atom p => v w p
  | .bot    => bot_forces w
  | .imp φ ψ => ∀ w', w ≤ w' -> IForces v bot_forces w' φ -> IForces v bot_forces w' ψ
  | ...
```

The forcing relation `IForces` is `World -> Atom -> Prop`-valued. The canonical world type
`IntCanonicalWorld Atom := {S : Set (PL.Proposition Atom) // IntPrimeDCCS S}` and the
canonical valuation:

```lean
def intCanonicalVal (w : IntCanonicalWorld Atom) (p : Atom) : Prop :=
  Proposition.atom p ∈ w.val
```

This is structurally identical to the classical case, with `Prop` membership. The architecture
is:
- Classical: `Valuation Atom := Atom -> Prop` (one-world Kripke model)
- Intuitionistic: `World -> Atom -> Prop` (general Kripke model)
- Minimal: `World -> Atom -> Prop` with arbitrary `bot_forces : World -> Prop`

The classical bivalent valuation is a **degenerate case** of the intuitionistic valuation with
`World = Unit`. This architectural unity is only possible with `Prop`.

### 6. Why `Atom -> Bool` Is Used in `BimodalCountermodelExtraction.lean`

The Bimodal decidability module uses `atomValuation : WorldIndex -> TimeIndex -> Atom -> Bool`
for countermodel extraction because that module is about **computational extraction** of
countermodels from tableaux. The `Bool` there represents a computed witness, not the semantic
domain of the logic itself. The semantic truth relation for that module still uses `Prop`:

```lean
-- BimodalCountermodelExtraction.lean
def CountermodelSatisfies ... : Formula Atom -> Prop
  | .atom p => cm.atomValuation w t p = true  -- Bool coerced to Prop via = true
```

This confirms the pattern: `Bool` is used only where computation matters, and the `Prop` wrapper
is still needed for the semantic relation.

---

## Evidence: Key Structural Connections

### Connection 1: `Prop` Enables Proof-Theoretic Identity

The deepest connection is that `Evaluate v φ : Prop` means:
- A proof of `Evaluate v (φ -> ψ)` is literally a Lean function `Evaluate v φ -> Evaluate v ψ`
- A proof of `Evaluate v (φ /\ ψ)` is literally a Lean pair `Evaluate v φ × Evaluate v ψ`
- A proof of `Evaluate v φ` for atomic `φ` is literally `v φ`

This definitional unfolding means that the soundness proof can use Lean's native `intro`,
`exact`, `constructor` tactics directly on semantic goals. With `Bool`, every step would need
a coercion layer (`= true` or `decide`), making proofs substantially more cumbersome.

### Connection 2: No `DecidableEq` Required for Semantics

The semantics layer has `variable {Atom : Type*}` (no `DecidableEq` assumption). The
`Defs.lean` file does have `variable {Atom : Type u} [DecidableEq Atom]`, but only because
the syntax (`inductive Proposition` with `deriving DecidableEq, BEq`) needs it. The semantics
is deliberately more general -- it works for any `Atom` type, including ones with no
decidable equality. A `Bool`-valued valuation would need `DecidableEq Atom` or some
decidable membership predicate.

### Connection 3: `Classical.propDecidable` Is Scoped

In `StrongCompleteness.lean` and `IntLindenbaum.lean`:
```lean
attribute [local instance] Classical.propDecidable
```
This is `local`, meaning classical logic is activated **only for the completeness proof files**.
The soundness proofs do not need it. This scoped use of classical logic is elegant: the semantic
domain is `Prop`, which is classically provable to be bivalent (every `Prop` is either true or
false), and the completeness proof exploits this. A `Bool` design would bake in bivalence at the
type level unconditionally, even for modules that don't need it.

---

## Mathematical Elegance Assessment

### Arguments for `Atom -> Prop` (Current Design)

1. **Curry-Howard correspondence**: The semantic evaluation of a formula is literally its
   Lean proof term. No translation layer needed.

2. **Uniform semantic domain**: Classical, intuitionistic, and minimal logic all use `Prop`-valued
   semantics. The classical case is the degenerate one-world Kripke model.

3. **Canonical model naturalness**: The canonical valuation `fun p => atom p ∈ S` is only
   definable as `Prop` for abstract sets.

4. **Generality**: Works for non-decidable atom types. Useful when `Atom` is an arbitrary type
   (e.g., natural numbers used as propositional variables in abstract metamathematics).

5. **Scoped classicality**: `Classical.propDecidable` is only needed locally in completeness
   proofs, not in the semantic definitions themselves.

6. **Mathematical literature alignment**: Standard mathematical logic (e.g., Chagrov-Zakharyaschev)
   uses set-theoretic valuations `v : Atom -> {0, 1}`, which corresponds precisely to
   `Atom -> Prop` (via `True = 1` and `False = 0`). Not `Bool` (which is a computational type).

### Arguments for `Atom -> Bool` (Harrison's Approach)

1. **Computation**: A `Bool`-valued evaluation function is computable. One can `#eval` specific
   valuations and check satisfiability by enumeration.

2. **DPLL connection**: DPLL and SAT solvers operate on Boolean values. A `Bool` model bridges
   directly to algorithm verification without coercion.

3. **Decidability**: For finite atom types, `Tautology φ` becomes decidable: `∀ v : Atom -> Bool, Evaluate v φ`. 
   With `Prop`, this is a `Prop`-valued universal statement that cannot be decided computationally.

4. **Harrison's book compatibility**: The port of Harrison's AIPLR book uses `Bool` models.

### The Mathematical Resolution

The two approaches target **different goals**:

- `Atom -> Prop` targets **mathematical elegance and proof-theoretic completeness** (proving
  that any semantic consequence is provable). It is ideal for the logic layer of a library
  that will extend to modal, temporal, and intuitionistic logics.

- `Atom -> Bool` targets **computational verification** (implementing DPLL, CNF transformation,
  SAT solving, and verifying algorithms). It is ideal for a library focused on decision procedures.

These goals are **not mutually exclusive** but serve different purposes. CSLib's current design
chooses the mathematical path, consistent with Chagrov-Zakharyaschev's treatment, Mathlib's
style, and the Kripke semantics already present for intuitionistic/minimal logic.

A coexistence design (both `Bool` and `Prop` models, with a bridge `evaluate_bool_iff_prop`) is
possible and would satisfy both constituencies, but the **primary semantic domain should remain
`Prop`** for the reasons above.

---

## Downstream Dependency Analysis

### Theorems that would break with `Atom -> Bool`

1. **`canonicalValuation`** - Cannot be `Bool`-valued for abstract `Set` types; needs
   `DecidablePred S`.

2. **`prop_truth_lemma`** - The iff `Evaluate (canonicalValuation S) φ ↔ φ ∈ S` works
   cleanly in `Prop`; in `Bool` it needs `= true` rewrites throughout.

3. **`prop_strong_completeness`** - The contrapositive argument uses `by_contra` at the
   `Prop` level. The `Bool` approach would need a different proof structure.

4. **`int_truth_lemma`** and **`int_strong_completeness`** - The intuitionistic canonical
   model uses `Prop` forcing (`IForces`); a `Bool` classical model would be structurally
   incompatible with the `Prop` Kripke model.

5. **`prop_axiom_sound` for `peirce`** - The proof `by by_contra h_not; exact h_not (h (fun h_phi => absurd h_phi h_not))` 
   is native `Prop` reasoning. With `Bool`, this becomes decidable computation, losing the
   proof-theoretic flavor.

### Theorems that would be enabled by `Atom -> Bool`

1. **Decidable `Tautology`** for finite atom types (decidability of propositional tautologies).

2. **Direct interface to DPLL**: Algorithm correctness proofs could use `Bool` models without
   coercion.

3. **`#eval` and `#decide`** for checking specific formulas.

---

## Confidence Level: High

The analysis is based on direct examination of 12 source files. The core claims are:

- **Confirmed** (direct evidence in code):
  - `Valuation Atom := Atom -> Prop` (Basic.lean line 33)
  - `canonicalValuation S := fun p => atom p ∈ S` returns `Atom -> Prop` (StrongCompleteness.lean line 74)
  - `attribute [local instance] Classical.propDecidable` scoped to completeness files (StrongCompleteness.lean line 65)
  - `IForces` uses `World -> Atom -> Prop` (Kripke.lean line 82)
  - `Modal.Model.v : World -> Atom -> Prop` (Modal/Basic.lean line 63)
  - `Temporal.TemporalModel.valuation : D -> Atom -> Prop` (Temporal/Semantics/Model.lean line 44)
  - Bimodal decidability uses `Atom -> Bool` only for computed countermodels (CountermodelExtraction.lean line 249)

- **Strongly inferred** (from code structure):
  - Switching to `Bool` breaks the canonical model construction for abstract sets
  - `Atom -> Prop` maintains uniformity with Kripke semantics layers

- **Mathematical claim** (standard result):
  - `Atom -> Prop` corresponds to set-theoretic truth-value assignments in classical model theory
  - `Bool` is a computational representation, not the standard mathematical one
