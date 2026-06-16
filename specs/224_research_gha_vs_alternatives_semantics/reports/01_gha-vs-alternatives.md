# Research Report: Task #224

**Task**: Research GHA vs alternatives for propositional semantics
**Date**: 2026-06-16
**Mode**: Single-agent research

## Summary

GeneralizedHeytingAlgebra (GHA) is the correct algebraic framework for CSLib's propositional
semantics, but it requires a `bot_val : H` parameter to handle the primitive `bot` constructor
in `PL.Proposition`. HeytingAlgebra is strictly too strong (it forces ex falso, ruling out
MPL), while BooleanAlgebra is only appropriate for CPL. The existing Prop-valued canonical
model construction in strong completeness is fully compatible with GHA semantics -- it is a
special case with `H = Prop`. The three-level hierarchy MPL/IPL/CPL maps cleanly onto
GHA/HeytingAlgebra/BooleanAlgebra with no workarounds.

## Key Findings

### 1. The Algebraic Hierarchy Maps Exactly to the Logic Hierarchy

**Confidence: HIGH**

The Mathlib typeclass chain `GeneralizedHeytingAlgebra < HeytingAlgebra < BooleanAlgebra`
corresponds precisely to the logic strength chain `MPL < IPL < CPL`:

| Logic | Algebra | Key Axiom | Mathlib Lemma |
|-------|---------|-----------|---------------|
| MPL (minimal) | `GeneralizedHeytingAlgebra` | No ex falso | `le_himp_iff` (deduction theorem) |
| IPL (intuitionistic) | `HeytingAlgebra` | `bot_le : ⊥ ≤ a` (ex falso) | `bot_himp : ⊥ ⇨ a = ⊤` |
| CPL (classical) | `BooleanAlgebra` | `compl_compl : aᶜᶜ = a` (DNE) | `compl_compl` |

GHA provides exactly the algebraic operations needed for the `{atom, bot, imp, and, or}`
signature:
- `⇨` (HImp) interprets implication
- `⊓` (inf) interprets conjunction
- `⊔` (sup) interprets disjunction
- `⊤` (top) is the truth value for validity

GHA does NOT provide `⊥`, which is the crux of the design question.

### 2. GHA Handles Primitive Bot Correctly via `bot_val` Parameter

**Confidence: HIGH**

Since `PL.Proposition` has a primitive `.bot` constructor but GHA has no canonical `⊥`,
the evaluation function must take a `bot_val : H` parameter:

```lean
def ghaEvaluate [GeneralizedHeytingAlgebra H] (v : Atom → H) (bot_val : H) :
    PL.Proposition Atom → H
  | .atom a => v a
  | .bot => bot_val
  | .imp φ ψ => ghaEvaluate v bot_val φ ⇨ ghaEvaluate v bot_val ψ
  | .and φ ψ => ghaEvaluate v bot_val φ ⊓ ghaEvaluate v bot_val ψ
  | .or φ ψ => ghaEvaluate v bot_val φ ⊔ ghaEvaluate v bot_val ψ
```

This is NOT a workaround -- it is the mathematically correct construction:

- **For MPL**: `bot_val` is an arbitrary element of `H`. The Lindenbaum-Tarski algebra of
  MPL has equivalence class `[⊥]` which is NOT the least element (no ex falso in MPL).
  Setting `bot_val = [⊥]` gives the correct evaluation.

- **For IPL**: Restrict to `HeytingAlgebra H` and set `bot_val = ⊥` (the algebra's bottom).
  The `bot_le` axiom then gives `⊥ ≤ a` for all `a`, which is ex falso. The Mathlib lemma
  `bot_himp : ⊥ ⇨ a = ⊤` confirms that `⊥ → A` evaluates to `⊤` (valid) -- precisely
  the EFQ axiom.

- **For CPL**: Restrict to `BooleanAlgebra H` with `bot_val = ⊥`. The `compl_compl` axiom
  gives double negation elimination.

Verified: both `ghaEvaluate` and the HeytingAlgebra specialization compile and satisfy
`haEvaluate v φ = ghaEvaluate v ⊥ φ` by a straightforward structural induction.

### 3. HeytingAlgebra Alone Is Insufficient

**Confidence: HIGH**

If the evaluation function is typed as:
```lean
def haEvaluate [HeytingAlgebra H] (v : Atom → H) : PL.Proposition Atom → H
  | .bot => ⊥  -- forced to use the algebra's least element
```

then `bot_himp : ⊥ ⇨ a = ⊤` forces ex falso quodlibet in every model. This makes
HeytingAlgebra semantics equivalent to IPL semantics -- MPL formulas that are not
IPL-valid will be incorrectly classified as invalid.

Concretely: `⊥ → p` is NOT valid in MPL (it is the ex falso axiom that distinguishes
IPL from MPL). But under HeytingAlgebra semantics, `haEvaluate v (⊥ → p) = ⊥ ⇨ v p = ⊤`
by `bot_himp`, so it would be classified as valid. This is wrong for MPL.

Since CSLib already has a fully proved `min_strong_completeness` for MPL with Kripke
semantics, the algebraic semantics must be compatible. HeytingAlgebra alone is not.

### 4. Thomaskwaring's PR #587 Design and Its Adaptation

**Confidence: HIGH**

In PR #587, thomaskwaring defines:
```lean
structure HeytingModel (Atom : Type*) where
  H : Type*
  [inst : GeneralizedHeytingAlgebra H]
  v : Atom → H

def HeytingModel.interp (M : HeytingModel Atom) : Proposition Atom → M.H
  | Proposition.atom x => M.v x
  | Proposition.and A B => M.interp A ⊓ M.interp B
  | Proposition.or A B => M.interp A ⊔ M.interp B
  | Proposition.impl A B => M.interp A ⇨ M.interp B
  -- NO bot case
```

This works because his `Proposition` type uses `{and, or, impl}` constructors with
bot encoded as an atom via `[Bot Atom]`. With that design, `interp (.atom ⊥) = v ⊥`,
which is an arbitrary element of `H` -- exactly the MPL-correct behavior.

**Adaptation for primitive bot**: With `PL.Proposition` having a `.bot` constructor, the
`HeytingModel` structure should be extended to include a `bot_val` field:

```lean
structure HeytingModel (Atom : Type*) where
  H : Type*
  [inst : GeneralizedHeytingAlgebra H]
  v : Atom → H
  bot_val : H  -- interpretation of the primitive bot constructor
```

Or equivalently, the valuation can be extended to cover bot as well as atoms,
using a sum type `Atom ⊕ Unit → H` or similar. The `bot_val` field approach is
more transparent and matches the existing `KripkeModel.botForces` pattern.

### 5. Compatibility with Existing Prop-Valued Semantics

**Confidence: HIGH**

The existing CSLib semantics files are all special cases of GHA evaluation:

| File | Target Type | GHA Instance | bot_val |
|------|-------------|--------------|---------|
| `Semantics/Basic.lean` (`Evaluate`) | `Prop` | `HeytingAlgebra Prop` | `False` (= `⊥` in Prop) |
| `Semantics/Bool.lean` (`BoolEvaluate`) | `Bool` | `BooleanAlgebra Bool` | `false` (= `⊥` in Bool) |
| `Semantics/Kripke.lean` (`IForces` intuitionistic) | `Prop` (pointwise) | `HeytingAlgebra Prop` | `False` |
| `Semantics/Kripke.lean` (`IForces` minimal) | `Prop` (pointwise) | `HeytingAlgebra Prop` | `bot_forces w` (arbitrary) |

The minimal Kripke case is revealing: `IForces v bot_forces w` maps `.bot` to
`bot_forces w`, which is an arbitrary `Prop`. This is structurally identical to
`ghaEvaluate v bot_val` with `H = Prop` and `bot_val = bot_forces w`. The existing
`minBotForces` (canonical model) sets `bot_val = (⊥ ∈ w.val)`, which is a genuine
`Prop` that is neither `True` nor `False` in general.

**Canonical model interaction**: The canonical model construction in
`MinStrongCompleteness.lean` uses `MinCanonicalWorld Atom = { S | MinPrimeTheory S }`
with:
- `minCanonicalVal w p = (atom p ∈ w.val)` -- Prop-valued
- `minBotForces w = (⊥ ∈ w.val)` -- Prop-valued, arbitrary

This is exactly `ghaEvaluate minCanonicalVal minBotForces` over `H = Prop`.
The truth lemma `min_truth_lemma` establishes `ghaEvaluate v b w φ ↔ φ ∈ w.val`,
where the bot case is `Iff.rfl` (since `bot_val = (⊥ ∈ w.val)` and the evaluation
of `.bot` is `(⊥ ∈ w.val)`).

No changes to the existing completeness proofs are needed. The GHA framework
subsumes them as instances.

### 6. Downstream Modal/Temporal/Bimodal Compatibility

**Confidence: HIGH**

All three downstream logics use Prop-valued semantics with `.bot => False`:

| Logic | Satisfies Definition | bot Interpretation |
|-------|---------------------|--------------------|
| Modal (`Modal.Satisfies`) | `\| .bot => False` | Always false (classical) |
| Temporal (`Temporal.Satisfies`) | `\| .bot => False` | Always false (classical) |
| Bimodal (`truthAt`) | `\| Formula.bot => False` | Always false (classical) |

These are all HeytingAlgebra semantics (or BooleanAlgebra, since they use classical
reasoning). They would instantiate as `ghaEvaluate v ⊥ φ` in the GHA framework.

The GHA framework does NOT require changes to any downstream logic. It provides
a more general algebraic semantics that the downstream Kripke semantics can invoke
when needed (e.g., for algebraic completeness proofs) but does not replace the
existing Kripke-style definitions.

### 7. Recommended API Design

**Confidence: MEDIUM-HIGH**

The semantics follow-up PR should provide three layers:

**Layer 1: GHA evaluation (most general)**
```lean
def Evaluate [GeneralizedHeytingAlgebra H] (v : Atom → H) (bot_val : H) :
    PL.Proposition Atom → H
```

**Layer 2: HeytingAlgebra evaluation (IPL specialization)**
```lean
def haEvaluate [HeytingAlgebra H] (v : Atom → H) : PL.Proposition Atom → H :=
  Evaluate v ⊥
```

**Layer 3: Classical instances**
```lean
-- Prop-valued (current Evaluate in Basic.lean)
-- Bool-valued (current BoolEvaluate in Bool.lean, via BooleanAlgebra Bool)
```

**Model structure** (compatible with thomaskwaring's PR #587 direction):
```lean
structure AlgebraicModel (Atom : Type*) where
  H : Type*
  [inst : GeneralizedHeytingAlgebra H]
  v : Atom → H
  bot_val : H
```

**Validity definitions**:
```lean
-- MPL algebraic validity
def GHAValid (φ : PL.Proposition Atom) : Prop :=
  ∀ (H : Type*) [GeneralizedHeytingAlgebra H] (v : Atom → H) (b : H),
    Evaluate v b φ = ⊤

-- IPL algebraic validity
def HAValid (φ : PL.Proposition Atom) : Prop :=
  ∀ (H : Type*) [HeytingAlgebra H] (v : Atom → H),
    Evaluate v ⊥ φ = ⊤

-- CPL algebraic validity (equiv to Tautology)
def BAValid (φ : PL.Proposition Atom) : Prop :=
  ∀ (H : Type*) [BooleanAlgebra H] (v : Atom → H),
    Evaluate v ⊥ φ = ⊤
```

The algebraic completeness theorems would then be:
- `GHAValid φ ↔ Derivable MinPropAxiom φ`
- `HAValid φ ↔ Derivable IntPropAxiom φ`
- `BAValid φ ↔ Derivable PropositionalAxiom φ`

### 8. Key Mathlib Lemmas for GHA Soundness Proofs

**Confidence: HIGH**

The following Mathlib lemmas in `Mathlib.Order.Heyting.Basic` provide the algebraic
counterparts of the propositional axioms:

| Axiom | Lean Name | Mathlib Lemma |
|-------|-----------|---------------|
| impI: `A → (B → A)` | `le_himp` via `inf_le_left` | `le_himp_iff.mpr inf_le_left` |
| impS: `(A→B→C)→(A→B)→(A→C)` | K combinator | `himp_himp` + `le_himp_iff` |
| Deduction theorem | currying | `himp_himp : a ⇨ b ⇨ c = a ⊓ b ⇨ c` |
| Identity: `A → A` | | `himp_self : a ⇨ a = ⊤` |
| Validity criterion | | `himp_eq_top_iff : a ⇨ b = ⊤ ↔ a ≤ b` |
| andI: `A → B → A ∧ B` | | `le_inf` |
| andE1: `A ∧ B → A` | | `inf_le_left` |
| andE2: `A ∧ B → B` | | `inf_le_right` |
| orI1: `A → A ∨ B` | | `le_sup_left` |
| orI2: `B → A ∨ B` | | `le_sup_right` |
| EFQ: `⊥ → A` (IPL only) | | `bot_himp : ⊥ ⇨ a = ⊤` |
| DNE: `¬¬A → A` (CPL only) | | `compl_compl` |

All lemmas verified to exist in the current Mathlib via `lean_loogle`.

## Tactic Survey Results

For GHA soundness proofs, the primary tactics would be:
- `simp` with `[himp_eq_top_iff, le_himp_iff, inf_le_left, inf_le_right, ...]`
- `exact le_himp_iff.mpr inf_le_left` (for impI)
- `exact himp_self` (for identity axiom)
- `calc` chains using `le_himp_iff` for more complex axioms

No novel tactics are needed; the Mathlib API for GHA/HA/BA is mature.

## Recommendation for Zulip Response Line 5

The current line 5 reads:

> @Thomas Waring I agree that GHA is the right approach for the semantics follow-up.
> One wrinkle: since `Proposition` now has a primitive `bot` constructor and GHA has no
> canonical `⊥`, we'll need either a `bot_val` field or an extended valuation -- curious
> how you'd handle that given your development.

This is accurate but could be sharpened. The research confirms that:

1. GHA IS the right approach (not just "I agree" -- the math proves it)
2. The `bot_val` parameter is not a "wrinkle" but the mathematically natural way to
   handle MPL over a formula type with primitive bot
3. `HeytingAlgebra` forces ex falso (via `bot_himp`), making it IPL-only
4. The existing Kripke semantics are compatible -- they are GHA instances

**Suggested revision for line 5**:

> @Thomas Waring Agreed that GHA is the right framework for the semantics follow-up.
> Since `Proposition` now has a primitive `bot` constructor and GHA has no canonical
> bottom element, the evaluation function takes a `bot_val : H` parameter (for MPL
> this is unconstrained; for IPL it specializes to `⊥` in a `HeytingAlgebra`).
> This matches the existing Kripke semantics where `bot_forces` is arbitrary for MPL
> and `fun _ => False` for IPL. Also, there's a naming conflict: this PR uses
> `HasImp`/`imp` but your #587 and fmontesi's #607 use `HasImpl`/`impl`, and both
> #648 and #587 create `Cslib/Foundations/Logic/Connectives.lean`. Would it make
> sense to open a joint design thread on that file before either PR proceeds?

## References

- Mathlib: `Mathlib.Order.Heyting.Basic` (GHA/HA definitions and lemmas)
- Mathlib: `Mathlib.Order.BooleanAlgebra.Defs` (BA definition)
- CSLib: `Cslib/Logics/Propositional/Semantics/Basic.lean` (current Prop-valued Evaluate)
- CSLib: `Cslib/Logics/Propositional/Semantics/Kripke.lean` (IForces with bot_forces)
- CSLib: `Cslib/Logics/Propositional/Metalogic/MinStrongCompleteness.lean` (MPL canonical model)
- CSLib: `Cslib/Logics/Propositional/Metalogic/IntStrongCompleteness.lean` (IPL canonical model)
- PR #587 (thomaskwaring): HeytingModel with GHA, no bot case (3-constructor formula)
- PR #607 (fmontesi): Logical operators with HasImpl naming
- PR #648 (benbrastmckie): 5-constructor formula with primitive bot
