# Teammate B Findings (Round 3): Alternative Valuation Approaches

## Context

This report investigates: (1) the `Atom -> Bool` approach and its advantages for SAT/DPLL,
(2) the `GeneralizedHeytingAlgebra` suggestion from Thomas Waring, and (3) best practices
across Lean 4 projects, Harrison's handbook, and other proof assistants. It complements
Teammate A's codebase analysis by focusing on external evidence and alternative designs.

---

## Key Findings

### 1. Harrison's Handbook Uses `atom -> bool` -- in OCaml

Harrison's OCaml code (`prop.ml`) uses `atom -> bool` as the valuation type. The Haskell port
(`atp-haskell`) confirms: `eval :: JustPropositional pf => pf -> (AtomOf pf -> Bool) -> Bool`.
This is the computational, executable version appropriate for an ATP implementation textbook.

However, this is an OCaml/Haskell choice, not a Lean 4 choice. In those languages, `bool` and
propositional truth are isomorphic -- there is no distinction between `bool` and `Prop`. In Lean 4,
the choice between `Bool` and `Prop` carries real type-theoretic significance.

### 2. FormalizedFormalLogic (the largest Lean 4 logic project) Uses `atom -> Prop`

The Foundation project by the FormalizedFormalLogic team -- the most comprehensive Lean 4 logic
formalization -- defines its boolean/classical valuation as:

```lean
abbrev Boolean.Valuation (α : Type*) := α → Prop

def val (v : Valuation α) : Formula α → Prop
  | atom a  => v a
  | ⊥       => False
  | φ 🡒 ψ  => val v φ → val v ψ
  | φ ⋏ ψ  => val v φ ∧ val v ψ
  | φ ⋎ ψ  => val v φ ∨ val v ψ
```

This is identical to CSLib's current design (`Valuation := Atom → Prop`, `Evaluate` by recursion
into `Prop`). Foundation calls this "Boolean semantics" despite using `Prop` as the truth type.
This demonstrates that the `Atom -> Prop` choice is the standard in serious Lean 4 PL projects.

### 3. The `GeneralizedHeytingAlgebra` Suggestion Is Mis-Scoped

Thomas Waring suggested `GeneralizedHeytingAlgebra` for soundness proofs. Here is the actual
Mathlib hierarchy:

```
GeneralizedHeytingAlgebra
  -- lattice with top + heyting implication
  -- NO bottom element, NO negation
  extends: Lattice, OrderTop, HImp
  defining: a ≤ b ⇨ c ↔ a ⊓ b ≤ c

HeytingAlgebra extends GeneralizedHeytingAlgebra, OrderBot, Compl
  -- adds bottom + complement aᶜ = a ⇨ ⊥
  instances: Prop.instHeytingAlgebra, Pi.instHeytingAlgebra

BooleanAlgebra extends DistribLattice, Compl, SDiff, HImp, Top, Bot
  -- classical complement: a ⊓ aᶜ = ⊥ and a ⊔ aᶜ = ⊤
  instances: Prop.instBooleanAlgebra, Bool.instBooleanAlgebra
```

For classical propositional logic:
- `GeneralizedHeytingAlgebra` is too weak: lacks `⊥` and negation (needed for `efq`)
- `HeytingAlgebra` is the right algebraic structure for *intuitionistic* logic soundness
- `BooleanAlgebra` is the right algebraic structure for *classical* logic soundness

The FormalizedFormalLogic project uses exactly this: `HeytingAlgebra ℍ` for parameterized
evaluation in their `Heyting/Semantics.lean`:

```lean
def hVal {ℍ : Type*} [HeytingAlgebra ℍ] (v : α → ℍ) : Formula α → ℍ
  | atom a => v a
  | ⊥      => ⊥
  | φ ⋏ ψ  => φ.hVal v ⊓ ψ.hVal v
  | φ ⋎ ψ  => φ.hVal v ⊔ ψ.hVal v
  | φ 🡒 ψ  => φ.hVal v ⇨ ψ.hVal v
```

Waring's suggestion to use `GeneralizedHeytingAlgebra` would need to be `HeytingAlgebra` to
include `⊥` for `efq`, or `BooleanAlgebra` for classical logic.

### 4. Both `Bool` and `Prop` Are `BooleanAlgebra` Instances

Mathlib confirms:
- `Prop.instBooleanAlgebra : BooleanAlgebra Prop` (classical logic, uses `Classical.em`)
- `Bool.instBooleanAlgebra : BooleanAlgebra Bool`
- `Equiv.propEquivBool : Prop ≃ Bool` (the two are isomorphic!)

This means any parameterized valuation `Atom -> α` with `[BooleanAlgebra α]` subsumes both
`Atom -> Bool` and `Atom -> Prop` as special cases. Under classical axioms (`Classical.em`),
the two approaches are logically equivalent.

### 5. Mathlib's Own SAT Internal Uses `Nat -> Prop`, Not `Nat -> Bool`

The `Sat.Valuation` type in Mathlib (used in `Tactic.Sat.FromLRAT`) is defined as
`Nat -> Prop` (a list-backed `Prop`-valued function), not `Nat -> Bool`. Even Mathlib's
internal SAT tactic infrastructure avoids `Bool` in favor of `Prop`. This corroborates the
`Atom -> Prop` choice for proof-theoretic work.

### 6. `Atom -> Bool` Buys Computability -- At Real Costs

The genuine advantages of `Bool` over `Prop`:
- `Evaluate v φ` becomes a computable `Bool`-valued function, enabling the `decide` tactic
- Finite truth-table enumeration for small formulas
- Direct interoperability with `List.any`, `List.all`, decidable quantifiers over finite atoms

The real costs:
- Cannot use classical reasoning (em, by_contra) in proofs -- must remain constructive
- Every case distinction on `Evaluate v φ = true` vs `false` requires `if-then-else`
- Connector proofs (soundness) require `Bool.and_true`, `Bool.or_false` lemmas rather than
  natural `∧`/`∨` destructuring
- Interoperability with Lean 4's `Prop`-based logic system is indirect (via `Bool.decide_iff`)
- DPLL models produce `Atom -> Bool` assignments, but verifying them against `Evaluate` requires
  `bEq`/`decide` calls or explicit coercions

---

## Alternative Design Space

Four choices exist for the valuation codomain:

### Option 1: `Atom -> Prop` (Current CSLib)

```lean
abbrev Valuation (Atom : Type*) := Atom → Prop
def Evaluate (v : Valuation Atom) : PL.Proposition Atom → Prop
```

**Strengths:**
- Natural: evaluation is membership in Lean's logic system
- Proof-theoretic: soundness/completeness proofs use `intro`, `exact`, `cases` directly
- Compositional: `Evaluate v (imp a b) = Evaluate v a → Evaluate v b` computes definitionally
- Consistent with CSLib's modal semantics (`World -> Atom -> Prop` in `KripkeModel`)
- Consistent with FormalizedFormalLogic Foundation and Mathlib conventions
- Non-classical axioms (`by_contra`, `Classical.em`) available for classical soundness

**Weaknesses:**
- Cannot use `decide` or `#eval` to test tautologies on concrete atoms
- No direct computational extraction of models

**Best for:** Proof-theoretic formalization, soundness/completeness theorems.

### Option 2: `Atom -> Bool` (Harrison/DPLL approach)

```lean
abbrev Valuation (Atom : Type*) := Atom → Bool
def Evaluate (v : Valuation Atom) : PL.Proposition Atom → Bool
```

**Strengths:**
- Computable: `#eval tautology myFormula` just works
- Direct DPLL output format
- Decidable enumeration over finite atom types (`Fintype Atom` => decidable `∀ v, ...`)
- `decide` tactic on concrete closed formulas

**Weaknesses:**
- Boolean combinators (`&&`, `||`, `!`) vs logical connectives -- proofs become syntactically
  awkward (`Bool.and_comm`, `Bool.or_false` instead of `And.comm`, `Or.elim`)
- Soundness proof for Peirce's law requires `Bool.decide_iff`-style coercion
- Must define `BoolEvaluate` alongside `PropEvaluate` OR coerce using `decide` everywhere
- Breaks alignment with Kripke semantics (which must use `Prop` for world quantification)
- The two-valuation ecosystem becomes fragmented

**Best for:** Executable DPLL, model extraction, SAT preprocessing.

### Option 3: `Atom -> α` with `[BooleanAlgebra α]` (Unified classical)

```lean
def Evaluate [BooleanAlgebra α] (v : Atom → α) : PL.Proposition Atom → α
  | .atom x => v x
  | .bot => ⊥
  | .imp a b => Evaluate v a ⇨ Evaluate v b  -- heyting implication = ¬a ⊔ b
  | .and a b => Evaluate v a ⊓ Evaluate v b
  | .or a b  => Evaluate v a ⊔ Evaluate v b
```

**Strengths:**
- Subsumes both `Bool` and `Prop` as special cases
- Soundness theorem states: if `⊢ φ` then `Evaluate v φ = ⊤` for ALL `[BooleanAlgebra α]`
- Mathematically elegant: captures "truth in any two-element algebra"
- Immediately specializes to DPLL by choosing `α = Bool`

**Weaknesses:**
- `himp` (`⇨`) in `BooleanAlgebra` is defined as `b ⊔ ¬a` (classical), which is correct but
  expressed via lattice operations not implication -- proof aesthetics suffer
- More abstract: the current users (classical PL soundness) don't need the abstraction
- Interacts with `[Nontrivial α]` requirement (to avoid trivial single-element algebras)
- Overkill for a standalone classical PL module; appropriate for an algebraic completeness theorem

**Best for:** Algebraic completeness (Lindenbaum-Tarski style), unification of Bool/Prop, but
requires careful nontriviality handling.

### Option 4: `Atom -> α` with `[HeytingAlgebra α]` (Waring's actual suggestion, corrected)

```lean
def Evaluate [HeytingAlgebra α] (v : Atom → α) : PL.Proposition Atom → α
```

This is what FormalizedFormalLogic uses for *intuitionistic* soundness (see above). For
*classical* logic, `HeytingAlgebra` is insufficient because Peirce's law
(`((φ → ψ) → φ) → φ`) requires the law of excluded middle which doesn't hold in all Heyting
algebras. `BooleanAlgebra` is required for classical soundness.

**Best for:** Intuitionistic soundness only. Waring's suggestion is correct in spirit but
should be `HeytingAlgebra` (for the Int system) or `BooleanAlgebra` (for the Cl system),
not `GeneralizedHeytingAlgebra` (which lacks `⊥` needed for `efq`).

---

## Best Practices Summary

### From Proof Assistants Community

| System | Classical PL Valuation | Source |
|--------|----------------------|--------|
| Harrison OCaml | `atom -> bool` | Computational textbook |
| Isabelle/HOL | `'atom => bool` | Standard HOL typing |
| Coq | `Atom -> Prop` via `Classical` | Standard Coq approach |
| Lean 4 (leanprover-community) | `Prop` (semantics_of_PL) | Logic and Proof textbook |
| Lean 4 (FormalizedFormalLogic) | `α → Prop` as `Boolean.Valuation` | Foundation library |
| Lean 4 Mathlib SAT | `Nat -> Prop` via `Sat.Valuation` | Tactic.Sat.FromLRAT |
| CSLib current | `Atom → Prop` | Consistent with above |

The consensus in Lean 4 proof formalization is `Atom -> Prop`. The `Atom -> Bool` choice is
primarily for OCaml/Haskell ATP implementations or when executability is the primary goal.

### On the DPLL Use Case

Matthew Doty's concern about DPLL portability is legitimate but has an alternative solution:
**define DPLL with `Atom -> Bool` as a separate module that doesn't touch the semantic
`Evaluate` function.** The standard approach is:

```lean
-- Proof-theoretic module: Atom -> Prop
def Evaluate (v : Atom → Prop) : Proposition Atom → Prop := ...

-- DPLL module: Atom -> Bool, with a bridge lemma
def BoolEvaluate (v : Atom → Bool) : Proposition Atom → Bool := ...

theorem bool_eval_iff_prop_eval (v : Atom → Bool) (φ : Proposition Atom) :
    BoolEvaluate v φ = true ↔ Evaluate (fun a => v a = true) φ := by
  induction φ <;> simp [BoolEvaluate, Evaluate, *]
```

This gives the DPLL user `Atom -> Bool` without changing the core semantics. The bridge lemma
is straightforward and requires no sorry. Critically, `Prop ≃ Bool` (`Equiv.propEquivBool`)
confirms these are interchangeable under classical logic.

---

## Recommended Approach

For the PR #648 review response, the recommendation is:

**Keep `Atom -> Prop` for the core semantics. Add a separate `DecidableSemantics` or
`BoolSemantics` module with `Atom -> Bool` for DPLL users.**

Reasoning:
1. `Atom -> Prop` is the Lean 4 community standard (FormalizedFormalLogic, Mathlib, Logic and Proof)
2. Switching would break alignment with CSLib's Kripke semantics (`World -> Atom -> Prop`)
3. Soundness proofs are cleaner with `Prop` (use `by_contra`, `Classical.em` directly)
4. Switching would make the Lindenbaum-Tarski completeness proof harder (needs `Prop` for MCS)
5. The DPLL use case is better served by a dedicated `BoolSemantics` layer with a bridge lemma

For `GeneralizedHeytingAlgebra`: Waring's suggestion is mathematically interesting but
mis-scoped. The correct abstract soundness typeclass for classical PL is `BooleanAlgebra`
(both `Prop` and `Bool` are instances). For intuitionistic PL (the Int and Min systems),
`HeytingAlgebra` is the right abstraction, as demonstrated by FormalizedFormalLogic.

A future algebraic completeness module could add:
```lean
theorem algebraic_soundness [BooleanAlgebra α] [Nontrivial α] ...
```
This would be a separate module, not a replacement for the current `Atom -> Prop` semantics.

---

## Evidence Summary

| Claim | Evidence Source |
|-------|----------------|
| Harrison uses `atom -> bool` | Haskell ATP port docs: `eval :: pf -> (AtomOf pf -> Bool) -> Bool` |
| FormalizedFormalLogic uses `α → Prop` | Foundation/Propositional/Boolean/Basic.lean (direct source) |
| FormalizedFormalLogic uses `HeytingAlgebra` for Int soundness | Foundation/Propositional/Heyting/Semantics.lean (direct source) |
| Mathlib SAT uses `Nat -> Prop` | Mathlib/Tactic/Sat/FromLRAT.lean (`Sat.Valuation = List Prop` backed) |
| `BooleanAlgebra Prop` and `BooleanAlgebra Bool` both hold | `Prop.instBooleanAlgebra`, `Bool.instBooleanAlgebra` in Mathlib |
| `Prop ≃ Bool` (isomorphism) | `Equiv.propEquivBool` in Mathlib.Logic.Equiv.Defs |
| `GeneralizedHeytingAlgebra` lacks `⊥` | Mathlib class definition: no `OrderBot` in GHA |
| CSLib's Kripke uses `Prop` | Cslib/Logics/Propositional/Semantics/Kripke.lean |

---

## Confidence Level

**High confidence** on the factual claims (verified by direct source examination).

**Medium confidence** on the DPLL bridge approach (the approach is standard but CSLib has not
yet formalized DPLL, so exact integration details remain to be worked out).

**Observation**: The `GeneralizedHeytingAlgebra` suggestion from Waring appears to be a
reasonable algebraic intuition but the specific typeclass is incorrect for classical logic.
The right level would be `BooleanAlgebra` for Cl or `HeytingAlgebra` for Int/Min. Whether
to add such algebraic soundness is a scope decision, not a correctness issue with the current
`Atom -> Prop` approach.
