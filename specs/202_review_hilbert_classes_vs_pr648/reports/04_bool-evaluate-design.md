# BoolEvaluate Design Report

## 1. Current State of `Evaluate`

**File**: `Cslib/Logics/Propositional/Semantics/Basic.lean`
**Namespace**: `Cslib.Logic.PL`
**Type**: `def Evaluate (v : Valuation Atom) : PL.Proposition Atom → Prop`

Where `Valuation Atom := Atom → Prop`.

Recursive cases:
- `.atom x => v x`
- `.bot => False`
- `.imp a b => Evaluate v a → Evaluate v b`
- `.and a b => Evaluate v a ∧ Evaluate v b`
- `.or a b => Evaluate v a ∨ Evaluate v b`

Companion `@[simp]` lemmas exist for each case (`Evaluate_atom`, `Evaluate_bot`, `Evaluate_imp`,
`Evaluate_and`, `Evaluate_or`). `Tautology φ := ∀ v, Evaluate v φ` is also defined here.

## 2. BoolEvaluate Definition

### Recommended Type

```lean
abbrev BoolValuation (Atom : Type*) := Atom → Bool

def BoolEvaluate (v : BoolValuation Atom) : PL.Proposition Atom → Bool
  | .atom x => v x
  | .bot => false
  | .imp a b => !BoolEvaluate v a || BoolEvaluate v b
  | .and a b => BoolEvaluate v a && BoolEvaluate v b
  | .or a b => BoolEvaluate v a || BoolEvaluate v b
```

### Why `!a || b` for `imp`

The classical material conditional `a → b` is equivalent to `¬a ∨ b`. In Boolean algebra,
`!a || b` is the standard encoding. Alternatives considered:

- `bne a false || b` -- overly complex, non-idiomatic
- `if a then b else true` -- correct but less recognizable
- `!a || b` -- **chosen**: idiomatic, matches standard Boolean logic, standard Lean 4 notation

### Companion `@[simp]` Lemmas

Following the pattern of `Evaluate`, five `@[simp]` lemmas (all `rfl`):
- `BoolEvaluate_atom`, `BoolEvaluate_bot`, `BoolEvaluate_imp`, `BoolEvaluate_and`, `BoolEvaluate_or`

## 3. File Location

**Recommendation: New file `Cslib/Logics/Propositional/Semantics/Bool.lean`**

Rationale:
- `Basic.lean` is imported by 5 downstream files (Soundness, StrongCompleteness,
  SemanticConsequence, Modal/FromPropositional, Temporal/ConservativeExtension). Adding
  `BoolEvaluate` there would force all of them to carry the Bool machinery even when unused.
- A separate file keeps the Bool-related evaluation self-contained.
- Follows the existing pattern where `Kripke.lean` and `SemanticConsequence.lean` are
  separate files in the same directory.

**Import**: Only needs `Cslib.Logics.Propositional.Semantics.Basic` (no Mathlib imports beyond
what Basic already provides).

**CI requirement**: After creating the file, run `lake exe mk_all --module` to update `Cslib.lean`.

## 4. Bridge Lemma

### Statement

```lean
theorem BoolEvaluate_eq_iff (v : BoolValuation Atom) (φ : PL.Proposition Atom) :
    BoolEvaluate v φ = true ↔ Evaluate (fun a => v a = true) φ
```

### Proof (verified, compiles)

```lean
theorem BoolEvaluate_eq_iff (v : BoolValuation Atom) (φ : PL.Proposition Atom) :
    BoolEvaluate v φ = true ↔ Evaluate (fun a => v a = true) φ := by
  induction φ with
  | atom x => simp [BoolEvaluate, Evaluate]
  | bot => simp [BoolEvaluate, Evaluate]
  | imp a b iha ihb =>
    simp only [BoolEvaluate, Evaluate_imp, ← iha, ← ihb]
    cases BoolEvaluate v a <;> cases BoolEvaluate v b <;> simp
  | and a b iha ihb => simp [BoolEvaluate, Evaluate, iha, ihb]
  | or a b iha ihb => simp [BoolEvaluate, Evaluate, iha, ihb]
```

### Proof Difficulty Assessment

**Easy** -- the proof is 8 lines of tactic code. The key insight is the `imp` case:

- After rewriting with `iha` and `ihb`, the goal reduces to
  `(!a || b) = true ↔ (a = true → b = true)` where `a, b : Bool`.
- `cases ... <;> cases ... <;> simp` exhaustively handles all four `Bool` combinations.
- The `and` and `or` cases close automatically via `simp` with the induction hypotheses,
  using `Bool.and_eq_true_iff` and `Bool.or_eq_true_iff` (both in `Init.Data.Bool`).

No Mathlib lemmas beyond what is already transitively imported are needed.

## 5. Reuse Check

- **No existing `BoolEvaluate`**: `lean_local_search` for `BoolEvaluate` returns empty.
- **No existing Bool evaluation**: `grep` for `BoolEval`, `Bool.*Eval`, `Evaluate.*Bool` returns no results in the CSLib codebase.
- **No existing decidability infrastructure**: `grep` for `Decidable.*Evaluate` returns nothing.
- **Mathlib**: `Std.Tactic.BVDecide.Normalize.Bool.imp_to_or` provides
  `(a = true → b = true) = ((!a || b) = true)` but this is internal to BVDecide and not
  intended for external use. The proof strategy (`cases <;> simp`) is simpler anyway.

## 6. Additional Useful Lemmas (verified, all compile)

### Negation bridge

```lean
theorem BoolEvaluate_eq_false_iff (v : BoolValuation Atom) (φ : PL.Proposition Atom) :
    BoolEvaluate v φ = false ↔ ¬Evaluate (fun a => v a = true) φ := by
  rw [← BoolEvaluate_eq_iff]
  cases BoolEvaluate v φ <;> simp
```

### Factoring through Bool

```lean
theorem Evaluate_eq_BoolEvaluate (v : Valuation Atom) [∀ a, Decidable (v a)]
    (φ : PL.Proposition Atom) :
    Evaluate v φ ↔ BoolEvaluate (fun a => decide (v a)) φ = true := by
  rw [BoolEvaluate_eq_iff]
  induction φ with
  | atom x => simp [Evaluate, decide_eq_true_eq]
  | bot => simp [Evaluate]
  | imp a b iha ihb => simp [Evaluate, iha, ihb]
  | and a b iha ihb => simp [Evaluate, iha, ihb]
  | or a b iha ihb => simp [Evaluate, iha, ihb]
```

### Decidability instance

```lean
instance instDecidableBoolEvaluate (v : BoolValuation Atom) (φ : PL.Proposition Atom) :
    Decidable (Evaluate (fun a => v a = true) φ) :=
  decidable_of_iff _ (BoolEvaluate_eq_iff v φ)
```

## 7. Naming Conventions

Following CSLib patterns observed in `Semantics/Basic.lean`:
- **Definition names**: PascalCase (`BoolEvaluate`, not `boolEvaluate` or `Evaluate.bool`)
- **Companion simp lemmas**: `BoolEvaluate_atom`, `BoolEvaluate_bot`, etc. (matches `Evaluate_atom`, `Evaluate_bot`, etc.)
- **Bridge lemma**: `BoolEvaluate_eq_iff` (standard Lean/Mathlib `_iff` suffix for iff lemmas)
- **Type abbreviation**: `BoolValuation` parallels `Valuation`
- **Namespace**: `Cslib.Logic.PL` (same as `Evaluate`)
- **Docstring style**: Present tense, describes what the definition does, references related definitions

## 8. Complete Draft Implementation

```lean
/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Propositional.Semantics.Basic

/-! # Boolean Evaluation for Propositional Logic

This module defines a Boolean (computable) evaluation function for propositional logic,
mirroring the `Prop`-valued `Evaluate` from `Semantics.Basic`.

## Main Definitions

- `BoolValuation`: A Boolean propositional valuation assigns a `Bool` to each atom.
- `BoolEvaluate`: Evaluate a proposition under a Boolean valuation, returning `Bool`.
- `BoolEvaluate_eq_iff`: Bridge between `BoolEvaluate` and `Evaluate`.
- `instDecidableBoolEvaluate`: Decidability of `Evaluate` under Boolean valuations.

## Design Notes

`BoolEvaluate` uses `!a || b` for implication, matching the standard material conditional
in Boolean algebra. The bridge lemma `BoolEvaluate_eq_iff` relates `BoolEvaluate v φ = true`
to `Evaluate (fun a => v a = true) φ`, enabling decidable evaluation.

## References

* [A. Chagrov, M. Zakharyaschev, *Modal Logic*][ChagrovZakharyaschev1997], Section 1.2
-/

@[expose] public section

namespace Cslib.Logic.PL

variable {Atom : Type*}

/-- A Boolean propositional valuation assigns a `Bool` value to each atom. -/
abbrev BoolValuation (Atom : Type*) := Atom → Bool

/-- Boolean evaluation of a proposition under a Boolean valuation.

This mirrors `Evaluate`, using `Bool` instead of `Prop`. The key benefit is decidability:
`BoolEvaluate v φ` can be computed, while `Evaluate v φ` lives in `Prop`.
See `BoolEvaluate_eq_iff` for the bridge between the two. -/
def BoolEvaluate (v : BoolValuation Atom) : PL.Proposition Atom → Bool
  | .atom x => v x
  | .bot => false
  | .imp a b => !BoolEvaluate v a || BoolEvaluate v b
  | .and a b => BoolEvaluate v a && BoolEvaluate v b
  | .or a b => BoolEvaluate v a || BoolEvaluate v b

@[simp] theorem BoolEvaluate_atom (v : BoolValuation Atom) (x : Atom) :
    BoolEvaluate v (.atom x) = v x := rfl

@[simp] theorem BoolEvaluate_bot (v : BoolValuation Atom) :
    BoolEvaluate v (.bot) = false := rfl

@[simp] theorem BoolEvaluate_imp (v : BoolValuation Atom) (a b : PL.Proposition Atom) :
    BoolEvaluate v (.imp a b) = (!BoolEvaluate v a || BoolEvaluate v b) := rfl

@[simp] theorem BoolEvaluate_and (v : BoolValuation Atom) (a b : PL.Proposition Atom) :
    BoolEvaluate v (.and a b) = (BoolEvaluate v a && BoolEvaluate v b) := rfl

@[simp] theorem BoolEvaluate_or (v : BoolValuation Atom) (a b : PL.Proposition Atom) :
    BoolEvaluate v (.or a b) = (BoolEvaluate v a || BoolEvaluate v b) := rfl

/-- Bridge between Boolean and propositional evaluation: `BoolEvaluate v φ = true` if and
only if `Evaluate (fun a => v a = true) φ`.

The proof proceeds by structural induction on `φ`. The `imp` case requires case-splitting
on the Boolean values, since the translation of `!a || b = true` to `a = true → b = true`
is not automatic. -/
theorem BoolEvaluate_eq_iff (v : BoolValuation Atom) (φ : PL.Proposition Atom) :
    BoolEvaluate v φ = true ↔ Evaluate (fun a => v a = true) φ := by
  induction φ with
  | atom x => simp [BoolEvaluate, Evaluate]
  | bot => simp [BoolEvaluate, Evaluate]
  | imp a b iha ihb =>
    simp only [BoolEvaluate, Evaluate_imp, ← iha, ← ihb]
    cases BoolEvaluate v a <;> cases BoolEvaluate v b <;> simp
  | and a b iha ihb => simp [BoolEvaluate, Evaluate, iha, ihb]
  | or a b iha ihb => simp [BoolEvaluate, Evaluate, iha, ihb]

/-- Negation form of the bridge: `BoolEvaluate v φ = false` iff
`¬ Evaluate (fun a => v a = true) φ`. -/
theorem BoolEvaluate_eq_false_iff (v : BoolValuation Atom) (φ : PL.Proposition Atom) :
    BoolEvaluate v φ = false ↔ ¬Evaluate (fun a => v a = true) φ := by
  rw [← BoolEvaluate_eq_iff]
  cases BoolEvaluate v φ <;> simp

/-- Every propositional valuation with decidable atoms factors through Boolean evaluation. -/
theorem Evaluate_eq_BoolEvaluate (v : Valuation Atom) [∀ a, Decidable (v a)]
    (φ : PL.Proposition Atom) :
    Evaluate v φ ↔ BoolEvaluate (fun a => decide (v a)) φ = true := by
  rw [BoolEvaluate_eq_iff]
  induction φ with
  | atom x => simp [Evaluate, decide_eq_true_eq]
  | bot => simp [Evaluate]
  | imp a b iha ihb => simp [Evaluate, iha, ihb]
  | and a b iha ihb => simp [Evaluate, iha, ihb]
  | or a b iha ihb => simp [Evaluate, iha, ihb]

/-- Evaluation under a Boolean valuation is decidable. -/
instance instDecidableBoolEvaluate (v : BoolValuation Atom) (φ : PL.Proposition Atom) :
    Decidable (Evaluate (fun a => v a = true) φ) :=
  decidable_of_iff _ (BoolEvaluate_eq_iff v φ)

end Cslib.Logic.PL
```

## 9. Implementation Checklist

1. Create `Cslib/Logics/Propositional/Semantics/Bool.lean` with the code above
2. Run `lake exe mk_all --module` to add it to `Cslib.lean`
3. Run `lake build Cslib.Logics.Propositional.Semantics.Bool` to verify
4. Run full CI pipeline: `lake build`, `lake exe checkInitImports`, `lake exe lint-style`

## 10. Risk Assessment

**Zero sorry risk**: All proofs are complete and verified via `lean_run_code`.
**No new axioms**: Everything follows from structural induction and case analysis on `Bool`.
**No Mathlib dependencies beyond transitive**: Only `Init.Data.Bool` lemmas are used,
which are already available through the existing import chain.
**Backward compatible**: New file, no modifications to existing files.
