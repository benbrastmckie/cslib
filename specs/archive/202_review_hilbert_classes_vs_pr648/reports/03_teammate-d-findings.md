# Teammate D (Horizons) Findings: DPLL Portability and Long-Term Valuation Architecture

**Role**: Horizons — strategic evaluation of long-term architecture direction
**Task**: 202 — Round 3: `Atom → Prop` vs `Atom → Bool`, DPLL portability, GeneralizedHeytingAlgebra
**Date**: 2026-06-15
**Session**: research phase

---

## Context and Question

Matthew Doty is asking about switching CSLib's propositional models from `Atom → Prop` to
`Atom → Bool` for DPLL portability. Thomas Waring suggests `GeneralizedHeytingAlgebra` for
soundness. Doty is pivoting to porting Harrison's Handbook of Practical Logic and Automated
Reasoning and proving DPLL works as a decision procedure. This is a new contributor bringing
an algorithm-first perspective into a library currently dominated by proof-theoretic
completeness results. This document assesses the architecture decision from the long-term
perspective.

---

## Key Findings

### 1. The Current `Atom → Prop` Design Is Deeply Load-Bearing

The current `Valuation (Atom : Type*) := Atom → Prop` definition in
`Cslib/Logics/Propositional/Semantics/Basic.lean` is not an arbitrary choice — it is
structurally entangled with the completeness infrastructure.

The canonical model construction in `StrongCompleteness.lean` defines:

```lean
def canonicalValuation (S : Set (PL.Proposition Atom)) : Valuation Atom :=
  fun p => Proposition.atom p ∈ S
```

This is a function into `Prop` because MCS membership is a `Prop`. The entire completeness
proof — Lindenbaum's lemma, the Truth Lemma, strong completeness — runs on this. If
`Valuation` were changed to `Atom → Bool`, the canonical valuation could not be defined
without first deciding MCS membership (which is computationally undecidable for general `Atom`
types, and decidability would need to come from somewhere).

**Bottom line**: Switching the global `Valuation` type alias from `Atom → Prop` to
`Atom → Bool` would break the canonical model construction in `StrongCompleteness.lean` and
all three completeness theorems (classical, intuitionistic, minimal). This is not a viable
path.

### 2. All Four Logic Levels Use `→ Prop` Valuations

Every semantics module in the current codebase uses a `Prop`-valued valuation:

| Module | Valuation type |
|--------|---------------|
| `PL.Semantics.Basic` | `abbrev Valuation (Atom) := Atom → Prop` |
| `Modal.Basic` | `v : World → Atom → Prop` (inside `Model` struct) |
| `Temporal.Semantics.Model` | `valuation : D → Atom → Prop` (inside `TemporalModel`) |
| `Bimodal.Semantics.TaskModel` | `valuation : ℱ.WorldState → Atom → Prop` (inside `TaskModel`) |

This is a library-wide convention: `→ Prop` is the language of semantic truth in CSLib.
Switching the propositional level alone would create an inconsistency with modal, temporal,
and bimodal levels that all share the same philosophical framework.

### 3. `Bool` Valuations Make Sense as a Separate Computational Layer

The `Atom → Bool` design is not wrong — it is appropriate for a *different purpose*:
computational evaluation, model checking, and SAT-solver implementation. Harrison's Handbook
treats valuations as `Atom → Bool` precisely because his goal is executable decision
procedures, not theoretical completeness proofs.

These two purposes are reconcilable via a coercion:

```lean
-- A Bool-valued valuation for computational purposes
abbrev BoolValuation (Atom : Type*) := Atom → Bool

-- Coerce to Prop-valued for theoretical purposes
def BoolValuation.toProp {Atom : Type*} (v : BoolValuation Atom) : Valuation Atom :=
  fun a => (v a = true)
```

This is a standard pattern in Lean 4/Mathlib: `Bool` and `Prop` are bridged via `= true`
and `Decidable` instances. The key theorem would be:

```lean
theorem Evaluate_BoolEval_agree (v : BoolValuation Atom) (φ : Proposition Atom) :
    Evaluate v.toProp φ ↔ (BoolEvaluate v φ = true) := ...
```

With this bridge, DPLL correctness can be stated as: the DPLL procedure returns `true` iff
the formula is satisfiable iff there exists a `Valuation Atom` that evaluates it to `Prop`-true.

### 4. Waring's `GeneralizedHeytingAlgebra` Suggestion Addresses a Different Level

Thomas Waring's suggestion of `GeneralizedHeytingAlgebra` for soundness operates at the
*semantic algebra* level, not the *valuation* level. The distinction matters:

- **Valuation level**: What the atoms map into (`Prop`, `Bool`, or a general algebra `α`)
- **Algebra level**: What algebraic structure the truth-value domain carries

A `GeneralizedHeytingAlgebra`-parameterized soundness theorem would say:

```lean
theorem gha_soundness {α : Type*} [GeneralizedHeytingAlgebra α]
    (v : Atom → α) (φ : Proposition Atom) :
    Derivable PropositionalAxiom φ → GHAEvaluate v φ = ⊤ := ...
```

This is the *algebraic completeness* direction, which is more general than bivalent soundness.
It instantiates to `Prop` (giving the current `prop_soundness`) and also to `Bool`, Heyting
algebras, etc. Waring's suggestion and Doty's request are thus *orthogonal* improvements that
both strengthen the library in different ways.

However, `GeneralizedHeytingAlgebra` soundness is non-trivial:

1. `Proposition` has five connectives but `GeneralizedHeytingAlgebra` only has `⊓`, `⊔`, `⇨`,
   `⊥`, `⊤` — the `or` connective maps to `⊔` which is not definable from `⇨` and `⊥` in a
   GHA alone (that requires Boolean algebra or a distributive lattice).
2. Intuitionistic logic soundness with respect to Heyting algebras IS a standard result
   (Algebraic Completeness Theorem), but it requires `HeytingAlgebra` not just `GHA`.
3. For classical propositional logic, `BooleanAlgebra` is the right algebraic structure.

**Assessment**: Waring is pointing toward a real architectural improvement. The right
framing is: "Make the semantic evaluation universe-polymorphic over a `HeytingAlgebra` (for
intuitionistic logic) or `BooleanAlgebra` (for classical logic)." This would subsume both
the `Prop` and `Bool` cases as instances.

### 5. How Modal Logic Would Behave with `Bool` Valuations

The modal semantics in `Modal.Basic` uses:

```lean
structure Model (World : Type*) (Atom : Type*) where
  r : World → World → Prop
  v : World → Atom → Prop
```

The accessibility relation `r` must remain `→ Prop` (it is not Boolean — no `Bool`-valued
function characterizes "accessible world" without losing the `exists w' such that...`
quantification in the satisfaction relation). The atom valuation `v : World → Atom → Prop`
could be generalized to `World → Atom → Bool` for computational modal model checking, but
for Kripke completeness proofs, the canonical model uses a `Set`-based valuation as in the
propositional case.

**Conclusion**: `Bool`-valued semantics for modal/temporal logic makes sense for *finite
model checking* (e.g., checking validity on a specified finite frame), but the canonical
completeness infrastructure requires `Prop`-valued semantics throughout. This is identical
to the propositional situation.

### 6. What Harrison Himself Would Advise

Harrison's Handbook (OCaml implementation) uses `Bool`-valued valuations throughout because:
- His goal is verified executable procedures (his "verification" is OCaml type-checking)
- His completeness theorems are stated with respect to `bool` evaluators
- He does not prove Lindenbaum's lemma or canonical model constructions — he proves DPLL
  termination and satisfiability equivalence

For CSLib's goals (Lean 4 formalization with fully proved soundness *and* completeness), the
appropriate strategy is **layered**:

1. **Theory layer** (`→ Prop`): all existing soundness/completeness infrastructure stays
2. **Computational layer** (`→ Bool`): new `BoolEvaluate` function + `BoolValuation`
3. **Bridge layer**: theorems connecting the two (correctness of `BoolEvaluate`, DPLL
   correctness stated as equivalence with `Tautology`)
4. **DPLL layer**: the DPLL algorithm itself, proved correct against the bridge

This is exactly the architecture used in Verified SAT-solver formalizations in Lean (e.g.,
`LeanSAT`) and in Isabelle/HOL verified SAT solver proofs.

### 7. The Collaborative Response Strategy

Doty is not asking for something incompatible with the current design. He is asking for the
computational layer that the current design naturally extends to. The ideal response is:

1. **Acknowledge the legitimate need**: DPLL requires decidable evaluation, which needs
   either `Bool`-valued semantics or a `Decidable` instance on `Prop`-valued evaluation
2. **Propose the layered design**: Not "instead of `Prop`" but "in addition to `Prop`"
3. **Offer a concrete interface**: Define `BoolEvaluate` and the bridge theorem; this is
   a small addition (~30 lines) that enables all of Doty's work without breaking anything
4. **Confirm Waring's direction is compatible**: `GeneralizedHeytingAlgebra`/`BooleanAlgebra`
   soundness would subsume both the current `Prop` soundness and the new `Bool` soundness

---

## Strategic Assessment

### Three Visions Are Complementary, Not Competing

| Contributor | Vision | Design Need | Layer |
|------------|---------|-------------|-------|
| This fork | Proof-theoretic completeness (canonical models, Lindenbaum) | `Atom → Prop` valuations | Theory |
| Doty | Computational decision procedures (DPLL, SAT) | `Atom → Bool` + decidable evaluation | Computation |
| Waring | Abstract algebraic soundness (GHA instantiations) | `Atom → α` for `[HeytingAlgebra α]` | Abstraction |

These three visions form a natural hierarchy: the computational layer is an instance of the
theory layer (via `Bool.toProp` coercion), and the theory layer is an instance of the
abstraction layer (via the `Prop.instHeytingAlgebra` Mathlib instance). Building all three
into CSLib creates a complete stack: abstract soundness → concrete Prop soundness →
computational Bool evaluation → DPLL decision procedure.

### The Immediate Technical Step Is Small

The change needed to support Doty's work without disrupting anything is minimal:

```lean
-- In a new file: Cslib/Logics/Propositional/Semantics/Bool.lean

/-- Bool-valued evaluation of propositions. -/
def BoolEvaluate (v : Atom → Bool) : Proposition Atom → Bool
  | .atom x => v x
  | .bot => false
  | .imp a b => !BoolEvaluate v a || BoolEvaluate v b
  | .and a b => BoolEvaluate v a && BoolEvaluate v b
  | .or a b => BoolEvaluate v a || BoolEvaluate v b

/-- Bool-valued evaluation agrees with Prop-valued evaluation. -/
theorem BoolEvaluate_iff_Evaluate (v : Atom → Bool) (φ : Proposition Atom) :
    BoolEvaluate v φ = true ↔ Evaluate (fun a => v a = true) φ := ...

/-- A formula is a tautology iff Bool-evaluation is always true. -/
def BoolTautology (φ : Proposition Atom) [Fintype Atom] : Bool :=
  ∀ v : Atom → Bool, BoolEvaluate v φ

theorem BoolTautology_iff_Tautology [Fintype Atom] (φ : Proposition Atom) :
    BoolTautology φ = true ↔ Tautology φ := ...
```

This adds ~50 lines and enables DPLL correctness proofs against `BoolEvaluate`.

### Long-Term Roadmap Integration

The ROADMAP.md currently lists the following remaining items:
- Discrete completeness (`Logics/Bimodal/Metalogic/`)
- Continuous extension completeness (`Logics/Bimodal/Metalogic/`)

A Harrison Handbook port would add at the propositional level:
- `BoolEvaluate` + bridge theorem
- DPLL as a decision procedure
- Proved correctness (`dpll_sound`: DPLL `true` → formula is satisfiable)
- Proved completeness (`dpll_complete`: formula is satisfiable → DPLL `true`)

This fits naturally as a `Logics/Propositional/Decidability/` module, parallel to the
existing `Logics/Bimodal/Metalogic/Decidability/` for bimodal logic. The CSLib roadmap
already demonstrates the decidability pattern; extending it to propositional logic is
coherent.

---

## Recommended Design Direction

### Tier 1: Do Not Change the Existing `Valuation` Definition

`abbrev Valuation (Atom : Type*) := Atom → Prop` must remain as-is. Changing it would break
three completeness theorems and the canonical model construction. This is non-negotiable.

### Tier 2: Add `BoolEvaluate` as a Parallel Computational Layer

Add a new file `Cslib/Logics/Propositional/Semantics/Bool.lean` (or extend the existing
`Basic.lean`) with:
1. `BoolEvaluate : (Atom → Bool) → Proposition Atom → Bool`
2. `BoolEvaluate_iff_Evaluate`: bridge theorem
3. `BoolTautology` and its equivalence with `Tautology` for `[Fintype Atom]`

This is the minimal change that unblocks Doty's DPLL formalization.

### Tier 3: Consider Algebra-Parameterized Soundness (Medium-Term)

Waring's direction: define `AlgEvaluate {α : Type*} [BooleanAlgebra α]` and prove algebraic
soundness. This subsumes both Tier 1 (`Prop`, via `Prop.instBooleanAlgebra`) and Tier 2
(`Bool`, via `Bool.instBooleanAlgebra`). This is a non-trivial PR in its own right but is
the architecturally cleanest outcome.

**For Zulip**: Respond to Doty with the Tier 2 proposal — a `BoolEvaluate` bridge — and
note that this keeps `Atom → Prop` as the canonical theoretical notion while giving him a
clean `Atom → Bool` layer for DPLL. Acknowledge Waring's direction as the long-term
abstraction goal. Frame the three contributions as three floors of the same building, not
as competing designs for the ground floor.

---

## Confidence Level

**High** on:
- The `Atom → Prop` definition being load-bearing for completeness proofs (confirmed by
  reading `StrongCompleteness.lean` and `canonicalValuation`)
- All four logic levels using `→ Prop` valuations (confirmed by reading each semantics file)
- The `BoolEvaluate` bridge being a small, non-breaking addition (standard Lean 4 pattern)
- The three visions being complementary (confirmed by analyzing the architectural levels)

**Medium** on:
- Whether Waring's `GeneralizedHeytingAlgebra` suggestion was specifically for soundness
  w.r.t. the formula language or for a different purpose (could not read the Zulip message)
- Whether Doty intends to contribute directly to CSLib or is asking as a design question
- Whether `BooleanAlgebra` (not GHA) is the right algebraic structure for classical PL
  soundness (this needs a formal check, but it is the standard result)

**Low** on:
- The exact scope of Doty's Harrison port (is it one PR or many?)
- Whether the CSLib maintainers would want `BoolEvaluate` in the same PR as PR #648 or as
  a follow-on PR

---

## Summary

The `Atom → Prop` design in PR #648 is correct and must not be changed. A `BoolEvaluate`
layer can be added alongside it to support DPLL/SAT work. Waring's algebra abstraction would
subsume both. These are three non-competing floors of a well-designed semantic tower:
abstract algebra at top, `Prop` semantics in the middle, `Bool` computation at the bottom.
The collaborative Zulip response should propose this three-tier design and invite all three
contributors to build their respective layers.
