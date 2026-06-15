# Team Research Report: `Atom -> Bool` vs `Atom -> Prop` for Propositional Valuations

**Task**: 202 — Comprehensive review of cslib PR #648
**Date**: 2026-06-15
**Mode**: Team Research (4 teammates), Round 3
**Session**: sess_1781543759_497ab0

## Summary

This round addresses the actual Zulip reviewer comment from Matthew Doty, who asks whether CSLib's propositional models could switch from `Atom -> Prop` to `Atom -> Bool` for DPLL portability. Thomas Waring separately suggests `GeneralizedHeytingAlgebra` as the right generality for soundness.

**Unanimous conclusion across all four teammates**: `Atom -> Prop` must remain the primary semantic domain. Switching to `Atom -> Bool` would break the canonical model construction and all three completeness theorems. The correct response is to add a thin `BoolEvaluate` computational layer (~50 lines) alongside the existing semantics, with a bridge lemma connecting the two.

Waring's `GeneralizedHeytingAlgebra` suggestion names the wrong class — GHA lacks `⊥`. The correct algebraic generalization is `HeytingAlgebra` (intuitionistic) or `BooleanAlgebra` (classical).

---

## The Reviewer's Comment (Verbatim)

Matthew Doty on the CSLib Zulip (#Propositional Logic):

> I see that @Benjamin Brast-McKie's models are from Atom -> Prop; would it be possible to switch to Atom -> Bool? In my case, I'd argue Atom -> Bool will be more portable for implementing DPLL for finding models.

Doty has already implemented Tseitin transformation to CNF with `Atom -> Bool` semantics and wants to prove DPLL works as a decision procedure, following Harrison's Handbook of Practical Logic.

---

## Key Findings

### 1. `Atom -> Prop` Is Structurally Required for Completeness (HIGH confidence)

The canonical model construction in `StrongCompleteness.lean` defines:
```lean
canonicalValuation S := fun p => Proposition.atom p ∈ S
```
This maps atoms to set membership in a Maximally Consistent Set — which is inherently `Atom -> Prop` because `∈` on `Set` returns `Prop`. The MCS is built via Lindenbaum's lemma (using Zorn's lemma / `Classical.choice`), making membership computationally undecidable. There is no `DecidablePred` instance, so a `Bool`-valued canonical valuation is **type-theoretically impossible** without fundamentally restructuring the proof.

All three completeness theorems (classical, intuitionistic, minimal) depend on this construction. Changing `Valuation` from `Prop` to `Bool` would break them all.

### 2. Architectural Uniformity Across All Logic Levels (HIGH confidence)

Every semantics module in CSLib uses `→ Prop` valuations:

| Module | Valuation type |
|--------|---------------|
| Propositional `Semantics/Basic.lean` | `Atom → Prop` |
| Modal `Modal/Basic.lean` | `World → Atom → Prop` |
| Temporal `Temporal/Semantics/Model.lean` | `D → Atom → Prop` |
| Bimodal `Bimodal/Semantics/TaskModel.lean` | `WorldState → Atom → Prop` |

The propositional `Atom → Prop` is the one-world degenerate case of Kripke's `World → Atom → Prop`. Switching propositional to `Bool` would create an architectural split that destroys this uniformity.

### 3. Curry-Howard Correspondence Makes `Prop` Mathematically Natural (HIGH confidence)

With `Prop` valuations, `Evaluate v (a → b)` is definitionally equal to `Evaluate v a → Evaluate v b` — a proof of the semantic formula literally IS a Lean function. No coercion layer is needed. This is the Curry-Howard correspondence at its purest and is the standard approach in serious Lean 4 logic formalizations (confirmed by FormalizedFormalLogic's Foundation project, which uses the identical design).

### 4. `GeneralizedHeytingAlgebra` Is the Wrong Class (HIGH confidence)

All four teammates converged on this finding:
- **GHA** extends `Lattice`, `OrderTop`, `HImp` — it has `⊤` but **no** `⊥` and no negation
- CSLib's `Proposition` has a primitive `bot` constructor; `Evaluate v .bot` would have no image in a GHA
- The correct hierarchy:
  - `HeytingAlgebra` — for intuitionistic soundness (has both `⊤` and `⊥`, used by FormalizedFormalLogic)
  - `BooleanAlgebra` — for classical soundness (both `Prop` and `Bool` are instances)

Waring's suggestion points in a valid architectural direction (algebra-parameterized soundness) but names the wrong algebraic class.

### 5. The Answer Is "Both" — Add `BoolEvaluate` as a Separate Layer (UNANIMOUS)

All four teammates independently recommended the same solution: add a thin `BoolEvaluate` computational layer alongside the existing `Evaluate`:

```lean
-- New file: Semantics/Bool.lean (~50 lines)
def BoolEvaluate (v : Atom → Bool) : Proposition Atom → Bool
  | .atom x => v x
  | .bot    => false
  | .imp a b => !BoolEvaluate v a || BoolEvaluate v b
  | .and a b => BoolEvaluate v a && BoolEvaluate v b
  | .or  a b => BoolEvaluate v a || BoolEvaluate v b

-- Bridge lemma connecting the two
theorem BoolEvaluate_eq_iff (v : Atom → Bool) (φ : Proposition Atom) :
    BoolEvaluate v φ = true ↔ Evaluate (fun a => v a = true) φ := by
  induction φ <;> simp [BoolEvaluate, Evaluate, *]
```

This gives Doty everything he needs for DPLL:
- Computable `Bool`-valued evaluation for algorithms
- Bridge to the existing `Prop` metatheory for correctness proofs
- No changes to any existing file

### 6. Three-Tier Architecture Serves All Contributors (STRATEGIC)

The three contributors' visions form a natural stack:

| Tier | Contributor | Approach | Type |
|------|------------|----------|------|
| Top | Waring | Algebra-parameterized soundness | `Atom → α` where `[HeytingAlgebra α]` |
| Middle | This fork | Proof-theoretic completeness | `Atom → Prop` |
| Bottom | Doty | Computational DPLL/SAT | `Atom → Bool` |

These are three floors of the same building. Each tier instantiates the one above:
- `Bool` and `Prop` are both `BooleanAlgebra` instances
- `HeytingAlgebra` soundness subsumes both
- The bridge lemma connects computational and metatheoretic layers

---

## Synthesis

### Conflicts Resolved

No significant conflicts between teammates. All four independently reached the same core conclusion: keep `Atom -> Prop`, add `BoolEvaluate`. The main variance was in emphasis:
- A emphasized the Curry-Howard and proof-irrelevance properties
- B provided external validation (FormalizedFormalLogic, Harrison's actual approach)
- C identified that Doty's "portability" claim is about convenience, not mathematical substance
- D framed the three-tier architecture and collaborative response strategy

### Recommended Zulip Response

Based on the synthesis, the response to Doty should:

1. **Agree** that `Atom → Bool` is needed for DPLL — he's right about the use case
2. **Explain** why the core `Valuation` can't switch: the canonical model construction in strong completeness requires `Prop` (set membership in MCS)
3. **Propose** the `BoolEvaluate` bridge: a pure addition of ~50 lines that gives him computable Bool evaluation with a bridge lemma to the existing metatheory
4. **Correct** Waring's class suggestion: `HeytingAlgebra` (not `GeneralizedHeytingAlgebra`) for intuitionistic, `BooleanAlgebra` for classical
5. **Invite** collaboration: Doty builds DPLL on `BoolEvaluate`, this fork provides the soundness/completeness bridge, Waring provides the algebraic generalization layer

---

## Teammate Contributions

| Teammate | Angle | Status | Key Contribution |
|----------|-------|--------|-----------------|
| A | Current `Atom → Prop` design | Completed | Documented 7 structural reasons Prop is required; Curry-Howard, canonical model, architectural uniformity |
| B | Alternative approaches | Completed | Confirmed FormalizedFormalLogic uses identical design; corrected GHA to HeytingAlgebra; found `Equiv.propEquivBool` |
| C | Critic (all positions) | Completed | Identified GHA lacks `⊥` (verified via `lean_run_code`); showed "portability" is convenience not substance |
| D | Strategic horizons | Completed | Three-tier architecture framing; collaborative response strategy; confirmed all 4 logic levels use `→ Prop` |

---

## References

- CSLib `Semantics/Basic.lean`: `Valuation` and `Evaluate` definitions
- CSLib `Metalogic/StrongCompleteness.lean`: `canonicalValuation` construction
- CSLib `Semantics/Kripke.lean`: Kripke models with `World → Atom → Prop`
- FormalizedFormalLogic Foundation: `Boolean.Valuation (α) := α → Prop` (identical design)
- Mathlib `HeytingAlgebra` / `BooleanAlgebra` hierarchy
- Harrison, J. "Handbook of Practical Logic and Automated Reasoning" (OCaml `atom -> bool`)
- Mathlib `Equiv.propEquivBool`: classical isomorphism between `Prop` and `Bool`
