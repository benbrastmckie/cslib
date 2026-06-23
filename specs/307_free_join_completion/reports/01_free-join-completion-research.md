# Research Report: Free Join Completion (Brouwerian Semilattice to Heyting Algebra)

## Task 307 — Free Join Completion

### Executive Summary

The free join completion of a `BrouwerianSemilattice B` is realized by the lattice of
lower sets `LowerSet B`, which already has a `HeytingAlgebra` instance in Mathlib (via
`CompletelyDistribLattice`). The principal downset embedding `LowerSet.Iic : B → LowerSet B`
preserves `⊓` (Mathlib), `⊤` (Mathlib), and `⇨` (new, proved in this research). The
embedding lemma for or-bot-free formulas follows by structural induction.

**Key finding**: Mathlib provides almost everything needed. The main new content is:
1. `Iic_himp` (preservation of `⇨`)
2. The commutation lemma (structural induction on or-bot-free formulas)
3. The embedding lemma (consequence of the commutation lemma)

### 1. Construction: LowerSet B

**Definition**: For a `BrouwerianSemilattice B`, the free join completion is
`LowerSet B` — the type of downward-closed subsets of `B`, ordered by inclusion.

**Why LowerSet (not WithBot or Order.Ideal)**:
- `WithBot B` only adds `⊥` but not `⊔`. A `BrouwerianSemilattice` has no joins, so
  `WithBot B` would still lack joins and cannot form a `HeytingAlgebra`.
- `Order.Ideal B` (directed downward-closed subsets) is too restrictive — we want all
  downward-closed subsets to get the full frame structure.
- `LowerSet B` provides the complete Heyting algebra structure via unions (joins),
  intersections (meets), and the frame implication.

**Mathlib instances already available on `LowerSet B`**:

| Instance | Source File |
|----------|------------|
| `CompletelyDistribLattice (LowerSet α)` | `Mathlib.Order.UpperLower.CompleteLattice` |
| `CompleteLattice (LowerSet α)` | (from above) |
| `HeytingAlgebra (LowerSet α)` | `Mathlib.Order.CompleteBooleanAlgebra` (via `CompletelyDistribLattice.toBiheytingAlgebra`) |
| `PartialOrder (LowerSet α)` | `Mathlib.Order.UpperLower.CompleteLattice` |

**Verified via `inferInstance`**: `HeytingAlgebra (LowerSet Nat)` synthesizes successfully.

### 2. Embedding: LowerSet.Iic

**Definition**: `LowerSet.Iic : α → LowerSet α` maps `a` to the principal downset
`↓a = {x | x ≤ a}`.

**Type**: `{α : Type*} → [Preorder α] → α → LowerSet α`

**Existing Mathlib lemmas**:

| Lemma | Statement |
|-------|-----------|
| `LowerSet.mem_Iic_iff` | `b ∈ LowerSet.Iic a ↔ b ≤ a` |
| `LowerSet.Iic_inf` | `LowerSet.Iic (a ⊓ b) = LowerSet.Iic a ⊓ LowerSet.Iic b` |
| `LowerSet.Iic_top` | `LowerSet.Iic ⊤ = ⊤` |
| `LowerSet.Iic_injective` | `Function.Injective LowerSet.Iic` (for `PartialOrder`) |
| `LowerSet.iicInfHom` | Bundled `InfHom α (LowerSet α)` |

**Missing (to be proved in task)**:

| Lemma | Statement |
|-------|-----------|
| `Iic_himp` | `LowerSet.Iic (a ⇨ b) = LowerSet.Iic a ⇨ LowerSet.Iic b` |

### 3. Proof of Iic_himp (Key New Result)

**Theorem**: For `[BrouwerianSemilattice B]` and `a b : B`:
```
LowerSet.Iic (a ⇨ b) = LowerSet.Iic a ⇨ LowerSet.Iic b
```

**Proof strategy** (verified — compiles in Lean):

**(≤) direction**: By `le_himp_iff` on `LowerSet`, it suffices to show
`Iic (a ⇨ b) ⊓ Iic a ≤ Iic b`. Rewrite via `← Iic_inf` to get
`Iic ((a ⇨ b) ⊓ a) ≤ Iic b`, which follows from `himp_inf_le` in `BrouwerianSemilattice`
(or `BrouwerianSemilattice.himp_inf_le`) and monotonicity of `Iic`.

**(≥) direction**: For `x ∈ (Iic a ⇨ Iic b)`, show `x ≤ a ⇨ b`. By the
`BrouwerianSemilattice` adjunction, this is equivalent to `x ⊓ a ≤ b`. Since `Iic a ⇨ Iic b`
is a lower set and contains `x`, it also contains `x ⊓ a` (because `x ⊓ a ≤ x`). Also
`x ⊓ a ∈ Iic a` (because `x ⊓ a ≤ a`). Then `himp_inf_le` on `LowerSet` gives
`x ⊓ a ∈ Iic b`, i.e., `x ⊓ a ≤ b`.

**Proof (complete, verified)**:
```lean
theorem Iic_himp {B : Type*} [BrouwerianSemilattice B] (a b : B) :
    LowerSet.Iic (a ⇨ b) = LowerSet.Iic a ⇨ LowerSet.Iic b := by
  apply le_antisymm
  · rw [le_himp_iff, ← LowerSet.Iic_inf]
    intro x hx
    exact LowerSet.mem_Iic_iff.mpr
      (le_trans (LowerSet.mem_Iic_iff.mp hx) BrouwerianSemilattice.himp_inf_le)
  · intro x hx
    refine LowerSet.mem_Iic_iff.mpr
      ((BrouwerianSemilattice.le_himp_iff x a b).mpr ?_)
    have hxa : x ⊓ a ∈ (LowerSet.Iic a ⇨ LowerSet.Iic b : LowerSet B) :=
      (LowerSet.Iic a ⇨ LowerSet.Iic b).lower inf_le_left hx
    have hxa_in_a : x ⊓ a ∈ LowerSet.Iic a :=
      LowerSet.mem_Iic_iff.mpr inf_le_right
    exact LowerSet.mem_Iic_iff.mp
      (himp_inf_le (α := LowerSet B) ⟨hxa, hxa_in_a⟩)
```

### 4. Commutation Lemma

**Theorem**: For `[BrouwerianSemilattice B]`, `v : Atom → B`, and `φ : Proposition Atom`
with `φ.IsOrBotFree = true`:
```
AlgEvaluate (LowerSet.Iic ∘ v) ⊥ φ = LowerSet.Iic (BrouwerianEvaluate v φ)
```

**Proof**: Structural induction on `φ`, using `IsOrBotFree` to eliminate `bot` and `or` cases.
- `atom x`: definitional equality
- `imp a b`: by IH + `Iic_himp`
- `and a b`: by IH + `LowerSet.Iic_inf`
- `bot`, `or`: impossible (contradicts `IsOrBotFree`)

**Verified — compiles in Lean.**

### 5. Embedding Lemma

**Theorem**: For `[BrouwerianSemilattice B]`, `v : Atom → B`, and `φ : Proposition Atom`
with `φ.IsOrBotFree = true`:
```
BrouwerianEvaluate v φ = ⊤ ↔ AlgEvaluate (LowerSet.Iic ∘ v) ⊥ φ = ⊤
```

**Proof**: From the commutation lemma:
- (→): If `BrouwerianEvaluate v φ = ⊤`, then `AlgEvaluate ... = Iic ⊤ = ⊤` (by `Iic_top`).
- (←): If `AlgEvaluate ... = ⊤`, then `Iic (BrouwerianEvaluate v φ) = ⊤`, so
  `BrouwerianEvaluate v φ = ⊤` (by `Iic_injective` + `Iic_top`).

**Verified — compiles in Lean.**

### 6. Required Imports

```lean
import Cslib.Init
public import Cslib.Logics.Propositional.Semantics.Algebra
public import Cslib.Logics.Propositional.Semantics.Algebra.Brouwerian
public import Cslib.Logics.Propositional.Semantics.Algebra.FragmentPredicates
public import Mathlib.Order.UpperLower.CompleteLattice
public import Mathlib.Order.UpperLower.Principal
public import Mathlib.Order.CompleteBooleanAlgebra
```

Note: `Mathlib.Order.CompleteBooleanAlgebra` is needed for `CompletelyDistribLattice` which
provides `HeytingAlgebra` on `LowerSet`. The `FragmentPredicates` import provides `IsOrBotFree`.

### 7. File Structure

**File**: `Cslib/Logics/Propositional/Semantics/Algebra/FreeJoinCompletion.lean`

```
Section 1: Iic Preservation Lemmas
  - Iic_himp : Iic (a ⇨ b) = Iic a ⇨ Iic b
  - Iic_eq_top_iff : Iic x = ⊤ ↔ x = ⊤  (helper)

Section 2: Commutation Lemma
  - iic_BrouwerianEvaluate_eq_AlgEvaluate : commutation for or-bot-free formulas

Section 3: Embedding Lemma
  - brouwerian_embedding_lemma : BrouwerianEvaluate v φ = ⊤ ↔ AlgEvaluate (Iic ∘ v) ⊥ φ = ⊤
```

### 8. Proof Complexity Assessment

| Component | Difficulty | Lines (est.) | Notes |
|-----------|-----------|-------------|-------|
| Iic_himp | Medium | 15-20 | Key new result; proof verified |
| Iic_eq_top_iff | Easy | 5 | Helper from Iic_injective + Iic_top |
| Commutation lemma | Easy | 15-20 | Structural induction, uses Iic_himp + Iic_inf |
| Embedding lemma | Easy | 5-10 | Direct from commutation + Iic_eq_top_iff |
| File boilerplate | - | 30-40 | Imports, module docstring, section docstrings |
| **Total** | **Easy-Medium** | **70-90** | All proofs already verified |

### 9. Reuse Check Results

| Concept | Checked | Result |
|---------|---------|--------|
| `HeytingAlgebra (LowerSet α)` | Mathlib | Available via `CompletelyDistribLattice` |
| `LowerSet.Iic` | Mathlib | Available in `Mathlib.Order.UpperLower.Principal` |
| `LowerSet.Iic_inf` | Mathlib | Available |
| `LowerSet.Iic_top` | Mathlib | Available |
| `LowerSet.Iic_injective` | Mathlib | Available |
| `LowerSet.Iic_himp` | Mathlib | **NOT available** — must prove |
| `BrouwerianSemilattice` | CSLib | Available in `Cslib.Foundations.Order.BrouwerianSemilattice` |
| `BrouwerianEvaluate` | CSLib | Available in `Cslib.Logics.Propositional.Semantics.Algebra.Brouwerian` |
| `AlgEvaluate` | CSLib | Available in `Cslib.Logics.Propositional.Semantics.Algebra` |
| `IsOrBotFree` | CSLib | Available in `Cslib.Logics.Propositional.Semantics.Algebra.FragmentPredicates` |
| `coe_AlgEvaluate_orBotFree` | CSLib | Available but **NOT directly usable** (requires both algebras to be GHA) |

### 10. Risk Assessment and Blockers

**No blockers identified.** All proofs have been verified in Lean during this research.

**Risks**:
- **Low**: Import management — need to ensure `Mathlib.Order.CompleteBooleanAlgebra` doesn't
  transitively conflict with existing imports. Mitigated by the fact that it's a standard
  Mathlib import.
- **Low**: The `CompletelyDistribLattice → HeytingAlgebra` chain may produce a non-definitionally
  simple `⇨` on `LowerSet`, but the proof only uses `le_himp_iff` abstractly, so this is not
  an issue.

### 11. Alternative Approaches Considered

1. **WithBot construction**: Cannot work because `BrouwerianSemilattice` lacks `⊔`, so
   `WithBot B` would not be a lattice (let alone a Heyting algebra).

2. **Order.Ideal construction**: `Order.Ideal` adds a directedness condition that is unnecessary
   and would complicate the proof. `LowerSet` is the standard and simpler choice.

3. **Reuse of `coe_AlgEvaluate_orBotFree`**: This morphism lemma from FragmentPredicates requires
   both source and target to be `GeneralizedHeytingAlgebra`. Since `B` is only a
   `BrouwerianSemilattice`, we cannot use it. The direct induction proof is cleaner.

4. **Custom Heyting algebra construction**: Building `HImp` on a custom type manually. Unnecessary
   since Mathlib already provides `HeytingAlgebra` on `LowerSet` via `CompletelyDistribLattice`.

### 12. Relationship to Task 308

Task 308 proves "IPL is conservative over IPL⟨∧,→,⊤⟩". It uses the embedding lemma from this
task to bridge Brouwerian-validity and HA-validity:

- If `φ` is or-bot-free and HA-valid, then for any `BrouwerianSemilattice B` and valuation `v`:
  `AlgEvaluate (Iic ∘ v) ⊥ φ = ⊤` (since `LowerSet B` is a Heyting algebra).
  By the embedding lemma, `BrouwerianEvaluate v φ = ⊤`. Since `B` and `v` were arbitrary,
  `φ` is Brouwerian-valid.

This is the algebraic backbone of the conservative extension theorem.

### 13. Tactic Survey

| Tactic | Applicable? | Where |
|--------|-------------|-------|
| `le_antisymm` | Yes | Core of `Iic_himp` proof |
| `le_himp_iff` (rewrite) | Yes | Both directions of `Iic_himp` |
| `LowerSet.Iic_inf` (rewrite) | Yes | `Iic_himp` forward direction |
| `LowerSet.mem_Iic_iff` | Yes | Throughout, for membership characterization |
| `simp` | Yes | `IsOrBotFree` case analysis in induction |
| `rfl` | Yes | Atom case of commutation lemma |
| `exact` / `refine` | Yes | All proofs |
| No `sorry` needed | - | All proofs verified |
